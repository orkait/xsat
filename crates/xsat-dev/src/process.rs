use std::{
    io,
    os::unix::process::{CommandExt as _, ExitStatusExt as _},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc::{self, RecvTimeoutError},
    },
    thread,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

#[derive(Debug)]
pub(crate) struct Ran {
    pub(crate) code: i32,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
}

fn drained(mut from: impl io::Read + Send + 'static) -> thread::JoinHandle<io::Result<Vec<u8>>> {
    thread::spawn(move || {
        let mut bytes = Vec::new();
        from.read_to_end(&mut bytes)?;
        Ok(bytes)
    })
}

fn joined(reader: Option<thread::JoinHandle<io::Result<Vec<u8>>>>) -> io::Result<Vec<u8>> {
    reader.map_or_else(
        || Ok(Vec::new()),
        |reader| {
            reader
                .join()
                .map_err(|_| io::Error::other("an output reader died"))?
        },
    )
}

pub(crate) fn run(command: &mut Command, deadline: Duration) -> io::Result<Option<Ran>> {
    let mut child = command
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let stdout = child.stdout.take().map(drained);
    let stderr = child.stderr.take().map(drained);
    let group = format!("-{}", child.id());
    let (done, finished) = mpsc::channel::<()>();
    let watchdog = thread::spawn(move || {
        finished.recv_timeout(deadline) == Err(RecvTimeoutError::Timeout)
            && Command::new("kill")
                .args(["-KILL", "--", &group])
                .status()
                .is_ok()
    });
    let status = child.wait();
    let _ = done.send(());
    let overran = watchdog.join().unwrap_or(true);
    let (stdout, stderr) = (joined(stdout)?, joined(stderr)?);
    if overran {
        return Ok(None);
    }
    let status = status?;
    let code = status
        .code()
        .or_else(|| status.signal().map(|signal| -signal))
        .unwrap_or_default();
    Ok(Some(Ran {
        code,
        stdout,
        stderr,
    }))
}

#[derive(Debug)]
pub(crate) struct TempDir(PathBuf);

impl TempDir {
    pub(crate) fn new(tag: &str) -> io::Result<TempDir> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!("{tag}-{}-{now}", std::process::id()));
        std::fs::create_dir(&dir)?;
        Ok(TempDir(dir))
    }

    pub(crate) fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

pub(crate) fn parallel<T: Sync, R: Send>(
    items: &[T],
    jobs: usize,
    work: impl Fn(&T) -> R + Sync,
) -> io::Result<Vec<R>> {
    let next = AtomicUsize::new(0);
    let mut results: Vec<(usize, R)> = thread::scope(|scope| {
        let workers: Vec<_> = (0..jobs.max(1))
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let at = next.fetch_add(1, Ordering::Relaxed);
                        let Some(item) = items.get(at) else {
                            return done;
                        };
                        done.push((at, work(item)));
                    }
                })
            })
            .collect();
        let mut all = Vec::new();
        for worker in workers {
            all.extend(
                worker
                    .join()
                    .map_err(|_| io::Error::other("a worker died"))?,
            );
        }
        Ok::<_, io::Error>(all)
    })?;
    results.sort_by_key(|(at, _)| *at);
    Ok(results.into_iter().map(|(_, result)| result).collect())
}
