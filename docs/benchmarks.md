# Benchmarks

Wall-clock time on one X925 core of a DGX Spark (aarch64), against Kissat 4.0.4 built with gcc `-O3`, on ten SAT Competition 2025 instances with a 600 second limit, one run each, measured on 2026-11-17.

| Instance | Kissat | xsat | xsat / Kissat |
|---|---:|---:|---:|
| 1890f49a | 26.8 s | 30.0 s | 1.12 |
| a2fe3213 | 5.4 s | 5.9 s | 1.10 |
| 51482a5b | 29.0 s | 30.4 s | 1.05 |
| d88c6afc | 9.9 s | 10.1 s | 1.02 |
| 16c999d0 | 46.1 s | 49.8 s | 1.08 |
| d0298807 | 19.8 s | 20.6 s | 1.04 |
| 0876c518 | 9.0 s | 9.0 s | 0.99 |
| 7a044c99 | 566.4 s | 544.8 s | 0.96 |
| 45742d06 | timeout | timeout | |
| 90843387 | timeout | timeout | |

Geometric mean over the eight solved instances: 1.04. Both solvers run the same search, so the ratio is the cost per step.
