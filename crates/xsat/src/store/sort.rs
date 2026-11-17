const QUICK_SORT_LIMIT: usize = 10;

fn greater_swap<T: Copy>(items: &mut [T], p: usize, q: usize, less: &impl Fn(T, T) -> bool) {
    if less(items[q], items[p]) {
        items.swap(p, q);
    }
}

fn partition<T: Copy>(
    items: &mut [T],
    low: usize,
    high: usize,
    less: &impl Fn(T, T) -> bool,
) -> usize {
    let pivot = items[high];
    let mut i = low - 1;
    let mut j = high;
    loop {
        loop {
            i += 1;
            if !less(items[i], pivot) {
                break;
            }
        }
        loop {
            j -= 1;
            if !less(pivot, items[j]) || j == low {
                break;
            }
        }
        if i >= j {
            break;
        }
        items.swap(i, j);
    }
    items.swap(i, high);
    i
}

fn quick_sort<T: Copy>(items: &mut [T], less: &impl Fn(T, T) -> bool) {
    let (mut low, mut high) = (0, items.len() - 1);
    if high - low <= QUICK_SORT_LIMIT {
        return;
    }
    let mut sorter = Vec::new();
    loop {
        let middle = low + (high - low) / 2;
        items.swap(middle, high - 1);
        greater_swap(items, low, high - 1, less);
        greater_swap(items, low, high, less);
        greater_swap(items, high - 1, high, less);
        let pivot = partition(items, low + 1, high - 1, less);
        let (other_low, other_high);
        if pivot - low < high - pivot {
            other_low = pivot + 1;
            other_high = high;
            high = pivot - 1;
        } else {
            other_low = low;
            other_high = pivot - 1;
            low = pivot + 1;
        }
        if high - low > QUICK_SORT_LIMIT {
            sorter.extend([other_low, other_high]);
        } else if other_high - other_low > QUICK_SORT_LIMIT {
            low = other_low;
            high = other_high;
        } else if let (Some(top), Some(below)) = (sorter.pop(), sorter.pop()) {
            high = top;
            low = below;
        } else {
            break;
        }
    }
}

fn insertion_sort<T: Copy>(items: &mut [T], less: &impl Fn(T, T) -> bool) {
    let n = items.len();
    for i in (1..n).rev() {
        greater_swap(items, i - 1, i, less);
    }
    for i in 2..n {
        let pivot = items[i];
        let mut j = i;
        while less(pivot, items[j - 1]) {
            items[j] = items[j - 1];
            j -= 1;
        }
        items[j] = pivot;
    }
}

pub(crate) fn sort<T: Copy>(items: &mut [T], less: impl Fn(T, T) -> bool) {
    if items.is_empty() {
        return;
    }
    quick_sort(items, &less);
    insertion_sort(items, &less);
}
