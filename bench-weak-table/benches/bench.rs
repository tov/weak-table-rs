
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion, Throughput};
use std::collections::VecDeque;
use std::rc::{Rc, Weak};
use weak_table::WeakHashSet;

fn insert_and_expire_init(size: usize) -> (WeakHashSet<Weak<usize>>, VecDeque<Rc<usize>>) {
    let mut weak: WeakHashSet<Weak<usize>> = Default::default();
    let mut strong: VecDeque<Rc<usize>> = Default::default();

    for val in 0..size {
        let rc = Rc::new(val);
        strong.push_back(rc.clone());
        weak.insert(rc);
    }

    (weak, strong)
}

// Insert `elements` elements into a WeakHashSet,
// removing elements as necessary to keep the size to `size`.
fn insert_and_expire(
    weak: &mut WeakHashSet<Weak<usize>>,
    strong: &mut VecDeque<Rc<usize>>,
    size: usize,
    elements: usize,
) {
    for val in size..elements {
        let rc = Rc::new(val);
        strong.push_back(rc.clone());
        weak.insert(rc);
        strong.pop_front();
    }
}

fn lookup_init(size: usize) -> (WeakHashSet<Weak<usize>>, Vec<Rc<usize>>) {
    let strong: Vec<Rc<usize>> = (0..size).map(Rc::new).collect();
    let weak: WeakHashSet<Weak<usize>> = strong.iter().cloned().collect();
    (weak, strong)
}

fn lookup(set: &WeakHashSet<Weak<usize>>, max: usize) {
    let mut x = 0_usize;
    for n in 0..max {
        x += set.contains(&n) as usize;
    }
    black_box(x);
}

fn bench_insert_and_expire(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert-and-expire");
    for size in [50, 500, 5000, 50000] {
        let n: usize = size * 30;
        //group.measurement_time(Duration::new(15, 0));
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(format!("Size={size}, N={n}"), &size, |b, sz| {
            b.iter_batched(
                || insert_and_expire_init(*sz),
                |(mut w, mut s)| insert_and_expire(&mut w, &mut s, *sz, n),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

fn bench_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("lookup");
    for size in [50, 500, 5000, 50000] {
        let max = size * 3;
        group.throughput(Throughput::Elements(max as u64));
        group.bench_with_input(format!("Size={size}, N={max}"), &size, |b, sz| {
            b.iter_batched(
                || lookup_init(*sz),
                |(set, _strong)| lookup(&set, max),
                BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(hashset, bench_insert_and_expire, bench_lookup);
criterion_main!(hashset);
