pub fn new_boxed_option_slice<T>(size: usize) -> Box<[Option<T>]> {
    let mut vector = Vec::with_capacity(size);
    for _ in 0 .. size {
        vector.push(None)
    }
    vector.into_boxed_slice()
}
