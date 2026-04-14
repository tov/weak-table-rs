//! Internal utility functions.

use crate::compat::*;

/// Use `hash_builder` to compute the hash of `value`.
///
/// (We provide this because [`BuildHasher::hash_one`] is not available at our MSRV.)
pub(crate) fn hash_one<H: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, value: &H) -> u64 {
    let mut hasher = hash_builder.build_hasher();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Given a reference to an array, returns an array of references,
/// such that the `i`'th in the result is a reference to `array[i]`.
///
/// This is a replacement for [`array::each_ref`],
/// which is not available at our MSRV.
/// (It was introduced in Rust 1.77.)
///
/// [`array::each_ref`]: https://doc.rust-lang.org/std/primitive.array.html#method.each_ref
pub(crate) fn each_ref<T, const N: usize>(array: &[T; N]) -> [&T; N] {
    if N == 0 {
        // We have to special-case N == 0 because of our non-use of MaybeUninit below.
        return vec![]
            .try_into()
            .map_err(|_vec| ())
            .expect("Unable to construct empty array!");
    }

    // We use this initializer to avoid MaybeUninit;
    // nothing else in this crate requires unsafe and it seems prudent to keep
    // it that way.
    // With any luck, the compiler will optimize this sensibly.
    // (In my experiments, it appears to do so.)
    let mut refs = [&array[0]; N];
    for i in 0..N {
        refs[i] = &array[i];
    }

    refs

    /*
    This is roughly how the unsafe version would look like at our MSRV:

    {
        use crate::compat::mem::MaybeUninit;

        let mut refs: [MaybeUninit<&T>; N] = [MaybeUninit::uninit(); N];
        for i in 0..N {
            refs[i].write(&array[i]);
        }

        refs.map(|r| unsafe { r.assume_init() })
    }
    */
}

#[cfg(test)]
mod test {
    use crate::compat::sync::Arc;

    use super::each_ref;

    #[test]
    fn check_each_ref() {
        let abc = [Arc::new(1), Arc::new(2), Arc::new(3)];
        let abc_ref: [&Arc<_>; 3] = each_ref(&abc);
        for (x, y) in abc.iter().zip(abc_ref) {
            assert!(Arc::ptr_eq(x, y));
        }

        let empty: [u32; 0] = [];
        let _empty_ref: [&u32; 0] = each_ref(&empty);
    }
}
