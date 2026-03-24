use crate::compat::*;

/// Use `hash_builder` to compute the hash of `value`.
///
/// (We provide this because [`BuildHasher::hash_one`] is not available at our MSRV.)
pub(crate) fn hash_one<H: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, value: &H) -> u64 {
    let mut hasher = hash_builder.build_hasher();
    value.hash(&mut hasher);
    hasher.finish()
}
