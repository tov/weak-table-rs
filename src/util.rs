use crate::compat::*;

pub(crate) fn hash_one<H: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, value: &H) -> u64 {
    let mut hasher = hash_builder.build_hasher();
    value.hash(&mut hasher);
    hasher.finish()
}
