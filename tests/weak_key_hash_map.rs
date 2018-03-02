extern crate weak_table;
#[macro_use]
extern crate quickcheck;

mod util;

#[test]
fn random_script() {
    quickcheck! {
        fn prop_run_script(script: util::weak_key_hash_map::Script<String, usize>) -> bool {
            true
        }
    }
}
