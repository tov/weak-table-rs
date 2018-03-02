default: build
hard: test

CRATE = weak_table
REPO  = weak-table-rs

build:
	clear
	cargo build
	make doc

clippy:
	rustup run nightly cargo build --features=clippy

doc:
	cargo doc
	echo "<meta http-equiv='refresh' content='0;url=$(CRATE)/'>" > target/doc/index.html

test:
	clear
	cargo test

upload-doc:
	make doc
	ghp-import -n target/doc
	git push -f https://github.com/tov/$(REPO).git gh-pages
