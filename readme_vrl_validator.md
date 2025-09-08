VRL Validator (Rust)

This crate implements the runtime validator and checker for the Verified Repair Layer (VRL).
It mirrors the invariants and repair primitives defined in Coq, but runs on actual filesystem snapshots.

Features

Snapshot model (FSStateSnap, Inode)

Checkers:

check_block_range (all inode blocks < total_blocks)

check_bitmap_soundness (used blocks must be marked in bitmap)

check_unique_ownership (no two inodes share the same block)

RepairAction:

FixBitmap primitive

Validator:

validate_action ensures FixBitmap preconditions are met

CLI:

Load a JSON snapshot, run all invariants, propose and validate repairs

Building

Install Rust toolchain (cargo + rustc):

rustc --version
cargo --version


Clone and build:

cd vrl_validator
cargo build --release

Usage

Prepare a snapshot JSON file (snapshot.json).

Run the CLI:

cargo run --release -- snapshot.json


Output example:

Checking invariants...
Block range: ✅
Bitmap soundness: ❌
Unique ownership: ❌

Proposed repair: FixBitmap
After repair:
Block range: ✅
Bitmap soundness: ✅
Unique ownership: ❌

How it connects to Coq

Invariants mirror inv_block_range, inv_bitmap_soundness, inv_unique_ownership.

FixBitmap corresponds to the Coq primitive fix_bitmap.

Behavior: fixes bitmap soundness only; does not resolve duplicate ownership (as expected).
