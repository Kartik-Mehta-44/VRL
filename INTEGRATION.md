# VRL Integration

This document explains how the Coq proofs (formal side) correspond to the Rust validator (runtime side). It serves as the bridge between the verified model and the executable CLI.

## 📂 State Representation
| Concept          | Coq (fs\_model.v) | Rust (lib.rs)        |
| ---------------- | ----------------- | -------------------- |
| Block identifier | `nat` (`BlockId`) | `usize` (`BlockId`)  |
| Inode identifier | `nat` (`InodeId`) | `usize` (`InodeId`)  |
| Inode            | `Record Inode`    | `struct Inode`       |
| Bitmap           | `list bool`       | `Vec<bool>`          |
| FS state         | `Record FSState`  | `struct FSStateSnap` |

Both sides model:

total_blocks

bitmap

inodes

## 🔒 Invariants
| Invariant            | Coq (invariants.v)     | Rust (lib.rs)            | Status                                                    |
| -------------------- | ---------------------- | ------------------------ | --------------------------------------------------------- |
| Block range validity | `inv_block_range`      | `check_block_range`      | ✅ Proven in Coq, implemented in Rust                      |
| Bitmap soundness     | `inv_bitmap_soundness` | `check_bitmap_soundness` | ✅ Proven in Coq, implemented in Rust                      |
| Unique ownership     | `inv_unique_ownership` | `check_unique_ownership` | ⚠️ Defined but not proven in Coq (checker exists in Rust) |


Coq: Encodes invariants as Prop and proves lemmas about them.

Rust: Implements checkers as boolean functions (true/false).

## 🛠️ Repair Primitives
| Concept   | Coq (fix\_bitmap.v)                    | Rust (validate\_action)       | Status                            |
| --------- | -------------------------------------- | ----------------------------- | --------------------------------- |
| Repair    | `fix_bitmap` function                  | `RepairAction::FixBitmap`     | Implemented                       |
| Guarantee | `fix_bitmap_restores_bitmap_soundness` | Applies same logic concretely | ✅ Proven in Coq, mirrored in Rust |


Coq: Proves fix_bitmap restores bitmap soundness without changing inodes.

Rust: Replays the same logic concretely on snapshots.

Key difference:

Coq gives mathematical proof.

Rust provides executable enforcement, but not proofs.

## 🔄 Validator Flow

Input: Snapshot (snapshot.json or FFI from ext4 dumper).

Checks: Run check_block_range, check_bitmap_soundness, check_unique_ownership.

If failure: Propose FixBitmap.

Apply repair: Update bitmap accordingly.

Re-check invariants.

## 📌 Current Status

All three invariants defined in Coq.

Proven in Coq:

inv_block_range

inv_bitmap_soundness

fix_bitmap primitive

Rust validator: Implements all 3 checkers + validate_action(FixBitmap).

CLI tested with sample snapshots: behavior matches Coq design (FixBitmap repairs bitmap soundness but does not fix unique ownership).

CI/CD:

  GitHub Actions runs Coq proofs (coqc fs_model.v invariants.v fix_bitmap.v).

  Rust validator builds + runs unit tests.

✅ Both jobs passing.

## ⚖️ Assumptions & Limitations

Bitmap length = total_blocks (checked before applying fix).

Ext4 parsing code (future work) must ensure snapshot consistency.

Rust validator does not enforce proof obligations — it mirrors Coq logic.

Only FixBitmap is proven in Coq.

Other repairs (resolve_duplicate_block, restore_inode_links, replay_journal) are not yet specified/proven.

Journal semantics are currently out of scope.
