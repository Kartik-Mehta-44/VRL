VRL Integration
Purpose

This document explains how the Coq proofs (formal side) correspond to the Rust validator (practical side).
It serves as a bridge between the verified model and the executable CLI.

1. State Representation
Concept	              Coq (fs_model.v)	 Rust (lib.rs)
Block identifier	nat (BlockId)	usize (BlockId)
Inode identifier	nat (InodeId)	usize (InodeId)
Inode	               Record Inode	struct Inode
Bitmap	                 list bool	Vec<bool>
FS state	       Record FSState	struct FSStateSnap

Both sides model:

total_blocks

bitmap

inodes

2. Invariants
Invariant	Coq definition (invariants.v)	Rust checker (lib.rs)
Block range	        inv_block_range	         check_block_range
Bitmap soundness	inv_bitmap_soundness	 check_bitmap_soundness
Unique ownership	inv_unique_ownership	 check_unique_ownership

Coq encodes invariants as propositions and proves lemmas.

Rust implements the same logic as boolean functions returning true/false.

3. Repair Primitive
Concept	       Coq (fix_bitmap.v)	Rust (validate_action)
Repair	        fix_bitmap function	RepairAction::FixBitmap
Guarantee	fix_bitmap_restores_bitmap_soundness proven in Coq	Reimplemented in Rust by setting bitmap bits for all used blocks

Key difference:

Coq proves that fix_bitmap restores bitmap soundness (under assumptions).

Rust replays the same logic concretely on snapshots.

Rust does not provide proofs but is designed to mirror the verified Coq semantics.

4. Validator Flow

Input: Snapshot (JSON or FFI from ext4).

Checks: Run check_block_range, check_bitmap_soundness, check_unique_ownership.

If failure: Propose FixBitmap.

Apply repair: Update bitmap accordingly.

Re-check invariants.

5. Current Status

All three invariants defined and proven in Coq.

fix_bitmap proven to restore bitmap soundness (in Coq).

Rust validator implements the same logic and passes sample tests.

Next: Add FFI to read real ext4 state into FSStateSnap.

Next: Add CI/CD to check proofs + build Rust automatically.

6. Assumptions

Bitmap length matches total_blocks (ensured before applying fix).

Ext4 parsing code (future work) must ensure snapshot consistency before running checkers.

Rust validator does not yet enforce formal proof obligations (only mirrors logic).
