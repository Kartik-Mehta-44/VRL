# VRL Proofs

This document summarizes the current state of formal verification for the Verified Repair Layer (VRL). It lists invariants and repair primitives, marks which ones are fully proven in Coq, and highlights assumptions and limitations. It also records the CI status for reproducibility.

## 📂 Files

**fs_model.v**
Defines core types: BlockId, InodeId, Inode, Bitmap, FSState.

**invariants.v**
Encodes three invariants:

1. inv_bitmap_soundness: Every block referenced by an inode is marked allocated in the bitmap.

2. inv_unique_ownership: No two inodes reference the same block.

3. inv_block_range: All inode blocks fall within [0, total_blocks).

**fix_bitmap.v**
Defines the repair primitive FixBitmap:

Sets bitmap bits for all inode-referenced blocks.

Leaves inodes unchanged.

## ✅ Invariants

| Invariant                  | Description                                     | Proof Status                                                 |
| -------------------------- | ----------------------------------------------- | ------------------------------------------------------------ |
| **inv\_block\_range**      | All inode block IDs are within valid range.     | **Fully proven in Coq**                                      |
| **inv\_bitmap\_soundness** | Bitmap matches set of blocks used by inodes.    | **Fully proven (via FixBitmap)**                             |
| **inv\_unique\_ownership** | No block is referenced by two different inodes. | **Defined, but not proven** (not needed for FixBitmap proof) |

## 🔧 Repair Primitives
| Primitive                 | Description                                                       | Proof Status                                                                                                                                   |
| ------------------------- | ----------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| **FixBitmap**             | Reconciles bitmap with inode usage.                               | **Fully proven**: <br/>- `fix_bitmap_preserves_inodes` <br/>- `fix_bitmap_preserves_used_blocks` <br/>- `fix_bitmap_restores_bitmap_soundness` |
| **ResolveDuplicateBlock** | Handle case where two inodes share a block (clone or lost+found). | **Not specified in Coq yet**                                                                                                                   |
| **RestoreInodeLinks**     | Correct inconsistent link counts.                                 | **Not specified in Coq yet**                                                                                                                   |
| **ReplayJournal**         | Apply pending journal operations.                                 | **Not modeled in Coq**                                                                                                                         |
| **ClearInode**            | Free a corrupted inode (destructive).                             | **Not modeled in Coq**                                                                                                                         |

## ⚖️ Assumptions & Limitations

Scope restricted to metadata (superblock, inodes, bitmap).

File content recovery is out of scope (no reconstruction beyond metadata consistency).

Journal not modeled in current proofs.

Only FixBitmap is fully proven. Other repair primitives are defined or planned but not formally proven.

Unique ownership invariant is specified but not proven for FixBitmap (not required, since FixBitmap does not modify inode block sets).

All Coq proofs are carried out in Coq 8.19, no Admitted used.

## 🔄 CI / Reproducibility

GitHub Actions CI pipeline configured:

1. Coq job: compiles fs_model.v, invariants.v, fix_bitmap.v.

2. Rust job: builds and tests vrl_validator (Rust validator stub + CLI).

✅ Both jobs pass (green check).

This ensures proofs and validator build are reproducible on every commit.
