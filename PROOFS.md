# VRL Proofs

## Files
- `fs_model.v`: Defines BlockId, InodeId, Inode, Bitmap, FSState.
- `invariants.v`: Encodes three invariants:
  1. **inv_bitmap_soundness**: All allocated inodes’ blocks are marked in bitmap.
  2. **inv_unique_ownership**: No two inodes share the same block.
  3. **inv_block_range**: All inode blocks are within [0, total_blocks).

- `fix_bitmap.v`: Defines `fix_bitmap` repair primitive.
  - Sets bitmap bits for all used inode blocks.
  - Leaves inodes unchanged.

## Proven
- `inv_block_range` is a straightforward property (fully proven).
- `fix_bitmap_preserves_inodes`: Inodes are unchanged.
- `fix_bitmap_restores_bitmap_soundness`: After fix_bitmap, bitmap soundness holds.
- Helper lemmas for setting bits (`set_bitmap_true_nth`, `set_many_true_sets`) fully proven.

## Admitted
- None (all goals in these files are proven).
- Unique ownership invariant is defined but not proven against fix_bitmap (not needed for now).

## Notes
- Coq warnings about `From Coq` → `From Stdlib` are harmless (version change).
- Invariants are **formally checked in Coq**, not just written as comments.
