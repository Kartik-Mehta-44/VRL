// src/lib.rs
//! Minimal Rust mirror of Coq boolean checkers and a validate_action stub.
//! Keep this logic in sync with Coq's checkers.

use serde::{Deserialize, Serialize};
use anyhow::Result;

pub type BlockId = usize;
pub type InodeId = usize;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Inode {
    pub inode_blocks: Vec<BlockId>,
    pub inode_size: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FSStateSnap {
    pub total_blocks: usize,
    pub bitmap: Vec<bool>,
    pub inodes: Vec<(InodeId, Inode)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RepairAction {
    FixBitmap,
}

/// helper: collect blocks_of_inodes
fn blocks_of_inodes(inodes: &[(InodeId, Inode)]) -> Vec<usize> {
    let mut out = Vec::new();
    for (_id, inode) in inodes {
        out.extend(inode.inode_blocks.iter().cloned());
    }
    out
}

/// check_block_range: all blocks < total_blocks
pub fn check_block_range(s: &FSStateSnap) -> bool {
    let all = blocks_of_inodes(&s.inodes);
    all.into_iter().all(|x| x < s.total_blocks)
}

/// check_bitmap_soundness: every used block is true in bitmap
pub fn check_bitmap_soundness(s: &FSStateSnap) -> bool {
    let mut used = blocks_of_inodes(&s.inodes);
    used.sort_unstable();
    used.dedup();
    for b in used {
        if b >= s.bitmap.len() { return false; }
        if !s.bitmap[b] { return false; }
    }
    true
}

/// check_unique_ownership: no duplicate block assignments across inodes
pub fn check_unique_ownership(s: &FSStateSnap) -> bool {
    let mut all = blocks_of_inodes(&s.inodes);
    if all.is_empty() { return true; }
    all.sort_unstable();
    for i in 1..all.len() {
        if all[i] == all[i-1] { return false; }
    }
    true
}

/// simulate the FixBitmap repair and validate invariants on the result.
pub fn validate_action(s: &FSStateSnap, act: &RepairAction) -> Result<bool> {
    match act {
        RepairAction::FixBitmap => {
            let mut bm = s.bitmap.clone();
            // make sure bitmap has length total_blocks (Coq assumption)
            if bm.len() < s.total_blocks {
                bm.resize(s.total_blocks, false);
            }
            let mut used = blocks_of_inodes(&s.inodes);
            used.sort_unstable();
            used.dedup();
            for b in used {
                if b < bm.len() {
                    bm[b] = true;
                }
            }
            let s2 = FSStateSnap {
                total_blocks: s.total_blocks,
                bitmap: bm,
                inodes: s.inodes.clone(),
            };
            Ok(check_block_range(&s2) && check_bitmap_soundness(&s2) && check_unique_ownership(&s2))
        }
    }
}
