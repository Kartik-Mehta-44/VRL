// planner/src/main.rs
use anyhow::Result;
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::path::PathBuf;

/* -----------------------------
   CLI
   ----------------------------- */
#[derive(Parser)]
#[command(name = "vrl", author, version, about = "Verified Repair Layer CLI")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Dump filesystem snapshot to JSON (stub)
    Inspect {
        #[arg(short, long)]
        image: PathBuf,
        #[arg(short, long)]
        out: PathBuf,
    },

    /// Compute a repair plan from diagnostics (Week 3)
    Plan {
        #[arg(short, long)]
        diagnostic: PathBuf,
        #[arg(short, long)]
        out: PathBuf,
    },

    /// Apply plan to image (atomic per-action with undo log)
    Apply {
        #[arg(short, long)]
        image: PathBuf,
        #[arg(short, long)]
        plan: PathBuf,
        #[arg(long)]
        undo: Option<PathBuf>,
    },

    /// Diagnose a snapshot.json and write diagnostic.json
    Diagnose {
        #[arg(short, long)]
        snapshot: PathBuf,
        #[arg(short, long)]
        out: PathBuf,
    },
}

/* -----------------------------
   Snapshot & Diagnostic types
   ----------------------------- */
#[derive(Serialize, Deserialize, Debug, Clone)]
struct Snapshot {
    superblock: Superblock,
    block_groups: Vec<BlockGroup>,
    inodes: Vec<Inode>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Superblock {
    block_size: u64,
    blocks_count: u64,
    inodes_count: u64,
    blocks_per_group: u64,
    inodes_per_group: u64,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct BlockGroup {
    group_index: u64,
    block_start: u64,
    block_bitmap: Vec<bool>, // true = allocated
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Inode {
    inode: u64,
    link_count: u64,
    blocks: Vec<u64>, // list of block numbers
}

#[derive(Serialize, Deserialize, Debug)]
struct Diagnostic {
    referenced_but_free: Vec<u64>,
    allocated_but_unreferenced: Vec<u64>,
    duplicate_block_owners: Vec<DuplicateOwner>,
    referenced_count: usize,
    allocated_count: usize,
}

#[derive(Serialize, Deserialize, Debug)]
struct DuplicateOwner {
    block: u64,
    owners: Vec<u64>,
}

/* -----------------------------
   Plan types
   ----------------------------- */
#[derive(Serialize, Deserialize, Debug)]
struct Plan {
    actions: Vec<Action>,
    total_cost: u64,
    notes: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(tag = "kind")]
enum Action {
    FlipBitmap { block: u64, set: bool, cost: u64, justification: String },
    RemoveBlockRef { block: u64, from_inode: u64, cost: u64, justification: String },
    AddBlockRef { block: u64, to_inode: u64, cost: u64, justification: String },
}

/* -----------------------------
   Main
   ----------------------------- */
fn main() -> Result<()> {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Inspect { image, out } => {
            println!("INSPECT stub. image={:?} out={:?}", image, out);
            create_sample_snapshot(out)?;
            println!("Sample snapshot created at {:?}", out);
        }
        Commands::Plan { diagnostic, out } => {
            println!("PLAN running: diagnostic={:?} -> out={:?}", diagnostic, out);
            let f = File::open(diagnostic)?;
            let diag: Diagnostic = serde_json::from_reader(f)?;
            let sf = File::open("experiments/snap.json")?;
            let mut snap: Snapshot = serde_json::from_reader(sf)?;
            let plan = generate_plan(&mut snap, &diag)?;
            let outf = File::create(out)?;
            serde_json::to_writer_pretty(outf, &plan)?;
            println!("Plan written to {:?}", out);
        }
        Commands::Apply { image, plan, undo } => {
            println!("APPLY running: image={:?} plan={:?} undo={:?}", image, plan, undo);
            let planf = File::open(plan)?;
            let plan: Plan = serde_json::from_reader(planf)?;

            let mut imgf = File::open(image)?;
            let mut snapshot: Snapshot = serde_json::from_reader(&mut imgf)?;

            let mut undo_actions: Vec<Action> = Vec::new();
            let mut current_diag = compute_diagnose_from_snapshot(&snapshot);

            for action in &plan.actions {
                println!("Applying action: {:?}", action);

                let inverse = compute_inverse_action(&snapshot, action)?;
                apply_action_mut(&mut snapshot, action)?;

                let post_diag = compute_diagnose_from_snapshot(&snapshot);

                if is_acceptible_change(&current_diag, &post_diag) {
                    undo_actions.push(inverse);
                    current_diag = post_diag;
                } else {
                    println!("Action caused worse diagnostics — reverting action");
                    apply_action_mut(&mut snapshot, &inverse)?;
                    if let Some(undo_path) = undo {
                        write_undo_log(undo_path, &undo_actions)?;
                    }
                    let mut f = File::create(image)?;
                    serde_json::to_writer_pretty(&mut f, &snapshot)?;
                    anyhow::bail!("Apply aborted: regression detected; undo log written");
                }
            }

            let mut f = File::create(image)?;
            serde_json::to_writer_pretty(&mut f, &snapshot)?;
            println!("Wrote updated image snapshot to {:?}", image);

            if let Some(undo_path) = undo {
                write_undo_log(undo_path, &undo_actions)?;
                println!("Undo log written to {:?}", undo_path);
            } else {
                println!("No undo path provided; skipping undo log write.");
            }
        }
        Commands::Diagnose { snapshot, out } => {
            println!("DIAGNOSE running: snapshot={:?} -> out={:?}", snapshot, out);
            run_diagnose(snapshot, out)?;
            println!("Diagnostic written to {:?}", out);
        }
    }

    Ok(())
}

/* -----------------------------
   Sample Snapshot Generator
   ----------------------------- */
fn create_sample_snapshot(out: &std::path::Path) -> Result<()> {
    let snap = Snapshot {
        superblock: Superblock {
            block_size: 4096,
            blocks_count: 1024,
            inodes_count: 128,
            blocks_per_group: 1024,
            inodes_per_group: 128,
        },
        block_groups: vec![BlockGroup {
            group_index: 0,
            block_start: 0,
            block_bitmap: vec![false, true, true, false, false, false, true],
        }],
        inodes: vec![
            Inode { inode: 2, link_count: 1, blocks: vec![1, 2] },
            Inode { inode: 3, link_count: 1, blocks: vec![4] },
            Inode { inode: 5, link_count: 1, blocks: vec![2, 6] },
        ],
    };

    let f = File::create(out)?;
    serde_json::to_writer_pretty(f, &snap)?;
    Ok(())
}

/* -----------------------------
   Diagnose Implementation
   ----------------------------- */
fn run_diagnose(snapshot_path: &std::path::Path, out_path: &std::path::Path) -> Result<()> {
    let f = File::open(snapshot_path)?;
    let snap: Snapshot = serde_json::from_reader(f)?;
    let diag = compute_diagnose_from_snapshot(&snap);
    let outf = File::create(out_path)?;
    serde_json::to_writer_pretty(outf, &diag)?;
    Ok(())
}

fn compute_diagnose_from_snapshot(snap: &Snapshot) -> Diagnostic {
    let mut referenced: HashSet<u64> = HashSet::new();
    for ino in &snap.inodes {
        for &b in &ino.blocks {
            referenced.insert(b);
        }
    }

    let mut allocated: HashSet<u64> = HashSet::new();
    for bg in &snap.block_groups {
        for (i, &bit) in bg.block_bitmap.iter().enumerate() {
            if bit {
                allocated.insert(bg.block_start + i as u64);
            }
        }
    }

    let mut owners: HashMap<u64, Vec<u64>> = HashMap::new();
    for ino in &snap.inodes {
        for &b in &ino.blocks {
            owners.entry(b).or_default().push(ino.inode);
        }
    }

    Diagnostic {
        referenced_but_free: referenced.difference(&allocated).cloned().collect(),
        allocated_but_unreferenced: allocated.difference(&referenced).cloned().collect(),
        duplicate_block_owners: owners
            .into_iter()
            .filter(|(_, v)| v.len() > 1)
            .map(|(block, owners)| DuplicateOwner { block, owners })
            .collect(),
        referenced_count: referenced.len(),
        allocated_count: allocated.len(),
    }
}

/* -----------------------------
   Planner Implementation
   ----------------------------- */
fn generate_plan(snapshot: &mut Snapshot, diag: &Diagnostic) -> Result<Plan> {
    let mut actions = Vec::new();
    let mut total_cost = 0;

    for &blk in &diag.referenced_but_free {
        actions.push(Action::FlipBitmap {
            block: blk,
            set: true,
            cost: 1,
            justification: format!("Referenced but free: fix bitmap for block {}", blk),
        });
        total_cost += 1;
        set_bitmap_for_block(snapshot, blk, true)?;
    }

    for &blk in &diag.allocated_but_unreferenced {
        actions.push(Action::FlipBitmap {
            block: blk,
            set: false,
            cost: 1,
            justification: format!("Allocated but unreferenced: free block {}", blk),
        });
        total_cost += 1;
        set_bitmap_for_block(snapshot, blk, false)?;
    }

    for dup in &diag.duplicate_block_owners {
        let keep = dup.owners.iter().min().cloned().unwrap();
        for &owner in &dup.owners {
            if owner != keep {
                actions.push(Action::RemoveBlockRef {
                    block: dup.block,
                    from_inode: owner,
                    cost: 5,
                    justification: format!("Duplicate block {}: remove from inode {}", dup.block, owner),
                });
                total_cost += 5;
                remove_block_from_inode(snapshot, owner, dup.block)?;
            }
        }
    }

    Ok(Plan {
        actions,
        total_cost,
        notes: "greedy planner v0.1".to_string(),
    })
}

/* -----------------------------
   Apply helpers
   ----------------------------- */
fn compute_inverse_action(_snapshot: &Snapshot, action: &Action) -> Result<Action> {
    match action {
        Action::FlipBitmap { block, set, .. } => Ok(Action::FlipBitmap {
            block: *block,
            set: !*set,
            cost: 1,
            justification: format!("undo FlipBitmap for block {}", block),
        }),
        Action::RemoveBlockRef { block, from_inode, .. } => Ok(Action::AddBlockRef {
            block: *block,
            to_inode: *from_inode,
            cost: 5,
            justification: format!("undo RemoveBlockRef: re-add block {} to inode {}", block, from_inode),
        }),
        Action::AddBlockRef { block, to_inode, .. } => Ok(Action::RemoveBlockRef {
            block: *block,
            from_inode: *to_inode,
            cost: 5,
            justification: format!("undo AddBlockRef: remove block {} from inode {}", block, to_inode),
        }),
    }
}

fn apply_action_mut(snapshot: &mut Snapshot, action: &Action) -> Result<()> {
    match action {
        Action::FlipBitmap { block, set, .. } => set_bitmap_for_block(snapshot, *block, *set),
        Action::RemoveBlockRef { block, from_inode, .. } => remove_block_from_inode(snapshot, *from_inode, *block),
        Action::AddBlockRef { block, to_inode, .. } => add_block_to_inode(snapshot, *to_inode, *block),
    }
}

fn write_undo_log(path: &PathBuf, undo_actions: &Vec<Action>) -> Result<()> {
    let f = File::create(path)?;
    serde_json::to_writer_pretty(f, undo_actions)?;
    Ok(())
}

/* -----------------------------
   Helpers to mutate snapshot
   ----------------------------- */
fn set_bitmap_for_block(snapshot: &mut Snapshot, block: u64, value: bool) -> Result<()> {
    for bg in &mut snapshot.block_groups {
        if block >= bg.block_start && block < bg.block_start + (bg.block_bitmap.len() as u64) {
            let idx = (block - bg.block_start) as usize;
            bg.block_bitmap[idx] = value;
            return Ok(());
        }
    }
    anyhow::bail!("block {} not in any block group", block);
}

fn remove_block_from_inode(snapshot: &mut Snapshot, inode_num: u64, block: u64) -> Result<()> {
    for ino in &mut snapshot.inodes {
        if ino.inode == inode_num {
            let before = ino.blocks.len();
            ino.blocks.retain(|&b| b != block);
            if ino.blocks.len() == before {
                anyhow::bail!("block {} not found in inode {}", block, inode_num);
            }
            return Ok(());
        }
    }
    anyhow::bail!("inode {} not found", inode_num);
}

fn add_block_to_inode(snapshot: &mut Snapshot, inode_num: u64, block: u64) -> Result<()> {
    for ino in &mut snapshot.inodes {
        if ino.inode == inode_num {
            if !ino.blocks.contains(&block) {
                ino.blocks.push(block);
            }
            return Ok(());
        }
    }
    anyhow::bail!("inode {} not found", inode_num);
}

/* -----------------------------
   Acceptability check
   ----------------------------- */
fn violation_score(diag: &Diagnostic) -> usize {
    diag.referenced_but_free.len() + diag.allocated_but_unreferenced.len() + diag.duplicate_block_owners.len()
}

fn is_acceptible_change(before: &Diagnostic, after: &Diagnostic) -> bool {
    violation_score(after) <= violation_score(before)
}
