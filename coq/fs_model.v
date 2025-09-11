(* coq/fs_model.v
   Minimal VRL filesystem model: BlockId, Inode, Bitmap, FSState,
   boolean checkers to mirror into Rust/OCaml.
*)

From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

(* Basic ids *)
Definition BlockId := nat.
Definition InodeId := nat.

Record Inode := {
  inode_blocks : list BlockId;
  inode_size : nat
}.

Definition Bitmap := list bool.

Record FSState := {
  total_blocks : nat;
  bitmap : Bitmap;
  inodes : list (InodeId * Inode)
}.

(* --- helpers ------------------------------------------------------------- *)

Fixpoint nth_default_bool (d : bool) (l : list bool) (n : nat) : bool :=
  match l, n with
  | [], _ => d
  | b :: _, 0 => b
  | _ :: tl, S n' => nth_default_bool d tl n'
  end.

Definition bitmap_get (bm : Bitmap) (b : BlockId) : bool :=
  nth_default_bool false bm b.

Fixpoint blocks_of_inodes (xs : list (InodeId * Inode)) : list BlockId :=
  match xs with
  | [] => []
  | (_, inode) :: tl => inode_blocks inode ++ blocks_of_inodes tl
  end.

(* remove_duplicates: returns a list where later duplicates are removed *)
Fixpoint remove_duplicates (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
      if existsb (Nat.eqb x) xs then remove_duplicates xs else x :: remove_duplicates xs
  end.

Definition used_blocks (s : FSState) : list BlockId :=
  remove_duplicates (blocks_of_inodes (inodes s)).

(* --- boolean checkers (for extraction / mirroring) ------------------------ *)

Fixpoint all_blocks_lt (n : nat) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => if x <? n then all_blocks_lt n xs else false
  end.

Definition check_block_range (s : FSState) : bool :=
  all_blocks_lt (total_blocks s) (blocks_of_inodes (inodes s)).

Fixpoint no_dup_bool (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => if existsb (Nat.eqb x) xs then false else no_dup_bool xs
  end.

Definition check_unique_ownership (s : FSState) : bool :=
  no_dup_bool (blocks_of_inodes (inodes s)).

Fixpoint check_bitmap_soundness_aux (bm : Bitmap) (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      if x <? length bm
      then andb (bitmap_get bm x) (check_bitmap_soundness_aux bm xs)
      else false
  end.

Definition check_bitmap_soundness (s : FSState) : bool :=
  check_bitmap_soundness_aux (bitmap s) (remove_duplicates (blocks_of_inodes (inodes s))).

(* --- Prop invariants ---------------------------------------------------- *)

(* 1) bitmap soundness: every used block is marked true in bitmap *)
Definition inv_bitmap_soundness (s : FSState) : Prop :=
  forall b, In b (used_blocks s) -> bitmap_get (bitmap s) b = true.

(* 2) unique ownership: blocks assigned at most once *)
Definition inv_unique_ownership (s : FSState) : Prop :=
  NoDup (blocks_of_inodes (inodes s)).

(* 3) block range: every block id in inodes is < total_blocks *)
Definition inv_block_range (s : FSState) : Prop :=
  forall b, In b (blocks_of_inodes (inodes s)) -> b < total_blocks s.
