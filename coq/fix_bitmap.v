(* fix_bitmap.v
   A simple fix_bitmap primitive and correctness lemmas.
   Works with Coq 8.19.
*)
From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import fs_model.
Require Import invariants.

(* --- bitmap update helpers --------------------------------------------- *)
Fixpoint set_bitmap_true (bm : Bitmap) (i : nat) : Bitmap :=
  match bm, i with
  | [], _ => []    (* out-of-range -> no change *)
  | _ :: tl, 0 => true :: tl
  | b :: tl, S i' => b :: set_bitmap_true tl i'
  end.

Fixpoint set_many_true (bm : Bitmap) (l : list nat) : Bitmap :=
  match l with
  | [] => bm
  | x :: xs => set_many_true (set_bitmap_true bm x) xs
  end.

(* --- repair primitive -------------------------------------------------- *)
Definition fix_bitmap (s : FSState) : FSState :=
  {| total_blocks := total_blocks s;
     bitmap := set_many_true (bitmap s) (used_blocks s);
     inodes := inodes s |}.

(* --- correctness lemmas ------------------------------------------------ *)
Lemma fix_bitmap_preserves_inodes :
  forall s, inodes (fix_bitmap s) = inodes s.
Proof. intros s; reflexivity. Qed.

Lemma fix_bitmap_preserves_used_blocks :
  forall s, used_blocks (fix_bitmap s) = used_blocks s.
Proof. intros s; reflexivity. Qed.

Lemma set_bitmap_true_nth :
  forall bm i,
    i < length bm ->
    nth_default_bool false (set_bitmap_true bm i) i = true.
Proof.
  induction bm as [| b bm' IH]; simpl; intros i Hlen.
  - lia.
  - destruct i as [| i'].
    + reflexivity.
    + simpl in Hlen. simpl. apply IH. lia.
Qed.

Lemma set_bitmap_true_length :
  forall bm i, length (set_bitmap_true bm i) = length bm.
Proof.
  induction bm as [| b bm' IH]; simpl; intros i.
  - reflexivity.
  - destruct i; simpl; rewrite ?IH; reflexivity.
Qed.

(* Helper lemma: set_bitmap_true preserves other positions *)
Lemma set_bitmap_true_nth_neq :
  forall bm i j,
    i <> j ->
    nth_default_bool false (set_bitmap_true bm i) j = nth_default_bool false bm j.
Proof.
  induction bm as [| b bm' IH]; simpl; intros i j Hneq.
  - reflexivity.
  - destruct i as [| i'], j as [| j'].
    + contradiction.
    + reflexivity.
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

(* Helper lemma: if a bit is already true, set_many_true preserves it *)
Lemma set_many_true_preserves_true :
  forall bm l i,
    i < length bm ->
    nth_default_bool false bm i = true ->
    nth_default_bool false (set_many_true bm l) i = true.
Proof.
  intros bm l. generalize dependent bm.
  induction l as [| x xs IH]; intros bm i Hlen Htrue.
  - simpl. assumption.
  - simpl. apply IH.
    + rewrite set_bitmap_true_length. assumption.
    + destruct (Nat.eq_dec i x) as [Heq | Hneq].
      * subst. apply set_bitmap_true_nth. assumption.
      * rewrite set_bitmap_true_nth_neq; [exact Htrue | apply Nat.neq_sym; exact Hneq].
Qed.

Lemma set_many_true_sets :
  forall bm l x,
    In x l ->
    x < length bm ->
    nth_default_bool false (set_many_true bm l) x = true.
Proof.
  intros bm l. generalize dependent bm.
  induction l as [| y ys IH]; intros bm x Hin Hlen.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst x. (* x = y *)
      simpl. apply set_many_true_preserves_true.
      * rewrite set_bitmap_true_length. assumption.
      * apply set_bitmap_true_nth. assumption.
    + (* x ∈ ys *)
      simpl. apply IH.
      * assumption.
      * rewrite set_bitmap_true_length. assumption.
Qed.

Lemma In_remove_duplicates :
  forall (l : list nat) (x : nat),
    In x (remove_duplicates l) -> In x l.
Proof.
  induction l as [| y ys IH]; simpl; intros x Hin.
  - contradiction.
  - destruct (existsb (Nat.eqb y) ys) eqn:E.
    + (* y is already in ys, so remove_duplicates l = remove_duplicates ys *)
      right. apply IH. assumption.
    + (* y is not in ys, so remove_duplicates l = y :: remove_duplicates ys *)
      destruct Hin as [Hx | Hin].
      * (* x = y *)
        left. assumption.
      * (* x ∈ remove_duplicates ys *)
        right. apply IH. assumption.
Qed.

Lemma fix_bitmap_restores_bitmap_soundness :
  forall s,
    length (bitmap s) = total_blocks s ->
    inv_block_range s ->
    inv_bitmap_soundness (fix_bitmap s).
Proof.
  intros s Hlen Hrange b Hin.
  unfold fix_bitmap, inv_bitmap_soundness, bitmap_get. simpl.
  rewrite fix_bitmap_preserves_used_blocks in Hin.
  apply set_many_true_sets.
  - exact Hin.
  - rewrite Hlen. apply Hrange. apply In_remove_duplicates. exact Hin.
Qed.
