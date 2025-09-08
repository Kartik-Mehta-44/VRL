 (* invariants.v
   Soundness proofs: boolean checkers => Prop invariants.
   Works with Coq 8.19 (use "From Coq" not "From Stdlib").
*)

From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import fs_model.

(* --- block-range: if check_block_range = true then inv_block_range holds --- *)

Lemma all_lt_implies_elem_lt :
  forall (limit : nat) (l : list nat) (x : nat),
    all_blocks_lt limit l = true ->
    In x l ->
    x < limit.
Proof.
  intros limit l.
  induction l as [| y ys IH]; intros x Hcheck Hin; simpl in *.
  - contradiction.
  - destruct (y <? limit) eqn:E.
    + simpl in Hcheck.
      destruct Hin as [Heq | Hin'].
      * subst. apply Nat.ltb_lt in E. assumption.
      * apply IH; assumption.
    + discriminate Hcheck.
Qed.

Lemma check_block_range_sound :
  forall s, check_block_range s = true -> inv_block_range s.
Proof.
  intros s Hcheck b HinBlocks.
  unfold check_block_range in Hcheck.
  eapply all_lt_implies_elem_lt; eauto.
Qed.

(* --- unique ownership: boolean -> NoDup ---------------------------------- *)

Lemma existsb_eqb_false_no_in :
  forall x xs,
    existsb (Nat.eqb x) xs = false ->
    ~ In x xs.
Proof.
  induction xs as [| y ys IH]; simpl; intros H.
  - congruence.
  - destruct (Nat.eqb x y) eqn:Eq.
    + apply Nat.eqb_eq in Eq. subst. simpl in H. discriminate.
    + intros [Hin | Hin].
      * subst. rewrite Nat.eqb_refl in Eq. discriminate.
      * apply IH; assumption.
Qed.

Lemma no_dup_bool_NoDup :
  forall l, no_dup_bool l = true -> NoDup l.
Proof.
  induction l as [| x xs IH]; simpl; intros H.
  - constructor.
  - destruct (existsb (Nat.eqb x) xs) eqn:E.
    + discriminate H.
    + constructor.
      * intro Hin. apply (existsb_eqb_false_no_in x xs) in E. contradiction.
      * apply IH. assumption.
Qed.

Lemma check_unique_ownership_sound :
  forall s, check_unique_ownership s = true -> inv_unique_ownership s.
Proof.
  intros s Hcheck.
  unfold check_unique_ownership in Hcheck.
  apply no_dup_bool_NoDup in Hcheck.
  exact Hcheck.
Qed.

(* --- bitmap soundness: boolean -> Prop ---------------------------------- *)

Lemma check_bitmap_soundness_aux_props :
  forall bm l x,
    check_bitmap_soundness_aux bm l = true ->
    In x l ->
    x < length bm /\ bitmap_get bm x = true.
Proof.
  induction l as [| y ys IH]; simpl; intros x Hcheck Hin.
  - contradiction.
  - destruct (y <? length bm) eqn:E.
    + simpl in Hcheck. apply andb_true_iff in Hcheck as [Hcur Hrest].
      destruct Hin as [Heq | Hin].
      * subst. split; [apply Nat.ltb_lt in E; assumption | exact Hcur].
      * apply IH; assumption.
    + discriminate Hcheck.
Qed.

Lemma check_bitmap_soundness_sound :
  forall s, check_bitmap_soundness s = true -> inv_bitmap_soundness s.
Proof.
  intros s Hcheck b HinUsed.
  unfold check_bitmap_soundness in Hcheck.
  apply check_bitmap_soundness_aux_props with
      (bm := bitmap s) (l := remove_duplicates (blocks_of_inodes (inodes s))) (x := b).
  - exact Hcheck.
  - exact HinUsed.
Qed.

