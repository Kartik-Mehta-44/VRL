Lemma In_remove_duplicates :
  forall (l : list nat) (x : nat),
    In x (remove_duplicates l) -> In x l.
Proof.
  induction l as [| y ys IH]; simpl; intros x Hin.
  - contradiction.
  - destruct (existsb (Nat.eqb y) ys) eqn:E.
    + right. apply IH. assumption.
    + destruct Hin as [Hx | Hin].
      * subst. auto.
      * right. apply IH. assumption.
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
  apply set_many_true_sets; try assumption.
  rewrite Hlen. apply Hrange. apply In_remove_duplicates. exact Hin.
Qed.
