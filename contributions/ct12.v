Require Export ct08.

Conjecture HdRel_merge_snd_cons : forall (a a0 : nat) (l1 l2 : list nat),
  sorted (a :: l1) -> sorted (a0 :: l2) -> a <= a0
  -> HdRel le a (merge l1 (a0 :: l2)).

Conjecture sorted_merge_cons : forall (a a0 : nat) (l1 l2 : list nat),
  (sorted (a :: l1) -> sorted l2 -> sorted (merge (a :: l1) l2))
 -> sorted (a :: l1) -> sorted (a0 :: l2)
  -> sorted (merge (a :: l1) l2).

Conjecture HdRel_merge_fst_cons : forall (a a0 : nat) (l1 l2 : list nat),
  (sorted (a :: l1) -> sorted l2 -> sorted (merge (a :: l1) l2))
  -> sorted (a :: l1) -> sorted (a0 :: l2) -> a0 < a
  -> HdRel le a0 (merge (a :: l1) l2).

Lemma merge_sorted : forall (l1 l2 : list nat),
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
induction l1; induction l2; intros; simpl; auto.
destruct (le_lt_dec a a0).
- constructor. apply IHl1; inversion H; auto. apply HdRel_merge_snd_cons; auto.
- constructor. eapply sorted_merge_cons; eassumption. 
  apply HdRel_merge_fst_cons; auto.
Qed.