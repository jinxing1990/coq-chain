Require Export ct12 ct15 ct23.

Conjecture permutation_split_pivot : forall (a : nat) (l : list nat),
  Permutation (fst (split_pivot nat le le_dec a l) 
    ++ snd (split_pivot nat le le_dec a l)) l.

Lemma sort_prog_split_pivot : forall (a : nat) (l l' l'0: list nat),
     sorted l' -> permutation l' (snd (split_pivot nat le le_dec a l))
  -> sorted l'0 -> permutation l'0 (fst (split_pivot nat le le_dec a l))
  -> {l'1 : list nat | sorted l'1 /\ permutation l'1 (a :: l)}.
Proof.
intros; exists (merge l'0 (a :: l')); split.
+ apply merge_sorted; auto; constructor; auto.
  assert (Forall (le a) l').
  eapply Permutation_Forall. apply Permutation_sym; apply H0.
  apply Forall_snd_split_pivot; intros; 
  apply not_le, gt_le_S,le_Sn_le in H3; auto.
  inversion H3; auto.
+ rewrite permutation_merge_concat, <- Permutation_middle; constructor;
  rewrite H0, H2; apply permutation_split_pivot.
Qed.