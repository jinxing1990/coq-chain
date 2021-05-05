Require Export ct08.

Conjecture permutation_merge_concat : forall (l1 l2 : list nat),
  permutation (merge l1 l2) (l1 ++ l2).

Conjecture permutation_split : forall (l : list nat),
  permutation (fst (split nat l) ++ snd (split nat l)) l.

Lemma merge_permutation : forall (l l1 l2 : list nat),
  permutation l1 (fst (split nat l)) -> permutation l2 (snd (split nat l)) 
  -> permutation (merge l1 l2) l.
Proof.
intros; rewrite permutation_merge_concat, H, H0; apply permutation_split.
Qed.