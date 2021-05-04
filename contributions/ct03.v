Require Export ct01.

Conjecture perm_nil_sort_cons : forall (a : nat) (l :list nat), 
  permutation [] l -> {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.

Conjecture sort_ind_case : forall (a a0 : nat) (l' l x : list nat), 
  sorted (a0 :: l') -> permutation (a0 :: l') l 
  -> sorted x -> permutation x (a :: l')
  -> {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.

Lemma sort_prog_IH : forall (a : nat) (l l' : list nat),
  sorted l' -> permutation l' l -> 
  {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.
Proof.
intros; revert l H H0; induction l'; intros.
- apply perm_nil_sort_cons; eassumption.
- destruct (IHl' l'); clear IHl'.
  + inversion H; eassumption.
  + apply Permutation_refl.
  + destruct a1; eapply sort_ind_case; eassumption.
Qed.