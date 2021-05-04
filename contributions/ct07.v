Require Export ct03.

Conjecture inserted_sorted : forall (a0 a : nat) (l' x : list nat),
  sorted (a0 :: l') -> sorted x -> permutation x (a :: l') -> a0 < a -> 
  sorted (a0 :: x).

Conjecture perm_tail_cross : forall (a a0 : nat) (l l' x : list nat),
  permutation (a0 :: l') l -> permutation x (a :: l')
  -> permutation (a0 :: x) (a :: l).

Lemma sort_ind_case : forall (a a0 : nat) (l' l x : list nat), 
  sorted (a0 :: l') -> permutation (a0 :: l') l 
  -> sorted x -> permutation x (a :: l')
  -> {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.
Proof.
intros; destruct (le_lt_dec a a0).
- exists (a :: a0 :: l'); split; constructor; auto.
- exists (a0 :: x); split.
  + eapply inserted_sorted; eassumption.
  + eapply perm_tail_cross; eassumption.
Qed.