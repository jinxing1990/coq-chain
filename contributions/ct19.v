Require Export ct00 ct02 ct06 ct16.

Conjecture sort_prog_pair : forall (a1 a2 : nat) (l l' l'0 : list nat),
  sorted l' -> permutation l' l -> 
  sorted l'0 -> permutation l'0 [a1; a2] ->
  {l'1 : list nat | sorted l'1 /\ permutation l'1 (a1 :: a2 :: l)}.

Lemma sort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
div_conq_pair.
- apply sort_prog_base.
- apply sort_prog_one.
- intros; destruct (le_lt_dec a1 a2).
  + exists [a1; a2]; split; repeat constructor; auto.
  + exists [a2; a1]; split; repeat constructor; apply Nat.lt_le_incl; auto.
- intros; destruct H,H0,a,a0; 
  eapply sort_prog_pair. apply H1. auto. apply H. auto.
Qed.