Require Export ct00 ct02 ct22.

Conjecture sort_prog_split_pivot : forall (a : nat) (l l' l'0: list nat),
     sorted l' -> permutation l' (snd (split_pivot nat le le_dec a l))
  -> sorted l'0 -> permutation l'0 (fst (split_pivot nat le le_dec a l))
  -> {l'1 : list nat | sorted l'1 /\ permutation l'1 (a :: l)}.

Lemma sort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
unshelve div_conq_pivot. exact le. exact le_dec. 
- apply sort_prog_base.
- intros; destruct H,H0,a0,a1; eapply sort_prog_split_pivot.
  exact H1. assumption. exact H. assumption.
Qed.