Require Export ct00 ct02 ct04.

Conjecture sort_prog_one : forall a : nat, 
  {l' : list nat | sorted l' /\ permutation l' [a]}.

Conjecture sort_prog_split : forall (ls l' l'0: list nat),
  sorted l'0 -> permutation l'0 (fst (split nat ls))
  -> sorted l' -> permutation l' (snd (split nat ls))
  -> {l'1 : list nat | sorted l'1 /\ permutation l'1 ls}.

Lemma sort_prog : forall (l : list nat), 
  {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
div_conq_split. 
- apply sort_prog_base.
- apply sort_prog_one.
- intros; destruct H; destruct a; destruct H0; destruct a; 
  eapply sort_prog_split. exact H. eassumption. exact H0. eassumption.
Qed.