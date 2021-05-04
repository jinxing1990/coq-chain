Require Export ct00.

Conjecture sort_prog_base : {l' : list nat | sorted l' /\ permutation l' []}.

Conjecture sort_prog_IH : forall (a : nat) (l x : list nat), 
  sorted x -> permutation x l
  -> {l' : list nat | sorted l' /\ permutation l' (a :: l)}.

Lemma sort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
induction l.
- apply sort_prog_base.
- destruct IHl; destruct a0; eapply sort_prog_IH; eassumption.
Qed.