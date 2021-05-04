Require Import ct01.

From Hammer Require Import Hammer.

Lemma sort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof. (* try hammer. *) Abort.

Lemma sort_prog_base : {l' : list nat | sorted l' /\ permutation l' []}.
Proof. try hammer. Defined.

Lemma sort_prog_IH : forall (a : nat) (l x : list nat), 
  sorted x -> permutation x l
  -> {l' : list nat | sorted l' /\ permutation l' (a :: l)}.
Proof. (* try hammer. *) Abort.