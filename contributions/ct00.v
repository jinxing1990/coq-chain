Require Export Arith Sorted Permutation List. 
(* Suppose all the packages above are embedded in some blocks *)
Export List.ListNotations.
Open Scope list_scope.

Definition sorted := Sorted le.
Definition permutation := @Permutation nat.

Conjecture sort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.