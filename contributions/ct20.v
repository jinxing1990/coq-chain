Require Import ct12 ct15 ct19.

Lemma pair_merge_prog : forall (a1 a2 : nat) (l l' l'0 : list nat),
  sorted l' -> permutation l' l -> 
  sorted l'0 -> permutation l'0 [a1; a2] ->
  {l'1 : list nat | sorted l'1 /\ permutation l'1 (a1 :: a2 :: l)}.
Proof.
intros; exists (merge l'0 l'); split.
- apply merge_sorted; auto.
- rewrite permutation_merge_concat, H0, H2; simpl; repeat constructor; auto.
Defined.