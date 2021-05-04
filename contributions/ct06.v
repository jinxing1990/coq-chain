Require Import ct03 ct05.

From Hammer Require Import Hammer.

Lemma perm_nil_sort_cons : forall (a : nat) (l :list nat), 
  permutation [] l -> {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.
Proof. try hammer. Defined.

Lemma sort_ind_case : forall (a a0 : nat) (l' l x : list nat), 
  sorted (a0 :: l') -> permutation (a0 :: l') l 
  -> sorted x -> permutation x (a :: l')
  -> {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.
Proof. (* try hammer. *) Abort.

Lemma sort_prog_one : forall a : nat, 
  {l' : list nat | sorted l' /\ permutation l' [a]}.
Proof. try hammer. Defined.

Lemma sort_prog_split : forall (ls l' l'0: list nat),
  sorted l'0 -> permutation l'0 (fst (split nat ls))
  -> sorted l' -> permutation l' (snd (split nat ls))
  -> {l'1 : list nat | sorted l'1 /\ permutation l'1 ls}.
Proof. (* try hammer. *) Abort.