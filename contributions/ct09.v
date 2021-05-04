Require Import ct07 ct08.

From Hammer Require Import Hammer.

Lemma inserted_sorted : forall (a0 a : nat) (l' x : list nat),
  sorted (a0 :: l') -> sorted x -> permutation x (a :: l') -> a0 < a -> 
  sorted (a0 :: x).
Proof. (* try hammer. *) Abort.

Lemma perm_tail_cross : forall (a a0 : nat) (l l' x : list nat),
  permutation (a0 :: l') l -> permutation x (a :: l')
  -> permutation (a0 :: x) (a :: l).
Proof. try hammer. Defined.

Lemma merge_sorted : forall (l1 l2 : list nat),
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof. (* try hammer. *) Abort.

Lemma merge_permutation : forall (l l1 l2 : list nat),
  permutation l1 (fst (split nat l)) -> permutation l2 (snd (split nat l)) 
  -> permutation (merge l1 l2) l.
Proof. (* try hammer. *) Abort.