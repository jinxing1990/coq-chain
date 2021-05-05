Require Import ct12 ct13.

From Hammer Require Import Hammer.

Lemma HdRel_merge_snd_cons : forall (a a0 : nat) (l1 l2 : list nat),
  sorted (a :: l1) -> sorted (a0 :: l2) -> a <= a0
  -> HdRel le a (merge l1 (a0 :: l2)).
Proof. try hammer. Defined.

Lemma sorted_merge_cons : forall (a a0 : nat) (l1 l2 : list nat),
  (sorted (a :: l1) -> sorted l2 -> sorted (merge (a :: l1) l2))
 -> sorted (a :: l1) -> sorted (a0 :: l2)
  -> sorted (merge (a :: l1) l2).
Proof. try hammer. Defined.

Lemma HdRel_merge_fst_cons : forall (a a0 : nat) (l1 l2 : list nat),
  (sorted (a :: l1) -> sorted l2 -> sorted (merge (a :: l1) l2))
  -> sorted (a :: l1) -> sorted (a0 :: l2) -> a0 < a
  -> HdRel le a0 (merge (a :: l1) l2).
Proof. try hammer. Defined.

Lemma permutation_merge_concat : forall (l1 l2 : list nat),
  permutation (merge l1 l2) (l1 ++ l2).
Proof. (* try hammer. *) Abort.

Lemma permutation_split : forall (l : list nat),
  permutation (fst (split nat l) ++ snd (split nat l)) l.
Proof. (* try hammer. *) Abort.