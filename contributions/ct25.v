Require Import ct24.

Section PermSplitPivot.

Variable A : Type.
Variable le: A -> A -> Prop.
Variable le_dec: forall (x y: A), {le x y} + {~le x y}.
Implicit Type l : list A.

Lemma Permutation_split_pivot: forall (a : A) l,
  Permutation (fst (split_pivot A le le_dec a l) 
    ++ snd (split_pivot A le le_dec a l)) l.
Proof.
induction l; simpl; auto.
destruct (split_pivot A le le_dec a l); simpl in *.
destruct (le_dec a0 a); simpl; auto;
rewrite <- Permutation_middle; constructor; auto.
Defined.

End PermSplitPivot.

Lemma permutation_split_pivot : forall (a : nat) (l : list nat),
  Permutation (fst (split_pivot nat le le_dec a l) 
    ++ snd (split_pivot nat le le_dec a l)) l.
Proof.
apply Permutation_split_pivot.
Defined.