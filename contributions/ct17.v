Require Export ct13 ct16.

From Hammer Require Import Hammer.

Lemma permutation_split : forall (l : list nat),
  permutation (fst (split nat l) ++ snd (split nat l)) l.
Proof.
div_conq_pair; intros; simpl; try (repeat constructor).
destruct (split nat l); simpl in *; constructor; 
apply Permutation_sym,Permutation_cons_app, Permutation_sym; auto.
Defined.