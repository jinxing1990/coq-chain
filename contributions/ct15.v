Require Import ct13.

Lemma permutation_merge_concat : forall (l1 l2 : list nat),
  permutation (merge l1 l2) (l1 ++ l2).
Proof.
induction l1.
- destruct l2; apply Permutation_refl.
- induction l2.
  + rewrite app_nil_r; apply Permutation_refl.
  + simpl merge; destruct (le_lt_dec a a0).
    * simpl; constructor; firstorder.
    * apply Permutation_cons_app, IHl2.
Defined.