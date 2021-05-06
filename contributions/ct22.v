Require Export ct16.

Section DivConq.

Variable A : Type.
Variable le: A -> A -> Prop.
Variable le_dec: forall (x y: A), {le x y} + {~le x y}.
Implicit Type l : list A.

(* split_pivot:= 
 * takes an input term as pivot and list l and split into two sublists where the
 * first sublist contains all element/s that is/are le_dec _ pivot and the
 * second sublist contains the rest of the element/s. 
 *)

Fixpoint split_pivot (pivot : A) l : list A * list A :=
  match l with
  | nil => (nil, nil)
  | a :: l' => let (l1, l2) := (split_pivot pivot l') in
    if le_dec a pivot 
    then (a :: l1, l2) else (l1, a :: l2)
  end.


(* split_pivot_wf:
 * states that for any list ls, each of the sublists generated has length less
 * than or equal to its original list's.
 *)

Lemma split_pivot_wf1 : forall a l, length (fst (split_pivot a l)) <= length l.
Proof.
induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l); 
simpl in *; auto; apply le_n_S; auto.
Defined.

Lemma split_pivot_wf2 : forall a l, length (snd (split_pivot a l)) <= length l.
Proof.
induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l); 
simpl in *; auto; apply le_n_S; auto.
Defined.


(* div_conq_pivot:
 * - another variation of div_conq_split, just that for this, it will use 
 *   split_pivot instead.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
 *   following:
 *   1. P holds for empty list, nil.
 *   2. If P hold fst(split_pivot a l) and snd(split_pivot a l), then P must
 *      also hold for (a :: l).
 *)

Theorem div_conq_pivot : 
  forall (P : list A -> Type),
    P nil
    -> (forall a l, P (fst (split_pivot a l)) -> P (snd (split_pivot a l)) 
      -> P (a :: l))
    -> forall l, P l.
Proof.
intros; eapply well_founded_induction_type. eapply lengthOrder_wf.
destruct x; intros; auto; apply X0; apply X1; apply le_lt_n_Sm.
apply split_pivot_wf1. apply split_pivot_wf2.
Defined.



Hypothesis notle_le: forall x y, ~ le x y -> le y x.


(* Forall_snd_split_pivot:
 * le a x for every element, x, in snd(split_pivot a l).
 *)

Lemma Forall_snd_split_pivot : forall a l, Forall (le a) (snd(split_pivot a l)).
Proof.
induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l);
simpl in *; auto.
Defined.

End DivConq.

Ltac div_conq_pivot := eapply div_conq_pivot.