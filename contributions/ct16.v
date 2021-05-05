Require Export ct04.

Section DivConq.

Variable A : Type.
Implicit Type l : list A.

(* div_conq_pair:
 * - works similar to induction (i.e. list_rect), but instead of cutting just
 *   head of the list in each recursive step, this induction principle cut two
 *   heads of the list in each recursive step.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
 *   following:
 *   1. P holds for empty list, nil.
 *   2. P holds for one-element list, (a :: nil).
 *   3. P holds for two-elements list, (a1 :: a2 :: nil).
 *   4. If P hold (a1 :: a2 :: nil) and l, then P must also hold for
 *      (a1 :: a2 :: l).
 *)

Lemma div_conq_pair : forall (P : list A -> Type),
    P nil -> (forall (a : A), P (a :: nil))
    -> (forall (a1 a2 : A), P (a1 :: a2 :: nil))
    -> (forall (a1 a2 : A) (l : list A), P (a1 :: a2 :: nil) -> P l 
       -> P (a1 :: a2 :: l)) 
    -> forall (l : list A), P l.
Proof.
intros; eapply well_founded_induction_type. eapply lengthOrder_wf.
destruct x; auto; destruct x; auto. intros; apply X2; auto.
apply X3; unfold lengthOrder; simpl; auto.
Defined.

End DivConq.

Ltac div_conq_pair := eapply div_conq_pair.
