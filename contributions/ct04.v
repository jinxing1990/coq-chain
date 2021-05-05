Require Export Arith List.

Section DivConq.

Variable A : Type.
Implicit Type l : list A.


(* (Ordering) lengthOrder ls1 ls2 :=
 * length ls1 < length ls2
 *)

Definition lengthOrder (ls1 ls2 : list A) := length ls1 < length ls2.

Lemma lengthOrder_wf' : forall len, forall ls, 
  length ls <= len -> Acc lengthOrder ls.
Proof.
unfold lengthOrder; induction len.
- intros; rewrite Nat.le_0_r,length_zero_iff_nil in H; rewrite H; constructor;
  intros; inversion H0.
- destruct ls; constructor; simpl; intros.
  + inversion H0.
  + simpl in H; apply le_S_n in H; apply lt_n_Sm_le in H0; apply IHlen; 
    eapply Nat.le_trans; eassumption.
Defined.


(* lengthOrder_wf: 
 * states that the ordering, lengthOrder, is well founded.
 *)

Lemma lengthOrder_wf : well_founded lengthOrder.
Proof.
red; intro; eapply lengthOrder_wf'; eauto.
Defined.


(* div_conq: 
 * Suppose for some arbitrary split function, splitF, with the condition that
 * for any list l, if the length of l is at least 2, then both the sublists
 * generated have length less than the input list. To prove some proposition P
 * holds for all lists ls, one needs to prove the following:
 * 1. P holds for empty list, nil.
 * 2. P holds for one-element list, (a :: nil).
 * 3. If P hold fst(splitF ls) and snd(splitF ls), then P must also hold for ls.
 *)

Lemma div_conq : 
  forall (P : list A -> Type) 
  (splitF : list A -> list A * list A)
  (splitF_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (splitF ls)) ls)
  (splitF_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (splitF ls)) ls),
    P nil -> (forall a, P (a :: nil))
    -> (forall ls, (P (fst (splitF ls)) -> P (snd (splitF ls)) -> P ls))
    -> forall ls, P ls.
Proof.
intros; apply (well_founded_induction_type lengthOrder_wf); intros.
destruct (le_lt_dec 2 (length x)).
- apply X1; apply X2.
  + apply splitF_wf1; auto.
  + apply splitF_wf2; auto.
- destruct x; auto. simpl in l; 
  apply le_S_n, le_S_n, Nat.le_0_r,length_zero_iff_nil  in l; rewrite l; auto.
Defined.


(* split:= 
 * split an input list ls into two sublists where the first sublist contains all
 * the odd indexed element/s and the second sublist contains all the even
 * indexed element/s. 
 *)

Fixpoint split (ls : list A) : list A * list A :=
  match ls with
  | nil => (nil, nil)
  | h :: nil => (h :: nil, nil)
  | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in
        (h1 :: ls1, h2 :: ls2)
  end.


(* split_wf: 
 * states that for any list ls of length at least 2, each of the two sublists
 * generated has length less than its original list's.
 *)

Lemma split_wf : forall len ls, 2 <= length ls <= len
  -> let (ls1, ls2) := split ls in lengthOrder ls1 ls /\ lengthOrder ls2 ls.
Proof.
unfold lengthOrder; induction len; intros.
- inversion H; inversion H1; rewrite H1 in H0; inversion H0.
- destruct ls; inversion H.
  + inversion H0.
  + destruct ls; simpl; auto. 
    destruct (le_lt_dec 2 (length ls)).
    * specialize (IHlen ls); destruct (split ls); destruct IHlen; simpl.
      simpl in H1; apply le_S_n in H1; split; auto. apply le_Sn_le; auto. 
      split; rewrite <- Nat.succ_lt_mono; auto.
    * inversion l. 
      -- destruct ls; inversion H3; apply length_zero_iff_nil in H4; rewrite H4;
         simpl; auto.
      -- apply le_S_n in H3. inversion H3. 
         apply length_zero_iff_nil in H5; rewrite H5; simpl; auto.
Defined.

Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
  destruct (split ls); destruct 1; auto.

Lemma split_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (split ls)) ls.
Proof.
split_wf.
Defined.

Lemma split_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (split ls)) ls.
Proof.
split_wf.
Defined.


(* div_conq_split: 
 * - an instance of div_conq where the arbitrary splitF function
 *   is replaced by the split function defined above.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
     following:
 *   1. P holds for empty list, nil.
 *   2. P holds for one-element list, (a :: nil).
 *   3. If P hold fst(split ls) and snd(split ls), then P must also hold for ls.
 *)

Definition div_conq_split P := div_conq P split split_wf1 split_wf2.

End DivConq.

Ltac div_conq_split := eapply div_conq_split.