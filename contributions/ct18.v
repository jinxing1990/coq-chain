Require Import ct00.
(* ct00 contains the original conjecture. *)

Require Import ct16.
(* ct16 contains all necessary divide-and-conquer tactics *)

Require Import ct02 ct06 ct14 ct15 ct17.
(* ct02 ct06 ct14 contains the following lemmas that are solved by the automated
 * system, CoqHammer:
 * - sort_prog_base
 * - sort_prog_one
 * - HdRel_merge_snd_cons
 * - sorted_merge_cons
 * - HdRel_merge_fst_cons
 * - permutation_merge_concat
 * - permutation_split
 *)

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if (le_lt_dec a1 a2) then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.

Lemma merge_sorted : forall (l1 l2 : list nat),
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
induction l1; induction l2; intros; simpl; auto.
destruct (le_lt_dec a a0).
- constructor. apply IHl1; inversion H; auto. apply HdRel_merge_snd_cons; auto.
- constructor. eapply sorted_merge_cons; eassumption. 
  apply HdRel_merge_fst_cons; auto.
Defined.

Lemma merge_permutation : forall (l l1 l2 : list nat),
  permutation l1 (fst (split nat l)) -> permutation l2 (snd (split nat l)) 
  -> permutation (merge l1 l2) l.
Proof.
intros; rewrite permutation_merge_concat, H, H0; apply permutation_split.
Defined.

Lemma sort_prog_split : forall (ls l' l'0: list nat),
  sorted l'0 -> permutation l'0 (fst (split nat ls))
  -> sorted l' -> permutation l' (snd (split nat ls))
  -> {l'1 : list nat | sorted l'1 /\ permutation l'1 ls}.
Proof.
intros; exists (merge l'0 l'); split.
  + apply merge_sorted; eassumption.
  + apply merge_permutation; eassumption.
Defined.

Lemma msort_prog : forall (l : list nat), 
  {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
div_conq_split. 
- apply sort_prog_base.
- apply sort_prog_one.
- intros; destruct H; destruct a; destruct H0; destruct a; 
  eapply sort_prog_split. exact H. eassumption. exact H0. eassumption.
Defined.

(*---------------------------------Extraction---------------------------------*)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
(* Suppose all the packages above are embedded in some trans *)

Extraction Language OCaml.
Set Extraction AccessOpaque.

Extraction "extraction/merge.ml" merge.
Extraction "extraction/msort.ml" msort_prog.

(*----------------------------------------------------------------------------*)