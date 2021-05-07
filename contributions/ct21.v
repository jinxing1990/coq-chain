Require Import ct00.
(* ct00 contains the original conjecture. *)

Require Import ct16.
(* ct16 contains all necessary divide-and-conquer tactics *)

Require Import ct02 ct06 ct20.
(* ct02 ct06 ct14 contains the following lemmas that are solved by the automated
 * system, CoqHammer:
 * - sort_prog_base
 * - sort_prog_one
 * - HdRel_merge_snd_cons
 * - sorted_merge_cons
 * - HdRel_merge_fst_cons
 * - sort_prog_pair
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

Lemma psort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
div_conq_pair.
- apply sort_prog_base.
- apply sort_prog_one.
- intros; destruct (le_lt_dec a1 a2).
  + exists [a1; a2]; split; repeat constructor; auto.
  + exists [a2; a1]; split; repeat constructor; apply Nat.lt_le_incl; auto.
- intros; destruct H,H0,a,a0; 
  eapply sort_prog_pair. apply H1. auto. apply H. auto.
Defined.

(*---------------------------------Extraction---------------------------------*)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
(* Suppose all the packages above are embedded in some trans *)

Extraction Language OCaml.
Set Extraction AccessOpaque.

Extraction "extraction/psort.ml" psort_prog.

(*----------------------------------------------------------------------------*)
