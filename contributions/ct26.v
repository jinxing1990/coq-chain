Require Import ct00.
(* ct00 contains the original conjecture. *)

Require Import ct22.
(* ct16 contains all necessary divide-and-conquer tactics *)

Require Import ct02 ct15 ct18 ct25.
(* ct02 ct15 ct18 ct25 contains the following proven lemmas:
 * - sort_prog_base
 * - permutation_merge_concat
 * - merge_sorted
 * - permutation_split_pivot
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

Lemma sort_prog_pivot : forall (a : nat) (l l' l'0: list nat),
     sorted l' -> permutation l' (snd (split_pivot nat le le_dec a l))
  -> sorted l'0 -> permutation l'0 (fst (split_pivot nat le le_dec a l))
  -> {l'1 : list nat | sorted l'1 /\ permutation l'1 (a :: l)}.
Proof.
intros; exists (merge l'0 (a :: l')); split.
+ apply merge_sorted; auto; constructor; auto.
  assert (Forall (le a) l').
  eapply Permutation_Forall. apply Permutation_sym; apply H0.
  apply Forall_snd_split_pivot; intros; 
  apply not_le, gt_le_S,le_Sn_le in H3; auto.
  inversion H3; auto.
+ rewrite permutation_merge_concat, <- Permutation_middle; constructor;
  rewrite H0, H2; apply permutation_split_pivot.
Defined.

Lemma qsort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
unshelve div_conq_pivot. exact le. exact le_dec. 
- apply sort_prog_base.
- intros; destruct H,H0,a0,a1; eapply sort_prog_pivot.
  exact H1. assumption. exact H. assumption.
Defined.

(*---------------------------------Extraction---------------------------------*)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
(* Suppose all the packages above are embedded in some trans *)

Extraction Language OCaml.
Set Extraction AccessOpaque.

Extraction "extraction/qsort.ml" qsort_prog.

(*----------------------------------------------------------------------------*)