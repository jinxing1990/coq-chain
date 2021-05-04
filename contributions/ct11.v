Require Import ct10 ct09 ct06 ct02.

Lemma sort_ind_case : forall (a a0 : nat) (l' l x : list nat), 
  sorted (a0 :: l') -> permutation (a0 :: l') l 
  -> sorted x -> permutation x (a :: l')
  -> {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.
Proof.
intros; destruct (le_lt_dec a a0).
- exists (a :: a0 :: l'); split; constructor; auto.
- exists (a0 :: x); split.
  + eapply inserted_sorted; eassumption.
  + eapply perm_tail_cross; eassumption.
Defined.

Lemma sort_prog_IH : forall (a : nat) (l l' : list nat),
  sorted l' -> permutation l' l -> 
  {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.
Proof.
intros; revert l H H0; induction l'; intros.
- apply perm_nil_sort_cons; eassumption.
- destruct (IHl' l'); clear IHl'.
  + inversion H; eassumption.
  + apply Permutation_refl.
  + destruct a1; eapply sort_ind_case; eassumption.
Defined.

Lemma isort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
induction l.
- apply sort_prog_base.
- destruct IHl; destruct a0; eapply sort_prog_IH; eassumption.
Defined.

(*---------------------------------Extraction---------------------------------*)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
(* Suppose all the packages above are embedded in some trans *)

Extraction Language OCaml.
Set Extraction AccessOpaque.

Definition insert_prog (a : nat) (l : list nat) := sort_prog_IH a l l.

Extraction "extraction/insert.ml" insert_prog.
Extraction "extraction/isort.ml" isort_prog.
