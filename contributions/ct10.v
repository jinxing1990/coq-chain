Require Import ct07.

Lemma inserted_sorted : forall (a0 a : nat) (l' x : list nat),
  sorted (a0 :: l') -> sorted x -> permutation x (a :: l') -> a0 < a -> 
  sorted (a0 :: x).
Proof.
intros; constructor; trivial.
- apply Sorted_extends in H.
  + assert (H3 : List.Forall (le a0) (a :: l')). 
    constructor. apply Nat.lt_le_incl; assumption. assumption.
    assert (H4 : List.Forall (le a0) x).
    eapply Permutation_Forall. apply Permutation_sym; exact H1. trivial.
    destruct x; auto. constructor. apply Forall_inv in H4; auto.
  + unfold Relations_1.Transitive; apply le_trans.
Defined.