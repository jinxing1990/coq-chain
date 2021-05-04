Require Export ct05.

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if (le_lt_dec a1 a2) then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.

Conjecture merge_sorted : forall (l1 l2 : list nat),
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).

Conjecture merge_permutation : forall (l l1 l2 : list nat),
  permutation l1 (fst (split nat l)) -> permutation l2 (snd (split nat l)) 
  -> permutation (merge l1 l2) l.

Lemma sort_prog_split : forall (ls l' l'0: list nat),
  sorted l'0 -> permutation l'0 (fst (split nat ls))
  -> sorted l' -> permutation l' (snd (split nat ls))
  -> {l'1 : list nat | sorted l'1 /\ permutation l'1 ls}.
Proof.
intros; exists (merge l'0 l'); split.
  + apply merge_sorted; eassumption.
  + apply merge_permutation; eassumption.
Qed.