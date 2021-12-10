From sorting Require Export Utils.
From sorting Require Export Sorted.


Fixpoint insert (i : nat) (l : list nat) := 
  match l with
  | nil => i::nil
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
 end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => insert h (insertion_sort t)
  end.

Definition insertion_sort_correct : Prop :=
  is_a_sorting_algorithm insertion_sort.


Lemma insert_perm:
  forall (x : nat) (l : list nat), Permutation (x::l) (insert x l).
Proof.
  induction l. {
    auto.
  } {
    simpl.
    bdestruct (x <=? a). {
      auto.
    } {
      induction l. {
        simpl.
        apply perm_swap.
      } {
        apply perm_trans with (a :: x :: a0 :: l).
        apply perm_swap.
        apply perm_skip.
        apply IHl.
      }
    }
  }
Qed.

Theorem sort_perm:
  forall (l : list nat), Permutation l (insertion_sort l).
Proof.
  intros.
  induction l. {
    auto.
  } {
    simpl.
    induction IHl. {
      auto.
    } {
      simpl.
      bdestruct (a <=? x). {
        auto.
      } {
        apply perm_trans with (x :: a :: l).
        apply perm_swap.
        auto.
      }
    } {
      simpl.
      bdestruct (a <=? y);
      bdestruct (a <=? x). {
        apply perm_skip.
        apply perm_swap.
      } {
        apply perm_trans with (a :: x :: y :: l).
        apply perm_skip.
        apply perm_swap.
        apply perm_swap.
      } {
        apply perm_skip.
        apply perm_swap.
      } {
        apply perm_trans with (a :: x :: y :: l).
        apply perm_skip.
        apply perm_swap.
        apply perm_trans with (x :: a :: y :: l).
        apply perm_swap.
        apply perm_skip.
        apply perm_trans with (y :: a :: l).
        apply perm_swap.
        apply perm_skip.
        apply insert_perm.
      }
    } {
      assert (Permutation (a :: l') (insert a l')).
      apply insert_perm.
      assert (Permutation (a :: l) (a :: l')).
      apply perm_skip.
      apply IHl1.
      apply perm_trans with (a :: l');
      auto.
    }
  }
Qed.


(** * Insertion of a element in a sorted list **)

Lemma insert_sorted:
  forall (a : nat) (l : list nat), sorted l -> sorted (insert a l).
Proof.
  intros.
  induction H. {
   simpl.
   apply sorted_1.
  } {
    simpl.
    bdestruct (a <=? x). {
      apply sorted_cons.
      trivial.
      apply sorted_1.
    } {
      apply sorted_cons.
      omega.
      apply sorted_1.
    }
  } {
    simpl.
    bdestruct (a <=? x);
    bdestruct (a <=? y);
    apply sorted_cons;
    try omega;
    try apply sorted_cons;
    try omega;
    try apply H0.
    simpl in IHsorted.
    bdestruct (a <=? y). {
      omega.
    } {
      trivial.
    }
  }
Qed.


(** * A list applied with insertion sort is sorted **)

Theorem sort_sorted:
  forall (l : list nat), sorted (insertion_sort l).
Proof.
  intros.
  induction l. {
    simpl.
    apply sorted_nil.
  } {
    simpl.
    apply insert_sorted.
    trivial.
  }
Qed.


Theorem insertion_sort_is_correct:
  insertion_sort_correct.
Proof.
  split.
  apply sort_perm.
  apply sort_sorted.
Qed.
