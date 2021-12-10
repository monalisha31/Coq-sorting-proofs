From sorting Require Export Utils.
From sorting Require Export Sorted.


Fixpoint select (x : nat) (l : list nat) : nat * list nat :=
  match l with
  |  nil => (x, nil)
  |  h :: t => if x <=? h
                 then let (j, l') := select x t in (j, h :: l')
                 else let (j, l') := select h t in (j, x :: l')
  end.

Fixpoint selsort (l : list nat) (n : nat) {struct n} :=
  match l, n with
  | x :: r, S n' => let (y,r') := select x r
                 in y :: selsort r' n'
  | nil, _ => nil
  | _ :: _, O => nil
  end.

Definition selection_sort (l : list nat) :=
  selsort l (length l).


Definition selection_sort_correct : Prop :=
  is_a_sorting_algorithm selection_sort.


Lemma select_perm:
  forall (x : nat) (l : list nat),
    let (y, r) := select x l in Permutation (x :: l) (y :: r).
Proof.
  intros x l; revert x.
  induction l; intros; simpl in *. {
    apply Permutation_refl.
  } {
    unfold select.
    bdestruct (x <=? a); fold select. {
      specialize (IHl x).
      destruct (select x l) eqn:Seq.
      apply perm_trans with (a :: n :: l0). {
        apply Permutation_sym.
        apply perm_trans with (a :: x :: l). {
          now apply perm_skip.
        } {
          apply perm_swap.
        }
      } {
        apply perm_swap.
      }
    } {
      specialize (IHl a).
      destruct (select a l) eqn:Seq.
      apply perm_trans with (x :: n :: l0). {
        now apply perm_skip.
      } {
        apply perm_swap.
      }
    }
  }
Qed.

Lemma selsort_perm:
  forall (n : nat) (l : list nat), length l = n -> Permutation l (selsort l n).
Proof.
  induction n. {
    intros.
    destruct l. {
      apply perm_nil.
    } {
      inversion H.
    }
  } {
    intros.
    destruct l. {
      intros.
      inversion H.
    } {
      simpl.
      destruct (select n0 l) eqn:Seq.
      apply perm_trans with (n1 :: l0). {
        assert (let (y, r) := select n0 l in Permutation (n0 :: l) (y :: r)). {
          apply (select_perm n0 l).
        }
        destruct (select n0 l).
        inv Seq.
        apply H0.
      } {
        apply perm_skip.
        apply IHn.
        assert (length (n0::l) = (length (n1::l0))). {
          apply Permutation_length.
          assert (let (y, r) := select n0 l in Permutation (n0 :: l) (y :: r)). {
            apply (select_perm n0 l).
          }
          destruct (select n0 l).
          inv Seq.
          apply H0.
        }
        inv H0.
        inv H.
        reflexivity.
      }
    }
  }
Qed.

Theorem selection_sort_perm:
  forall (l : list nat), Permutation l (selection_sort l).
Proof.
  unfold selection_sort.
  intros.
  apply selsort_perm.
  reflexivity.
Qed.


(** *selects the smallest element of a list *)

Lemma select_smallest_aux:
  forall (x : nat) (al : list nat) (y : nat) (bl : list nat),
    Forall (fun z => y <= z) bl ->
    select x al = (y,bl) ->
    y <= x.
Proof.
  intros.
  pose (select_perm x al).
  rewrite H0 in y0.
  apply (Permutation_in x) in y0. {
    destruct y0. {
      omega.
    } {
      rewrite Forall_forall in H.
      apply H.
      apply H1.
    }
  } {
    apply in_eq.
  }
Qed.

Theorem select_smallest:
  forall (x : nat) (al : list nat) (y : nat) (bl : list nat),
    select x al = (y,bl) ->
    Forall (fun z => y <= z) bl.
Proof.
  intros x al.
  revert x.
  induction al; intros; simpl in *. {
    inv H.
    easy.
  } {
    bdestruct (x <=? a). {
      destruct select eqn:Seq.
      inv H.
      apply Forall_cons. {
        apply (le_trans y x a). {
          apply (select_smallest_aux x al y l). {
            apply (IHal x y l).
            easy.
          } {
            easy.
          }
        } {
          easy.
        }
      } {
        apply (IHal x y l).
        easy.
      }
    } {
      destruct (select a al) eqn:?H.
      inv H.
      apply Forall_cons. {
        assert (y <= a). {
          apply (select_smallest_aux a al y l). {
            apply (IHal a y l).
            apply H1.
          } {
            apply H1.
          }
        }
        omega.
      } {
        apply (IHal a y l).
        easy.
      }
    }
  }
Qed.


(** * A list applied with selection sort is sorted **)

Lemma selection_sort_sorted_aux:
  forall (y : nat) (bl : list nat),
   sorted (selsort bl (length bl)) ->
   Forall (fun z : nat => y <= z) bl ->
   sorted (y :: selsort bl (length bl)).
Proof.
  induction bl. {
    simpl.
    intros.
    apply sorted_1.
  } {
    intros.
    simpl in *.
    destruct select eqn:Seq.
    apply sorted_cons. {
      rewrite Forall_forall in H0.
      apply H0.
      apply Permutation_in with (n :: l). {
        pose (select_perm a bl).
        rewrite Seq in y0.
        apply Permutation_sym.
        apply y0.
      } {
        apply in_eq.
      }
    } {
      apply H.
    }
  }
Qed.

Theorem selection_sort_sorted:
  forall (al : list nat), sorted (selection_sort al).
Proof.
  intros.
  unfold selection_sort.
  remember (length al) as n.
  generalize dependent al.
  induction n. {
    intros.
    simpl.
    destruct al. {
      apply sorted_nil.
    } {
      apply sorted_nil.
    }
  } {
    intros.
    destruct al. {
      apply sorted_nil.
    } {
      unfold selsort.
      fold selsort.
      destruct (select n0 al) eqn:Seq.
      pose (select_perm n0 al).
      rewrite Seq in y.
      apply Permutation_length in y.
      rewrite <- Heqn in y.
      inversion y.
      apply (selection_sort_sorted_aux n1 l). {
        rewrite <- H0.
        apply IHn.
        apply H0.
      } {
        apply (select_smallest n0 al n1 l).
        apply Seq.
      }
    }
  }
Qed.


Theorem selection_sort_is_correct:
  selection_sort_correct.
Proof.
  split.
  apply selection_sort_perm.
  apply selection_sort_sorted.
Qed.
