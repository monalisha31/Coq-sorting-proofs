Require Export Coq.omega.Omega.
Require Export Coq.Bool.Bool.

Lemma beq_reflect:
  forall (x y : nat), reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect.
  symmetry.
  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect:
  forall (x y : nat), reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect.
  symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma ble_reflect:
  forall (x y : nat), reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect.
  symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let
    H := fresh
  in let
    e := fresh "e"
  in
   evar (e: Prop);
   assert (H: reflect e X);
   subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac inv H := inversion H; clear H; subst.
