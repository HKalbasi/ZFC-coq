Require Import definition basic.

Axiom ax_power_set : forall x , exists y , forall z , z ⊆ x -> z ∈ y.

Definition power_set ( x : Zset ) := 
  { k ∈ proj1_exists (ax_power_set x) | k ⊆ x }.

Lemma power_set_def : forall x y , x ∈ power_set y <-> x ⊆ y.
Proof.
  intros.
  constructor; unfold power_set.
  intros.
  apply set_builder_property in H.
  auto.
  intros.
  apply set_builder_def.
  pose (a:= proj2_exists (ax_power_set y)).
  auto.
  auto.
Qed.

Ltac set_solver_power :=
  repeat match goal with
  | [ H : _ ∈ power_set _ |- _ ] => apply power_set_def in H
  | [ |- _ ∈ power_set _ ] => apply power_set_def
  | _ => set_solver
  end.

Lemma power_set_empty : power_set Ø = { Ø }.
Proof.
  set_solver_power.
Qed.

Lemma power_set_one : forall a, power_set { a } = { Ø , { a } }.
Proof.
  set_solver_power.
  pose (H z0 H2).
  set_solver.
  elim H0; intros.
  destruct H3.
  destruct (Classical_Prop.classic (x ∈ z)).
  pose (H x H5).
  pose (H3 H5).
  contradiction.
  destruct (Classical_Prop.classic (x ∉ {z0})).
  pose (H4 H6).
  contradiction.
  apply Classical_Prop.NNPP in H6.
  set_solver.
Qed.
