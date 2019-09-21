Require Import definition.

Lemma subset_equality : forall (x y : Zset), x ⊆ y -> y ⊆ x -> x = y.
Proof.
  intros.
  apply ax_extensionality.
  intros.
  split; auto.
Qed.

Lemma set_builder_subset : 
  forall (y : Zset) (P : Zset -> Prop) , { x ∈ y | P x } ⊆ y.
Proof.
  intros.
  unfold subset.
  intros.
  pose (a:= proj2_exists ( ax_specification y P )).
  pose (b:=a z).
  destruct b.
  pose (c:=H0 H).
  destruct c.
  auto.
Qed.

Lemma set_builder_property : forall x y P , x ∈ { k ∈ y | P k } -> P x.
Proof.
  intros.
  pose (a:=proj2_exists ( ax_specification y P )).
  pose (b:=a x).
  destruct b.
  pose (c:=H0 H).
  destruct c.
  auto.
Qed.

Lemma set_builder_def : forall x y (P : Zset -> Prop) , x ∈ y -> P x -> x ∈ { k ∈ y | P k }.
Proof.
  intros.
  pose (a:=proj2_exists ( ax_specification y P )).
  apply a.
  auto.
Qed.

Hint Resolve set_builder_subset set_builder_def : set.

Lemma empty_set_empty : forall x , ~ x ∈ Ø.
Proof.
  intros x; unfold not.
  apply set_builder_property.
Qed.

Lemma subset_of_empty : forall x , x ⊆ Ø -> Ø = x.
Proof.
  intros.
  apply subset_equality.
  unfold subset; intros.
  apply empty_set_empty in H0.
  contradiction.
  auto.
Qed.

Lemma union_set_subset : forall x y , x ∈ y -> x ⊆ union_set y.
Proof.
  unfold union_set.
  unfold subset.
  intros.
  apply set_builder_def.
  pose (a:= proj2_exists (ax_union y)).
  apply a with (b:=x); auto.
  exists x; auto.
Qed.

Lemma union_set_property : forall x y , x ∈ union_set y -> exists k , x ∈ k /\ k ∈ y.
Proof.
  intros x y.
  apply set_builder_property.
Qed.


Lemma set_of_two_members : forall x y z : Zset , z ∈ (set_of_two x y) <-> z = x \/ z = y.
Proof.
  intros.
  unfold set_of_two.
  split.
  intros.
  apply set_builder_property with (x:=z) (y:=proj1_exists (ax_pairing x y)).
  auto.
  intros.
  apply set_builder_def.
  pose (a:= proj2_exists (ax_pairing x y)).
  destruct a.
  case H; intros; rewrite H2; auto.
  auto.
Qed.


Lemma set_of_two_left : forall x y : Zset , x ∈ (set_of_two x y). 
Proof.
  intros.
  apply set_of_two_members.
  auto.
Qed.

Lemma set_of_two_right : forall x y : Zset , y ∈ (set_of_two x y).
Proof.
  intros.
  apply set_of_two_members.
  auto.
Qed.

Lemma union_def : forall x y z , z ∈ x ⋃ y <-> z ∈ x \/ z ∈ y.
Proof.
  unfold union.
  intros; split; intros.
  apply union_set_property in H.
  elim H.
  intros.
  destruct H0.
  assert ( x0 = x \/ x0 = y ).
  apply (set_of_two_members).
  auto.
  case H2; intros; rewrite <- H3; auto.
  case H; intros.
  apply (union_set_subset x).
  apply set_of_two_left.
  auto.
  apply (union_set_subset y).
  apply set_of_two_right.
  auto.
Qed.

Lemma intersect_def : forall x y z , z ∈ x ⋂ y <-> z ∈ x /\ z ∈ y.
Proof.
  intros.
  unfold intersect.
  constructor; intros.
  constructor.
  apply set_builder_subset in H.
  auto.
  apply set_builder_property in H.
  auto.
  apply set_builder_def; destruct H; auto.  
Qed.

Lemma set_of_one_def : forall x y , x ∈ set_of_one y <-> x = y.
Proof.
  intros.
  split; intros.
  unfold set_of_one in H.
  apply set_of_two_members in H.
  tauto.
  destruct H.
  apply set_of_two_left.
Qed.

Lemma extensionality_reverse : 
  forall x y , x <> y -> exists z , z ∈ x <-> z ∉ y.
Proof.
  intros.
  apply Classical_Prop.NNPP.
  unfold not.
  intros.
  apply H.
  apply ax_extensionality.
Admitted.

Ltac set_solver_step :=
  match goal with
  | [ H : False |- _ ] => contradiction
  | [ H : ?P |- ?P ] => exact H
  | [ A : ?P , B : ~ ?P |- _ ] => contradiction
  | [ |- True ] => constructor
  | [ |- _ ∈ set_of_one _ ] => apply set_of_one_def
  | [ H : ~ _ ∈ set_of_one _ |- _ ] => 
    apply (not_iff_compat (set_of_one_def _ _)) in H
  | [ H : _ ∈ Ø |- _ ] => apply empty_set_empty in H
  | [ H : _ ∈ set_of_one _ |- _ ] => apply set_of_one_def in H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : ~ (_ \/ _) |- _ ] => apply Classical_Prop.not_or_and in H
  | [ H : ~ (_ /\ _) |- _ ] => apply Classical_Prop.not_and_or in H
  | [ |- forall _, _ ] => intros  
  | [ |- _ /\ _ ] => constructor
  | [ |- _ \/ _ ] => Classical_Prop.classical_left
  | [ |- _ <-> _ ] => constructor
  | [ |- _ ⊆ _ ] => unfold subset; intros
  | [ |- _ ∈ _ ⋃ _ ] => apply union_def
  | [ H : _ ∈ _ ⋃ _ |- _ ] => apply union_def in H
  | [ H : ~ _ ∈ _ ⋃ _ |- _ ]
    => apply (not_iff_compat (union_def _ _ _)) in H
  | [ |- _ ∈ _ ⋂ _ ] => apply intersect_def
  | [ H : _ ∈ _ ⋂ _ |- _ ] => apply intersect_def in H
  | [ H : ~ _ ∈ _ ⋂ _ |- _ ]
    => apply (not_iff_compat (intersect_def _ _ _)) in H  
  | [ H : _ ⊆ Ø |- _ ] => apply subset_of_empty in H
  | [ H : _ = _ |- _ ] => destruct H
  | [ H : _ \/ _ |- _ ] => destruct H  
  | [ |- _ = _ ] => apply subset_equality
  | [ H : _ <> _ |- _ ] => apply extensionality_reverse in H
  end.

Ltac set_solver := repeat set_solver_step.

Lemma subset_self : forall x , x ⊆ x.
Proof.
  set_solver.
Qed.

Lemma subset_trans : forall x y z , x ⊆ y -> y ⊆ z -> x ⊆ z.
Proof.
  set_solver.
  apply H0.
  apply H.
  auto.
Qed.

Lemma empty_set_subset : forall x , Ø ⊆ x.
Proof.
  set_solver.
Qed.

Lemma empty_set_unique : 
  forall x , ( forall y , y ∈ x -> False ) -> x = Ø.
Proof.
  set_solver.
  pose ( H z H0 ).
  contradiction.
Qed.

Lemma union_empty : forall x , x ⋃ Ø = x.
Proof.
  set_solver.
Qed.

Lemma union_comm : forall a b , a ⋃ b = b ⋃ a.
Proof.
  set_solver.
Qed.

Lemma union_assoc : forall a b c , a ⋃ (b ⋃ c) = (a ⋃ b) ⋃ c.
Proof.
  set_solver.
Qed.

Hint Resolve union_empty union_comm union_def union_assoc : set.

Lemma intersect_empty : forall x , x ⋂ Ø = Ø.
Proof.
  set_solver.
Qed.

Lemma intersect_comm : forall a b , a ⋂ b = b ⋂ a.
Proof.
  set_solver.
Qed.

Lemma intersect_assoc : forall a b c , a ⋂ (b ⋂ c) = (a ⋂ b) ⋂ c.
Proof.
  set_solver.
Qed.

Hint Resolve intersect_empty intersect_comm intersect_def intersect_assoc : set.

Lemma intersect_in_union : forall a b c , (a ⋂ b) ⋃ ( a ⋂ c ) = a ⋂ ( b ⋃ c ).
Proof.
  set_solver.
Qed.

Lemma union_in_intersect : forall a b c , (a ⋃ b) ⋂ ( a ⋃ c ) = a ⋃ ( b ⋂ c ).
Proof.
  set_solver.
Qed.

Lemma set_builder_one : forall x a, x ∈ { a } <-> x = a.
Proof.
  set_solver.
Qed.

Lemma set_builder_two : forall x a b, x ∈ { a , b } <-> x = a \/ x = b.
Proof.
  set_solver.
Qed.

Lemma set_builder_three : forall x a b c, x ∈ { a , b , c } <-> x = a \/ x = b \/ x = c.
Proof.
  set_solver.
Qed.

Lemma set_builder_comm : forall a b , { a, b } = { b, a }.
Proof.
  set_solver.
Qed.

Lemma set_builder_sym : forall a , { a, a } = { a }.
Proof.
  set_solver.
Qed.
