Require Import definition.

Lemma subset_self : forall x , x ⊆ x.
Proof.
  intros.
  unfold subset.
  auto.
Qed.

Lemma subset_equality : forall (x y : Zset), x ⊆ y -> y ⊆ x -> x = y.
Proof.
  intros.
  apply ax_extensionality.
  intros.
  split; auto.
Qed.

Lemma subset_trans : forall x y z , x ⊆ y -> y ⊆ z -> x ⊆ z.
Proof.
  intros.
  unfold subset; intros.
  auto.
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

Lemma empty_set_subset : forall x , Ø ⊆ x.
Proof.
  unfold subset; intros.
  apply empty_set_empty in H.
  contradiction.
Defined.

Hint Resolve empty_set_empty empty_set_subset : set.

Lemma empty_set_unique : 
  forall x , ( forall y , y ∈ x -> False ) -> x = Ø.
Proof.
  intros.
  apply subset_equality.
  unfold subset; intros.
  apply H in H0.
  contradiction.
  auto with set.
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

Lemma union_empty : forall x , x ⋃ Ø = x.
Proof.
  intros.
  apply ax_extensionality.
  intros; split; intros.
  apply union_def in H.
  case H; auto.
  intros.
  apply False_ind.
  eapply empty_set_empty.
  eauto.
  apply union_def.
  auto.
Qed.

Lemma union_comm : forall a b , a ⋃ b = b ⋃ a.
Proof.
  assert ( forall a b , a ⋃ b ⊆ b ⋃ a ).
  unfold subset; intros.
  apply union_def.
  apply union_def in H.
  case H; auto.
  intros; apply subset_equality; auto.
Qed.

Hint Resolve union_empty union_comm union_def : set.

Lemma union_assoc : forall a b c , a ⋃ (b ⋃ c) = (a ⋃ b) ⋃ c.
Proof.
  intros; apply subset_equality; unfold subset; intros.
  - apply union_def.
    apply union_def in H.
    case H; intros.
    + left; apply union_def; auto.
    + apply union_def in H0; case H0; intros.
      * left; apply union_def; auto.
      * right; auto.
  - apply union_def.
    apply union_def in H.
    case H; intros.
    + apply union_def in H0; case H0; intros.
      * left; auto.
      * right; apply union_def; auto.
    + right; apply union_def; auto.
Qed.
  
Lemma set_builder_one : forall x y, x ∈ { y } <-> x = y.
Proof.
  intros.
  unfold set_of_one.
  rewrite union_empty.
  split; intros.  
  apply set_of_two_members in H.
  case H; auto.
  destruct H.
  apply set_of_two_left.
Qed.