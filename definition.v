Axiom Zset : Prop.

Axiom Zmember : Zset -> Zset -> Prop.

Infix "∈" := Zmember (at level 75).

Axiom ax_exist : Zset.

Axiom ax_extensionality : forall ( x y : Zset ) , 
  (forall z : Zset , (z ∈ x) <-> (z ∈ y)) -> x = y.

Axiom ax_pairing : forall ( x y : Zset ) , exists z , x ∈ z /\ y ∈ z.

Axiom ax_specification : forall ( x : Zset ) ( P : Zset -> Prop ) , 
  exists y : Zset , forall k : Zset , k ∈ y <-> k ∈ x /\ P k.

Axiom ax_union : forall x , exists y , forall a b, a ∈ b -> b ∈ x -> a ∈ y.

Definition proj1_exists := 
fun {A : Prop} {P : A -> Prop} (e : exists x : A , P x) =>
let (a, _) := e in a.

Definition proj2_exists := 
fun {A : Prop} {P : A -> Prop} (e : exists x : A , P x) =>
let (a, b) as e0 return (P (proj1_exists e0)) := e in b.

Definition set_builder ( x : Zset ) ( P : Zset -> Prop ) := 
  proj1_exists ( ax_specification x P ).

Notation "{ x ∈ y | P }" := 
  (set_builder y (fun x=>P)) (at level 0, x at level 49).

Definition set_of_two ( x y : Zset ) := { k ∈ proj1_exists (ax_pairing x y) | k = x \/ k = y }.

Definition union_set ( x : Zset ) := 
  { k ∈ proj1_exists (ax_union x) | exists b , k ∈ b /\ b ∈ x }.

Definition union ( x y : Zset ) := union_set ( set_of_two x y ).

Infix "⋃" := union ( at level 40 ).

Definition Ø := { x ∈ ax_exist | False }.

Notation "{ }" := Ø (at level 1 , only parsing).

Definition set_of_one (x : Zset) := set_of_two x x.

Notation "{ x , .. , y }" := (union (set_of_one x) .. (union (set_of_one y) Ø) ..) ( x , y at level 49 ).

Definition subset ( x y : Zset ) := forall z : Zset , z ∈ x -> z ∈ y.

Infix "⊆" := subset (at level 75).