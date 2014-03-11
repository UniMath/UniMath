Unset Automatic Introduction.
Require Export Ktheory.Primitive Ktheory.Elements.
Import Primitive.InitialObject.
Definition Data {C} (X:C==>SET) := InitialObject (Elements.cat X).
Definition Property {C} (X:C==>SET) := Utilities.squash (Data X).
Definition Pair {C} {X:C==>SET} (r:Data X) : ob (Elements.cat X)
  := theInitialObject _ r.
Definition IsInitial {C} {X:C==>SET} (r:Data X) : 
  isInitialObject (Elements.cat X) (Pair r).
Proof. intros. exact (theInitialProperty _ r). Qed.
Definition Object {C} {X:C==>SET} (r:Data X) := pr1 (Pair r) : ob C .
Definition Element {C} {X:C==>SET} (r:Data X) : set_to_type (X (Object r))
  := pr2 (Pair r).
Definition Map {C} {X:C==>SET} (r:Data X) (d:ob C) : 
  Hom (Object r) d -> set_to_type (X d).
Proof. intros ? ? ? ? p. exact (#X p (Element r)). Defined.
Lemma MapIsweq {C} {X:C==>SET} (r:Data X) (d:ob C) : isweq (Map r d).
Proof. intros. intros y. exact (IsInitial r (d,,y)). Qed.
Definition Iso {C} {X:C==>SET} (r:Data X) (d:ob C) 
     := weqpair (Map r d) (MapIsweq r d) 
      : weq (Object r → d) (set_to_type (X d)).
