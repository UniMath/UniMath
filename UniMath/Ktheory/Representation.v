Require Export UniMath.Ktheory.InitialAndFinalObject UniMath.Ktheory.Elements.
Local Open Scope cat.
Definition Data {C:precategory} (X:C==>SET) := InitialObject (Elements.cat X).
Definition Property {C:precategory} (X:C==>SET) := ∥ Data X ∥.
Definition Pair {C:precategory} {X:C==>SET} (r:Data X) : ob (Elements.cat X)
  := theInitialObject _ r.
Definition IsInitial {C:precategory} {X:C==>SET} (r:Data X) :
  isInitialObject (Elements.cat X) (Pair r).
Proof. intros. exact (theInitialProperty _ r). Qed.
Definition Object {C:precategory} {X:C==>SET} (r:Data X) := pr1 (Pair r) : ob C .
Definition Element {C:precategory} {X:C==>SET} (r:Data X) : set_to_type (X (Object r))
  := pr2 (Pair r).
Definition Map {C:precategory} {X:C==>SET} (r:Data X) (d:ob C) :
  Hom (Object r) d -> set_to_type (X d).
Proof. intros ? ? ? ? p. exact (#X p (Element r)). Defined.
Lemma MapIsweq {C:precategory} {X:C==>SET} (r:Data X) (d:ob C) : isweq (Map r d).
Proof. intros. intros y. exact (IsInitial r (d,,y)). Qed.
Definition Iso {C:precategory} {X:C==>SET} (r:Data X) (d:ob C)
     := weqpair (Map r d) (MapIsweq r d)
      : weq (Object r → d) (set_to_type (X d)).
