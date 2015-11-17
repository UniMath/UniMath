Require Export UniMath.Ktheory.InitialAndFinalObject UniMath.Ktheory.Elements.
Require Import UniMath.Ktheory.Precategories.

Local Open Scope cat.

Definition Data {C:precategory} (F:C==>SET) := InitialObject (Elements.cat F).

Definition Property {C:precategory} (F:C==>SET) := ∥ Data F ∥.

Definition Pair {C:precategory} {F:C==>SET} (r:Data F) : (Elements.cat F)
  := theInitialObject _ r.

Definition IsInitial {C:precategory} {F:C==>SET} (r:Data F) :
  isInitialObject (Elements.cat F) (Pair r).
Proof. intros. exact (theInitialProperty _ r). Qed.

Definition Object {C:precategory} {F:C==>SET} (r:Data F) := pr1 (Pair r) : C .

Definition Element {C:precategory} {F:C==>SET} (r:Data F) : set_to_type (F (Object r))
  := pr2 (Pair r).

Definition Map {C:precategory} {F:C==>SET} (r:Data F) (c:C) :
  Hom (Object r) c -> set_to_type (F c).
Proof. intros ? ? ? ? p. exact (#F p (Element r)). Defined.

Lemma MapIsweq {C:precategory} {F:C==>SET} (r:Data F) (c:C) : isweq (Map r c).
Proof. intros. intros y. exact (IsInitial r (c,,y)). Qed.

Definition Iso {C:precategory} {F:C==>SET} (r:Data F) (c:C) :
  Object r → c ≃ set_to_type (F c)
  := weqpair (Map r c) (MapIsweq r c).

Definition objectMap {C:precategory} {F F':C==>SET} (r:Data F) (r':Data F')
           (p : F ⟶ F') : Object r' → Object r
  := invmap (Iso r' (Object r)) (p (Object r) (Element r)).
