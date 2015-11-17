Require Export UniMath.Ktheory.InitialAndFinalObject UniMath.Ktheory.Elements.
Require Import UniMath.Ktheory.Precategories.

Local Open Scope cat.

Definition Data {C:precategory} (X:C==>SET) := InitialObject (Elements.cat X).

Definition Property {C:precategory} (X:C==>SET) := ∥ Data X ∥.

Definition Pair {C:precategory} {X:C==>SET} (r:Data X) : (Elements.cat X)
  := theInitialObject r.

Definition IsInitial {C:precategory} {X:C==>SET} (r:Data X) :
  isInitialObject (Elements.cat X) (Pair r).
Proof. intros. exact (theInitialProperty r). Qed.

Definition Object {C:precategory} {X:C==>SET} (r:Data X) := pr1 (Pair r) : C .

Definition Element {C:precategory} {X:C==>SET} (r:Data X) : set_to_type (X (Object r))
  := pr2 (Pair r).

Definition Map {C:precategory} {X:C==>SET} (r:Data X) (c:C) :
  Hom (Object r) c -> set_to_type (X c).
Proof. intros ? ? ? ? p. exact (#X p (Element r)). Defined.

Lemma MapIsweq {C:precategory} {X:C==>SET} (r:Data X) (c:C) : isweq (Map r c).
Proof. intros. intros y. exact (IsInitial r (c,,y)). Qed.

Definition Iso {C:precategory} {X:C==>SET} (r:Data X) (c:C) :
  Object r → c ≃ set_to_type (X c)
  := weqpair (Map r c) (MapIsweq r c).

Definition objectMap {C:precategory} {X X':C==>SET} (r:Data X) (r':Data X')
           (p : X ⟶ X') : Object r' → Object r
  := get_mor (thePoint (theInitialProperty r' (cat_on_nat_trans p (theInitialObject r)))).

Definition objectMapUniqueness {C:precategory} {X X':C==>SET} (r:Data X) (r':Data X') (p : X ⟶ X')
           (f : get_ob (theInitialObject r') → get_ob (theInitialObject r))
           (e : # X' f (get_el (theInitialObject r')) = get_el (cat_on_nat_trans p (theInitialObject r)))
  : f = objectMap r r' p
  := maponpaths get_mor (uniqueness (theInitialProperty r' (cat_on_nat_trans p (theInitialObject r))) (f,,e)).

Definition objectMapIdentity {C:precategory} {X:C==>SET} (r:Data X) :
  objectMap r r (nat_trans_id X) = identity (Object r)
  := maponpaths
       get_mor
       (theInitialIdentity r
          (thePoint
             (theInitialProperty
                r (cat_on_nat_trans (nat_trans_id X) (theInitialObject r))))).
