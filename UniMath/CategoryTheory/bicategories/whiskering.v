Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.equivalences.

Require Import UniMath.CategoryTheory.bicategories.prebicategory.
Require Import UniMath.CategoryTheory.bicategories.notations.

(******************************************************************************)
(* Whiskering *)

Definition whisker_left {C : prebicategory} {a b c : C}
           (f : a -1-> b) {g h : b -1-> c} (alpha : g -2-> h)
  : (f ;1; g) -2-> (f ;1; h)
  := (identity_2mor f) ;h; alpha.

Lemma whisker_left_id_1mor {C : prebicategory} {b c : C}
           {g h : b -1-> c} (alpha : g -2-> h)
  : whisker_left (identity_1mor _) alpha =
    left_unitor _ ;v; alpha ;v; iso_inv_from_iso (left_unitor _).
Proof.
  unfold whisker_left.
  apply id_2mor_left.
Defined.

Lemma whisker_left_id_2mor {C : prebicategory} {a b c : C}
           (f : a -1-> b) (g : b -1-> c)
  : whisker_left f (identity_2mor g) = identity_2mor (f ;1; g).
Proof.
  pathvia (functor_on_morphisms (compose_functor a b c)
                                (identity (prodcatpair f g))).
  reflexivity.
  apply functor_id.
Defined.

Definition whisker_left_iso {C : prebicategory} {a b c : C}
           (f : a -1-> b) {g h : b -1-> c} (alpha : iso g h)
  : iso (f ;1; g) (f ;1; h)
  := (identity_iso f) ;hi; alpha.

Definition whisker_left_inv {C : prebicategory} {a b c : C}
           (f : a -1-> b) {g h : b -1-> c} (alpha : iso g h)
  : whisker_left_iso f (iso_inv_from_iso alpha)
  = iso_inv_from_iso (whisker_left_iso f alpha).
Proof.
  unfold whisker_left_iso at 1.
  rewrite <- iso_inv_of_iso_id.
  apply inv_horizontal_comp.
Defined.

Lemma whisker_left_on_comp {C : prebicategory} {a b c : C}
  (f : a -1-> b) {g h i : b -1-> c}
  (alpha : g -2-> h) (alpha' : h -2-> i)
  : whisker_left f (alpha ;v; alpha')
  = whisker_left f alpha ;v; whisker_left f alpha'.
Proof.
  unfold whisker_left.
  pathvia ((identity_2mor f;v; identity_2mor f);h;(alpha;v;alpha')).
    rewrite id_left.
    reflexivity.
  now apply interchange.
Defined.

Definition whisker_right {C : prebicategory} {a b c : C}
  {f g : a -1-> b} (alpha : f -2-> g) (h : b -1-> c)
  : (f ;1; h) -2-> (g ;1; h)
  := alpha ;h; (identity_2mor h).

Lemma whisker_right_id_1mor {C : prebicategory} {a b : C}
           {f g : a -1-> b} (alpha : f -2-> g)
  : whisker_right alpha (identity_1mor _) =
    right_unitor _ ;v; alpha ;v; iso_inv_from_iso (right_unitor _).
Proof.
  unfold whisker_right.
  apply id_2mor_right.
Defined.

Lemma whisker_right_id_2mor {C : prebicategory} {a b c : C}
  (f : a -1-> b) (g : b -1-> c)
  : whisker_right (identity_2mor f) g = identity_2mor (f ;1; g).
Proof.
  pathvia (functor_on_morphisms (compose_functor a b c)
                                (identity (prodcatpair f g))).
  reflexivity.
  apply functor_id.
Defined.

Definition whisker_right_iso {C : prebicategory} {a b c : C}
           {f g : a -1-> b} (alpha : iso f g) (h : b -1-> c)
  : iso (f ;1; h) (g ;1; h)
  := alpha ;hi; (identity_iso h).

Definition whisker_right_inv {C : prebicategory} {a b c : C}
           {f g : a -1-> b} (alpha : iso f g) (h : b -1-> c)
  : whisker_right_iso (iso_inv_from_iso alpha) h
  = iso_inv_from_iso (whisker_right_iso alpha h).
Proof.
  unfold whisker_right_iso at 1.
  rewrite <- iso_inv_of_iso_id.
  apply inv_horizontal_comp.
Defined.

Lemma whisker_right_on_comp {C : prebicategory} {a b c : C}
  {f g h : a -1-> b} (alpha : f -2-> g) (alpha' : g -2-> h) (i : b -1-> c)
  : whisker_right (alpha ;v; alpha') i
  = whisker_right alpha i ;v; whisker_right alpha' i.
Proof.
  unfold whisker_right.
  pathvia ((alpha;v;alpha');h;(identity_2mor i;v; identity_2mor i)).
    rewrite id_left.
    reflexivity.
  now apply interchange.
Defined.

Lemma twomor_naturality {C : prebicategory} {a b c : C}
  {f g : a -1-> b}  {h k : b -1-> c}
  (gamma : f -2-> g) (delta  : h -2-> k)
  : (whisker_right gamma h) ;v; (whisker_left g delta)
  = (whisker_left f delta) ;v; (whisker_right gamma k).
Proof.
  unfold whisker_left, whisker_right.

  pathvia ((gamma ;v; identity_2mor g);h;(identity_2mor h ;v; delta)).
    apply pathsinv0.
    apply interchange.

  pathvia ((identity_2mor f ;v; gamma);h;(delta ;v; identity_2mor k)).
    rewrite !id_left, !id_right.
    reflexivity.

  apply interchange.
Defined.
