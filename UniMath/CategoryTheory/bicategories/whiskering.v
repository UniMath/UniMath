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
  : iso (f ;1; g) (f ;1; h).
Proof.
  exists (whisker_left f alpha).
  apply (functor_on_iso_is_iso _ _ _ _ _ (prodcatiso (identity_iso f) alpha)).
Defined.

Definition whisker_left_inv {C : prebicategory} {a b c : C}
           (f : a -1-> b) {g h : b -1-> c} (alpha : iso g h)
  : whisker_left_iso f (iso_inv_from_iso alpha)
  = iso_inv_from_iso (whisker_left_iso f alpha).
Proof.
  apply eq_iso.
  simpl.
  unfold whisker_left.
  unfold identity_2mor.

  pathvia (inv_from_iso (identity_iso f);h;inv_from_iso alpha).
    set (W := maponpaths pr1 (iso_inv_of_iso_id _ f)).
    simpl in W.
    rewrite <- W.
    reflexivity.

  apply (maponpaths pr1 (inv_horizontal_comp (identity_iso f) alpha)).
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
  : iso (f ;1; h) (g ;1; h).
Proof.
  exists (whisker_right alpha h).
  apply (functor_on_iso_is_iso _ _ _ _ _ (prodcatiso alpha (identity_iso h))).
Defined.

Definition whisker_right_inv {C : prebicategory} {a b c : C}
           {f g : a -1-> b} (alpha : iso f g) (h : b -1-> c)
  : whisker_right_iso (iso_inv_from_iso alpha) h
  = iso_inv_from_iso (whisker_right_iso alpha h).
Proof.
  apply eq_iso.
  simpl.
  unfold whisker_right.
  unfold identity_2mor.

  pathvia (inv_from_iso alpha ;h; inv_from_iso (identity_iso h)).
    set (W := maponpaths pr1 (iso_inv_of_iso_id _ h)).
    simpl in W.
    rewrite <- W.
    reflexivity.

  apply (maponpaths pr1 (inv_horizontal_comp alpha (identity_iso h))).
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

Lemma left_unitor_naturality {C : prebicategory} {a b : C}
  (f g : a -1-> b) (alpha : f -2-> g)
  : whisker_left (identity_1mor _) alpha ;v; left_unitor g
  = left_unitor f ;v; alpha.
Proof.
  pathvia ((functor_on_morphisms
                 (functor_composite
                     (pair_functor
                        (functor_composite (unit_functor _) (ob_as_functor (identity_1mor a)))
                        (functor_identity _))
                     (compose_functor a a b))
                 alpha)
           ;v;(left_unitor g)).
    apply (cancel_postcomposition _ _ _ _ _ _ (left_unitor g)).
    reflexivity.

  pathvia (left_unitor f ;v; functor_on_morphisms (functor_identity _) alpha).
    apply (nat_trans_ax (left_unitor_trans a b)).

  reflexivity.
Defined.

Lemma right_unitor_naturality {C : prebicategory} {a b : C}
  (f g : a -1-> b) (alpha : f -2-> g)
  : whisker_right alpha (identity_1mor _) ;v; right_unitor g
  = right_unitor f ;v; alpha.
Proof.
  pathvia ((functor_on_morphisms
                 (functor_composite
                    (pair_functor
                       (functor_identity _)
                       (functor_composite (unit_functor _) (ob_as_functor (identity_1mor b))))
                    (compose_functor a b b))
                 alpha)
           ;v;(right_unitor g)).
    apply (cancel_postcomposition _ _ _ _ _ _ (right_unitor g)).
    reflexivity.

  pathvia (right_unitor f ;v; functor_on_morphisms (functor_identity _) alpha).
    apply (nat_trans_ax (right_unitor_trans a b)).

  reflexivity.
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
