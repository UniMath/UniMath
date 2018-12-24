Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.StandardCategories. (* unit *)
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.prebicategory.
Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.Notations.

(******************************************************************************)
(* Whiskering *)

Definition whisker_left {C : prebicategory} {a b c : C}
           (f : a -1-> b) {g h : b -1-> c} (alpha : g -2-> h)
  : (f ;1; g) -2-> (f ;1; h)
  := identity f ;h; alpha.

Lemma whisker_left_id_1mor {C : prebicategory} {b c : C}
           {g h : b -1-> c} (alpha : g -2-> h)
  : whisker_left (identity1 _) alpha =
    left_unitor _ ;v; alpha ;v; inv_from_iso (left_unitor _).
Proof.
  unfold whisker_left.
  apply id_2mor_left.
Defined.

Lemma whisker_left_id_2mor {C : prebicategory} {a b c : C}
           (f : a -1-> b) (g : b -1-> c)
  : whisker_left f (identity g) = identity (f ;1; g).
Proof.
  intermediate_path (functor_on_morphisms (compose_functor a b c)
                                (identity (precatbinprodpair f g))).
  reflexivity.
  apply functor_id.
Defined.

Lemma cancel_whisker_left {C : prebicategory} {a b c : C}
      (f : a -1-> b) {g h : b -1-> c}
      {alpha alpha': g -2-> h} (p : alpha = alpha')
  : whisker_left f alpha = whisker_left f alpha'.
Proof.
  induction p.
  reflexivity.
Defined.

Definition whisker_left_iso {C : prebicategory} {a b c : C}
           (f : a -1-> b) {g h : b -1-> c} (alpha : iso g h)
  : iso (f ;1; g) (f ;1; h).
Proof.
  exists (whisker_left f alpha).
  apply (functor_on_iso_is_iso _ _ _ _ _ (precatbinprodiso (identity_iso f) alpha)).
Defined.

Lemma whisker_left_inv {C : prebicategory} {a b c : C}
           (f : a -1-> b) {g h : b -1-> c} (alpha : iso g h)
  : whisker_left f (iso_inv_from_iso alpha)
  = inv_from_iso (whisker_left_iso f alpha).
Proof.
  unfold whisker_left.
  intermediate_path (inv_from_iso (identity_iso f);h;inv_from_iso alpha).
    set (W := maponpaths pr1 (iso_inv_of_iso_id _ f)).
    simpl in W.
    rewrite <- W.
    reflexivity.

  apply (maponpaths pr1 (inv_horizontal_comp (identity_iso f) alpha)).
Defined.

Lemma whisker_left_id_inj {C : prebicategory} {b c : C}
  {g h : b -1-> c} (alpha alpha' : g -2-> h)
  : whisker_left (identity1 _) alpha = whisker_left (identity1 _) alpha'
    -> alpha = alpha'.
Proof.
  intros w.

  intermediate_path (iso_inv_from_iso (left_unitor _)
           ;v; whisker_left (identity1 _) alpha
           ;v; left_unitor _ ).
    apply pathsinv0.
    apply iso_inv_to_right.
    apply iso_inv_on_right.
    rewrite assoc.
    apply whisker_left_id_1mor.

  intermediate_path (iso_inv_from_iso (left_unitor _)
           ;v; whisker_left (identity1 _) alpha'
           ;v; left_unitor _ ).
    apply cancel_postcomposition.
    apply cancel_precomposition.
    assumption.

  apply iso_inv_to_right.
  apply iso_inv_on_right.
  rewrite assoc.
  apply whisker_left_id_1mor.
Defined.

Lemma whisker_left_on_comp {C : prebicategory} {a b c : C}
  (f : a -1-> b) {g h i : b -1-> c}
  (alpha : g -2-> h) (alpha' : h -2-> i)
  : whisker_left f (alpha ;v; alpha')
  = whisker_left f alpha ;v; whisker_left f alpha'.
Proof.
  unfold whisker_left.
  intermediate_path ((identity f;v; identity f);h;(alpha;v;alpha')).
    rewrite id_left.
    reflexivity.
  now apply interchange.
Defined.

Definition whisker_right {C : prebicategory} {a b c : C}
  {f g : a -1-> b} (alpha : f -2-> g) (h : b -1-> c)
  : (f ;1; h) -2-> (g ;1; h)
  := alpha ;h; identity h.

Lemma whisker_right_id_1mor {C : prebicategory} {a b : C}
           {f g : a -1-> b} (alpha : f -2-> g)
  : whisker_right alpha (identity1 _) =
    right_unitor _ ;v; alpha ;v; inv_from_iso (right_unitor _).
Proof.
  unfold whisker_right.
  apply id_2mor_right.
Defined.

Lemma whisker_right_id_2mor {C : prebicategory} {a b c : C}
  (f : a -1-> b) (g : b -1-> c)
  : whisker_right (identity f) g = identity (f ;1; g).
Proof.
  intermediate_path (functor_on_morphisms (compose_functor a b c)
                                (identity (precatbinprodpair f g))).
  reflexivity.
  apply functor_id.
Defined.

Definition cancel_whisker_right {C : prebicategory} {a b c : C}
    {f g : a -1-> b} {alpha alpha' : f -2-> g} (p : alpha = alpha') (h : b -1-> c)
  : whisker_right alpha h = whisker_right alpha' h.
Proof.
  induction p.
  reflexivity.
Defined.

Definition whisker_right_iso {C : prebicategory} {a b c : C}
           {f g : a -1-> b} (alpha : iso f g) (h : b -1-> c)
  : iso (f ;1; h) (g ;1; h).
Proof.
  exists (whisker_right alpha h).
  apply (functor_on_iso_is_iso _ _ _ _ _ (precatbinprodiso alpha (identity_iso h))).
Defined.

Lemma whisker_right_inv {C : prebicategory} {a b c : C}
           {f g : a -1-> b} (alpha : iso f g) (h : b -1-> c)
  : whisker_right (iso_inv_from_iso alpha) h
  = inv_from_iso (whisker_right_iso alpha h).
Proof.
  unfold whisker_right.
  intermediate_path (inv_from_iso alpha ;h; inv_from_iso (identity_iso h)).
    set (W := maponpaths pr1 (iso_inv_of_iso_id _ h)).
    simpl in W.
    rewrite <- W.
    reflexivity.

  apply (maponpaths pr1 (inv_horizontal_comp alpha (identity_iso h))).
Defined.

Lemma whisker_right_id_inj {C : prebicategory} {a b : C}
  {f g : a -1-> b} (alpha alpha' : f -2-> g)
  : whisker_right alpha (identity1 _) = whisker_right alpha' (identity1 _)
    -> alpha = alpha'.
Proof.
  intros w.

  intermediate_path (iso_inv_from_iso (right_unitor _)
           ;v; whisker_right alpha (identity1 _)
           ;v; right_unitor _ ).
    apply pathsinv0.
    apply iso_inv_to_right.
    apply iso_inv_on_right.
    rewrite assoc.
    apply whisker_right_id_1mor.

  intermediate_path (iso_inv_from_iso (right_unitor _)
           ;v; whisker_right alpha' (identity1 _)
           ;v; right_unitor _ ).
    apply cancel_postcomposition.
    apply cancel_precomposition.
    assumption.

  apply iso_inv_to_right.
  apply iso_inv_on_right.
  rewrite assoc.
  apply whisker_right_id_1mor.
Defined.

Lemma whisker_right_on_comp {C : prebicategory} {a b c : C}
  {f g h : a -1-> b} (alpha : f -2-> g) (alpha' : g -2-> h) (i : b -1-> c)
  : whisker_right (alpha ;v; alpha') i
  = whisker_right alpha i ;v; whisker_right alpha' i.
Proof.
  unfold whisker_right.
  intermediate_path ((alpha;v;alpha');h;(identity i;v; identity i)).
    rewrite id_left.
    reflexivity.
  now apply interchange.
Defined.

Lemma left_unitor_naturality {C : prebicategory} {a b : C}
  (f g : a -1-> b) (alpha : f -2-> g)
  : whisker_left (identity1 _) alpha ;v; left_unitor g
  = left_unitor f ;v; alpha.
Proof.
  intermediate_path ((functor_on_morphisms
                 (functor_composite
                     (bindelta_pair_functor
                        (functor_composite (functor_to_unit _) (constant_functor unit_category _ (identity1 a)))
                        (functor_identity _))
                     (compose_functor a a b))
                 alpha)
           ;v;(left_unitor g)).
    reflexivity.

  intermediate_path (left_unitor f ;v; functor_on_morphisms (functor_identity _) alpha).
    apply (nat_trans_ax (left_unitor_trans a b)).

  reflexivity.
Defined.

Lemma right_unitor_naturality {C : prebicategory} {a b : C}
  (f g : a -1-> b) (alpha : f -2-> g)
  : whisker_right alpha (identity1 _) ;v; right_unitor g
  = right_unitor f ;v; alpha.
Proof.
  intermediate_path ((functor_on_morphisms
                 (functor_composite
                    (bindelta_pair_functor
                       (functor_identity _)
                       (functor_composite (functor_to_unit _) (constant_functor unit_category _ (identity1 b))))
                    (compose_functor a b b))
                 alpha)
           ;v;(right_unitor _)).
    reflexivity.

  intermediate_path (right_unitor f ;v; functor_on_morphisms (functor_identity _) alpha).
    apply (nat_trans_ax (right_unitor_trans a b)).

  reflexivity.
Defined.

Lemma associator_naturality {C : prebicategory} { a b c d : C }
  {f f' : a -1-> b} (alpha : f -2-> f')
  {g g' : b -1-> c} (beta  : g -2-> g')
  {h h' : c -1-> d} (gamma : h -2-> h')
  : (alpha ;h; (beta ;h; gamma)) ;v; associator f' g' h'
  = associator f g h ;v; ((alpha ;h; beta) ;h; gamma).
Proof.
  intermediate_path ((functor_on_morphisms
            (functor_composite
              (pair_functor (functor_identity _) (compose_functor b c d))
              (compose_functor a b d))
           (precatbinprodmor alpha (precatbinprodmor beta gamma)))
           ;v; associator f' g' h'
          ).
    reflexivity.

  intermediate_path (associator f g h ;v;
          (functor_on_morphisms
            (functor_composite
              (precategory_binproduct_assoc _ _ _)
              (functor_composite
                (pair_functor (compose_functor a b c) (functor_identity _))
                (compose_functor a c d)))
            (precatbinprodmor alpha (precatbinprodmor beta gamma)))).
    apply (nat_trans_ax (associator_trans a b c d) _ _
                        (precatbinprodmor alpha (precatbinprodmor beta gamma))).

  reflexivity.
Defined.

Lemma twomor_naturality {C : prebicategory} {a b c : C}
  {f g : a -1-> b}  {h k : b -1-> c}
  (gamma : f -2-> g) (delta  : h -2-> k)
  : (whisker_right gamma h) ;v; (whisker_left g delta)
  = (whisker_left f delta) ;v; (whisker_right gamma k).
Proof.
  unfold whisker_left, whisker_right.

  intermediate_path ((gamma ;v; identity g);h;(identity h ;v; delta)).
    apply pathsinv0.
    apply interchange.

  intermediate_path ((identity f ;v; gamma);h;(delta ;v; identity k)).
    rewrite !id_left, !id_right.
    reflexivity.

  apply interchange.
Defined.

(******************************************************************************)
(* Kelly's Condition 5 *)
(* i.e., the two ways of going I(bc) -> bc are equal *)

Section kelly_left_pieces.
Variable C : prebicategory.
Variables a b c d : C.
Variable f : a -1-> b.
Variable g : b -1-> c.
Variable h : c -1-> d.

Local Lemma kelly_left_region_1235 :
      associator f (identity1 _) (g ;1; h)
  ;v; associator (f ;1; (identity1 _)) g h
  ;v; whisker_right (whisker_right (right_unitor f) g) h
  =   whisker_left f (associator (identity1 b) g h)
  ;v; associator f (identity1 _ ;1; g) h
  ;v; whisker_right (whisker_left f (left_unitor g)) h.
Proof.
  simpl.
  unfold whisker_left at 2.
  rewrite (cancel_whisker_right (triangle_axiom f g) h).
  rewrite whisker_right_on_comp.
  rewrite assoc.
  apply cancel_postcomposition.
  apply (pentagon_axiom f (identity1 b) g h).
Defined.

Local Lemma kelly_left_region_123 :
      associator f (identity1 _) (g ;1; h)
  ;v; associator (f ;1; (identity1 _)) g h
  ;v; whisker_right (whisker_right (right_unitor f) g) h
  =   whisker_left f (associator (identity1 b) g h)
  ;v; whisker_left f (whisker_right (left_unitor g) h)
  ;v; associator f g h.
Proof.
  rewrite <- (assoc _ _ (associator f g h)).
  unfold whisker_left at 2.
  unfold whisker_right at 3.
  rewrite associator_naturality.
  fold (whisker_left f (left_unitor g)).
  fold (whisker_right (whisker_left f (left_unitor g)) h).
  rewrite assoc.
  apply kelly_left_region_1235.
Defined.

Local Lemma kelly_left_region_12 :
      associator f (identity1 _) (g ;1; h)
  ;v; whisker_right (right_unitor f) (g ;1; h)
  =   whisker_left f (associator (identity1 b) g h)
  ;v; whisker_left f (whisker_right (left_unitor g) h).
Proof.
  apply (post_comp_with_iso_is_inj _ _ _ (associator f g h) (pr2 (associator f g h))).
  unfold whisker_right at 1.
  rewrite <- horizontal_comp_id.
  rewrite <- assoc.
  rewrite associator_naturality.
  rewrite assoc.
  apply kelly_left_region_123.
Defined.

Local Lemma kelly_left_region_1 :
      whisker_left f (left_unitor_2mor (g ;1; h))
  =   whisker_left f (associator (identity1 b) g h)
  ;v; whisker_left f (whisker_right (left_unitor g) h).
Proof.
  unfold whisker_left at 1.
  rewrite triangle_axiom.
  apply kelly_left_region_12.
Defined.

End kelly_left_pieces.

Lemma kelly_left {C : prebicategory} {b c d : C}
  {g : b -1-> c} {h : c -1-> d}
  : left_unitor_2mor (g ;1; h)
  = associator (identity1 b) g h ;v; whisker_right_iso (left_unitor g) h.
Proof.
  apply whisker_left_id_inj.
  rewrite whisker_left_on_comp.
  apply kelly_left_region_1.
Defined.

(* TODO: same for right *)

(******************************************************************************)
(* Kelly's Condition 4 *)
(* i.e., the two ways of going II -> I are equal *)

Lemma left_unitor_on_id {C : prebicategory} {a : C}
  : whisker_left (identity1 a) (left_unitor (identity1 a))
  = left_unitor (identity1 a ;1; identity1 a).
Proof.
  apply (post_comp_with_iso_is_inj _ _ _ (left_unitor (identity1 a))).
    apply (pr2 (left_unitor (identity1 a))).
  apply left_unitor_naturality.
Defined.

Lemma left_unitor_id_is_right_unitor_id {C : prebicategory} {a : C}
  : left_unitor_2mor (identity1 a)
  = right_unitor_2mor (identity1 a).
Proof.
  apply whisker_right_id_inj.
  apply (pre_comp_with_iso_is_inj _ _ _ _ (associator _ _ _) (pr2 (associator _ _ _))).
  intermediate_path (left_unitor_2mor ((identity1 a) ;1; (identity1 a))).
    apply pathsinv0.
    apply kelly_left.
  intermediate_path (whisker_left (identity1 a) (left_unitor (identity1 a))).
    apply pathsinv0.
    apply left_unitor_on_id.
  apply (triangle_axiom (identity1 a) (identity1 a)).
Defined.