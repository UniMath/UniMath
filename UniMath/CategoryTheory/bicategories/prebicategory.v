
(** **********************************************************

Mitchell Riley

June 2016

I am very grateful to Peter LeFanu Lumsdaine, whose unreleased
bicategories code strongly influenced the definitions in this
file.

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.equivalences.

Arguments functor_composite {_ _ _} _ _ .

(******************************************************************************)
(* Definition of a prebicategory *)

(* This is done in a few pieces. Instead of specifying all the data
   and the conditions afterwards, we interleave them, i.e., we have a
   precategory of morphisms immediately, instead of a type that is
   later said to be a precategory. This (possibly) makes the
   definition easier to work with. *)

(* The pieces are:
   precategory_ob_1mor_2mor: A type C, and for each a,b : C, a precategory (a -1-> b)
   precategory_id_comp:      For each a : C, an object of (a -1-> a),
                             For each a b c : C, a functor (a -1-> b) × (b -1-> c) to (a -1-> c)
   precategory_data:         For each a b c d : C, an associator natural transformation
                             For each a b : C, left and right unitor natural transformations
   precategory:              Proofs that:
                             Every precategory (a -1-> b)'s homs are sets
                             The natural transformations above are isos
                             The pentagon and triangle axioms hold
 *)

(* An alternative structure would be to define a prebicategory as a
   precategory such that each hom type itself has the structure of a
   precategory, together with appropriate axioms. *)

Local Notation "C c× D" := (precategory_binproduct C D) (at level 75, right associativity).

Local Notation "a -2-> b" := (precategory_morphisms a b)(at level 50).
(* To keep it straight in my head *)
Local Notation "alpha ;v; beta" := (compose alpha beta) (at level 50, format "alpha ;v; beta", no associativity).

Definition prebicategory_ob_1mor_2mor :=
  total2 (λ C : UU, forall a b : C, precategory).

Definition bicat_ob (C : prebicategory_ob_1mor_2mor) : UU := @pr1 _ _ C.
Coercion bicat_ob : prebicategory_ob_1mor_2mor >-> UU.

Definition homprecat {C : prebicategory_ob_1mor_2mor} (a b : C) : precategory :=
  (pr2 C) a b.

Local Notation "a -1-> b" := (homprecat a b)(at level 50).

Definition prebicategory_id_comp :=
  total2 ( λ C : prebicategory_ob_1mor_2mor,
    dirprod (forall a : C, a -1-> a)
            (forall a b c : C, functor ((a -1-> b) c× (b -1-> c)) (a -1-> c))).

Definition prebicategory_ob_1mor_2mor_from_prebicategory_id_comp (C : prebicategory_id_comp) :
  prebicategory_ob_1mor_2mor := pr1 C.
Coercion prebicategory_ob_1mor_2mor_from_prebicategory_id_comp :
  prebicategory_id_comp >-> prebicategory_ob_1mor_2mor.

Definition identity_1mor {C : prebicategory_id_comp} (a : C) : a -1-> a
  := pr1 (pr2 C) a.

Definition idto1mor {C : prebicategory_id_comp} { a b : C }
  (p : a = b)
  : a -1-> b.
Proof.
  induction p.
  apply identity_1mor.
Defined.

Definition identity_2mor {C : prebicategory_id_comp} {a b : C} (f : a -1-> b)
  := identity f.

Definition compose_functor {C : prebicategory_id_comp} (a b c : C) :
  functor ((a -1-> b) c× (b -1-> c)) (a -1-> c)
  := pr2 (pr2 C) a b c.

Definition compose_1mor {C : prebicategory_id_comp} {a b c : C} (f : a -1-> b) (g : b -1-> c)
  := functor_on_objects (compose_functor a b c) (dirprodpair f g).

Local Notation "f ;1; g" := (compose_1mor f g) (at level 50, format "f ;1; g", no associativity).

Definition compose_2mor_horizontal {C : prebicategory_id_comp} {a b c : C}
           { f f' : a -1-> b } { g g' : b -1-> c }
           ( alpha : f -2-> f' ) ( beta : g -2-> g' )
  : ( f ;1; g ) -2-> ( f' ;1; g' ).
Proof.
  apply functor_on_morphisms.
  exact (precatbinprodmor alpha beta).
Defined.

Local Notation "alpha ;h; beta" := (compose_2mor_horizontal alpha beta) (at level 50, format "alpha ;h; beta").
(* TODO: come up with a reasonable precedence for ;v; ;h; *)

Definition compose_2mor_iso_horizontal {C : prebicategory_id_comp} {a b c : C}
           { f f' : a -1-> b } { g g' : b -1-> c }
           ( alpha : iso f f' ) ( beta : iso g g' )
  : iso ( f ;1; g ) ( f' ;1; g' ).
Proof.
  apply functor_on_iso.
  exact (precatbinprodiso alpha beta).
Defined.

Local Notation "alpha ;hi; beta" := (compose_2mor_iso_horizontal alpha beta) (at level 50, format "alpha ;hi; beta").

Definition associator_trans_type { C : prebicategory_id_comp } (a b c d : C) :=
  nat_trans
    (functor_composite
      (pair_functor (functor_identity _) (compose_functor b c d))
      (compose_functor a b d))
    (functor_composite
      (precategory_binproduct_assoc _ _ _)
      (functor_composite
        (pair_functor (compose_functor a b c) (functor_identity _))
        (compose_functor a c d))).

Definition left_unitor_trans_type { C : prebicategory_id_comp } (a b : C) :=
  nat_trans
    (functor_composite
      (bindelta_pair_functor
        (functor_composite (unit_functor _) (constant_functor unit_precategory _ (identity_1mor a)))
        (functor_identity _))
      (compose_functor a a b))
    (functor_identity _).

Definition right_unitor_trans_type { C : prebicategory_id_comp } (a b : C) :=
  nat_trans
    (functor_composite
      (bindelta_pair_functor
        (functor_identity _)
        (functor_composite (unit_functor _) (constant_functor unit_precategory _ (identity_1mor b))))
      (compose_functor a b b))
    (functor_identity _).

Definition prebicategory_data :=
  total2 (λ C : prebicategory_id_comp,
    dirprod
      (forall a b c d : C, associator_trans_type a b c d)
      ( dirprod
        (forall a b : C, left_unitor_trans_type a b)
        (* Right *)
        (forall a b : C, right_unitor_trans_type a b)
      )).

Definition prebicategory_id_comp_from_prebicategory_data (C : prebicategory_data) :
     prebicategory_id_comp := pr1 C.
Coercion prebicategory_id_comp_from_prebicategory_data :
  prebicategory_data >-> prebicategory_id_comp.

Definition has_2mor_sets (C : prebicategory_data) :=
  forall a b : C,
  forall f g : a -1-> b,
    isaset (f -2-> g).

Definition associator_trans {C : prebicategory_data} ( a b c d : C )
  := pr1 (pr2 C) a b c d.

Definition associator_2mor {C : prebicategory_data} { a b c d : C }
           (f : a -1-> b)
           (g : b -1-> c)
           (h : c -1-> d)
  : (f ;1; (g ;1; h)) -2-> ((f ;1; g) ;1; h).
Proof.
  set (A := associator_trans a b c d).
  unfold associator_trans_type in A.
  exact (A (precatbinprodpair f (precatbinprodpair g h))).
Defined.

Definition left_unitor_trans {C : prebicategory_data} ( a b : C )
  := pr1 (pr2 (pr2 C)) a b.

Definition left_unitor_2mor {C : prebicategory_data} { a b : C }
           (f : a -1-> b)
  : (identity_1mor a) ;1; f -2-> f.
Proof.
  set (A := left_unitor_trans a b).
  unfold left_unitor_trans_type in A.
  exact (A f).
Defined.

Definition right_unitor_trans {C : prebicategory_data} ( a b : C )
  := pr2 (pr2 (pr2 C)) a b.

Definition right_unitor_2mor {C : prebicategory_data} { a b : C }
           (f : a -1-> b)
  : f ;1; (identity_1mor b) -2-> f.
Proof.
  set (A := right_unitor_trans a b).
  unfold right_unitor_trans_type in A.
  exact (A f).
Defined.

Definition associator_and_unitors_are_iso (C : prebicategory_data)
  :=   (forall a b c d : C,
        forall (f : a -1-> b)
          (g : b -1-> c)
          (h : c -1-> d), is_iso (associator_2mor f g h))
     × (forall a b : C,
        forall f : a -1-> b, is_iso (left_unitor_2mor f))
     × (forall a b : C,
        forall g : a -1-> b, is_iso (right_unitor_2mor g)).

(* It suffices to check the pentagon/triangle axioms pointwise *)

Definition pentagon_axiom_type { C : prebicategory_data } { a b c d e : C }
  (k : a -1-> b)
  (h : b -1-> c)
  (g : c -1-> d)
  (f : d -1-> e)
  :=
    (* Anticlockwise *)
        (associator_2mor k h (g ;1; f))
    ;v; (associator_2mor (k ;1; h) g f)
   =
    (* Clockwise *)
        ((identity k) ;h; (associator_2mor h g f))
    ;v; (associator_2mor k (h ;1; g) f)
    ;v; ((associator_2mor k h g) ;h; (identity f))
  .

Definition triangle_axiom_type {C : prebicategory_data} { a b c : C }
           (f : a -1-> b)
           (g : b -1-> c)
  :=       ((identity_2mor f) ;h; (left_unitor_2mor g))
     =     (associator_2mor f (identity_1mor b) g)
       ;v; ((right_unitor_2mor f) ;h; (identity_2mor g)).

Definition prebicategory_coherence (C : prebicategory_data)
  := (forall a b c d e : C,
      forall k : a -1-> b,
      forall h : b -1-> c,
      forall g : c -1-> d,
      forall f : d -1-> e,
        pentagon_axiom_type k h g f)
     ×
     (forall a b c : C,
      forall f : a -1-> b,
      forall g : b -1-> c,
        triangle_axiom_type f g).

Definition is_prebicategory (C : prebicategory_data) :=
                (has_2mor_sets C)
              × (associator_and_unitors_are_iso C)
              × (prebicategory_coherence C).

Definition prebicategory := total2 is_prebicategory.

Definition prebicategory_data_from_prebicategory (C : prebicategory) :
       prebicategory_data := pr1 C.
Coercion prebicategory_data_from_prebicategory : prebicategory >-> prebicategory_data.

Definition prebicategory_has_2mor_sets {C : prebicategory} (a b : C)
  : has_homsets (a -1-> b)
  := (pr1 (pr2 C)) a b.

Definition has_homcats (C : prebicategory)
  := forall a b : C, is_univalent (a -1-> b).

Definition associator {C : prebicategory} { a b c d : C }
           (f : a -1-> b)
           (g : b -1-> c)
           (h : c -1-> d)
  : iso (f ;1; (g ;1; h)) ((f ;1; g) ;1; h).
Proof.
  use tpair.
  - exact (associator_2mor _ _ _).
  - exact ((pr1 (pr1 (pr2 (pr2 C)))) a b c d f g h).
Defined.

Definition left_unitor {C : prebicategory} { a b : C }
           (f : a -1-> b)
  : iso ((identity_1mor a) ;1; f) f.
Proof.
  use tpair.
  - exact (left_unitor_2mor _).
  - exact ((pr1 (pr2 (pr1 (pr2 (pr2 C))))) a b f).
Defined.

Definition right_unitor {C : prebicategory} { a b : C }
           (f : a -1-> b)
  : iso (f ;1; (identity_1mor b)) f.
Proof.
  use tpair.
  - exact (right_unitor_2mor _).
  - exact ((pr2 (pr2 (pr1 (pr2 (pr2 C))))) a b f).
Defined.

Definition pentagon_axiom {C : prebicategory} { a b c d e: C }
  (k : a -1-> b)
  (h : b -1-> c)
  (g : c -1-> d)
  (f : d -1-> e)
  : pentagon_axiom_type k h g f
  := pr1 (pr2 (pr2 (pr2 C))) a b c d e k h g f.

Definition triangle_axiom {C : prebicategory} { a b c : C }
  (f : a -1-> b) (g : b -1-> c)
  : triangle_axiom_type f g
  := pr2 (pr2 (pr2 (pr2 C))) a b c f g.

(******************************************************************************)
(* Basics on identities and inverses *)

Lemma id_2mor_left {C : prebicategory} {b c : C}
  { g g' : b -1-> c }
  ( beta : g -2-> g' )
  : identity_2mor (identity_1mor _) ;h; beta
  = left_unitor _ ;v; beta ;v; iso_inv_from_iso (left_unitor _).
Proof.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply (nat_trans_ax (left_unitor_trans b c)).
Defined.

Lemma id_2mor_right {C : prebicategory} {a b : C}
  { f f' : a -1-> b }
  ( alpha : f -2-> f' )
  : alpha ;h; identity_2mor (identity_1mor _)
  = right_unitor _ ;v; alpha ;v; iso_inv_from_iso (right_unitor _).
Proof.
  apply iso_inv_on_left.
  apply pathsinv0.
  apply (nat_trans_ax (right_unitor_trans a b)).
Defined.

Lemma horizontal_comp_id {C : prebicategory_id_comp} {a b c : C}
  {f : a -1-> b} {g : b -1-> c}
  : identity_2mor f ;h; identity_2mor g
  = identity_2mor (f ;1; g).
Proof.
  unfold compose_2mor_horizontal.
  intermediate_path (functor_on_morphisms (compose_functor a b c)
            (identity (precatbinprodpair f g))).
    reflexivity.
  apply functor_id.
Defined.

Lemma inv_horizontal_comp {C : prebicategory_id_comp} {a b c : C}
      { f f' : a -1-> b } { g g' : b -1-> c }
      ( alpha : iso f f' ) ( beta : iso g g' )
  : (iso_inv_from_iso alpha) ;hi; (iso_inv_from_iso beta)
  = iso_inv_from_iso (alpha ;hi; beta).
Proof.
  unfold compose_2mor_iso_horizontal.
  rewrite precatbinprodiso_inv.
  apply functor_on_iso_inv.
Defined.

(******************************************************************************)
(* Interchange Law *)

Lemma interchange {C : prebicategory} {a b c : C}
  {f1 f2 f3 : a -1-> b} {g1 g2 g3 : b -1-> c}
  (a1 : f1 -2-> f2) (a2 : f2 -2-> f3)
  (b1 : g1 -2-> g2) (b2 : g2 -2-> g3)
  : (a1 ;v; a2) ;h; (b1 ;v; b2) = (a1 ;h; b1) ;v; (a2 ;h; b2).
Proof.
  unfold compose_2mor_horizontal.

  assert (X : (precatbinprodmor a1 b1) ;v; (precatbinprodmor a2 b2)
            = (precatbinprodmor (a1;v;a2) (b1;v;b2))) by reflexivity.
  rewrite <- X.

  apply functor_comp.
Qed.
