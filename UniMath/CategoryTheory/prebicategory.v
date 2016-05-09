Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Arguments functor_composite {_ _ _} _ _ .

(******************************************************************************)
(* Definition of a prebicategory *)

Local Notation "C c× D" := (product_precategory C D) (at level 75, right associativity).

Local Notation "a -2-> b" := (precategory_morphisms a b)(at level 50).
(* To keep it straight in my head *)
Local Notation "alpha ;v; beta" := (compose alpha beta) (at level 50, format "alpha ;v; beta", no associativity).

Definition prebicategory_ob_1mor_2mor :=
  total2 (fun C : UU => forall a b : C, precategory).

Definition bicat_ob (C : prebicategory_ob_1mor_2mor) : UU := @pr1 _ _ C.
Coercion bicat_ob : prebicategory_ob_1mor_2mor >-> UU.

Definition homprecat {C : prebicategory_ob_1mor_2mor} (a b : C) : precategory :=
  (pr2 C) a b.

Local Notation "a -1-> b" := (homprecat a b)(at level 50).

Definition prebicategory_id_comp :=
  total2 ( fun C : prebicategory_ob_1mor_2mor =>
    dirprod (forall a : C, a -1-> a)
            (forall a b c : C, functor ((a -1-> b) c× (b -1-> c)) (a -1-> c))).

Definition prebicategory_ob_1mor_2mor_from_prebicategory_id_comp (C : prebicategory_id_comp) :
  prebicategory_ob_1mor_2mor := pr1 C.
Coercion prebicategory_ob_1mor_2mor_from_prebicategory_id_comp :
  prebicategory_id_comp >-> prebicategory_ob_1mor_2mor.

Definition identity_1mor {C : prebicategory_id_comp} (a : C) : a -1-> a
  := pr1 (pr2 C) a.

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
  unfold precategory_morphisms.
  simpl.
  exact (dirprodpair alpha beta).
Defined.

Local Notation "alpha ;h; beta" := (compose_2mor_horizontal alpha beta) (at level 50, format "alpha ;h; beta").
(* TODO: come up with a reasonable precedence for ;v; ;h; *)

Definition associator_trans { C : prebicategory_id_comp } (a b c d : C) :=
  nat_trans
    (functor_composite
      (product_functor (functor_identity _) (compose_functor b c d))
      (compose_functor a b d))
    (functor_composite
      (product_precategory_assoc _ _ _)
      (functor_composite
        (product_functor (compose_functor a b c) (functor_identity _))
        (compose_functor a c d))).

Definition left_unitor_trans { C : prebicategory_id_comp } (a b : C) :=
  nat_trans
    (functor_composite
      (pair_functor
        (functor_composite (unit_functor _) (ob_as_functor (identity_1mor a)))
        (functor_identity _))
      (compose_functor a a b))
    (functor_identity _).

Definition right_unitor_trans { C : prebicategory_id_comp } (a b : C) :=
  nat_trans
    (functor_composite
      (pair_functor
        (functor_identity _)
        (functor_composite (unit_functor _) (ob_as_functor (identity_1mor b))))
      (compose_functor a b b))
    (functor_identity _).

Definition prebicategory_data :=
  total2 (fun C : prebicategory_id_comp =>
    dirprod
      (forall a b c d : C, associator_trans a b c d)
      ( dirprod
        (forall a b : C, left_unitor_trans a b)
        (* Right *)
        (forall a b : C, right_unitor_trans a b)
      )).

Definition prebicategory_id_comp_from_prebicategory_data (C : prebicategory_data) :
     prebicategory_id_comp := pr1 C.
Coercion prebicategory_id_comp_from_prebicategory_data :
  prebicategory_data >-> prebicategory_id_comp.

Definition has_2mor_sets (C : prebicategory_data) :=
  forall a b : C,
  forall f g : a -1-> b,
    isaset (f -2-> g).

(* Is this even what I want? *)
Definition associator {C : prebicategory_data} { a b c d : C }
           (f : a -1-> b)
           (g : b -1-> c)
           (h : c -1-> d)
  : (f ;1; (g ;1; h)) -2-> ((f ;1; g) ;1; h).
Proof.
  set (A := pr1 (pr2 C) a b c d).
  unfold associator_trans in A.
  exact (A (prodcatpair f (prodcatpair g h))).
Defined.

Definition left_unitor {C : prebicategory_data} { a b : C }
           (f : a -1-> b)
  : (identity_1mor a) ;1; f -2-> f.
Proof.
  set (A := pr1 (pr2 (pr2 C)) a b).
  unfold left_unitor_trans in A.
  exact (A f).
Defined.

Definition right_unitor {C : prebicategory_data} { a b : C }
           (f : a -1-> b)
  : f ;1; (identity_1mor b) -2-> f.
Proof.
  set (A := pr2 (pr2 (pr2 C)) a b).
  unfold right_unitor_trans in A.
  exact (A f).
Defined.

Definition associator_and_unitors_are_iso (C : prebicategory_data)
  :=   (forall a b c d : C,
        forall (f : a -1-> b)
          (g : b -1-> c)
          (h : c -1-> d), is_iso (associator f g h))
     × (forall a b : C,
        forall f : a -1-> b, is_iso (left_unitor f))
     × (forall a b : C,
        forall g : a -1-> b, is_iso (right_unitor g)).

Definition pentagon_axiom { C : prebicategory_data } { a b c d e : C }
  (k : a -1-> b)
  (h : b -1-> c)
  (g : c -1-> d)
  (f : d -1-> e)
  :=
    (* Anticlockwise *)
        (associator k h (g ;1; f))
    ;v; (associator (k ;1; h) g f)
   =
    (* Clockwise *)
        ((identity k) ;h; (associator h g f))
    ;v; (associator k (h ;1; g) f)
    ;v; ((associator k h g) ;h; (identity f))
  .

Definition triangle_axiom {C : prebicategory_data} { a b c : C }
           (f : a -1-> b)
           (g : b -1-> c)
  :=       ((identity_2mor f) ;h; (left_unitor g))
     =     (associator f (identity_1mor b) g)
       ;v; ((right_unitor f) ;h; (identity_2mor g)).

Definition prebicategory_coherence (C : prebicategory_data)
  := (forall a b c d e : C,
      forall k : a -1-> b,
      forall h : b -1-> c,
      forall g : c -1-> d,
      forall f : d -1-> e,
        pentagon_axiom k h g f)
     ×
     (forall a b c : C,
      forall f : a -1-> b,
      forall g : b -1-> c,
        triangle_axiom f g).

Definition is_prebicategory (C : prebicategory_data) :=
                (has_2mor_sets C)
              × (associator_and_unitors_are_iso C)
              × (prebicategory_coherence C).

Definition prebicategory := total2 is_prebicategory.

Definition prebicategory_data_from_prebicategory (C : prebicategory) :
       prebicategory_data := pr1 C.
Coercion prebicategory_data_from_prebicategory : prebicategory >-> prebicategory_data.

(******************************************************************************)
(* Whiskering *)

Definition whisker_left {C : prebicategory} {a b c : C}
           (f : a -1-> b) {g h : b -1-> c} (alpha : g -2-> h)
  : (f ;1; g) -2-> (f ;1; h)
  := (identity_2mor f) ;h; alpha.

Definition whisker_right {C : prebicategory} {a b c : C}
           {f g : a -1-> b} (alpha : f -2-> g) (h : b -1-> c)
  : (f ;1; h) -2-> (g ;1; h)
  := alpha ;h; (identity_2mor h).

(******************************************************************************)
(* The prebicategory of precategories *)

Definition PreCat_1mor_2mor : prebicategory_ob_1mor_2mor.
Proof.
  exists hs_precategory.
  intros a b.
  exact (functor_precategory a b (hs_precategory_has_homsets b)).
Defined.

Definition PreCat_id_comp : prebicategory_id_comp.
Proof.
  exists PreCat_1mor_2mor.
  split.
  - simpl.
    exact functor_identity.
  - simpl.
    intros a b c.
    exact (functorial_composition a b c (hs_precategory_has_homsets b) (hs_precategory_has_homsets c)).
Defined.

Definition PreCat_associator (a b c d : PreCat_id_comp) : associator_trans a b c d.
Proof.
  unfold associator_trans.
  unfold nat_trans.
  use tpair.
  - intros x. (* Step 1: Give the components of the natural transformation *)
    simpl.
    exists (fun x => identity _).
    induction x as [x1 [x2 x3]].
    unfold is_nat_trans.
    intros oba oba' f.
    simpl.
    simpl in d, x1, x2, x3.
    refine (id_right d _ _ _ @ !(id_left d _ _ _)).
  - intros [x1 [x2 x3]].
    simpl in x1, x2, x3.
    intros [y1 [y2 y3]].
    intros [f1 [f2 f3]].
    apply nat_trans_eq. exact (hs_precategory_has_homsets d).
    intros oba.
    simpl.
    simpl in d.
    rewrite (id_right d _ _ _).
    rewrite (id_left d  _ _ _).
    rewrite functor_comp.
    rewrite (assoc d).
    reflexivity.
Defined.

Definition PreCat_left_unitor (a b : PreCat_id_comp) : left_unitor_trans a b.
Proof.
  unfold associator_trans.
  unfold nat_trans.
  use tpair.
  - intros x.
    exists (fun x => identity _).
    intros oba oba' f.
    simpl.
    simpl in b.
    exact (id_right b _ _ _ @ !(id_left b _ _ _)).
  - intros x x' f.
    apply nat_trans_eq. exact (hs_precategory_has_homsets b).
    intros oba.
    simpl.
    simpl in x, x'.
    simpl in a, b.
    rewrite (id_right b _ _ _).
    rewrite (id_left b _ _ _).
    rewrite functor_id.
    rewrite (id_right b _ _ _).
    reflexivity.
Defined.

Definition PreCat_right_unitor (a b : PreCat_id_comp) : right_unitor_trans a b.
Proof.
  unfold associator_trans.
  unfold nat_trans.
  use tpair.
  - intros x.
    exists (fun x => identity _).
    intros oba oba' f.
    simpl.
    simpl in b.
    exact (id_right b _ _ _ @ !(id_left b _ _ _)).
  - intros x x' f.
    apply nat_trans_eq. exact (hs_precategory_has_homsets b).
    intros oba.
    simpl.
    simpl in x, x'.
    simpl in a, b.
    rewrite (id_right b _ _ _).
    rewrite (id_left b _ _ _).
    reflexivity.
Defined.

Definition PreCat_data : prebicategory_data.
Proof.
  unfold prebicategory_data.
  exists PreCat_id_comp.
  repeat split.
  - exact PreCat_associator.
  - exact PreCat_left_unitor.
  - exact PreCat_right_unitor.
Defined.

Definition PreCat_has_2mor_set : has_2mor_sets PreCat_data.
Proof.
  unfold has_2mor_sets.
  intros a b f g.
  apply isaset_nat_trans.
  exact (hs_precategory_has_homsets b).
Defined.

Definition PreCat_associator_and_unitors_are_iso : associator_and_unitors_are_iso PreCat_data.
Proof.
  unfold associator_and_unitors_are_iso.
  repeat split.
  - intros a b c d f g h.
    unfold associator.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism. (* What is even the point of this *)
    simpl in d.
    apply (identity_is_iso d).
  - intros a b f.
    unfold left_unitor.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism.
    simpl in b.
    apply (identity_is_iso b).
  - intros a b f.
    unfold right_unitor.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism.
    simpl in b.
    apply (identity_is_iso b).
Defined.

Definition PreCat_coherence : prebicategory_coherence PreCat_data.
Proof.
  unfold prebicategory_coherence.
  split.
  - intros a b c d e k h g f.
    unfold pentagon_axiom.
    apply nat_trans_eq. exact (hs_precategory_has_homsets e).
    intros x.
    simpl.
    simpl in e.
    repeat rewrite functor_id.
    repeat rewrite (id_left e _ _ _).
    reflexivity.
  - intros a b c f g.
    unfold triangle_axiom.
    apply nat_trans_eq. exact (hs_precategory_has_homsets c).
    intros x.
    simpl.
    simpl in c.
    repeat rewrite functor_id.
    repeat rewrite (id_left c _ _ _).
    reflexivity.
Defined.

Definition PreCat : prebicategory.
Proof.
  use tpair.
  exact PreCat_data.
  unfold is_prebicategory.
  split.
  exact PreCat_has_2mor_set.
  split.
  exact PreCat_associator_and_unitors_are_iso.
  exact PreCat_coherence.
Defined.
