Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductPrecategory.

(******************************************************************************)
(* Definition of a prebicategory *)

Local Notation "a -2-> b" := (precategory_morphisms a b)(at level 50).
(* To keep it straight in my head *)
Local Notation "alpha ;v; beta" := (compose alpha beta) (at level 50, format "alpha ;v; beta").

Definition prebicategory_ob_1mor_2mor :=
  total2 (fun C : UU => forall a b : C, precategory_data).

Definition bicat_ob (C : prebicategory_ob_1mor_2mor) : UU := @pr1 _ _ C.
Coercion bicat_ob : prebicategory_ob_1mor_2mor >-> UU.

Definition homprecat_data {C : prebicategory_ob_1mor_2mor} (a b : C) : precategory_data :=
  (pr2 C) a b.

Local Notation "a -1-> b" := (homprecat_data a b)(at level 50).

Definition prebicategory_id_comp :=
  total2 ( fun C : prebicategory_ob_1mor_2mor =>
    dirprod (forall a : C, a -1-> a)
            (forall a b c : C, functor_data (product_precategory_data (a -1-> b) (b -1-> c)) (a -1-> c))).

Definition prebicategory_ob_1mor_2mor_from_prebicategory_id_comp (C : prebicategory_id_comp) :
  prebicategory_ob_1mor_2mor := pr1 C.
Coercion prebicategory_ob_1mor_2mor_from_prebicategory_id_comp :
  prebicategory_id_comp >-> prebicategory_ob_1mor_2mor.

Definition identity_1mor {C : prebicategory_id_comp} (a : C) : a -1-> a
  := pr1 (pr2 C) a.

Definition identity_2mor {C : prebicategory_id_comp} {a b : C} (f : a -1-> b)
  := identity f.

Definition compose_functor_data {C : prebicategory_id_comp} (a b c : C) :
  functor_data (product_precategory_data (a -1-> b) (b -1-> c)) (a -1-> c)
  := pr2 (pr2 C) a b c.

Definition compose_1mor {C : prebicategory_id_comp} {a b c : C} (f : a -1-> b) (g : b -1-> c)
  := functor_on_objects (compose_functor_data a b c) (dirprodpair f g).

Local Notation "f ;1; g" := (compose_1mor f g) (at level 50, format "f ;1; g").

Definition compose_2mor_horizontal {C : prebicategory_id_comp} {a b c : C}
           { f f' : a -1-> b } { g g' : b -1-> c }
           ( alpha : f -2-> f' ) ( beta : g -2-> g' )
  : ( f ;1; g ) -2-> ( f' ;1; g' ).
Proof.
  apply functor_on_morphisms.
  unfold precategory_morphisms.
  simpl.
  exact (dirprodpair alpha beta).
Qed.

Local Notation "alpha ;h; beta" := (compose_2mor_horizontal alpha beta) (at level 50, format "alpha ;h; beta").
(* TODO: come up with a reasonable precedence for ;v; ;h; *)

Definition prebicategory_data :=
  total2 (fun C : prebicategory_id_comp =>
    dirprod
      (* Associator *)
      ( forall a b c d : C,
        forall f : a -1-> b,
        forall g : b -1-> c,
        forall h : c -1-> d,
          ((f ;1; (g ;1; h)) -2-> ((f ;1; g) ;1; h))
      )
      (* Unitors *)
      ( dirprod
          (* Left *)
          ( forall a b : C,
            forall f : a -1-> b,
              (identity_1mor a) ;1; f -2-> f
          )
          (* Right *)
          ( forall a b : C,
            forall f : a -1-> b,
              f ;1; (identity_1mor b) -2-> f
          )
      )).

Definition prebicategory_id_comp_from_prebicategory_data (C : prebicategory_data) :
     prebicategory_id_comp := pr1 C.
Coercion prebicategory_id_comp_from_prebicategory_data :
  prebicategory_data >-> prebicategory_id_comp.

Definition has_homprecats (C : prebicategory_data) :=
  forall a b : C, is_precategory (a -1-> b).

Definition has_2mor_sets (C : prebicategory_data) :=
  forall a b : C,
  forall f g : a -1-> b,
    isaset (f -2-> g).

Definition has_compose_functors (C : prebicategory_data) :=
  forall a b c : C, is_functor (compose_functor_data a b c).

Definition associator {C : prebicategory_data} { a b c d : C }
           (f : a -1-> b)
           (g : b -1-> c)
           (h : c -1-> d)
  : (f ;1; (g ;1; h)) -2-> ((f ;1; g) ;1; h)
  := pr1 (pr2 C) a b c d f g h.

Definition left_unitor {C : prebicategory_data} { a b : C }
           (f : a -1-> b)
  := pr1 (pr2 (pr2 C)) a b f.

Definition right_unitor {C : prebicategory_data} { a b : C }
           (f : a -1-> b)
  := pr2 (pr2 (pr2 C)) a b f.

Definition associator_and_unitors_are_iso (C : prebicategory_data)
  :=   (forall a b c d : C,
        forall (f : a -1-> b)
          (g : b -1-> c)
          (h : c -1-> d), is_iso (associator f g h))
     × (forall a b : C,
        forall f : a -1-> b, is_iso (left_unitor f))
     × (forall a b : C,
        forall g : a -1-> b, is_iso (right_unitor g)).

Definition associator_domain {C : prebicategory_data} ( a b c d : C )
  := (functor_composite_data
       (product_functor_data (functor_identity_data _) (compose_functor_data b c d))
       (compose_functor_data a b d)).

Definition associator_codomain {C : prebicategory_data} ( a b c d : C )
  := (functor_composite_data
        (product_precategory_assoc_data _ _ _)
        (functor_composite_data
           (product_functor_data (compose_functor_data a b c) (functor_identity_data _))
           (compose_functor_data a c d))).

Definition associator_as_trans {C : prebicategory_data} ( a b c d : C ) :
  forall x : product_precategory_data (a -1-> b)
       (product_precategory_data (b -1-> c) (c -1-> d)),
  associator_domain a b c d x -2-> associator_codomain a b c d x.
Proof.
  intros.
  induction x as [f x].
  induction x as [g h].
  exact (associator f g h).
Qed.

Definition left_unitor_as_trans {C : prebicategory_data} ( a b : C ) :
  forall x : _,
    (functor_composite_data
       (pair_functor_data
          (functor_composite_data (unit_functor _) (ob_as_functor_data (identity_1mor a)))
          (functor_identity _))
       (compose_functor_data a a b))
       x
   -2-> functor_identity (a -1-> b) x.
Proof.
  intros x.
  exact (left_unitor x).
Qed.

Definition right_unitor_as_trans {C : prebicategory_data} ( a b : C ) :
  forall x : _,
    (functor_composite_data
       (pair_functor_data
          (functor_identity _)
          (functor_composite_data (unit_functor _) (ob_as_functor_data (identity_1mor b))))
       (compose_functor_data a b b))
       x
   -2-> functor_identity (a -1-> b) x.
Proof.
  intros x.
  exact (right_unitor x).
Qed.

Definition associator_and_unitors_are_natural (C : prebicategory_data)
  := (forall a b c d : C, is_nat_trans _ _ (associator_as_trans a b c d))
   × (forall a b     : C, is_nat_trans _ _ (left_unitor_as_trans a b))
   × (forall a b     : C, is_nat_trans _ _ (right_unitor_as_trans a b)).

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
                (has_homprecats C)
              × (has_2mor_sets C)
              × (has_compose_functors C)
              × (associator_and_unitors_are_natural C)
              × (associator_and_unitors_are_iso C)
              × (prebicategory_coherence C).

(******************************************************************************)
(* The prebicategory of precategories *)
