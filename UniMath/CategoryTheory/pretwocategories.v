Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductPrecategory.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

Definition pretwoprecategory_data :=
  total2 (fun C : precategory_data =>
  total2 (fun twomor : forall a b : C, (a --> b) -> (a --> b) -> UU =>
    dirprod
      (* hom(A, B) has the data of a precategory *)
      (forall a b : C,
        let homab := precategory_ob_mor_pair _ (twomor a b) in
        dirprod (forall f : homab,
                   f --> f)
                (forall f g h : homab,
                   f --> g -> g --> h -> f --> h))
      (* hom(A, B) × hom(B, C) → hom(A, C) has an action on 2-morphisms *)
      (forall a b c : C,
        let homab := precategory_ob_mor_pair (a --> b) (twomor a b) in
        let hombc := precategory_ob_mor_pair (b --> c) (twomor b c) in
        forall fg fg' : dirprod homab hombc,
        dirprod (pr1 fg --> pr1 fg') (pr2 fg --> pr2 fg') -> twomor a c (compose (pr1 fg) (pr2 fg)) (compose (pr1 fg') (pr2 fg')))
  )).

Definition precategory_data_from_pretwoprecategory_data (C : pretwoprecategory_data) : precategory_data := pr1 C.
Coercion precategory_data_from_pretwoprecategory_data :
  pretwoprecategory_data >-> precategory_data.

Definition pretwoprecategory_twomor (C : pretwoprecategory_data) : forall a b, (a --> b) -> (a --> b) -> UU  :=
  pr1 (pr2 C).

(* This takes a really long time to check! *)
Definition homprecat_data {C : pretwoprecategory_data} (a b : C) : precategory_data :=
  tpair _
    (precategory_ob_mor_pair (a --> b) (pretwoprecategory_twomor C a b))
    ((pr1 (pr2 (pr2 C))) a b).

Local Notation "a -1-> b" := (homprecat_data a b)(at level 50).
(* The 2-morphisms will be written just with -->, unfortunately? *)

Definition has_homprecats (C : pretwoprecategory_data) :=
  forall a b : C, is_precategory (a -1-> b).

Definition compose_domain {C : pretwoprecategory_data} (a b c : C) : precategory_data :=
  product_precategory_data (a -1-> b) (b -1-> c).

(* This takes a REAAALLY long time to check! *)
Definition compose_functor_data (C : pretwoprecategory_data) (a b c : C) : functor_data (compose_domain a b c) (* to *) (a -1-> c) :=
  functor_data_constr
    (compose_domain a b c) (* to *) (a -1-> c)
    (uncurry compose)
    (pr2 (pr2 (pr2 C)) a b c).

Definition has_compose_functors (C : pretwoprecategory_data) :=
   forall a b c : C, is_functor (compose_functor_data C a b c).

Definition is_pretwoprecategory (C : pretwoprecategory_data) :=
  dirprod (dirprod
    (is_precategory C)
    (has_homprecats C))
    (has_compose_functors C).

Definition pretwoprecategory := total2 is_pretwoprecategory.

Definition pretwoprecategory_data_from_pretwoprecategory (C : pretwoprecategory) :
       pretwoprecategory_data := pr1 C.
Coercion pretwoprecategory_data_from_pretwoprecategory :
  pretwoprecategory >-> pretwoprecategory_data.
