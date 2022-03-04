(* In this file we show:
   1. If a displayed category over a monoidal category has the structure of a displayed monoidal category,
      then has the total category the structure of a monoidal category.
   2. The projection from the total category (equipped with this monoidal structure) to the base (monoidal) category
      is a strict monoidal functor.
*)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalCurried.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.


  (* These notations come from 'MonoidalCategoriesCurried' *)
  (*Notation "x ⊗_{ T } y" := (tensoronobjects_from_tensor_cat T x y) (at level 31).
  Notation "f ⊗^{ T } g" := (tensoronmorphisms_from_tensor_cat T  _ _ _ _ f g) (at level 31).*)

  (* This comes from displayedmonoidalcategoriescurried *)
  (*Notation "a ⊗_{{ dtd }} b" := (displayedtensor_on_objects_from_displayedtensor_data dtd _ _ a b) (at level 31).
  Notation "f' ⊗^{{ dtd }} g'" := (displayedtensor_on_morphisms_from_displayedtensor_data dtd _ _ _ _ _ _ _ _ _ _ f' g'  ) (at level 31).*)

  Definition total_category_has_tensor {C : category} {T : tensor C} {D : disp_cat C} (TD : displayed_tensor T D) :
    tensor (total_category D).
  Proof.
    use tpair.

    Check (λ xa yb, (pr1 xa) ⊗_{T} (pr1 yb) ,, (pr2 xa) ⊗_{{TD}} (pr2 yb)).
    intros xa yb xa' yb' f g.
    split with (pr1 f ⊗^{T} pr1 g).
    apply (pr2 TD).
    + exact (pr2 f).
    + exact (pr2 g).
  Defined.

  Proposition total_category_has_leftunitor {C : category } {T : tensor C} {I : C} {lu : left_unitor T I} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} (dlu : displayed_leftunitor TD i lu) :
    left_unitor (total_category_has_tensor T D TD) (I,,i).
  Proof.
    use tpair.
    + intro x.
      use tpair.
      - apply lu.
      - exact ((pr1 dlu) (pr1 x) (pr2 x)).
    +  intros x y f.
       use total2_paths_b.
        - (* abstract *) (exact ((pr2 lu) (pr1 x) (pr1 y) (pr1 f))).
        - abstract (exact ((pr2 dlu) (pr1 x) (pr1 y) (pr2 x) (pr2 y) (pr1 f) (pr2 f))).
  Defined.

  Proposition total_category_has_rightunitor {C : category } {T : tensor C} {I : C} {ru : right_unitor T I} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} (dru : displayed_rightunitor TD i ru) :
    right_unitor (total_category_has_tensor T D TD) (I,,i).
  Proof.
    use tpair.
    + intro x.
      use tpair.
      - apply ru.
      - exact ((pr1 dru) (pr1 x) (pr2 x)).
    +  intros x y f.
       use total2_paths_b.
        - exact ((pr2 ru) (pr1 x) (pr1 y) (pr1 f)).
        - exact ((pr2 dru) (pr1 x) (pr1 y) (pr2 x) (pr2 y) (pr1 f) (pr2 f)).
  Defined.

  Proposition total_category_has_associator {C : category } {T : tensor C} {α : associator T} {D : disp_cat C} {TD : displayed_tensor T D} (dα : displayed_associator α TD ) :
    associator (total_category_has_tensor T D TD).
  Proof.
    use tpair.
    + intros x y z.
      use tpair.
      - exact ((pr1 α) (pr1 x) (pr1 y) (pr1 z)).
      - exact ((pr1 dα) (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)).
    + intros x x' y y' z z' f g h.
      use total2_paths_b.
      - exact ((pr2 α) (pr1 x) (pr1 x') (pr1 y) (pr1 y') (pr1 z) (pr1 z') (pr1 f) (pr1 g) (pr1 h)).
      - exact ((pr2 dα) (pr1 x) (pr1 x') (pr1 y) (pr1 y') (pr1 z) (pr1 z')
                        (pr2 x) (pr2 x') (pr2 y) (pr2 y') (pr2 z) (pr2 z')
                        (pr1 f) (pr1 g) (pr1 h) (pr2 f) (pr2 g) (pr2 h) ).
  Defined.


  Proposition total_category_has_triangle_identity {C : category} {T : tensor C} {I : C} {lu : left_unitor T I} {ru : right_unitor T I} {α : associator T} {tri : triangle_identity T I lu ru α} {D : disp_cat C} {TD : displayed_tensor T D} {i : D I} {dlu : displayed_leftunitor TD i lu} {dru : displayed_rightunitor TD i ru} {dα : displayed_associator α TD} (dtri : displayed_triangle_identity tri i dlu dru dα)
    : triangle_identity (total_category_has_tensor T D TD)  (I,,i) (total_category_has_leftunitor dlu) (total_category_has_rightunitor dru) (total_category_has_associator dα).
  Proof.
    intros x y.
    use total2_paths_b.
    + exact (tri (pr1 x) (pr1 y)).
    + exact (dtri (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Proposition total_category_has_pentagon_identity {C : category} {T : tensor C} {α : associator T} {pen : pentagon_identity T α} {D : disp_cat C} {TD : displayed_tensor T D} {dα : displayed_associator α TD} (dpen : displayed_pentagon_identity pen dα)
    : pentagon_identity (total_category_has_tensor T D TD) (total_category_has_associator dα).
  Proof.
    intros w x y z.
    use total2_paths_b.
    + exact (pen (pr1 w) (pr1 x) (pr1 y) (pr1 z)).
    + exact (dpen (pr1 w) (pr1 x) (pr1 y) (pr1 z) (pr2 w) (pr2 x) (pr2 y) (pr2 z)).
  Qed.


  Theorem total_category_is_monoidal {M : monoidal_category} (DM : displayed_monoidal_category M) : monoidal_category.
  Proof.
    split with (total_category (pr1 DM)).
    split with (total_category_has_tensor M (pr1 DM) (pr1 (pr2 DM))).
    split with (unit_extraction_of_monoidalcat M ,, pr1 (pr2 (pr2 DM))).
    split with (total_category_has_leftunitor (pr1 (pr2 (pr2 (pr2 DM))))).
    split with (total_category_has_rightunitor (pr1 (pr2 (pr2 (pr2 (pr2 DM)))))).
    split with (total_category_has_associator (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 DM))))))).
    split with (total_category_has_triangle_identity (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DM)))))))).
    exact (total_category_has_pentagon_identity (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 DM)))))))).

  Defined.
