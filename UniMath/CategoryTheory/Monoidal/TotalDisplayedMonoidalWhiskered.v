Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section MonoidalTotalCategory.

  Import BifunctorNotations.
  Import MonoidalCategoryNotations.
  Import DisplayedBifunctorNotations.
  Import DisplayedMonoidalCategoryNotations.

  (* Variable C : category.
  Variable D : disp_cat C.
  Variable M : monoidalcategory C. *)

  Local Notation "T( D )" := (total_category D).

  (** DATA **)
  Definition totalcategory_tensor_data {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) : bifunctor_data T(D) T(D) T(D).
  Proof.
    use make_bifunctor_data.
    - intros x y.
      exact (pr1 x ⊗_{M} pr1 y ,, pr2 x ⊗⊗_{DT} pr2 y).
    - intros x y1 y2 g.
      exact (pr1 x ⊗^{M}_{l} pr1 g ,, pr2 x ⊗⊗^{DT}_{l} pr2 g).
    - intros y x1 x2 f.
      exact (pr1 f ⊗^{M}_{r} pr1 y ,, pr2 f ⊗⊗^{DT}_{r} pr2 y).
  Defined.

  Lemma totalcategory_leftidax {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) : bifunctor_leftidax (totalcategory_tensor_data DT).
  Proof.
    intros x y.
    use total2_paths_b.
    - exact (bifunctor_leftid (tensor_from_monoidalcatdata M) (pr1 x) (pr1 y)).
    - exact (disp_bifunctor_leftid DT (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Lemma totalcategory_rightidax {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) : bifunctor_rightidax (totalcategory_tensor_data DT).
  Proof.
    intros y x.
    use total2_paths_b.
    - exact (bifunctor_rightid (tensor_from_monoidalcatdata M) (pr1 y) (pr1 x)).
    - exact (disp_bifunctor_rightid DT (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Lemma totalcategory_leftcompax {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) : bifunctor_leftcompax (totalcategory_tensor_data DT).
  Proof.
    intros x y1 y2 y3 g1 g2.
    use total2_paths_b.
    - exact (bifunctor_leftcomp (tensor_from_monoidalcatdata M) (pr1 x) (pr1 y1) (pr1 y2) (pr1 y3) (pr1 g1) (pr1 g2)).
    - exact (disp_bifunctor_leftcomp DT (pr1 x) (pr1 y1) (pr1 y2) (pr1 y3) (pr1 g1) (pr1 g2) (pr2 x) (pr2 y1) (pr2 y2) (pr2 y3) (pr2 g1) (pr2 g2)).
  Qed.

  Lemma totalcategory_rightcompax {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) : bifunctor_rightcompax (totalcategory_tensor_data DT).
  Proof.
    intros y x1 x2 x3 f1 f2.
    use total2_paths_b.
    - exact (bifunctor_rightcomp (tensor_from_monoidalcatdata M) (pr1 y) (pr1 x1) (pr1 x2) (pr1 x3) (pr1 f1) (pr1 f2)).
    - exact (disp_bifunctor_rightcomp DT (pr1 x1) (pr1 x2) (pr1 x3) (pr1 y) (pr1 f1) (pr1 f2) (pr2 x1) (pr2 x2) (pr2 x3) (pr2 y) (pr2 f1) (pr2 f2)).
  Qed.

  Lemma totalcategory_functoronmorphisms_are_equal {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) : functoronmorphisms_are_equal (totalcategory_tensor_data DT).
  Proof.
    intros x1 x2 y1 y2 f g.
    use total2_paths_b.
    - exact (bifunctor_equalwhiskers (tensor_from_monoidalcatdata M) (pr1 x1) (pr1 x2) (pr1 y1) (pr1 y2) (pr1 f) (pr1 g)).
    - exact (disp_bifunctor_equalwhiskers DT (pr1 x1) (pr1 x2) (pr1 y1) (pr1 y2) (pr1 f) (pr1 g) (pr2 x1) (pr2 x2) (pr2 y1) (pr2 y2) (pr2 f) (pr2 g)).
  Qed.

  Definition totalcategory_tensor {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) :
    tensor T(D) := (totalcategory_tensor_data DT ,, totalcategory_leftidax DT ,, totalcategory_rightidax DT ,, totalcategory_leftcompax DT ,, totalcategory_rightcompax DT ,, totalcategory_functoronmorphisms_are_equal DT).
  Local Notation Tt := totalcategory_tensor.

  Definition totalcategory_associatordata {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : associator_data (Tt DT).
  Proof.
    intros x y z.
    use tpair.
    - exact ((associatordata_from_monoidalcatdata M) (pr1 x) (pr1 y) (pr1 z)).
    - exact (dα (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)).
  Defined.
  Notation Tα := totalcategory_associatordata.

  Definition totalcategory_unit {C : category} {D : disp_cat C} {M : monoidalcategory C} (DT : disp_tensor D M) (i : D (unit_from_monoidalcatdata M)): T(D) := (unit_from_monoidalcatdata M,,i).
  Notation Tu := totalcategory_unit.

  Definition totalcategory_leftunitordata {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} {i : D (unit_from_monoidalcatdata M)} (dlu : disp_leftunitor_data DT i) : leftunitor_data (Tt DT) (Tu DT i).
  Proof.
    intro x.
    use tpair.
    - exact ((leftunitordata_from_monoidalcatdata M) (pr1 x)).
    - exact (dlu (pr1 x) (pr2 x)).
  Defined.

  Definition totalcategory_rightunitordata {C : category} {D : disp_cat C} {M : monoidalcategory C} {DT : disp_tensor D M} {i : D (unit_from_monoidalcatdata M)} (dru : disp_rightunitor_data DT i) : rightunitor_data (Tt DT) (Tu DT i).
  Proof.
    intro x.
    use tpair.
    - exact ((rightunitordata_from_monoidalcatdata M) (pr1 x)).
    - exact (dru (pr1 x) (pr2 x)).
  Defined.

  Definition totalcategory_monoidalcatdata {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcat_data D M) : (monoidalcategory_data T(D) ).
  Proof.
    use make_monoidalcat_data.
    - exact (totalcategory_tensor DM).
    - exact (totalcategory_unit DM DM).
    - exact (totalcategory_leftunitordata DM).
    - exact (totalcategory_rightunitordata DM).
    - exact (totalcategory_associatordata DM).
  Defined.

  (** PROPERTIES **)
  Lemma totalcategory_tensor_assoc_nat_leftwhisker {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dαlnat : disp_tensor_assoc_nat_leftwhisker DM) : tensor_assoc_nat_leftwhisker (totalcategory_associatordata DM).
  Proof.
    intros x y z z' h.
    use total2_paths_b.
    - exact ((tensorassociator_natleft (moncat_associatorlaw M)) (pr1 x) (pr1 y) (pr1 z) (pr1 z') (pr1 h)).
    - exact (dαlnat (pr1 x) (pr1 y) (pr1 z) (pr1 z') (pr1 h) (pr2 x) (pr2 y) (pr2 z) (pr2 z') (pr2 h)).
  Qed.

  Lemma totalcategory_tensor_assoc_nat_rightwhisker {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dαrnat : disp_tensor_assoc_nat_rightwhisker DM) : tensor_assoc_nat_rightwhisker (totalcategory_associatordata DM).
  Proof.
    intros x1 x2 y z f.
    use total2_paths_b.
    - exact ((tensorassociator_natright (moncat_associatorlaw M)) (pr1 x1) (pr1 x2) (pr1 y) (pr1 z) (pr1 f)).
    - exact (dαrnat (pr1 x1) (pr1 x2) (pr1 y) (pr1 z) (pr1 f) (pr2 x1) (pr2 x2) (pr2 y) (pr2 z) (pr2 f)).
  Qed.

  Lemma totalcategory_tensor_assoc_nat_leftrightwhisker {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dαlrnat : disp_tensor_assoc_nat_leftrightwhisker DM) : tensor_assoc_nat_leftrightwhisker (totalcategory_associatordata DM).
  Proof.
    intros x y1 y2 z g.
    use total2_paths_b.
    - exact ((tensorassociator_natleftright (moncat_associatorlaw M)) (pr1 x) (pr1 y1) (pr1 y2) (pr1 z) (pr1 g)).
    - exact (dαlrnat (pr1 x) (pr1 y1) (pr1 y2) (pr1 z) (pr1 g) (pr2 x) (pr2 y1) (pr2 y2) (pr2 z) (pr2 g)).
  Qed.

  Lemma totalcategory_tensor_assoc_iso {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dαiso : disp_tensor_assoc_iso DM) : tensor_assoc_iso (totalcategory_associatordata DM).
  Proof.
    intros x y z.
    use tpair.
    - use tpair.
      + exact (pr1 ((tensorassociator_iso (moncat_associatorlaw M)) (pr1 x) (pr1 y) (pr1 z))).
      + exact (pr1 ((dαiso) (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z))).
    - use tpair.
      + use total2_paths_b.
        * exact (pr1 (pr2 (tensorassociator_iso (moncat_associatorlaw M) (pr1 x) (pr1 y) (pr1 z)))).
        * exact (pr2 (pr2 ((dαiso) (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)))).
      + use total2_paths_b.
        * exact (pr2 (pr2 (tensorassociator_iso (moncat_associatorlaw M) (pr1 x) (pr1 y) (pr1 z)))).
        * exact (pr1 (pr2 ((dαiso) (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)))).
  Qed.

  Lemma totalcategory_tensor_assoc_law {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dαiso : disp_assoc_law DM) : associator_law (totalcategory_associatordata DM).
  Proof.
    split with (totalcategory_tensor_assoc_nat_leftwhisker (disp_tensorassoc_natleft dαiso)).
    split with (totalcategory_tensor_assoc_nat_rightwhisker (disp_tensorassoc_natright dαiso)).
    split with (totalcategory_tensor_assoc_nat_leftrightwhisker (disp_tensorassoc_natleftright dαiso)).
    exact (totalcategory_tensor_assoc_iso (disp_tensorassoc_iso dαiso)).
  Qed.

  Lemma totalcategory_leftunitor_iso {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dluiso : disp_leftunitor_iso DM) : leftunitor_iso (totalcategory_leftunitordata DM).
  Proof.
    intros x.
    use tpair.
    - use tpair.
      + exact (pr1 (pr2 (moncat_leftunitorlaw M) (pr1 x))).
      + exact (pr1 (dluiso (pr1 x) (pr2 x))).
    - use tpair.
      + use total2_paths_b.
        * exact (pr1 (pr2 (pr2 (moncat_leftunitorlaw M) (pr1 x)))).
        * exact (pr2 (pr2 (dluiso (pr1 x) (pr2 x)))).
      + use total2_paths_b.
        * exact (pr2 (pr2 (pr2 (moncat_leftunitorlaw M) (pr1 x)))).
        * exact (pr1 (pr2 (dluiso (pr1 x) (pr2 x)))).
  Qed.

  Lemma totalcategory_leftunitor_nat {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dluiso : disp_leftunitor_nat DM) : leftunitor_nat (totalcategory_leftunitordata DM).
  Proof.
    intros x y f.
    use total2_paths_b.
    - exact ((pr1 (moncat_leftunitorlaw M)) (pr1 x) (pr1 y) (pr1 f)).
    - exact (dluiso (pr1 x) (pr1 y) (pr1 f) (pr2 x) (pr2 y) (pr2 f)).
  Defined.

  Lemma totalcategory_leftunitor_law {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dluiso : disp_leftunitor_law DM) : leftunitor_law (totalcategory_leftunitordata DM).
  Proof.
    exact (totalcategory_leftunitor_nat (pr1 dluiso),,totalcategory_leftunitor_iso (pr2 dluiso)).
  Defined.

  Lemma totalcategory_rightunitor_iso {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (druiso : disp_rightunitor_iso DM) : rightunitor_iso (totalcategory_rightunitordata DM).
  Proof.
    intros x.
    use tpair.
    - use tpair.
      + exact (pr1 (pr2 (moncat_rightunitorlaw M) (pr1 x))).
      + exact (pr1 (druiso (pr1 x) (pr2 x))).
    - use tpair.
      + use total2_paths_b.
        * exact (pr1 (pr2 (pr2 (moncat_rightunitorlaw M) (pr1 x)))).
        * exact (pr2 (pr2 (druiso (pr1 x) (pr2 x)))).
      + use total2_paths_b.
        * exact (pr2 (pr2 (pr2 (moncat_rightunitorlaw M) (pr1 x)))).
        * exact (pr1 (pr2 (druiso (pr1 x) (pr2 x)))).
  Qed.


  Lemma totalcategory_rightunitor_nat {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (druiso : disp_rightunitor_nat DM) : rightunitor_nat (totalcategory_rightunitordata DM).
  Proof.
    intros x y f.
    use total2_paths_b.
    - exact ((pr1 (moncat_rightunitorlaw M)) (pr1 x) (pr1 y) (pr1 f)).
    - exact (druiso (pr1 x) (pr1 y) (pr1 f) (pr2 x) (pr2 y) (pr2 f)).
  Defined.

  Lemma totalcategory_rightunitor_law {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (druiso : disp_rightunitor_law DM) : rightunitor_law (totalcategory_rightunitordata DM).
  Proof.
    exact (totalcategory_rightunitor_nat (pr1 druiso),,totalcategory_rightunitor_iso (pr2 druiso)).
  Defined.

  Lemma totalcategory_triangleidentity {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dti : disp_triangle_identity DM DM DM) : triangle_identity (totalcategory_leftunitordata DM) (totalcategory_rightunitordata DM) (totalcategory_associatordata DM).
  Proof.
    intros x y.
    use total2_paths_b.
    - exact ((moncat_triangleidentity M) (pr1 x) (pr1 y)).
    - exact (dti (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Lemma totalcategory_pentagonidentity {C : category} {D : disp_cat C} {M : monoidalcategory C} {DM : disp_monoidalcat_data D M} (dpi : disp_pentagon_identity DM) : pentagon_identity (totalcategory_associatordata DM).
  Proof.
    intros w x y z.
    use total2_paths_b.
    - exact ((moncat_pentagonidentity M) (pr1 w) (pr1 x) (pr1 y) (pr1 z)).
    - exact (dpi (pr1 w) (pr1 x) (pr1 y) (pr1 z) (pr2 w) (pr2 x) (pr2 y) (pr2 z)).
  Qed.

  Definition totalcategory_monoidallaws {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : monoidal_laws (totalcategory_monoidalcatdata DM).
  Proof.
    split with (totalcategory_tensor_assoc_law (disp_moncat_associator DM)).
    split with (totalcategory_leftunitor_law (disp_moncat_leftunitorlaw DM)).
    split with (totalcategory_rightunitor_law (disp_moncat_rightunitorlaw DM)).
    split with (totalcategory_triangleidentity (disp_moncat_triangleidentity DM)).
    exact (totalcategory_pentagonidentity (disp_moncat_pentagonidentity DM)).
  Qed.

  Definition totalcategory_monoidalcat {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M) : monoidalcategory T(D) := (totalcategory_monoidalcatdata DM,, totalcategory_monoidallaws DM).

  Context {C : category} {D : disp_cat C} {M : monoidalcategory C} (DM : disp_monoidalcategory D M).
  Notation π := (pr1_category D).
  Notation TM := (totalcategory_monoidalcat DM).

  Lemma projection_preserves_unit : preserves_unit TM M π.
  Proof.
    apply identity.
  Defined.

  Definition projection_preserves_tensor_data :  binat_trans_data (functor_tensorofimages π M) (functor_imageoftensor TM π).
  Proof.
    intros x y.
    apply identity.
  Defined.

  Definition projection_preserves_tensor_nat : is_binat_trans (projection_preserves_tensor_data).
  Proof.
   use tpair.
   - intros x y1 y2 g.
     rewrite id_right.
     rewrite id_left.
     apply idpath.
   - intros x1 x2 y f.
     rewrite id_right.
     rewrite id_left.
     apply idpath.
  Qed.

  Definition projection_preserves_tensor : preserves_tensor TM M π
    := (projection_preserves_tensor_data,, projection_preserves_tensor_nat).

  Definition projection_monoidalfunctor_data : monoidalfunctor_data TM M π
    := (projection_preserves_tensor,, projection_preserves_unit).

  Lemma projection_preserves_leftunitality : preserves_leftunitality TM M π projection_preserves_tensor projection_preserves_unit.
  Proof.
    intro x.
    rewrite (bifunctor_rightid M).
    rewrite id_left.
    apply id_left.
  Qed.

  Lemma projection_preserves_rightunitality : preserves_rightunitality TM M π projection_preserves_tensor projection_preserves_unit.
  Proof.
    intro x.
    rewrite (bifunctor_leftid M).
    rewrite id_left.
    apply id_left.
  Qed.

  Lemma projection_preserves_associativity : preserves_associativity TM M π projection_preserves_tensor.
  Proof.
    intros x y z.
    rewrite (bifunctor_leftid M).
    rewrite id_right.
    rewrite id_right.
    rewrite (bifunctor_rightid M).
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition projection_monoidalfunctor_laws : monoidalfunctor_laws TM M π projection_monoidalfunctor_data
    := (projection_preserves_associativity,, projection_preserves_leftunitality,, projection_preserves_rightunitality).


  Definition projection_monoidalfunctor : monoidalfunctor TM M π
    := (projection_monoidalfunctor_data,, projection_monoidalfunctor_laws).

  Definition projection_preservestensor_strictly : preserves_tensor_strictly TM M π projection_preserves_tensor.
  Proof.
    intros x y.
    use tpair.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition projection_preservesunit_strictly : preserves_unit_strictly TM M π projection_preserves_unit.
  Proof.
    use tpair.
    - apply idpath.
    - apply idpath.
  Qed.

End MonoidalTotalCategory.
