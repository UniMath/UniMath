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
  Import MonoidalNotations.
  Import DisplayedBifunctorNotations.
  Import DisplayedMonoidalNotations.

  Local Notation "T( D )" := (total_category D).

  (** DATA **)
  Definition total_tensor_data {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) : bifunctor_data T(D) T(D) T(D).
  Proof.
    use make_bifunctor_data.
    - intros x y.
      exact (pr1 x ⊗_{M} pr1 y ,, pr2 x ⊗⊗_{DT} pr2 y).
    - intros x y1 y2 g.
      exact (pr1 x ⊗^{M}_{l} pr1 g ,, pr2 x ⊗⊗^{DT}_{l} pr2 g).
    - intros y x1 x2 f.
      exact (pr1 f ⊗^{M}_{r} pr1 y ,, pr2 f ⊗⊗^{DT}_{r} pr2 y).
  Defined.

  Lemma total_leftidax {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) : bifunctor_leftidax (total_tensor_data DT).
  Proof.
    intros x y.
    use total2_paths_b.
    - exact (bifunctor_leftid (monoidal_tensor M) (pr1 x) (pr1 y)).
    - exact (disp_bifunctor_leftid DT (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Lemma total_rightidax {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) : bifunctor_rightidax (total_tensor_data DT).
  Proof.
    intros y x.
    use total2_paths_b.
    - exact (bifunctor_rightid (monoidal_tensor M) (pr1 y) (pr1 x)).
    - exact (disp_bifunctor_rightid DT (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Lemma total_leftcompax {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) : bifunctor_leftcompax (total_tensor_data DT).
  Proof.
    intros x y1 y2 y3 g1 g2.
    use total2_paths_b.
    - exact (bifunctor_leftcomp (monoidal_tensor M) (pr1 x) (pr1 y1) (pr1 y2) (pr1 y3) (pr1 g1) (pr1 g2)).
    - exact (disp_bifunctor_leftcomp DT (pr1 x) (pr1 y1) (pr1 y2) (pr1 y3) (pr1 g1) (pr1 g2) (pr2 x) (pr2 y1) (pr2 y2) (pr2 y3) (pr2 g1) (pr2 g2)).
  Qed.

  Lemma total_rightcompax {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) : bifunctor_rightcompax (total_tensor_data DT).
  Proof.
    intros y x1 x2 x3 f1 f2.
    use total2_paths_b.
    - exact (bifunctor_rightcomp (monoidal_tensor M) (pr1 y) (pr1 x1) (pr1 x2) (pr1 x3) (pr1 f1) (pr1 f2)).
    - exact (disp_bifunctor_rightcomp DT (pr1 x1) (pr1 x2) (pr1 x3) (pr1 y) (pr1 f1) (pr1 f2) (pr2 x1) (pr2 x2) (pr2 x3) (pr2 y) (pr2 f1) (pr2 f2)).
  Qed.

  Lemma total_functoronmorphisms_are_equal {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) : functoronmorphisms_are_equal (total_tensor_data DT).
  Proof.
    intros x1 x2 y1 y2 f g.
    use total2_paths_b.
    - exact (bifunctor_equalwhiskers (monoidal_tensor M) (pr1 x1) (pr1 x2) (pr1 y1) (pr1 y2) (pr1 f) (pr1 g)).
    - exact (disp_bifunctor_equalwhiskers DT (pr1 x1) (pr1 x2) (pr1 y1) (pr1 y2) (pr1 f) (pr1 g) (pr2 x1) (pr2 x2) (pr2 y1) (pr2 y2) (pr2 f) (pr2 g)).
  Qed.

  Definition total_tensor {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) :
    tensor T(D) := (total_tensor_data DT ,, total_leftidax DT ,, total_rightidax DT ,, total_leftcompax DT ,, total_rightcompax DT ,, total_functoronmorphisms_are_equal DT).
  Local Notation Tt := total_tensor.

  Definition total_associatordata {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} (dα : disp_associator_data DT) : associator_data (Tt DT).
  Proof.
    intros x y z.
    use tpair.
    - exact (α_{M} (pr1 x) (pr1 y) (pr1 z)).
    - exact (dα (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)).
  Defined.
  Notation Tα := total_associatordata.

  Definition total_unit {C : category} {D : disp_cat C} {M : monoidal C} (DT : disp_tensor D M) (i : D I_{M}): T(D) := (I_{M},,i).
  Notation Tu := total_unit.

  Definition total_leftunitordata {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dlu : disp_leftunitor_data DT i) : leftunitor_data (Tt DT) (Tu DT i).
  Proof.
    intro x.
    use tpair.
    - exact (lu_{M} (pr1 x)).
    - exact (dlu (pr1 x) (pr2 x)).
  Defined.

  Definition total_rightunitordata {C : category} {D : disp_cat C} {M : monoidal C} {DT : disp_tensor D M} {i : D I_{M}} (dru : disp_rightunitor_data DT i) : rightunitor_data (Tt DT) (Tu DT i).
  Proof.
    intro x.
    use tpair.
    - exact (ru_{M} (pr1 x)).
    - exact (dru (pr1 x) (pr2 x)).
  Defined.

  Definition total_monoidaldata {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal_data D M) : (monoidal_data T(D) ).
  Proof.
    use make_monoidal_data.
    - exact (total_tensor DM).
    - exact (total_unit DM dI_{DM}).
    - exact (total_leftunitordata dlu^{DM}).
    - exact (total_rightunitordata dru^{DM}).
    - exact (total_associatordata dα^{DM}).
  Defined.

  (** PROPERTIES **)
  Lemma total_associator_nat_leftwhisker {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dαlnat : disp_associator_nat_leftwhisker dα^{DM}) : associator_nat_leftwhisker (total_associatordata dα^{DM}).
  Proof.
    intros x y z z' h.
    use total2_paths_b.
    - exact ((associatorlaw_natleft (monoidal_associatorlaw M)) (pr1 x) (pr1 y) (pr1 z) (pr1 z') (pr1 h)).
    - exact (dαlnat (pr1 x) (pr1 y) (pr1 z) (pr1 z') (pr1 h) (pr2 x) (pr2 y) (pr2 z) (pr2 z') (pr2 h)).
  Qed.

  Lemma total_associator_nat_rightwhisker {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dαrnat : disp_associator_nat_rightwhisker dα^{DM}) : associator_nat_rightwhisker (total_associatordata dα^{DM}).
  Proof.
    intros x1 x2 y z f.
    use total2_paths_b.
    - exact ((associatorlaw_natright (monoidal_associatorlaw M)) (pr1 x1) (pr1 x2) (pr1 y) (pr1 z) (pr1 f)).
    - exact (dαrnat (pr1 x1) (pr1 x2) (pr1 y) (pr1 z) (pr1 f) (pr2 x1) (pr2 x2) (pr2 y) (pr2 z) (pr2 f)).
  Qed.

  Lemma total_associator_nat_leftrightwhisker {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dαlrnat : disp_associator_nat_leftrightwhisker dα^{DM}) : associator_nat_leftrightwhisker (total_associatordata dα^{DM}).
  Proof.
    intros x y1 y2 z g.
    use total2_paths_b.
    - exact ((associatorlaw_natleftright (monoidal_associatorlaw M)) (pr1 x) (pr1 y1) (pr1 y2) (pr1 z) (pr1 g)).
    - exact (dαlrnat (pr1 x) (pr1 y1) (pr1 y2) (pr1 z) (pr1 g) (pr2 x) (pr2 y1) (pr2 y2) (pr2 z) (pr2 g)).
  Qed.

  Lemma total_associator_iso {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dαiso : disp_associator_iso dα^{DM}) : associator_iso (total_associatordata dα^{DM}).
  Proof.
    intros x y z.
    use tpair.
    - use tpair.
      + exact (pr1 (associatorlaw_iso (monoidal_associatorlaw M) (pr1 x) (pr1 y) (pr1 z))).
      + exact (pr1 ((dαiso) (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z))).
    - use tpair.
      + use total2_paths_b.
        * exact (pr1 (pr2 (associatorlaw_iso (monoidal_associatorlaw M) (pr1 x) (pr1 y) (pr1 z)))).
        * exact (pr2 (pr2 ((dαiso) (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)))).
      + use total2_paths_b.
        * exact (pr2 (pr2 (associatorlaw_iso (monoidal_associatorlaw M) (pr1 x) (pr1 y) (pr1 z)))).
        * exact (pr1 (pr2 ((dαiso) (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)))).
  Qed.

  Lemma total_associator_law {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dαiso : disp_associator_law dα^{DM}) : associator_law (total_associatordata dα^{DM}).
  Proof.
    split with (total_associator_nat_leftwhisker (disp_associatorlaw_natleft dαiso)).
    split with (total_associator_nat_rightwhisker (disp_associatorlaw_natright dαiso)).
    split with (total_associator_nat_leftrightwhisker (disp_associatorlaw_natleftright dαiso)).
    exact (total_associator_iso (disp_associatorlaw_iso dαiso)).
  Qed.

  Lemma total_leftunitor_iso {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dluiso : disp_leftunitor_iso dlu^{DM}) : leftunitor_iso (total_leftunitordata dlu^{DM}).
  Proof.
    intros x.
    use tpair.
    - use tpair.
      + exact (pr1 (pr2 (monoidal_leftunitorlaw M) (pr1 x))).
      + exact (pr1 (dluiso (pr1 x) (pr2 x))).
    - use tpair.
      + use total2_paths_b.
        * exact (pr1 (pr2 (pr2 (monoidal_leftunitorlaw M) (pr1 x)))).
        * exact (pr2 (pr2 (dluiso (pr1 x) (pr2 x)))).
      + use total2_paths_b.
        * exact (pr2 (pr2 (pr2 (monoidal_leftunitorlaw M) (pr1 x)))).
        * exact (pr1 (pr2 (dluiso (pr1 x) (pr2 x)))).
  Qed.

  Lemma total_leftunitor_nat {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dluiso : disp_leftunitor_nat dlu^{DM}) : leftunitor_nat (total_leftunitordata dlu^{DM}).
  Proof.
    intros x y f.
    use total2_paths_b.
    - exact ((pr1 (monoidal_leftunitorlaw M)) (pr1 x) (pr1 y) (pr1 f)).
    - exact (dluiso (pr1 x) (pr1 y) (pr1 f) (pr2 x) (pr2 y) (pr2 f)).
  Defined.

  Lemma total_leftunitor_law {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dluiso : disp_leftunitor_law dlu^{DM}) : leftunitor_law (total_leftunitordata dlu^{DM}).
  Proof.
    exact (total_leftunitor_nat (pr1 dluiso),,total_leftunitor_iso (pr2 dluiso)).
  Defined.

  Lemma total_rightunitor_iso {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (druiso : disp_rightunitor_iso dru^{DM}) : rightunitor_iso (total_rightunitordata dru^{DM}).
  Proof.
    intros x.
    use tpair.
    - use tpair.
      + exact (pr1 (pr2 (monoidal_rightunitorlaw M) (pr1 x))).
      + exact (pr1 (druiso (pr1 x) (pr2 x))).
    - use tpair.
      + use total2_paths_b.
        * exact (pr1 (pr2 (pr2 (monoidal_rightunitorlaw M) (pr1 x)))).
        * exact (pr2 (pr2 (druiso (pr1 x) (pr2 x)))).
      + use total2_paths_b.
        * exact (pr2 (pr2 (pr2 (monoidal_rightunitorlaw M) (pr1 x)))).
        * exact (pr1 (pr2 (druiso (pr1 x) (pr2 x)))).
  Qed.


  Lemma total_rightunitor_nat {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (druiso : disp_rightunitor_nat dru^{DM}) : rightunitor_nat (total_rightunitordata dru^{DM}).
  Proof.
    intros x y f.
    use total2_paths_b.
    - exact ((pr1 (monoidal_rightunitorlaw M)) (pr1 x) (pr1 y) (pr1 f)).
    - exact (druiso (pr1 x) (pr1 y) (pr1 f) (pr2 x) (pr2 y) (pr2 f)).
  Defined.

  Lemma total_rightunitor_law {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (druiso : disp_rightunitor_law dru^{DM}) : rightunitor_law (total_rightunitordata dru^{DM}).
  Proof.
    exact (total_rightunitor_nat (pr1 druiso),,total_rightunitor_iso (pr2 druiso)).
  Defined.

  Lemma total_triangleidentity {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dti : disp_triangle_identity dlu^{DM} dru^{DM} dα^{DM}) : triangle_identity (total_leftunitordata dlu^{DM}) (total_rightunitordata dru^{DM}) (total_associatordata dα^{DM}).
  Proof.
    intros x y.
    use total2_paths_b.
    - exact ((monoidal_triangleidentity M) (pr1 x) (pr1 y)).
    - exact (dti (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Lemma total_pentagonidentity {C : category} {D : disp_cat C} {M : monoidal C} {DM : disp_monoidal_data D M} (dpi : disp_pentagon_identity dα^{DM}) : pentagon_identity (total_associatordata dα^{DM}).
  Proof.
    intros w x y z.
    use total2_paths_b.
    - exact ((monoidal_pentagonidentity M) (pr1 w) (pr1 x) (pr1 y) (pr1 z)).
    - exact (dpi (pr1 w) (pr1 x) (pr1 y) (pr1 z) (pr2 w) (pr2 x) (pr2 y) (pr2 z)).
  Qed.

  Definition total_monoidallaws {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : monoidal_laws (total_monoidaldata DM).
  Proof.
    split with (total_associator_law (disp_monoidal_associatorlaw DM)).
    split with (total_leftunitor_law (disp_monoidal_leftunitorlaw DM)).
    split with (total_rightunitor_law (disp_monoidal_rightunitorlaw DM)).
    split with (total_triangleidentity (disp_monoidal_triangleidentity DM)).
    exact (total_pentagonidentity (disp_monoidal_pentagonidentity DM)).
  Qed.

  Definition total_monoidal {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : monoidal T(D) := (total_monoidaldata DM,, total_monoidallaws DM).

  Notation "π^{ D }" := (pr1_category D).
  Notation "TM( DM )" := (total_monoidal DM).

  Lemma projection_preserves_unit {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_unit TM(DM) M π^{D}.
  Proof.
    apply identity.
  Defined.

  Lemma projection_preserves_tensordata {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_tensordata TM(DM) M π^{D}.
  Proof.
    intros x y.
    apply identity.
  Defined.

  Definition projection_fmonoidaldata {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : fmonoidal_data TM(DM) M π^{D}
    := (projection_preserves_tensordata DM,, projection_preserves_unit DM).

  Lemma projection_preserves_tensornatleft {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_tensor_nat_left (projection_preserves_tensordata DM).
  Proof.
    intros x y1 y2 g.
    rewrite id_left.
    apply id_right.
  Qed.

  Lemma projection_preserves_tensornatright {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_tensor_nat_right (projection_preserves_tensordata DM).
  Proof.
    intros x1 x2 y f.
    rewrite id_left.
    apply id_right.
  Qed.

  Lemma projection_preserves_leftunitality {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_leftunitality (projection_preserves_tensordata DM) (projection_preserves_unit DM).
  Proof.
    intro x.
    rewrite (bifunctor_rightid M).
    rewrite id_left.
    apply id_left.
  Qed.

  Lemma projection_preserves_rightunitality {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_rightunitality (projection_preserves_tensordata DM) (projection_preserves_unit DM).
  Proof.
    intro x.
    rewrite (bifunctor_leftid M).
    rewrite id_left.
    apply id_left.
  Qed.

  Lemma projection_preserves_associativity {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_associativity (projection_preserves_tensordata DM).
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

  (* currently incompatible
  Definition projection_fmonoidal_laws {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : fmonoidal_laws (projection_fmonoidaldata DM)
    := (projection_preserves_tensornatleft DM,, projection_preserves_tensornatright DM,, projection_preserves_associativity DM,, projection_preserves_leftunitality DM,, projection_preserves_rightunitality DM).


  Definition projection_fmonoidal {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : fmonoidal  TM(DM) M π^{D}
    := (projection_fmonoidaldata DM,, projection_fmonoidal_laws DM).
*)

  Definition projection_preservestensor_strictly {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_tensor_strictly (projection_preserves_tensordata DM).
  Proof.
    intros x y.
    use tpair.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition projection_preservesunit_strictly {C : category} {D : disp_cat C} {M : monoidal C} (DM : disp_monoidal D M) : preserves_unit_strictly (projection_preserves_unit DM).
  Proof.
    use tpair.
    - apply idpath.
    - apply idpath.
  Qed.

End MonoidalTotalCategory.
