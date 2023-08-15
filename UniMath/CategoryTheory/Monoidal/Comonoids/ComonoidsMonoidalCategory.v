(*
In this file, it is shown how the (displayed) category of comonoids (resp. commutative comonoids) is (displayed) symmetric.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.MonoidalSections.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Sigma.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.SymmetricMonoidalBuilder.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Comonoids.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsCategory.

Local Open Scope cat.
Import MonoidalNotations.

Section SymmetricMonoidalCategoryOfComonoids.

  Context {C : category} {M : monoidal C} (S : symmetric M).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Notation "σ_{ x , y }" := (monoidal_braiding_data (symmetric_to_braiding S) x y).
  Notation "μ_{ m }" := (comonoid_data_comultiplication _ m).
  Notation "η_{ m }" := (comonoid_data_counit _ m).

  Let S_nat_l := (pr112 S).
  Let S_nat_r := (pr212 S).
  Let S_iso := (pr122 S).
  Let S_pent1 := (pr1(pr222 S)).
  Let S_pent2 := (pr2(pr222 S)).

  Definition tensor_of_comonoids_data
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid_data M (x ⊗ y).
  Proof.
    split.
    - refine (μ_{mx} ⊗⊗ μ_{my} · _).
      exact (rearrange_prod S x x y y).
    - refine (η_{mx} ⊗⊗ η_{my} · lu _).
  Defined.

  Lemma precompose_rearrange_prod_with_augs_on_left
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : rearrange_prod S x x y y · (η_{ mx} ⊗^{ M} η_{ my}) ⊗^{ M}_{r} (x ⊗_{ M} y)
      = (η_{ mx} ⊗r _) ⊗⊗ (η_{ my} ⊗r y) · rearrange_prod S _ _ _ _.
  Proof.
    set (t := precompose_rearrange_prod S η_{mx} (identity x)  η_{my} (identity y)).
    refine (_ @ t @ _).
    - rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply M)).
    - now rewrite <- ! (when_bifunctor_becomes_rightwhiskering M).
  Qed.

  Lemma precompose_rearrange_prod_with_diag_on_left
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : rearrange_prod S x x y y · (μ_{ mx} ⊗^{ M} μ_{ my}) ⊗^{ M}_{r} (x ⊗_{ M} y)
      = (μ_{ mx} ⊗r _) ⊗⊗ (μ_{ my} ⊗r y) · rearrange_prod S _ _ _ _.
  Proof.
    set (t := precompose_rearrange_prod S μ_{mx} (identity x) μ_{my} (identity y)).
    refine (_ @ t @ _).
    - rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply M)).
    - now rewrite <- ! (when_bifunctor_becomes_rightwhiskering M).
  Qed.

  Lemma precompose_rearrange_prod_with_augs_on_right
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : rearrange_prod S x x y y · (x ⊗_{ M} y) ⊗^{ M}_{l} (η_{ mx} ⊗^{ M} η_{ my})
      = (_ ⊗l η_{ mx}) ⊗⊗ (_ ⊗l η_{ my}) · rearrange_prod S _ _ _ _.
  Proof.
    set (t := precompose_rearrange_prod S (identity x) η_{mx} (identity y)  η_{my}).
    refine (_ @ t @ _).
    - rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply M)).
    - now rewrite <- ! (when_bifunctor_becomes_leftwhiskering M).
  Qed.

  Lemma precompose_rearrange_prod_with_diag_on_right
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : rearrange_prod S x x y y · (x ⊗_{ M} y) ⊗^{ M}_{l} (μ_{ mx} ⊗^{ M} μ_{ my})
      = (_ ⊗l μ_{ mx}) ⊗⊗ (_ ⊗l μ_{ my}) · rearrange_prod S _ _ _ _.
  Proof.
    set (t := precompose_rearrange_prod S (identity x) μ_{mx} (identity y) μ_{my}).
    refine (_ @ t @ _).
    - rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply M)).
    - now rewrite <- ! (when_bifunctor_becomes_leftwhiskering M).
  Qed.

  Lemma tensor_of_comonoids_laws_unit_left
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid_laws_unit_left M (tensor_of_comonoids_data mx my).
  Proof.
    unfold comonoid_laws_unit_left.
    cbn.
    rewrite (bifunctor_rightcomp M).
    rewrite ! assoc.
    etrans. {
      do 2 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply precompose_rearrange_prod_with_augs_on_left.
    }

    rewrite assoc.
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    etrans. {
      rewrite ! assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (precompose_rearrange_prod_with_lunitors_on_right S x y).
    }

    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    etrans. {
      apply maponpaths.
      exact (pr12 my).
    }
    etrans. {
      apply maponpaths_2.
      exact (pr12 mx).
    }
    apply (bifunctor_distributes_over_id (F := M)) ; apply M.
  Qed.

  Lemma tensor_of_comonoids_laws_unit_right
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid_laws_unit_right M (tensor_of_comonoids_data mx my).
  Proof.
    unfold comonoid_laws_unit_right.
    cbn.
    rewrite (bifunctor_leftcomp M).
    rewrite ! assoc.
    etrans. {
      do 2 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply precompose_rearrange_prod_with_augs_on_right.
    }

    rewrite assoc.
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    etrans. {
      rewrite ! assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (precompose_rearrange_prod_with_lunitors_and_runitor S x y).
    }

    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    etrans. {
      apply maponpaths.
      exact (pr122 my).
    }
    etrans. {
      apply maponpaths_2.
      exact (pr122 mx).
    }
    apply (bifunctor_distributes_over_id (F := M)) ; apply M.
  Qed.

  Lemma tensor_of_comonoids_laws_assoc
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid_laws_assoc M (tensor_of_comonoids_data mx my).
  Proof.
    unfold comonoid_laws_assoc.
    cbn.

    rewrite ! assoc'.
    rewrite (bifunctor_rightcomp M).

    etrans. {
      apply maponpaths.
      apply pathsinv0.
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      apply pathsinv0.
      apply precompose_rearrange_prod_with_diag_on_left.
    }

    rewrite (bifunctor_leftcomp M).
    etrans.
    2: {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply pathsinv0.
      apply precompose_rearrange_prod_with_diag_on_right.
    }

    set (ax := comonoid_to_assoc_law M mx).
    set (ay := comonoid_to_assoc_law M my).
    unfold comonoid_laws_assoc in ax, ay.

    rewrite ! assoc.
    rewrite <- ! (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite <- ax.
    rewrite <- ay.
    clear ax ay.
    rewrite ! (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite ! assoc'.
    do 2 apply maponpaths.
    apply rearrange_hexagon.
  Qed.

  Lemma tensor_of_comonoids_laws
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid_laws M (tensor_of_comonoids_data mx my).
  Proof.
    refine (_ ,, _ ,, _).
    - exact (tensor_of_comonoids_laws_unit_left mx my).
    - exact (tensor_of_comonoids_laws_unit_right mx my).
    - exact (tensor_of_comonoids_laws_assoc mx my).
  Qed.

  Definition tensor_of_comonoids
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid M (x ⊗ y)
    := _ ,, tensor_of_comonoids_laws mx my.

  Definition tensor_of_comonoid_mor_mult_left
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor_mult M yy1 yy2 g)
    : is_comonoid_mor_mult M (tensor_of_comonoids xx yy1) (tensor_of_comonoids xx yy2) (x ⊗^{ M}_{l} g).
  Proof.
    unfold is_comonoid_mor_mult in *.
    cbn.
    etrans.
    2:{
      rewrite (bifunctor_equalwhiskers M).
      unfold functoronmorphisms2.
      rewrite ! assoc.
      rewrite <- (bifunctor_leftcomp M).
      now rewrite <- gg.
    }
    clear gg.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      refine (_ @ precompose_rearrange_prod S (identity x) (identity x) g g).
      now rewrite (when_bifunctor_becomes_leftwhiskering M).
    }
    rewrite ! assoc.
    apply maponpaths_2.
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite (bifunctor_equalwhiskers M).
    unfold functoronmorphisms2.
    do 2 apply maponpaths.
    rewrite (bifunctor_distributes_over_id (F := M)) ; try (apply M).
    apply id_right.
  Qed.

  Definition tensor_of_comonoid_mor_unit_left
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor_unit M yy1 yy2 g)
    : is_comonoid_mor_unit M (tensor_of_comonoids xx yy1) (tensor_of_comonoids xx yy2) (x ⊗^{ M}_{l} g).
  Proof.
    unfold is_comonoid_mor_unit.
    cbn.
    unfold is_comonoid_mor_unit in gg.
    rewrite assoc.
    apply maponpaths_2.
    rewrite <- gg.
    rewrite <- (when_bifunctor_becomes_leftwhiskering M).
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    apply maponpaths_2.
    apply id_left.
  Qed.

  Definition tensor_of_comonoid_mor_left
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor M yy1 yy2 g)
    : is_comonoid_mor M (tensor_of_comonoids xx yy1) (tensor_of_comonoids xx yy2) (x ⊗^{ M}_{l} g).
  Proof.
    split.
    - apply (tensor_of_comonoid_mor_mult_left (pr1 gg)).
    - apply (tensor_of_comonoid_mor_unit_left (pr2 gg)).
  Qed.

  Definition comonoid_disp_unit_data
    : comonoid_data M (monoidal_unit M).
  Proof.
    exists (luinv _).
    apply identity.
  Defined.

  Lemma comonoid_disp_unit_laws
    : comonoid_laws M comonoid_disp_unit_data.
  Proof.
    refine (_ ,, _ ,, _).
    - unfold comonoid_laws_unit_left.
      cbn.
      rewrite (bifunctor_rightid M).
      rewrite id_right.
      apply monoidal_leftunitorisolaw.
    - unfold comonoid_laws_unit_right.
      cbn.
      rewrite (bifunctor_leftid M).
      rewrite id_right.
      rewrite <- unitors_coincide_on_unit.
      apply monoidal_leftunitorisolaw.
    - unfold comonoid_laws_assoc.
      cbn.
      rewrite ! assoc'.
      apply maponpaths.
      apply lunitorinv_preserves_leftwhiskering_with_unit.
  Qed.

  Definition comonoid_disp_unit
    :  comonoid_disp_cat M (monoidal_unit M).
  Proof.
    exists comonoid_disp_unit_data.
    exact comonoid_disp_unit_laws.
  Defined.

  Lemma comonoid_disp_lunitor
    {x : C} (mx : comonoid M x)
    : is_comonoid_mor M (tensor_of_comonoids comonoid_disp_unit mx) mx lu^{ M }_{ x}.
  Proof.
    split.
    - unfold is_comonoid_mor_mult.
      cbn.
      rewrite <- (precompose_rearrange_prod_with_lunitors_on_right S).
      refine (_ @ monoidal_leftunitornat M _ _ μ_{mx}).
      rewrite ! assoc.
      apply maponpaths_2.

      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply rearrange_prod_inv.
      }
      rewrite id_right.
      rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
      rewrite id_right.
      rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      apply maponpaths_2.
      exact (pr2 (monoidal_leftunitorisolaw M I_{M})).
    - refine (! monoidal_leftunitornat M _ _ η_{mx} @ _).
      simpl.
      apply maponpaths_2.
      apply pathsinv0, (when_bifunctor_becomes_leftwhiskering M).
  Qed.

  Lemma comonoid_disp_lunitor_inv
    {x : C} (mx : comonoid M x)
    :  is_comonoid_mor M mx (tensor_of_comonoids comonoid_disp_unit mx) luinv^{ M }_{ x}.
  Proof.
    simpl in *.
    split.
    - unfold is_comonoid_mor_mult.
      cbn.
      use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
      {
        set (i := monoidal_leftunitorisolaw M x).
        use (is_z_iso_bifunctor_z_iso M)
        ; apply (_ ,, pr2 i ,, pr1 i).
      }
      cbn.
      rewrite <- (precompose_rearrange_prod_with_lunitors_on_right S).
      apply pathsinv0.
      etrans. {
        rewrite ! assoc'.
        do 2 apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        apply rearrange_prod_inv.
      }
      rewrite id_left.
      rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
      }
      etrans. {
        apply maponpaths.
        do 2 apply maponpaths_2.
        exact (pr2 (monoidal_leftunitorisolaw M I_{M})).
      }
      rewrite id_right.
      rewrite <- (bifunctor_equalwhiskers M).
      rewrite (when_bifunctor_becomes_leftwhiskering M).
      etrans. {
        apply maponpaths, (monoidal_leftunitornat M _ _ μ_{mx}).
      }
      rewrite assoc.
      rewrite (pr2 (monoidal_leftunitorisolaw M x)).
      apply id_left.
    - unfold is_comonoid_mor_unit.
      cbn.
      rewrite assoc.
      etrans. {
        apply maponpaths_2.
        refine (_ @ monoidal_leftunitorinvnat M _ _ η_{mx}).
        now rewrite (when_bifunctor_becomes_leftwhiskering M).
      }
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        exact (pr2 (monoidal_leftunitorisolaw M _)).
      }
      apply id_right.
  Qed.

  Lemma comonoid_disp_braiding
    {x y : C} (xx : comonoid M x) (yy : comonoid M y)
    : is_comonoid_mor M (tensor_of_comonoids xx yy) (tensor_of_comonoids yy xx) (pr1 S x y).
  Proof.
    split.
    - unfold is_comonoid_mor_mult.
      cbn.
      etrans.
      2: {
        rewrite assoc.
        apply maponpaths_2.
        apply (tensor_sym_mon_braiding ((C,,M),,S)).
      }
      rewrite ! assoc'.
      apply comult_before_rearrange_and_swap.
    - unfold is_comonoid_mor_unit.
      cbn.
      rewrite ! assoc.
      apply maponpaths_2.
      etrans. { apply pathsinv0, (tensor_sym_mon_braiding ((C,,M),,S)). }
      cbn.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (sym_mon_braiding_id ((C,,M),,S)).
  Qed.

  Lemma comonoid_disp_associator_mult
    {x y z : C}
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
    : is_comonoid_mor_mult M
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz)
        (tensor_of_comonoids xx (tensor_of_comonoids yy zz)) α^{ M }_{ x, y, z}.
  Proof.
    unfold is_comonoid_mor_mult.
    cbn.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      apply id_right.
    }
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite ! assoc.

    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply pathsinv0, associator_nat2.
    }

    rewrite ! assoc'.

    etrans. {
      apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0, id_right.
    }
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite ! assoc'.
    apply maponpaths.
    rewrite ! assoc.
    apply rearrange_hexagon'.
  Qed.

  Lemma comonoid_disp_associator_unit
    {x y z : C}
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
    : is_comonoid_mor_unit M
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz)
        (tensor_of_comonoids xx (tensor_of_comonoids yy zz)) α^{ M }_{ x, y, z}.
  Proof.
    unfold is_comonoid_mor_unit.
    cbn.
    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply (tensor_comp_l_id_l (V := C,,M)).
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    rewrite ! assoc.
    etrans. {
      do 2 apply maponpaths_2.
      apply pathsinv0, (tensor_lassociator (V := C,,M)).
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    apply maponpaths_2.
    etrans. {
      apply maponpaths_2.
      apply (tensor_lassociator (V := C,,M)).
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    rewrite assoc'.
    etrans. {
      apply maponpaths.
      apply pathsinv0.
      apply (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    }
    rewrite id_left.

    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply pathsinv0, id_right.
    }
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite assoc.

    etrans. {
      apply maponpaths_2.
      apply associator_nat2.
    }

    etrans.
    2: {
      apply maponpaths.
      apply id_right.
    }
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite assoc'.
    apply maponpaths.
    apply associator_before_lwhisker_with_lu.
  Qed.

  Lemma comonoid_disp_associator
    {x y z : C}
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
    : is_comonoid_mor M
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz)
        (tensor_of_comonoids xx (tensor_of_comonoids yy zz)) α^{ M }_{ x, y, z}.
  Proof.
    split.
    - exact (comonoid_disp_associator_mult xx yy zz).
    - exact (comonoid_disp_associator_unit xx yy zz).
  Qed.

  Lemma comonoid_disp_associatorinv_mult
    {x y z : C}
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
    : is_comonoid_mor_mult M (tensor_of_comonoids xx (tensor_of_comonoids yy zz))
     (tensor_of_comonoids (tensor_of_comonoids xx yy) zz) αinv^{ M }_{ x, y, z}.
  Proof.
    unfold is_comonoid_mor_mult.
    cbn.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths.
      apply id_right.
    }
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite ! assoc.

    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply monoidal_associatorinv_nat2.
    }

    rewrite ! assoc'.

    etrans. {
      apply maponpaths_2.
      apply maponpaths_2.
      apply pathsinv0, id_right.
    }

    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite ! assoc'.
    apply maponpaths.
    rewrite ! assoc.
    apply rearrange_hexagoninv'.
  Qed.

  Lemma comonoid_disp_associatorinv_unit {x y z : C}
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
    : is_comonoid_mor_unit M (tensor_of_comonoids xx (tensor_of_comonoids yy zz))
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz) αinv^{ M }_{ x, y, z}.
  Proof.
    unfold is_comonoid_mor_unit.
    cbn.

    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply (tensor_comp_r_id_r (V := C,,M)).
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    rewrite ! assoc.
    etrans. {
      do 2 apply maponpaths_2.
      apply pathsinv0, (tensor_rassociator (V := C,,M)).
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    apply maponpaths_2.
    etrans. {
      apply maponpaths_2.
      apply (tensor_rassociator (V := C,,M)).
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    rewrite assoc'.
    etrans. {
      apply maponpaths.
      apply pathsinv0.
      apply (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    }
    rewrite id_right.

    etrans. {
      apply maponpaths.
      apply maponpaths.
      apply pathsinv0, id_right.
    }
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite assoc.

    etrans. {
      apply maponpaths_2.
      apply pathsinv0.
      apply monoidal_associatorinv_nat2.
    }

    etrans.
    2: {
      apply maponpaths_2.
      apply id_right.
    }
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite assoc'.
    apply maponpaths.
    apply associator_before_rwhisker_with_lu.
  Qed.

  Lemma comonoid_disp_associatorinv
    {x y z : C}
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
    : is_comonoid_mor M (tensor_of_comonoids xx (tensor_of_comonoids yy zz))
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz) αinv^{M}_{x, y, z}.
  Proof.
    split.
    - exact (comonoid_disp_associatorinv_mult xx yy zz).
    - exact (comonoid_disp_associatorinv_unit xx yy zz).
  Qed.

  Definition comonoid_disp_symmetric_monoidal
    :  ∑ DM : disp_monoidal (comonoid_disp_cat M) M, disp_symmetric DM S.
  Proof.
    use make_symmetric_monoidal_disp_cat_locally_prop.
    - apply comonoid_disp_cat_locally_propositional.
    - exact (λ _ _ xx yy, tensor_of_comonoids xx yy).
    - intro ; intros ; apply tensor_of_comonoid_mor_left.
      assumption.
    - exact (λ _ _ xx yy, comonoid_disp_braiding xx yy).
    - exact comonoid_disp_unit.
    - exact (λ _ xx, comonoid_disp_lunitor xx).
    - exact (λ _ xx, comonoid_disp_lunitor_inv xx).
    - exact (λ _ _ _ xx yy zz, comonoid_disp_associator xx yy zz).
    - exact (λ _ _ _ xx yy zz, comonoid_disp_associatorinv xx yy zz).
  Defined.

  Definition monoidal_cat_of_comonoids
    : monoidal (category_of_comonoids_in_monoidal_cat M).
  Proof.
    exact (total_monoidal (pr1 comonoid_disp_symmetric_monoidal)).
  Defined.

  Definition symmetric_monoidal_cat_of_comonoids
    : symmetric monoidal_cat_of_comonoids.
  Proof.
    use total_symmetric.
    { exact S. }
    exact (pr2 comonoid_disp_symmetric_monoidal).
  Defined.

End SymmetricMonoidalCategoryOfComonoids.

Section SymmetricMonoidalCategoryOfCommutativeComonoids.

  Context {C : category} {M : monoidal C} (S : symmetric M).

  Lemma tensor_of_comm_comonoids
    {x y : C} {mx : comonoid M x} {my : comonoid M y}
    (sx : is_commutative S mx)
    (sy : is_commutative S my)
    : is_commutative S (tensor_of_comonoids S mx my).
  Proof.

    use (z_iso_inv_on_left _ _ _ _ (rearrange_prod S _ _ _ _ ,, rearrange_prod S _ _ _ _ ,, _)).
    { apply rearrange_prod_is_z_isomorphism. }
    cbn.
    unfold comonoid_data_comultiplication.
    cbn.

    rewrite assoc'.
    rewrite <- (rearrange_commute_with_swap S).
    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, (rearrange_prod_inv S).
    }
    rewrite id_right.
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    etrans.
    2: {
      apply maponpaths_2.
      apply (! sx).
    }
    apply maponpaths.
    exact (! sy).
  Qed.

  Definition disp_monoidal_cat_of_comm_comonoids
    : disp_monoidal (disp_full_sub
                       (category_of_comonoids_in_monoidal_cat M)
                       (λ x : ∑ x : C, comonoid M x, is_commutative S (pr2 x)))
        (monoidal_cat_of_comonoids S).
  Proof.
    use (disp_monoidal_fullsub _
           (λ x : category_of_comonoids_in_monoidal_cat M, (is_commutative S (pr2 x) ,, _))).
    - intro ; apply homset_property.
    - refine (_ @ id_right _).
      apply maponpaths.
      exact (sym_mon_braiding_id ((C,,M),,S)).
    - intros ? ? sx xy.
      apply (tensor_of_comm_comonoids sx xy).
  Defined.

  Definition monoidal_cat_of_comm_comonoids
    : monoidal (category_of_comm_comonoids_in_monoidal_cat S).
  Proof.
    use total_monoidal.
    - exact M.
    - use sigma_disp_cat_monoidal.
      + apply (comonoid_disp_symmetric_monoidal S).
      + apply disp_monoidal_cat_of_comm_comonoids.
      + apply comm_comonoid_disp_cat_locally_propositional.
  Defined.

  Definition disp_symmetric_monoidal_cat_of_comm_comonoids
    : disp_symmetric disp_monoidal_cat_of_comm_comonoids
        (symmetric_monoidal_cat_of_comonoids S).
  Proof.
    use tpair.
    - intro ; intros ; exact tt.
    - repeat split ; try (intro ; intros) ; apply isapropunit.
  Qed.

  Definition symmetric_monoidal_cat_of_comm_comonoids
    : symmetric monoidal_cat_of_comm_comonoids.
  Proof.
    use total_symmetric.
    - exact S.
    - use sigma_disp_cat_monoidal_symmetric.
      + apply (comonoid_disp_symmetric_monoidal S).
      + apply disp_symmetric_monoidal_cat_of_comm_comonoids.
  Defined.

End SymmetricMonoidalCategoryOfCommutativeComonoids.
