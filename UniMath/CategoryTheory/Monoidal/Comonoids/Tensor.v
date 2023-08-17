nner_swap
(*
nner_swap
In this file, the necessary ingredients to show how the (displayed) category of comonoids (resp. commutative comonoids) is (displayed) symmetric.
nner_swap
*)
nner_swap

nner_swap
Require Import UniMath.Foundations.All.
nner_swap
Require Import UniMath.MoreFoundations.All.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Core.Categories.
nner_swap
Require Import UniMath.CategoryTheory.Core.Functors.
nner_swap
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
nner_swap
Require Import UniMath.CategoryTheory.Core.Isos.
nner_swap
Require Import UniMath.CategoryTheory.limits.binproducts.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Categories.
nner_swap
Import BifunctorNotations.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Functors.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.MonoidalSections.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Examples.Sigma.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
nner_swap

nner_swap
Import MonoidalNotations.
nner_swap
Import ComonoidNotations.
nner_swap

nner_swap
Local Open Scope cat.
nner_swap
Local Open Scope moncat.
nner_swap

nner_swap
Section TensorOfComonoids.
nner_swap

nner_swap
  Context (M : sym_monoidal_cat).
nner_swap

nner_swap
  Definition tensor_of_comonoids_data
nner_swap
    (mx my : comonoid M)
nner_swap
    : comonoid_data M.
nner_swap
  Proof.
nner_swap
    exists (mx ⊗ my).
nner_swap
    split.
nner_swap
    - refine (δ_{mx} ⊗^{M} δ_{my} · _).
nner_swap
      exact (rearrange_prod M mx mx my my).
nner_swap
    - exact (ε_{mx} ⊗^{M} ε_{my} · lu^{M}_{_}).
nner_swap
  Defined.
nner_swap

nner_swap
  Lemma precompose_rearrange_prod_with_augs_on_left
nner_swap
    (mx my : comonoid M)
nner_swap
    : rearrange_prod M mx mx my my · (ε_{ mx} ⊗^{ M} ε_{ my}) ⊗^{ M}_{r} (mx ⊗_{ M} my)
nner_swap
      = (ε_{ mx} ⊗^{M}_{r} _) ⊗^{M} (ε_{ my} ⊗^{M}_{r} my) · rearrange_prod M _ _ _ _.
nner_swap
  Proof.
nner_swap
    refine (_ @ precompose_rearrange_prod (M) ε_{mx} (identity _)  ε_{my} (identity _) @ _).
nner_swap
    - rewrite <- (when_bifunctor_becomes_rightwhiskering M).
nner_swap
      do 2 apply maponpaths.
nner_swap
      apply pathsinv0, tensor_id_id.
nner_swap
    - now rewrite <- ! (when_bifunctor_becomes_rightwhiskering M).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma precompose_rearrange_prod_with_diag_on_left
nner_swap
    (mx my : comonoid M)
nner_swap
    : rearrange_prod (M) mx mx my my · (δ_{ mx} ⊗^{ M} δ_{ my}) ⊗^{ M}_{r} (mx ⊗_{ M} my)
nner_swap
      = (δ_{ mx} ⊗^{M}_{r} _) ⊗^{M} (δ_{ my} ⊗^{M}_{r} my) · rearrange_prod M _ _ _ _.
nner_swap
  Proof.
nner_swap
    refine (_ @ precompose_rearrange_prod (M) δ_{mx} (identity _) δ_{my} (identity _) @ _).
nner_swap
    - rewrite <- (when_bifunctor_becomes_rightwhiskering M).
nner_swap
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply (pr21 M))).
nner_swap
    - now rewrite <- ! (when_bifunctor_becomes_rightwhiskering M).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma precompose_rearrange_prod_with_augs_on_right
nner_swap
    (mx my : comonoid M)
nner_swap
    : rearrange_prod (M) mx mx my my · (mx ⊗_{ M} my) ⊗^{ M}_{l} (ε_{mx} ⊗^{ M} ε_{my})
nner_swap
      = (_ ⊗^{M}_{l} ε_{mx}) ⊗^{M} (_ ⊗^{M}_{l} ε_{my}) · rearrange_prod (M) _ _ _ _.
nner_swap
  Proof.
nner_swap
    refine (_ @ precompose_rearrange_prod (M) (identity _) ε_{mx} (identity _) ε_{my} @ _).
nner_swap
    - rewrite <- (when_bifunctor_becomes_leftwhiskering M).
nner_swap
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply (pr21 M))).
nner_swap
    - now rewrite <- ! (when_bifunctor_becomes_leftwhiskering M).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma precompose_rearrange_prod_with_diag_on_right
nner_swap
    (mx my : comonoid M)
nner_swap
    : rearrange_prod (M) mx mx my my · (mx ⊗_{ M} my) ⊗^{ M}_{l} (δ_{ mx} ⊗^{ M} δ_{ my})
nner_swap
      = (_ ⊗^{M}_{l} δ_{ mx}) ⊗^{M} (_ ⊗^{M}_{l} δ_{ my}) · rearrange_prod (M) _ _ _ _.
nner_swap
  Proof.
nner_swap
    refine (_ @ precompose_rearrange_prod (M) (identity _) δ_{mx} (identity _) δ_{my} @ _).
nner_swap
    - rewrite <- (when_bifunctor_becomes_leftwhiskering M).
nner_swap
      apply maponpaths.
nner_swap
      apply maponpaths_2.
nner_swap
      apply pathsinv0.
nner_swap
      apply tensor_id_id.
nner_swap
    - now rewrite <- ! (when_bifunctor_becomes_leftwhiskering M).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma tensor_of_comonoids_laws_unit_left
nner_swap
    (mx my : comonoid M)
nner_swap
    : comonoid_laws_unit_left M (tensor_of_comonoids_data mx my).
nner_swap
  Proof.
nner_swap
    unfold comonoid_laws_unit_left.
nner_swap
    cbn.
nner_swap
    rewrite (bifunctor_rightcomp M).
nner_swap
    rewrite ! assoc.
nner_swap
    etrans. {
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply precompose_rearrange_prod_with_augs_on_left.
nner_swap
    }
nner_swap

nner_swap
    rewrite assoc.
nner_swap
    etrans. {
nner_swap
      do 3 apply maponpaths_2.
nner_swap
      apply pathsinv0, tensor_comp_mor.
nner_swap
    }
nner_swap

nner_swap
    etrans. {
nner_swap
      rewrite ! assoc'.
nner_swap
      apply maponpaths.
nner_swap
      rewrite assoc.
nner_swap
      exact (precompose_rearrange_prod_with_lunitors_on_right (M) mx my).
nner_swap
    }
nner_swap
    cbn.
nner_swap
    etrans. {
nner_swap
      apply pathsinv0.
nner_swap
      apply tensor_comp_mor.
nner_swap
    }
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply comonoid_to_law_unit_left.
nner_swap
    }
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      apply comonoid_to_law_unit_left.
nner_swap
    }
nner_swap
    apply tensor_id_id.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma tensor_of_comonoids_laws_unit_right
nner_swap
    (mx my : comonoid M)
nner_swap
    : comonoid_laws_unit_right M (tensor_of_comonoids_data mx my).
nner_swap
  Proof.
nner_swap
    unfold comonoid_laws_unit_right.
nner_swap
    cbn.
nner_swap
    rewrite (bifunctor_leftcomp M).
nner_swap
    rewrite ! assoc.
nner_swap
    etrans. {
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply precompose_rearrange_prod_with_augs_on_right.
nner_swap
    }
nner_swap

nner_swap
    rewrite assoc.
nner_swap
    etrans. {
nner_swap
      do 3 apply maponpaths_2.
nner_swap
      apply pathsinv0, tensor_comp_mor.
nner_swap
    }
nner_swap

nner_swap
    etrans. {
nner_swap
      rewrite ! assoc'.
nner_swap
      apply maponpaths.
nner_swap
      rewrite assoc.
nner_swap
      exact (precompose_rearrange_prod_with_lunitors_and_runitor (M) mx my).
nner_swap
    }
nner_swap

nner_swap
    etrans. {
nner_swap
      apply pathsinv0, tensor_comp_mor.
nner_swap
    }
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply comonoid_to_law_unit_right.
nner_swap
    }
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      apply comonoid_to_law_unit_right.
nner_swap
    }
nner_swap
    apply tensor_id_id.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma tensor_of_comonoids_laws_assoc
nner_swap
    (mx my : comonoid M)
nner_swap
    : comonoid_laws_assoc M (tensor_of_comonoids_data mx my).
nner_swap
  Proof.
nner_swap
    unfold comonoid_laws_assoc.
nner_swap
    cbn.
nner_swap

nner_swap
    rewrite ! assoc'.
nner_swap
    rewrite (bifunctor_rightcomp M).
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0.
nner_swap
      rewrite ! assoc.
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply pathsinv0.
nner_swap
      apply precompose_rearrange_prod_with_diag_on_left.
nner_swap
    }
nner_swap

nner_swap
    rewrite (bifunctor_leftcomp M).
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths.
nner_swap
      rewrite assoc.
nner_swap
      apply maponpaths_2.
nner_swap
      apply pathsinv0.
nner_swap
      apply precompose_rearrange_prod_with_diag_on_right.
nner_swap
    }
nner_swap

nner_swap
    rewrite ! assoc.
nner_swap
    rewrite <- ! (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 3 apply maponpaths_2.
nner_swap
      apply comonoid_to_law_assoc.
nner_swap
    }
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply maponpaths.
nner_swap
      apply comonoid_to_law_assoc.
nner_swap
    }
nner_swap

nner_swap
    rewrite ! (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
nner_swap
    rewrite ! assoc'.
nner_swap
    do 2 apply maponpaths.
nner_swap
    apply rearrange_hexagon.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma tensor_of_comonoids_laws
nner_swap
    (mx my : comonoid M)
nner_swap
    : comonoid_laws M (tensor_of_comonoids_data mx my).
nner_swap
  Proof.
nner_swap
    refine (_ ,, _ ,, _).
nner_swap
    - exact (tensor_of_comonoids_laws_unit_left mx my).
nner_swap
    - exact (tensor_of_comonoids_laws_unit_right mx my).
nner_swap
    - exact (tensor_of_comonoids_laws_assoc mx my).
nner_swap
  Qed.
nner_swap

nner_swap
  Definition tensor_of_comonoids
nner_swap
    (mx my : comonoid M)
nner_swap
    : comonoid M.
nner_swap
  Proof.
nner_swap
    refine (_ ,, _ ,, _).
nner_swap
    exact (tensor_of_comonoids_laws mx my).
nner_swap
  Defined.
nner_swap

nner_swap
  Definition tensor_of_comonoid_mor_mult_left
nner_swap
    (m : comonoid M) {m1 m2 : comonoid M}
nner_swap
    {g : M⟦m1,m2⟧}
nner_swap
    (gg : δ_{_} · g ⊗^{M} g = g · δ_{_})
nner_swap
    : δ_{tensor_of_comonoids m m1} · (m ⊗^{ M}_{l} g) ⊗^{M} (m ⊗^{ M}_{l} g) = (m ⊗^{ M}_{l} g) · δ_{tensor_of_comonoids m m2}.
nner_swap
  Proof.
nner_swap
    cbn.
nner_swap
    etrans.
nner_swap
    2:{
nner_swap
      rewrite (bifunctor_equalwhiskers M).
nner_swap
      unfold functoronmorphisms2.
nner_swap
      rewrite ! assoc.
nner_swap
      rewrite <- (bifunctor_leftcomp M).
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply maponpaths.
nner_swap
      exact gg.
nner_swap
    }
nner_swap

nner_swap
    etrans. {
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      refine (_ @ precompose_rearrange_prod (M) (identity _) (identity _) g g).
nner_swap
      now rewrite <- (when_bifunctor_becomes_leftwhiskering M).
nner_swap
    }
nner_swap
    rewrite ! assoc.
nner_swap
    apply maponpaths_2.
nner_swap
    refine (! tensor_comp_mor _ _ _ _ @ _).
nner_swap
    rewrite tensor_id_id.
nner_swap
    rewrite id_right.
nner_swap
    apply (bifunctor_equalwhiskers M).
nner_swap
  Qed.
nner_swap

nner_swap
  Definition tensor_of_comonoid_mor_unit_left
nner_swap
    (m : comonoid M) {m1 m2 : comonoid M}
nner_swap
    {g : M⟦m1,m2⟧}
nner_swap
    (gg : ε_{_} · identity I_{M} = g · ε_{_})
nner_swap
    : ε_{tensor_of_comonoids _ _} · identity I_{M} =  (m ⊗^{ M}_{l} g) · ε_{tensor_of_comonoids _ _}.
nner_swap
  Proof.
nner_swap
    cbn.
nner_swap
    rewrite id_right.
nner_swap
    rewrite assoc.
nner_swap
    apply maponpaths_2.
nner_swap
    rewrite id_right in gg.
nner_swap
    rewrite <- (when_bifunctor_becomes_leftwhiskering M).
nner_swap
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
nner_swap
    rewrite id_left.
nner_swap
    apply maponpaths.
nner_swap
    exact gg.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition tensor_of_comonoid_mor_left
nner_swap
    (m : comonoid M) {m1 m2 : comonoid M}
nner_swap
    {g : M⟦m1,m2⟧}
nner_swap
    (gg1 : δ_{_} · g ⊗^{M} g = g · δ_{_})
nner_swap
    (gg2 : ε_{_} · identity I_{M} = g · ε_{_})
nner_swap
    : comonoid_mor_struct M (tensor_of_comonoids m m1) (tensor_of_comonoids m m2) (m ⊗^{ M}_{l} g).
nner_swap
  Proof.
nner_swap
    use make_is_comonoid_mor.
nner_swap
    - apply (tensor_of_comonoid_mor_mult_left m gg1).
nner_swap
    - apply (tensor_of_comonoid_mor_unit_left m gg2).
nner_swap
  Qed.
nner_swap

nner_swap
  Definition comonoid_disp_unit_data
nner_swap
    : comonoid_data M.
nner_swap
  Proof.
nner_swap
    exists (monoidal_unit M).
nner_swap
    exists (luinv^{M}_{_}).
nner_swap
    apply identity.
nner_swap
  Defined.
nner_swap

nner_swap
  Lemma comonoid_disp_unit_laws
nner_swap
    : comonoid_laws M comonoid_disp_unit_data.
nner_swap
  Proof.
nner_swap
    refine (_ ,, _ ,, _).
nner_swap
    - unfold comonoid_laws_unit_left.
nner_swap
      cbn.
nner_swap
      rewrite (bifunctor_rightid M).
nner_swap
      rewrite id_right.
nner_swap
      apply monoidal_leftunitorisolaw.
nner_swap
    - unfold comonoid_laws_unit_right.
nner_swap
      cbn.
nner_swap
      rewrite (bifunctor_leftid M).
nner_swap
      rewrite id_right.
nner_swap
      rewrite mon_runitor_I_mon_lunitor_I.
nner_swap
      apply monoidal_leftunitorisolaw.
nner_swap
    - unfold comonoid_laws_assoc.
nner_swap
      cbn.
nner_swap
      rewrite ! assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply lunitorinv_preserves_leftwhiskering_with_unit.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition comonoid_disp_unit
nner_swap
    :  comonoid M.
nner_swap
  Proof.
nner_swap
    exists comonoid_disp_unit_data.
nner_swap
    refine (_ ,, _).
nner_swap
    exact comonoid_disp_unit_laws.
nner_swap
  Defined.
nner_swap

nner_swap
  Lemma comonoid_disp_lunitor
nner_swap
    (m : comonoid M)
nner_swap
    : comonoid_mor_struct M (tensor_of_comonoids comonoid_disp_unit m) m lu^{ M }_{m}.
nner_swap
  Proof.
nner_swap
    use make_is_comonoid_mor.
nner_swap
    - cbn.
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        apply pathsinv0.
nner_swap
        apply (precompose_rearrange_prod_with_lunitors_on_right (M)).
nner_swap
      }
nner_swap

nner_swap
      refine (_ @ monoidal_leftunitornat M _ _ δ_{m}).
nner_swap
      rewrite ! assoc.
nner_swap
      apply maponpaths_2.
nner_swap

nner_swap
      etrans. {
nner_swap
        apply maponpaths_2.
nner_swap
        rewrite assoc'.
nner_swap
        apply maponpaths.
nner_swap
        apply rearrange_prod_inv.
nner_swap
      }
nner_swap
      rewrite id_right.
nner_swap
      rewrite <- (when_bifunctor_becomes_rightwhiskering M).
nner_swap
      etrans. {
nner_swap
        apply pathsinv0, tensor_comp_mor.
nner_swap
      }
nner_swap

nner_swap
      rewrite id_right.
nner_swap
      rewrite <- (when_bifunctor_becomes_leftwhiskering M).
nner_swap
      apply maponpaths_2.
nner_swap
      apply (monoidal_leftunitorisolaw M I_{M}).
nner_swap
    - refine (_ @ monoidal_leftunitornat M _ _ ε_{m}).
nner_swap
      rewrite id_right.
nner_swap
      cbn.
nner_swap
      apply maponpaths_2.
nner_swap
      apply (when_bifunctor_becomes_leftwhiskering M).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comonoid_disp_lunitor_inv
nner_swap
    (m : comonoid M)
nner_swap
    : comonoid_mor_struct M m (tensor_of_comonoids comonoid_disp_unit m) luinv^{M}_{m}.
nner_swap
  Proof.
nner_swap
    use make_is_comonoid_mor.
nner_swap
    - cbn.
nner_swap
      use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
nner_swap
      {
nner_swap
        set (i := monoidal_leftunitorisolaw M m).
nner_swap
        use (is_z_iso_bifunctor_z_iso M)
nner_swap
        ; apply (_ ,, pr2 i ,, pr1 i).
nner_swap
      }
nner_swap
      cbn.
nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        apply maponpaths.
nner_swap
        apply (precompose_rearrange_prod_with_lunitors_on_right M).
nner_swap
      }
nner_swap

nner_swap
      apply pathsinv0.
nner_swap
      etrans. {
nner_swap
        rewrite ! assoc'.
nner_swap
        do 2 apply maponpaths.
nner_swap
        rewrite assoc.
nner_swap
        apply maponpaths_2.
nner_swap
        apply rearrange_prod_inv.
nner_swap
      }
nner_swap
      rewrite id_left.
nner_swap
      rewrite <- (when_bifunctor_becomes_rightwhiskering M).
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        rewrite assoc.
nner_swap
        apply maponpaths_2.
nner_swap
        apply pathsinv0, tensor_comp_mor.
nner_swap
      }
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        do 2 apply maponpaths_2.
nner_swap
        apply monoidal_leftunitorisolaw.
nner_swap
      }
nner_swap
      rewrite id_right.
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        refine (_ @ monoidal_leftunitornat M _ _ δ_{m}).
nner_swap
        apply maponpaths_2.
nner_swap
        apply (when_bifunctor_becomes_leftwhiskering M).
nner_swap
      }
nner_swap
      rewrite assoc.
nner_swap
      refine (_ @ id_left _).
nner_swap
      apply maponpaths_2.
nner_swap
      apply monoidal_leftunitorisolaw.
nner_swap
    - cbn.
nner_swap
      rewrite assoc.
nner_swap
      apply pathsinv0.
nner_swap
      etrans. {
nner_swap
        apply maponpaths_2.
nner_swap
        refine (_ @ monoidal_leftunitorinvnat M _ _ ε_{m}).
nner_swap
        now rewrite (when_bifunctor_becomes_leftwhiskering M).
nner_swap
      }
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply monoidal_leftunitorisolaw.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comonoid_disp_braiding
nner_swap
    (mx my : comonoid M)
nner_swap
    : comonoid_mor_struct M (tensor_of_comonoids mx my) (tensor_of_comonoids my mx) (sym_mon_braiding M mx my).
nner_swap
  Proof.
nner_swap
    apply make_is_comonoid_mor.
nner_swap
    - cbn.
nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        rewrite assoc.
nner_swap
        apply maponpaths_2.
nner_swap
        apply (tensor_sym_mon_braiding).
nner_swap
      }
nner_swap
      rewrite ! assoc'.
nner_swap
      apply comult_before_rearrange_and_swap.
nner_swap
    - cbn.
nner_swap
      rewrite ! assoc.
nner_swap
      rewrite id_right.
nner_swap
      apply maponpaths_2.
nner_swap
      etrans.
nner_swap
      2: { apply (tensor_sym_mon_braiding M). }
nner_swap
      cbn.
nner_swap
      refine (! id_right _ @ _).
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0, sym_mon_braiding_id.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comonoid_disp_associator
nner_swap
    (xx yy zz : comonoid M)
nner_swap
    : comonoid_mor_struct M
nner_swap
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz)
nner_swap
        (tensor_of_comonoids xx (tensor_of_comonoids yy zz)) α^{ M }_{xx, yy, zz}.
nner_swap
  Proof.
nner_swap
    apply make_is_comonoid_mor.
nner_swap
    - cbn.
nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        rewrite assoc.
nner_swap
        apply maponpaths_2.
nner_swap
        apply maponpaths.
nner_swap
        apply maponpaths_2.
nner_swap
        apply id_right.
nner_swap
      }
nner_swap
      rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
nner_swap
      rewrite ! assoc.
nner_swap

nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        do 2 apply maponpaths_2.
nner_swap
        apply pathsinv0, associator_nat2.
nner_swap
      }
nner_swap

nner_swap
      rewrite ! assoc'.
nner_swap

nner_swap
      etrans. {
nner_swap
        apply maponpaths_2.
nner_swap
        apply maponpaths.
nner_swap
        apply pathsinv0, id_right.
nner_swap
      }
nner_swap

nner_swap
      rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
nner_swap
      rewrite ! assoc'.
nner_swap
      apply maponpaths.
nner_swap
      rewrite ! assoc.
nner_swap
      apply rearrange_hexagon'.
nner_swap
    - cbn.
nner_swap
      apply pathsinv0.
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        apply maponpaths_2.
nner_swap
        apply tensor_comp_l_id_l.
nner_swap
      }
nner_swap
      unfold monoidal_cat_tensor_mor.
nner_swap
      cbn.
nner_swap
      rewrite ! assoc.
nner_swap
      etrans. {
nner_swap
        do 2 apply maponpaths_2.
nner_swap
        apply pathsinv0, tensor_lassociator.
nner_swap
      }
nner_swap
      unfold monoidal_cat_tensor_mor.
nner_swap
      cbn.
nner_swap
      rewrite id_right.
nner_swap
      apply maponpaths_2.
nner_swap
      etrans. {
nner_swap
        apply maponpaths_2.
nner_swap
        apply tensor_lassociator.
nner_swap
      }
nner_swap
      unfold monoidal_cat_tensor_mor.
nner_swap
      cbn.
nner_swap
      rewrite assoc'.
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        apply pathsinv0.
nner_swap
        apply tensor_comp_mor.
nner_swap
      }
nner_swap
      rewrite id_left.
nner_swap

nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        apply maponpaths_2.
nner_swap
        apply pathsinv0, id_right.
nner_swap
      }
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        apply tensor_comp_mor.
nner_swap
      }
nner_swap
      rewrite assoc.
nner_swap

nner_swap
      etrans. {
nner_swap
        apply maponpaths_2.
nner_swap
        apply associator_nat2.
nner_swap
      }
nner_swap

nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        apply maponpaths.
nner_swap
        apply id_right.
nner_swap
      }
nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        apply pathsinv0, tensor_comp_mor.
nner_swap
      }
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply associator_before_lwhisker_with_lu.
nner_swap
  Qed.
nner_swap

nner_swap
  (* Lemma comonoid_disp_associatorinv_mult
nner_swap
    {x y z : C}
nner_swap
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
nner_swap
    : is_comonoid_mor_mult M (tensor_of_comonoids xx (tensor_of_comonoids yy zz))
nner_swap
     (tensor_of_comonoids (tensor_of_comonoids xx yy) zz) αinv^{ M }_{ x, y, z}.
nner_swap
  Proof.
nner_swap
    unfold is_comonoid_mor_mult.
nner_swap
    cbn.
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      rewrite assoc.
nner_swap
      apply maponpaths_2.
nner_swap
      apply maponpaths.
nner_swap
      apply maponpaths.
nner_swap
      apply id_right.
nner_swap
    }
nner_swap
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
nner_swap
    rewrite ! assoc.
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply monoidal_associatorinv_nat2.
nner_swap
    }
nner_swap

nner_swap
    rewrite ! assoc'.
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      apply maponpaths_2.
nner_swap
      apply pathsinv0, id_right.
nner_swap
    }
nner_swap

nner_swap
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap
    rewrite ! assoc.
nner_swap
    apply rearrange_hexagoninv'.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comonoid_disp_associatorinv_unit {x y z : C}
nner_swap
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
nner_swap
    : is_comonoid_mor_unit M (tensor_of_comonoids xx (tensor_of_comonoids yy zz))
nner_swap
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz) αinv^{ M }_{ x, y, z}.
nner_swap
  Proof.
nner_swap
    unfold is_comonoid_mor_unit.
nner_swap
    cbn.
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply maponpaths_2.
nner_swap
      apply (tensor_comp_r_id_r).
nner_swap
    }
nner_swap
    unfold monoidal_cat_tensor_mor.
nner_swap
    cbn.
nner_swap
    rewrite ! assoc.
nner_swap
    etrans. {
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply pathsinv0, tensor_rassociator.
nner_swap
    }
nner_swap
    unfold monoidal_cat_tensor_mor.
nner_swap
    cbn.
nner_swap
    apply maponpaths_2.
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      apply tensor_rassociator.
nner_swap
    }
nner_swap
    unfold monoidal_cat_tensor_mor.
nner_swap
    cbn.
nner_swap
    rewrite assoc'.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0.
nner_swap
      apply (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
nner_swap
    }
nner_swap
    rewrite id_right.
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0, id_right.
nner_swap
    }
nner_swap
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
nner_swap
    rewrite assoc.
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      apply pathsinv0.
nner_swap
      apply monoidal_associatorinv_nat2.
nner_swap
    }
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths_2.
nner_swap
      apply id_right.
nner_swap
    }
nner_swap
    rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
nner_swap
    rewrite assoc'.
nner_swap
    apply maponpaths.
nner_swap
    apply associator_before_rwhisker_with_lu.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comonoid_disp_associatorinv
nner_swap
    {x y z : C}
nner_swap
    (xx : comonoid M x) (yy : comonoid M y) (zz : comonoid M z)
nner_swap
    : is_comonoid_mor M (tensor_of_comonoids xx (tensor_of_comonoids yy zz))
nner_swap
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz) αinv^{M}_{x, y, z}.
nner_swap
  Proof.
nner_swap
    split.
nner_swap
    - exact (comonoid_disp_associatorinv_mult xx yy zz).
nner_swap
    - exact (comonoid_disp_associatorinv_unit xx yy zz).
nner_swap
  Qed. *)
nner_swap

nner_swap
End TensorOfComonoids.
nner_swap

nner_swap
Section TensorOfCommutativeComonoids.
nner_swap

nner_swap
  Context (V : sym_monoidal_cat).
nner_swap

nner_swap
  Lemma tensor_of_comm_comonoids
nner_swap
    (mx my : commutative_comonoid V)
nner_swap
    : is_commutative V (tensor_of_comonoids V mx my).
nner_swap
  Proof.
nner_swap
    unfold disp_cat_of_commutative_comonoids.
nner_swap
    cbn.
nner_swap

nner_swap
    use (z_iso_inv_on_left _ _ _ _ (rearrange_prod V _ _ _ _ ,, rearrange_prod V _ _ _ _ ,, _)).
nner_swap
    { apply rearrange_prod_is_z_isomorphism. }
nner_swap
    cbn.
nner_swap
    rewrite assoc'.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths.
nner_swap
      apply rearrange_commute_with_swap.
nner_swap
    }
nner_swap

nner_swap
    rewrite assoc.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths_2.
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0, rearrange_prod_inv.
nner_swap
    }
nner_swap
    rewrite id_right.
nner_swap
    refine (_@ tensor_comp_mor _ _ _ _).
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths_2.
nner_swap
      apply pathsinv0, commutative_comonoid_is_commutative.
nner_swap
    }
nner_swap
    apply maponpaths.
nner_swap
    apply pathsinv0, commutative_comonoid_is_commutative.
nner_swap
  Qed.
nner_swap

nner_swap
End TensorOfCommutativeComonoids.
