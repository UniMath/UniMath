(*
In this file, the necessary ingredients to show how the (displayed) category of comonoids (resp. commutative comonoids) is (displayed) symmetric.
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
(* Require Import UniMath.CategoryTheory.Monoidal.Displayed.SymmetricMonoidalBuilder. *)

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
(* Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsCategory. *)

Import MonoidalNotations.
Import ComonoidNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section TensorOfComonoids.

  Context (M : sym_monoidal_cat).

  Notation "σ_{ x , y }" := (sym_mon_braiding M x y).

  Let S_nat_l := monoidal_braiding_naturality_left (pr2 M).
  Let S_nat_r := monoidal_braiding_naturality_right (pr2 M).
  Let S_iso := is_z_isomorphism_sym_mon_braiding M.
  Search braiding_law_hexagon1.
  Let S_pent1 := (pr1(pr222 (pr2 M))).
  Let S_pent2 := (pr2(pr222 (pr2 M))).

  Definition tensor_of_comonoids_data
    (mx my : comonoid M)
    : comonoid_data M.
  Proof.
    exists (mx ⊗ my).
    split.
    - refine (δ_{mx} ⊗^{M} δ_{my} · _).
      exact (rearrange_prod (pr2 M) mx mx my my).
    - exact (ε_{mx} ⊗^{M} ε_{my} · lu^{M}_{_}).
  Defined.

  Lemma precompose_rearrange_prod_with_augs_on_left
    (mx my : comonoid M)
    : rearrange_prod M mx mx my my · (ε_{ mx} ⊗^{ M} ε_{ my}) ⊗^{ M}_{r} (mx ⊗_{ M} my)
      = (ε_{ mx} ⊗^{M}_{r} _) ⊗^{M} (ε_{ my} ⊗^{M}_{r} my) · rearrange_prod M _ _ _ _.
  Proof.
    refine (_ @ precompose_rearrange_prod (M) ε_{mx} (identity _)  ε_{my} (identity _) @ _).
    - rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      do 2 apply maponpaths.
      apply pathsinv0, tensor_id_id.
    - now rewrite <- ! (when_bifunctor_becomes_rightwhiskering M).
  Qed.

  Lemma precompose_rearrange_prod_with_diag_on_left
    (mx my : comonoid M)
    : rearrange_prod (M) mx mx my my · (δ_{ mx} ⊗^{ M} δ_{ my}) ⊗^{ M}_{r} (mx ⊗_{ M} my)
      = (δ_{ mx} ⊗^{M}_{r} _) ⊗^{M} (δ_{ my} ⊗^{M}_{r} my) · rearrange_prod M _ _ _ _.
  Proof.
    refine (_ @ precompose_rearrange_prod (M) δ_{mx} (identity _) δ_{my} (identity _) @ _).
    - rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply (pr21 M))).
    - now rewrite <- ! (when_bifunctor_becomes_rightwhiskering M).
  Qed.

  Lemma precompose_rearrange_prod_with_augs_on_right
    (mx my : comonoid M)
    : rearrange_prod (M) mx mx my my · (mx ⊗_{ M} my) ⊗^{ M}_{l} (ε_{mx} ⊗^{ M} ε_{my})
      = (_ ⊗^{M}_{l} ε_{mx}) ⊗^{M} (_ ⊗^{M}_{l} ε_{my}) · rearrange_prod (M) _ _ _ _.
  Proof.
    refine (_ @ precompose_rearrange_prod (M) (identity _) ε_{mx} (identity _) ε_{my} @ _).
    - rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply (pr21 M))).
    - now rewrite <- ! (when_bifunctor_becomes_leftwhiskering M).
  Qed.

  Lemma precompose_rearrange_prod_with_diag_on_right
    (mx my : comonoid M)
    : rearrange_prod (M) mx mx my my · (mx ⊗_{ M} my) ⊗^{ M}_{l} (δ_{ mx} ⊗^{ M} δ_{ my})
      = (_ ⊗^{M}_{l} δ_{ mx}) ⊗^{M} (_ ⊗^{M}_{l} δ_{ my}) · rearrange_prod (M) _ _ _ _.
  Proof.
    refine (_ @ precompose_rearrange_prod (M) (identity _) δ_{mx} (identity _) δ_{my} @ _).
    - rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply (pr21 M))).
    - now rewrite <- ! (when_bifunctor_becomes_leftwhiskering M).
  Qed.

  Lemma tensor_of_comonoids_laws_unit_left
    (mx my : comonoid M)
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
    etrans. {
      do 3 apply maponpaths_2.
      apply pathsinv0, tensor_comp_mor.
    }

    etrans. {
      rewrite ! assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (precompose_rearrange_prod_with_lunitors_on_right (M) mx my).
    }
    cbn.
    etrans. {
      apply pathsinv0.
      apply tensor_comp_mor.
    }
    etrans. {
      apply maponpaths.
      apply comonoid_to_law_unit_left.
    }

    etrans. {
      apply maponpaths_2.
      apply comonoid_to_law_unit_left.
    }
    apply tensor_id_id.
  Qed.

  Lemma tensor_of_comonoids_laws_unit_right
    (mx my : comonoid M)
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
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
    etrans. {
      rewrite ! assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (precompose_rearrange_prod_with_lunitors_and_runitor (M) mx my).
    }

    etrans. {
      apply pathsinv0, tensor_comp_mor.
    }

    etrans. {
      apply maponpaths.
      apply comonoid_to_law_unit_right.
    }
    etrans. {
      apply maponpaths_2.
      apply comonoid_to_law_unit_right.
    }
    apply tensor_id_id.
  Qed.

  Lemma tensor_of_comonoids_laws_assoc
    (mx my : comonoid M)
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

    rewrite ! assoc.
    rewrite <- ! (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).

    etrans.
    2: {
      do 3 apply maponpaths_2.
      apply comonoid_to_law_assoc.
    }
    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply maponpaths.
      apply comonoid_to_law_assoc.
    }

    rewrite ! (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
    rewrite ! assoc'.
    do 2 apply maponpaths.
    apply rearrange_hexagon.
  Qed.

  Lemma tensor_of_comonoids_laws
    (mx my : comonoid M)
    : comonoid_laws M (tensor_of_comonoids_data mx my).
  Proof.
    refine (_ ,, _ ,, _).
    - exact (tensor_of_comonoids_laws_unit_left mx my).
    - exact (tensor_of_comonoids_laws_unit_right mx my).
    - exact (tensor_of_comonoids_laws_assoc mx my).
  Qed.

  Definition tensor_of_comonoids
    (mx my : comonoid M)
    : comonoid M.
  Proof.
    refine (_ ,, _ ,, _).
    exact (tensor_of_comonoids_laws mx my).
  Defined.

  Definition tensor_of_comonoid_mor_mult_left
    (m : comonoid M) {m1 m2 : comonoid M}
    {g : M⟦m1,m2⟧}
    (gg : δ_{_} · g ⊗^{M} g = g · δ_{_})
    : δ_{tensor_of_comonoids m m1} · (m ⊗^{ M}_{l} g) ⊗^{M} (m ⊗^{ M}_{l} g) = (m ⊗^{ M}_{l} g) · δ_{tensor_of_comonoids m m2}.
  Proof.
    cbn.
    etrans.
    2:{
      rewrite (bifunctor_equalwhiskers M).
      unfold functoronmorphisms2.
      rewrite ! assoc.
      rewrite <- (bifunctor_leftcomp M).
      do 2 apply maponpaths_2.
      apply maponpaths.
      exact gg.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      refine (_ @ precompose_rearrange_prod (M) (identity _) (identity _) g g).
      now rewrite (when_bifunctor_becomes_leftwhiskering M).
    }
    rewrite ! assoc.
    apply maponpaths_2.
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
    rewrite (bifunctor_equalwhiskers M).
    unfold functoronmorphisms2.
    do 2 apply maponpaths.
    rewrite (bifunctor_distributes_over_id (F := M)) ; try (apply (pr21 M)).
    apply id_right.
  Qed.

  Definition tensor_of_comonoid_mor_unit_left
    (m : comonoid M) {m1 m2 : comonoid M}
    {g : M⟦m1,m2⟧}
    (gg : ε_{_} · identity I_{M} = g · ε_{_})
    : ε_{tensor_of_comonoids _ _} · identity I_{M} =  (m ⊗^{ M}_{l} g) · ε_{tensor_of_comonoids _ _}.
  Proof.
    cbn.
    rewrite id_right.
    rewrite assoc.
    apply maponpaths_2.
    rewrite id_right in gg.
    rewrite <- (when_bifunctor_becomes_leftwhiskering M).
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
    rewrite id_left.
    apply maponpaths.
    exact gg.
  Qed.

  Definition tensor_of_comonoid_mor_left
    (m : comonoid M) {m1 m2 : comonoid M}
    {g : M⟦m1,m2⟧}
    (gg1 : δ_{_} · g ⊗^{M} g = g · δ_{_})
    (gg2 : ε_{_} · identity I_{M} = g · ε_{_})
    : comonoid_mor_struct M (tensor_of_comonoids m m1) (tensor_of_comonoids m m2) (m ⊗^{ M}_{l} g).
  Proof.
    use make_is_comonoid_mor.
    - apply (tensor_of_comonoid_mor_mult_left m gg1).
    - apply (tensor_of_comonoid_mor_unit_left m gg2).
  Qed.

  Definition comonoid_disp_unit_data
    : comonoid_data M.
  Proof.
    exists (monoidal_unit M).
    exists (luinv^{M}_{_}).
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
    :  comonoid M.
  Proof.
    exists comonoid_disp_unit_data.
    refine (_ ,, _).
    exact comonoid_disp_unit_laws.
  Defined.

  Lemma comonoid_disp_lunitor
    (m : comonoid M)
    : comonoid_mor_struct M (tensor_of_comonoids comonoid_disp_unit m) m lu^{ M }_{m}.
  Proof.
    use make_is_comonoid_mor.
    - cbn.
      etrans. {
        apply maponpaths.
        apply pathsinv0.
        apply (precompose_rearrange_prod_with_lunitors_on_right (M)).
      }

      refine (_ @ monoidal_leftunitornat M _ _ δ_{m}).
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
      etrans. {
        apply pathsinv0, tensor_comp_mor.
      }

      rewrite id_right.
      rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      apply maponpaths_2.
      apply (monoidal_leftunitorisolaw M I_{M}).
    - refine (_ @ monoidal_leftunitornat M _ _ ε_{m}).
      rewrite id_right.
      cbn.
      apply maponpaths_2.
      apply (when_bifunctor_becomes_leftwhiskering M).
  Qed.

  Lemma comonoid_disp_lunitor_inv
    (m : comonoid M)
    : comonoid_mor_struct M m (tensor_of_comonoids comonoid_disp_unit m) luinv^{M}_{m}.
  Proof.
    use make_is_comonoid_mor.
    - cbn.
      use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
      {
        set (i := monoidal_leftunitorisolaw M m).
        use (is_z_iso_bifunctor_z_iso M)
        ; apply (_ ,, pr2 i ,, pr1 i).
      }
      cbn.
      etrans.
      2: {
        apply maponpaths.
        apply (precompose_rearrange_prod_with_lunitors_on_right (M)).
      }

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
        rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
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
        apply maponpaths, (monoidal_leftunitornat M _ _ δ_{m}).
      }
      rewrite assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply (pr2 (monoidal_leftunitorisolaw M m)).
    - cbn.
      rewrite assoc.
      apply pathsinv0.
      etrans. {
        apply maponpaths_2.
        refine (_ @ monoidal_leftunitorinvnat M _ _ ε_{m}).
        now rewrite (when_bifunctor_becomes_leftwhiskering M).
      }
      rewrite assoc'.
      apply maponpaths.
      exact (pr2 (monoidal_leftunitorisolaw M _)).
  Qed.

  Lemma comonoid_disp_braiding
    (mx my : comonoid M)
    : comonoid_mor_struct M (tensor_of_comonoids mx my) (tensor_of_comonoids my mx) (sym_mon_braiding M mx my).
  Proof.
    apply make_is_comonoid_mor.
    - cbn.
      etrans.
      2: {
        rewrite assoc.
        apply maponpaths_2.
        apply (tensor_sym_mon_braiding).
      }
      rewrite ! assoc'.
      apply comult_before_rearrange_and_swap.
    - cbn.
      rewrite ! assoc.
      rewrite id_right.
      apply maponpaths_2.
      etrans.
      2: { apply (tensor_sym_mon_braiding M). }
      cbn.
      refine (! id_right _ @ _).
      apply maponpaths.
      apply pathsinv0, sym_mon_braiding_id.
  Qed.

  Lemma comonoid_disp_associator
    (xx yy zz : comonoid M)
    : comonoid_mor_struct M
        (tensor_of_comonoids (tensor_of_comonoids xx yy) zz)
        (tensor_of_comonoids xx (tensor_of_comonoids yy zz)) α^{ M }_{xx, yy, zz}.
  Proof.
    apply make_is_comonoid_mor.
    - cbn.
      etrans.
      2: {
        rewrite assoc.
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        apply id_right.
      }
      rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
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
      rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
      rewrite ! assoc'.
      apply maponpaths.
      rewrite ! assoc.
      apply rearrange_hexagon'.
    - cbn.
      apply pathsinv0.
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        apply tensor_comp_l_id_l.
      }
      unfold monoidal_cat_tensor_mor.
      cbn.
      rewrite ! assoc.
      etrans. {
        do 2 apply maponpaths_2.
        apply pathsinv0, tensor_lassociator.
      }
      unfold monoidal_cat_tensor_mor.
      cbn.
      rewrite id_right.
      apply maponpaths_2.
      etrans. {
        apply maponpaths_2.
        apply tensor_lassociator.
      }
      unfold monoidal_cat_tensor_mor.
      cbn.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        apply pathsinv0.
        apply tensor_comp_mor.
      }
      rewrite id_left.

      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        apply pathsinv0, id_right.
      }
      etrans. {
        apply maponpaths.
        apply tensor_comp_mor.
      }
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

      rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply (pr21 M)).
      rewrite assoc'.
      apply maponpaths.
      apply associator_before_lwhisker_with_lu.
  Qed.

  (* Lemma comonoid_disp_associatorinv_mult
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
      apply (tensor_comp_r_id_r).
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    rewrite ! assoc.
    etrans. {
      do 2 apply maponpaths_2.
      apply pathsinv0, tensor_rassociator.
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    apply maponpaths_2.
    etrans. {
      apply maponpaths_2.
      apply tensor_rassociator.
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
  Qed. *)

  (* Definition comonoid_disp_symmetric_monoidal
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
  Defined. *)

End TensorOfComonoids.

Section TensorOfCommutativeComonoids.

  Context (V : sym_monoidal_cat).

  Lemma tensor_of_comm_comonoids
    (mx my : commutative_comonoid V)
    : is_commutative V (tensor_of_comonoids V mx my).
  Proof.
    unfold disp_cat_of_commutative_comonoids.
    cbn.

    use (z_iso_inv_on_left _ _ _ _ (rearrange_prod V _ _ _ _ ,, rearrange_prod V _ _ _ _ ,, _)).
    { apply rearrange_prod_is_z_isomorphism. }
    cbn.
    rewrite assoc'.
    etrans.
    2: {
      apply maponpaths.
      apply rearrange_commute_with_swap.
    }

    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, rearrange_prod_inv.
    }
    rewrite id_right.
    refine (_@ tensor_comp_mor _ _ _ _).
    etrans.
    2: {
      apply maponpaths_2.
      apply pathsinv0, commutative_comonoid_is_commutative.
    }
    apply maponpaths.
    apply pathsinv0, commutative_comonoid_is_commutative.
  Qed.

  (* Definition disp_monoidal_cat_of_comm_comonoids
    : disp_monoidal (disp_full_sub
                       (category_of_comonoids_in_monoidal_cat M)
                       (λ x : ∑ x : C, comonoid M x, is_commutative S (pr2 x)))
        (monoidal_cat_of_comonoids S).
  Proof.
    use (disp_monoidal_fullsub _
           (λ x : category_of_comonoids_in_monoidal_cat M, (is_commutative S (pr2 x : comonoid M (pr1 x))))).
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
  Defined. *)

End TensorOfCommutativeComonoids.
