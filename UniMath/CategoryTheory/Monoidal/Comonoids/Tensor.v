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
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Sigma.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.

Import MonoidalNotations.
Import ComonoidNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section TensorOfComonoids.

  Context (M : sym_monoidal_cat).

  Definition tensor_of_comonoids_data
    (mx my : comonoid M)
    : comonoid_data M.
  Proof.
    exists (mx ⊗ my).
    split.
    - refine (δ_{mx} #⊗ δ_{my} · _).
      exact (inner_swap M mx mx my my).
    - exact (ε_{mx} #⊗ ε_{my} · lu^{M}_{_}).
  Defined.

  Lemma precompose_inner_swap_with_augs_on_left
    (mx my : comonoid M)
    : inner_swap M mx mx my my · (ε_{ mx} ⊗^{ M} ε_{ my}) ⊗^{ M}_{r} (mx ⊗_{ M} my)
      = (ε_{ mx} ⊗^{M}_{r} _) #⊗ (ε_{ my} ⊗^{M}_{r} my) · inner_swap M _ _ _ _.
  Proof.
    refine (_ @ naturality_inner_swap (M) ε_{mx} (identity _)  ε_{my} (identity _) @ _).
    - rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      do 2 apply maponpaths.
      apply pathsinv0, tensor_id_id.
    - now rewrite <- ! (when_bifunctor_becomes_rightwhiskering M).
  Qed.

  Lemma precompose_inner_swap_with_diag_on_left
    (mx my : comonoid M)
    : inner_swap (M) mx mx my my · (δ_{ mx} ⊗^{ M} δ_{ my}) ⊗^{ M}_{r} (mx ⊗_{ M} my)
      = (δ_{ mx} ⊗^{M}_{r} _) #⊗ (δ_{ my} ⊗^{M}_{r} my) · inner_swap M _ _ _ _.
  Proof.
    refine (_ @ naturality_inner_swap (M) δ_{mx} (identity _) δ_{my} (identity _) @ _).
    - rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply (pr21 M))).
    - now rewrite <- ! (when_bifunctor_becomes_rightwhiskering M).
  Qed.

  Lemma precompose_inner_swap_with_augs_on_right
    (mx my : comonoid M)
    : inner_swap (M) mx mx my my · (mx ⊗_{ M} my) ⊗^{ M}_{l} (ε_{mx} ⊗^{ M} ε_{my})
      = (_ ⊗^{M}_{l} ε_{mx}) #⊗ (_ ⊗^{M}_{l} ε_{my}) · inner_swap (M) _ _ _ _.
  Proof.
    refine (_ @ naturality_inner_swap (M) (identity _) ε_{mx} (identity _) ε_{my} @ _).
    - rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      now (rewrite <- (bifunctor_distributes_over_id (F := M)) ; try (apply (pr21 M))).
    - now rewrite <- ! (when_bifunctor_becomes_leftwhiskering M).
  Qed.

  Lemma precompose_inner_swap_with_diag_on_right
    (mx my : comonoid M)
    : inner_swap (M) mx mx my my · (mx ⊗_{ M} my) ⊗^{ M}_{l} (δ_{ mx} ⊗^{ M} δ_{ my})
      = (_ ⊗^{M}_{l} δ_{ mx}) #⊗ (_ ⊗^{M}_{l} δ_{ my}) · inner_swap (M) _ _ _ _.
  Proof.
    refine (_ @ naturality_inner_swap (M) (identity _) δ_{mx} (identity _) δ_{my} @ _).
    - rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      apply maponpaths.
      apply maponpaths_2.
      apply pathsinv0.
      apply tensor_id_id.
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
      apply precompose_inner_swap_with_augs_on_left.
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
      exact (precompose_inner_swap_with_lunitors_on_right (M) mx my).
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
      apply precompose_inner_swap_with_augs_on_right.
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
      exact (precompose_inner_swap_with_lunitors_and_runitor (M) mx my).
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
      apply precompose_inner_swap_with_diag_on_left.
    }

    rewrite (bifunctor_leftcomp M).
    etrans.
    2: {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply pathsinv0.
      apply precompose_inner_swap_with_diag_on_right.
    }

    rewrite ! assoc.
    rewrite <- ! tensor_comp_mor.

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
    rewrite ! tensor_comp_mor.
    rewrite ! assoc'.
    do 2 apply maponpaths.
    apply inner_swap_hexagon.
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
    (gg : δ_{_} · g #⊗ g = g · δ_{_})
    : δ_{tensor_of_comonoids m m1} · (m ⊗^{ M}_{l} g) #⊗ (m ⊗^{M}_{l} g) = (m ⊗^{M}_{l} g) · δ_{tensor_of_comonoids m m2}.
  Proof.
    cbn.
    etrans.
    2:{
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      refine (_ @ tensor_comp_mor _ _ _ _ ).
      rewrite id_left.
      apply maponpaths.
      exact gg.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      refine (_ @ naturality_inner_swap (M) (identity _) (identity _) g g).
      now rewrite <- (when_bifunctor_becomes_leftwhiskering M).
    }
    rewrite ! assoc.
    apply maponpaths_2.
    refine (! tensor_comp_mor _ _ _ _ @ _).
    rewrite tensor_id_id.
    now rewrite id_right.
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
    refine (_ @ tensor_comp_mor _ _ _ _).
    rewrite id_left.
    apply maponpaths.
    exact gg.
  Qed.

  Definition tensor_of_comonoid_mor_left
    (m : comonoid M) {m1 m2 : comonoid M}
    {g : M⟦m1,m2⟧}
    (gg1 : δ_{_} · g #⊗ g = g · δ_{_})
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
    exists (mon_linvunitor _).
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
      rewrite mon_runitor_I_mon_lunitor_I.
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
    : comonoid_mor_struct M (tensor_of_comonoids comonoid_disp_unit m) m (mon_lunitor m).
  Proof.
    use make_is_comonoid_mor.
    - cbn.
      etrans. {
        apply maponpaths.
        apply pathsinv0.
        apply (precompose_inner_swap_with_lunitors_on_right (M)).
      }

      refine (_ @ monoidal_leftunitornat M _ _ δ_{m}).
      rewrite ! assoc.
      apply maponpaths_2.

      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply inner_swap_inv.
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
    : comonoid_mor_struct M m (tensor_of_comonoids comonoid_disp_unit m) (mon_linvunitor m).
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
        apply (precompose_inner_swap_with_lunitors_on_right M).
      }

      apply pathsinv0.
      etrans. {
        rewrite ! assoc'.
        do 2 apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        apply inner_swap_inv.
      }
      rewrite id_left.
      rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        apply pathsinv0, tensor_comp_mor.
      }
      etrans. {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply monoidal_leftunitorisolaw.
      }
      rewrite id_right.
      etrans. {
        apply maponpaths.
        refine (_ @ monoidal_leftunitornat M _ _ δ_{m}).
        apply maponpaths_2.
        apply (when_bifunctor_becomes_leftwhiskering M).
      }
      rewrite assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply monoidal_leftunitorisolaw.
    - cbn.
      rewrite assoc.
      apply pathsinv0.
      etrans. {
        apply maponpaths_2.
        refine (_ @ monoidal_leftunitorinvnat M _ _ ε_{m}).
        now rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      }
      rewrite assoc'.
      apply maponpaths.
      apply monoidal_leftunitorisolaw.
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
      apply comult_before_inner_swap_and_swap.
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
        (tensor_of_comonoids xx (tensor_of_comonoids yy zz))
        (mon_lassociator xx yy zz).
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
      rewrite tensor_comp_mor.
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

      rewrite tensor_comp_mor.
      rewrite ! assoc'.
      apply maponpaths.
      rewrite ! assoc.
      apply inner_swap_hexagon'.
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
      etrans.
      2: {
        apply pathsinv0, tensor_comp_mor.
      }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply pathsinv0, mon_triangle. }
      apply maponpaths_2.
      apply mon_runitor_I_mon_lunitor_I.
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

End TensorOfComonoids.

Section TensorOfCommutativeComonoids.

  Context (V : sym_monoidal_cat).

  Lemma tensor_of_comm_comonoids
    (mx my : commutative_comonoid V)
    : is_commutative V (tensor_of_comonoids V mx my).
  Proof.
    use (z_iso_inv_on_left _ _ _ _ (inner_swap V _ _ _ _ ,, inner_swap V _ _ _ _ ,, _)).
    { apply inner_swap_is_z_isomorphism. }
    cbn.
    rewrite assoc'.
    etrans.
    2: {
      apply maponpaths.
      apply inner_swap_commute_with_swap.
    }

    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, inner_swap_inv.
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

End TensorOfCommutativeComonoids.
