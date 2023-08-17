nner_swap
(*
nner_swap
This file contains certain (coherence) properties involving the braiding, of a fixed symmetric monoidal category.
nner_swap
Two coherences, needed somewhere else, are admitted. These holes will be fixed.
nner_swap

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
Require Import UniMath.CategoryTheory.Core.Isos.
nner_swap
Require Import UniMath.CategoryTheory.limits.binproducts.
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
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
nner_swap

nner_swap
Local Open Scope cat.
nner_swap
Local Open Scope moncat.
nner_swap

nner_swap
Import MonoidalNotations.
nner_swap

nner_swap
Section Rearranging.
nner_swap

nner_swap
  Context (V : sym_monoidal_cat).
nner_swap

nner_swap
  Definition rearrange_prod (x y z w : V)
nner_swap
    : V⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
nner_swap
  Proof.
nner_swap
    refine (mon_lassociator _ _ _ · _).
nner_swap
    refine (_ · mon_rassociator _ _ _).
nner_swap
    refine (x ⊗^{V}_{l} _).
nner_swap
    refine (mon_rassociator _ _ _ · _).
nner_swap
    refine (_ · mon_lassociator _ _ _).
nner_swap
    exact (sym_mon_braiding V y z ⊗^{V}_{r} w).
nner_swap
  Defined.
nner_swap

nner_swap
  Definition rearrange_prod' (x y z w : V)
nner_swap
    : V⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
nner_swap
  Proof.
nner_swap
    refine (mon_lassociator _ _ _ · _).
nner_swap
    refine (_ · mon_rassociator _ _ _).
nner_swap
    refine (x ⊗^{V}_{l} _).
nner_swap
    exact (sym_mon_braiding _ _ _ · mon_lassociator _ _ _ · _ ⊗^{V}_{l} sym_mon_braiding _ _ _).
nner_swap
  Defined.
nner_swap

nner_swap
  Definition rearrange_prod'' (x y z w : V)
nner_swap
    : V⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
nner_swap
  Proof.
nner_swap
    refine (mon_lassociator _ _ _ · _).
nner_swap
    refine (x ⊗^{V}_{l} _ · _).
nner_swap
    - exact (sym_mon_braiding _ _ _ · mon_lassociator _ _ _).
nner_swap
    - exact (mon_rassociator x z (w ⊗ y) · (x ⊗ z) ⊗^{V}_{l} sym_mon_braiding _ w y).
nner_swap
  Defined.
nner_swap

nner_swap
  Definition rearrange_prod''' (x y z w : V)
nner_swap
    : V⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
nner_swap
  Proof.
nner_swap
    refine (sym_mon_braiding _ _ _ ⊗^{V}_{r} _  · mon_lassociator _ _ _ · sym_mon_braiding _ _ (_ ⊗ _) · _).
nner_swap
    refine (_ · _ ⊗^{V}_{l} sym_mon_braiding _ _ _).
nner_swap
    refine (_ · mon_rassociator _ _ _).
nner_swap
    refine (_ · x ⊗^{V}_{l} mon_lassociator _ _ _).
nner_swap
    apply mon_lassociator.
nner_swap
  Defined.
nner_swap

nner_swap
  Lemma sym_monoidal_braiding_hexagon1_variant (y z w : V)
nner_swap
    : mon_rassociator y z w · (sym_mon_braiding _ y z ⊗^{V}_{r} w · mon_lassociator z y w)
nner_swap
      = sym_mon_braiding _ _ _ · mon_lassociator _ _ _ · _ ⊗^{V}_{l} sym_mon_braiding _ _ _.
nner_swap
  Proof.
nner_swap
    rewrite assoc.
nner_swap
    apply pathsinv0.
nner_swap
    use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
nner_swap
    {
nner_swap
      use (is_z_iso_leftwhiskering_z_iso V).
nner_swap
      apply is_z_isomorphism_sym_mon_braiding.
nner_swap
    }
nner_swap
    cbn.
nner_swap
    rewrite ! assoc'.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths.
nner_swap
      rewrite assoc.
nner_swap
      refine (sym_mon_hexagon_lassociator V _ _ _ @ _).
nner_swap
      rewrite <- (when_bifunctor_becomes_rightwhiskering V).
nner_swap
      now rewrite <- (when_bifunctor_becomes_leftwhiskering V).
nner_swap
    }
nner_swap
    rewrite ! assoc.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply pathsinv0, monoidal_associatorisolaw.
nner_swap
    }
nner_swap
    now rewrite id_left.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_prod_characterization
nner_swap
    (x y z w : V)
nner_swap
    : rearrange_prod x y z w = rearrange_prod' x y z w.
nner_swap
  Proof.
nner_swap
    unfold rearrange_prod, rearrange_prod'.
nner_swap
    apply maponpaths.
nner_swap
    apply maponpaths_2.
nner_swap
    apply maponpaths.
nner_swap
    apply sym_monoidal_braiding_hexagon1_variant.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_prod_characterization' (x y z w : V)
nner_swap
    : rearrange_prod' x y z w = rearrange_prod'' x y z w.
nner_swap
  Proof.
nner_swap
    unfold rearrange_prod', rearrange_prod''.
nner_swap
    apply maponpaths.
nner_swap
    rewrite ! (bifunctor_leftcomp V).
nner_swap
    rewrite ! assoc'.
nner_swap
    do 2 apply maponpaths.
nner_swap
    apply monoidal_associatorinvnatleft.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_prod_characterization''
nner_swap
    (x y z w : V)
nner_swap
    : rearrange_prod x y z w = rearrange_prod'' x y z w.
nner_swap
  Proof.
nner_swap
    refine (rearrange_prod_characterization _ _ _ _ @ _).
nner_swap
    apply rearrange_prod_characterization'.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_prod_characterization''' (x y z w : V)
nner_swap
    : rearrange_prod'' x y z w = rearrange_prod''' x y z w.
nner_swap
  Proof.
nner_swap
    unfold rearrange_prod'', rearrange_prod'''.
nner_swap
    rewrite ! assoc.
nner_swap
    do 2 apply maponpaths_2.
nner_swap
    rewrite ! (bifunctor_leftcomp V).
nner_swap
    rewrite ! assoc.
nner_swap
    apply maponpaths_2.
nner_swap
    apply sym_mon_tensor_lassociator1.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_prod_characterization'''' (x y z w : V)
nner_swap
    : rearrange_prod x y z w = rearrange_prod''' x y z w.
nner_swap
  Proof.
nner_swap
    etrans. { apply rearrange_prod_characterization''. }
nner_swap
    apply rearrange_prod_characterization'''.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma precompose_rearrange_prod
nner_swap
    {x y z w : V}
nner_swap
    {x' y' z' w' : V}
nner_swap
    (fx : V⟦x,x'⟧)
nner_swap
    (fy : V⟦y,y'⟧)
nner_swap
    (fz : V⟦z,z'⟧)
nner_swap
    (fw : V⟦w,w'⟧)
nner_swap
    : rearrange_prod x y z w · ((fx #⊗ fz) #⊗ (fy #⊗ fw))
nner_swap
      = ((fx #⊗ fy) #⊗ (fz #⊗ fw)) · rearrange_prod _ _ _ _.
nner_swap
  Proof.
nner_swap
    unfold rearrange_prod.
nner_swap

nner_swap
    etrans. {
nner_swap
      rewrite ! assoc'.
nner_swap
      do 2 apply maponpaths.
nner_swap
      apply pathsinv0.
nner_swap
      exact (monoidal_associatorinv_nat2 V fx fz (fy #⊗ fw)).
nner_swap
    }
nner_swap

nner_swap
    rewrite ! assoc.
nner_swap
    apply maponpaths_2.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths_2.
nner_swap
      apply associator_nat2.
nner_swap
    }
nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      apply maponpaths.
nner_swap
      apply (sym_monoidal_braiding_hexagon1_variant y z w).
nner_swap
    }
nner_swap

nner_swap
    rewrite <- ! (when_bifunctor_becomes_leftwhiskering V).
nner_swap
    refine (! tensor_comp_mor _ _ _ _ @ _).
nner_swap
    refine (_ @ tensor_comp_mor _ _ _ _ ).
nner_swap
    rewrite id_left, id_right.
nner_swap
    apply maponpaths.
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths.
nner_swap
      exact (! sym_monoidal_braiding_hexagon1_variant y' z' w').
nner_swap
    }
nner_swap

nner_swap
    rewrite ! assoc.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply pathsinv0, tensor_sym_mon_braiding.
nner_swap
    }
nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap
    unfold monoidal_cat_tensor_mor.
nner_swap
    cbn.
nner_swap
    rewrite ! assoc.
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths_2.
nner_swap
      apply associator_nat2.
nner_swap
    }
nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap
    refine (! tensor_comp_mor _ _ _ _ @ _).
nner_swap

nner_swap
    rewrite id_left.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0, tensor_sym_mon_braiding.
nner_swap
    }
nner_swap
    cbn.
nner_swap
    rewrite <- (when_bifunctor_becomes_leftwhiskering V).
nner_swap
    refine (_ @ tensor_comp_mor _ _ _ _).
nner_swap
    apply maponpaths_2.
nner_swap
    apply pathsinv0, id_right.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_along_unit (x y : V)
nner_swap
    : rearrange_prod x I_{V} I_{V} y = identity _.
nner_swap
  Proof.
nner_swap
    unfold rearrange_prod.
nner_swap
    rewrite sym_mon_braiding_id.
nner_swap
    rewrite (bifunctor_rightid V).
nner_swap
    rewrite id_left.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply maponpaths_2.
nner_swap
      apply maponpaths.
nner_swap
      apply monoidal_associatorisolaw.
nner_swap
    }
nner_swap
    rewrite (bifunctor_leftid V).
nner_swap
    rewrite id_left.
nner_swap
    apply monoidal_associatorisolaw.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_prod_inv
nner_swap
    (x y z w : V)
nner_swap
    : rearrange_prod x y z w · rearrange_prod x z y w = identity _.
nner_swap
  Proof.
nner_swap
    unfold rearrange_prod.
nner_swap
    apply pathsinv0.
nner_swap
    rewrite ! assoc'.
nner_swap
    use (z_iso_inv_to_left _ _ _ (_ ,, _)).
nner_swap
    {
nner_swap
      apply (_ ,, monoidal_associatorisolaw V _ _ _).
nner_swap
    }
nner_swap
    cbn.
nner_swap
    rewrite ! assoc.
nner_swap
    use (z_iso_inv_on_left _ _ _ _ (mon_lassociator _ _ _ ,, mon_rassociator _ _ _ ,, _)).
nner_swap
    {
nner_swap
      apply (_ ,, monoidal_associatorisolaw _ _ _ _).
nner_swap
    }
nner_swap
    cbn.
nner_swap
    rewrite id_right.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply pathsinv0.
nner_swap
      apply monoidal_associatorisolaw.
nner_swap
    }
nner_swap
    cbn.
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
      apply monoidal_associatorisolaw.
nner_swap
    }
nner_swap
    rewrite id_right.
nner_swap
    refine (! bifunctor_leftcomp V _ _ _ _ _ _ @ _).
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      rewrite ! assoc.
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply monoidal_associatorisolaw.
nner_swap
    }
nner_swap
    rewrite id_left.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      rewrite assoc.
nner_swap
      apply maponpaths_2.
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _).
nner_swap
      apply maponpaths.
nner_swap
      apply (monoidal_braiding_inverses V).
nner_swap
    }
nner_swap
    rewrite (bifunctor_rightid V).
nner_swap
    rewrite id_right.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply monoidal_associatorisolaw.
nner_swap
    }
nner_swap
    apply (bifunctor_leftid V).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_prod_is_z_isomorphism
nner_swap
    (x y z w : V)
nner_swap
    : is_z_isomorphism (rearrange_prod x y z w).
nner_swap
  Proof.
nner_swap
    use make_is_z_isomorphism.
nner_swap
    - apply rearrange_prod.
nner_swap
    - split ; apply rearrange_prod_inv.
nner_swap
  Defined.
nner_swap

nner_swap
  Lemma mon_lunitor_triangle_transposed (x : V)
nner_swap
    : mon_lunitor (monoidal_unit V ⊗_{V} x)
nner_swap
      = mon_rassociator I_{V} I_{V} x · mon_lunitor I_{V} ⊗^{V}_{r} x.
nner_swap
  Proof.
nner_swap
    rewrite <- (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      apply maponpaths, mon_lunitor_triangle.
nner_swap
    }
nner_swap
    rewrite assoc.
nner_swap
    refine (! id_left _ @ _).
nner_swap
    apply maponpaths_2.
nner_swap
    apply pathsinv0.
nner_swap
    apply monoidal_associatorisolaw.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rightwhisker_of_lunitor_with_unit (x : V)
nner_swap
    : monoidal_unit V ⊗^{V}_{l} lu^{V}_{x} = lu^{V}_{monoidal_unit V ⊗ x}.
nner_swap
  Proof.
nner_swap
    refine (_ @ ! mon_lunitor_triangle_transposed x).
nner_swap

nner_swap
    use (z_iso_inv_to_left _ _ _ (mon_rassociator _ _ _ ,, mon_lassociator _ _ _ ,, _)).
nner_swap
    {
nner_swap
      split ; apply monoidal_associatorisolaw.
nner_swap
    }
nner_swap

nner_swap
    refine (monoidal_triangleidentity _ _ _ @ _).
nner_swap
    apply maponpaths.
nner_swap
    apply pathsinv0, unitors_coincide_on_unit.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma whiskering_on_both_sides_with_lunitor_left_unit (x y : V)
nner_swap
    : monoidal_unit V ⊗^{V}_{l} (mon_lunitor x ⊗^{V}_{r} y)
nner_swap
      = monoidal_unit V ⊗^{V}_{l} mon_lassociator _ _ _
nner_swap
          · (mon_rassociator _ _ (x ⊗ y) · mon_lunitor _ ⊗^{V}_{r} (x ⊗ y)).
nner_swap
  Proof.
nner_swap
    refine (Categories.right_whisker_with_lunitor' _ _ _ @ _).
nner_swap
    rewrite (bifunctor_leftcomp V).
nner_swap
    apply maponpaths.
nner_swap
    refine (_ @ mon_lunitor_triangle_transposed _).
nner_swap
    exact (rightwhisker_of_lunitor_with_unit (x ⊗ y)).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma precompose_rearrange_prod_with_lunitors_on_right (x y : V)
nner_swap
    : rearrange_prod (monoidal_unit V) x (monoidal_unit V) y
nner_swap
        · mon_lunitor (monoidal_unit V) ⊗^{V}_{r} (x ⊗ y) · mon_lunitor (x ⊗ y)
nner_swap
      = (mon_lunitor x #⊗ mon_lunitor y).
nner_swap
  Proof.
nner_swap
    unfold rearrange_prod.
nner_swap

nner_swap
    rewrite ! (bifunctor_leftcomp V).
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      rewrite ! assoc'.
nner_swap
      do 2 apply maponpaths.
nner_swap

nner_swap
      refine (_ @ idpath (monoidal_unit V ⊗^{V}_{l} (mon_runitor x ⊗^{V}_{r} y))).
nner_swap

nner_swap
      apply pathsinv0.
nner_swap
      use (z_iso_inv_to_left _ _ _ (_ ,, _)).
nner_swap
      {
nner_swap
        use is_z_iso_leftwhiskering_z_iso.
nner_swap
        use (is_z_iso_rightwhiskering_z_iso V).
nner_swap
        apply (_ ,, monoidal_braiding_inverses V _ _).
nner_swap
      }
nner_swap
      cbn.
nner_swap
      rewrite <- (bifunctor_leftcomp V).
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _).
nner_swap
        apply maponpaths.
nner_swap
        apply sym_mon_braiding_runitor.
nner_swap
      }
nner_swap
      apply whiskering_on_both_sides_with_lunitor_left_unit.
nner_swap
    }
nner_swap

nner_swap
    rewrite <- (bifunctor_leftcomp V).
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      do 2 apply maponpaths.
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        refine (_ @ mon_triangle x y).
nner_swap
        apply pathsinv0, (when_bifunctor_becomes_rightwhiskering V).
nner_swap
      }
nner_swap
      rewrite assoc.
nner_swap
      apply maponpaths_2.
nner_swap
      apply monoidal_associatorisolaw.
nner_swap
    }
nner_swap
    rewrite id_left.
nner_swap
    unfold monoidal_cat_tensor_mor.
nner_swap
    cbn.
nner_swap
    etrans. {
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      refine (_ @ tensor_lunitor (identity x #⊗ mon_lunitor y)).
nner_swap
      now rewrite <- (when_bifunctor_becomes_leftwhiskering V).
nner_swap
    }
nner_swap

nner_swap
    rewrite assoc.
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      apply mon_lunitor_triangle.
nner_swap
    }
nner_swap
    apply pathsinv0, tensor_split'.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma precompose_rearrange_prod_with_lunitors_and_runitor (x y : V)
nner_swap
    : rearrange_prod x (monoidal_unit V) y (monoidal_unit V)
nner_swap
        · (x ⊗ y) ⊗^{V}_{l} mon_lunitor (monoidal_unit V) · mon_runitor (x ⊗ y)
nner_swap
      = (mon_runitor x #⊗ mon_runitor y).
nner_swap
  Proof.
nner_swap

nner_swap
    unfold rearrange_prod.
nner_swap

nner_swap
    rewrite ! (bifunctor_leftcomp V).
nner_swap
    etrans. {
nner_swap
      apply maponpaths_2.
nner_swap
      rewrite ! assoc'.
nner_swap
      do 2 apply maponpaths.
nner_swap
      refine (_ @ idpath (x ⊗^{V}_{l} (mon_lunitor y ⊗^{V}_{r} monoidal_unit V) · mon_rassociator _ _ _)).
nner_swap

nner_swap
      apply pathsinv0.
nner_swap
      use (z_iso_inv_to_left _ _ _ (_ ,, _)).
nner_swap
      {
nner_swap
        use is_z_iso_leftwhiskering_z_iso.
nner_swap
        use (is_z_iso_rightwhiskering_z_iso V).
nner_swap
        apply (_ ,, monoidal_braiding_inverses V _ _).
nner_swap
      }
nner_swap
      cbn.
nner_swap
      rewrite ! assoc.
nner_swap
      rewrite <- (bifunctor_leftcomp V).
nner_swap
      etrans. {
nner_swap
        apply maponpaths_2.
nner_swap
        apply maponpaths.
nner_swap
        refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _).
nner_swap
        apply maponpaths.
nner_swap
        apply sym_mon_braiding_lunitor.
nner_swap
      }
nner_swap

nner_swap
      etrans. {
nner_swap
        apply maponpaths_2.
nner_swap
        apply maponpaths.
nner_swap
        refine (_ @ mon_triangle _ _).
nner_swap
        apply pathsinv0.
nner_swap
        apply (when_bifunctor_becomes_rightwhiskering V).
nner_swap
      }
nner_swap
      cbn.
nner_swap
      rewrite (bifunctor_leftcomp V).
nner_swap
      rewrite ! assoc'.
nner_swap
      apply maponpaths.
nner_swap
      unfold monoidal_cat_tensor_mor.
nner_swap
      cbn.
nner_swap
      rewrite (when_bifunctor_becomes_leftwhiskering V).
nner_swap
      apply (monoidal_associatorinvnatleft V).
nner_swap
    }
nner_swap

nner_swap
    rewrite ! assoc'.
nner_swap
    etrans. {
nner_swap
      do 3 apply maponpaths.
nner_swap
      apply mon_runitor_triangle.
nner_swap
    }
nner_swap
    unfold monoidal_cat_tensor_mor.
nner_swap
    cbn.
nner_swap
    unfold functoronmorphisms1.
nner_swap
    unfold monoidal_cat_tensor_pt.
nner_swap
    cbn.
nner_swap

nner_swap
    rewrite ! assoc.
nner_swap
    apply maponpaths_2.
nner_swap
    rewrite (bifunctor_rightid V).
nner_swap
    rewrite id_right.
nner_swap
    rewrite assoc'.
nner_swap
    rewrite <- (bifunctor_leftcomp V).
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      refine (! mon_triangle  _ _ @ _).
nner_swap
      apply (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    }
nner_swap

nner_swap
    apply maponpaths.
nner_swap
    rewrite <- (when_bifunctor_becomes_leftwhiskering V).
nner_swap
    apply maponpaths.
nner_swap

nner_swap
    use (z_iso_inv_on_right _ _ _ (mon_lassociator _ _ _ ,, _ ,, _)).
nner_swap
    { apply monoidal_associatorisolaw. }
nner_swap
    cbn.
nner_swap
    rewrite <- (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    apply (! mon_lunitor_triangle _ _).
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_hexagon (x1 x2 y1 y2 z1 z2 : V)
nner_swap
    : rearrange_prod (x1 ⊗ x2) y1 (y2 ⊗ z1) z2
nner_swap
         · (rearrange_prod x1 x2 y2 z1 ⊗^{V}_{r} (y1 ⊗ z2)
nner_swap
              · mon_lassociator _ _ _)
nner_swap
       = (mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _)
nner_swap
           · (rearrange_prod x1 (x2 ⊗ y1) y2 (z1 ⊗ z2)
nner_swap
                · (x1 ⊗ y2) ⊗^{V}_{l} rearrange_prod x2 y1 z1 z2).
nner_swap
  Proof.
nner_swap
  Admitted.
nner_swap

nner_swap
  Lemma rearrange_hexagon_2 (x y : V)
nner_swap
    : rearrange_prod (x ⊗ x) x (y ⊗ y) y
nner_swap
         · (rearrange_prod x x y y ⊗^{V}_{r} (x ⊗ y)
nner_swap
              · mon_lassociator _ _ _)
nner_swap
       = mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _
nner_swap
           · (rearrange_prod x (x ⊗ x) y (y ⊗ y)
nner_swap
                · (x ⊗ y) ⊗^{V}_{l} rearrange_prod x x y y).
nner_swap
  Proof.
nner_swap
    apply rearrange_hexagon.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_hexagon' (x1 x2 y1 y2 z1 z2 : V)
nner_swap
    : rearrange_prod x1 x2 y1 y2 #⊗ identity (z1 ⊗ z2)
nner_swap
        · rearrange_prod (x1 ⊗ y1) (x2 ⊗ y2) z1 z2
nner_swap
        · mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _
nner_swap
      = mon_lassociator _ _ _
nner_swap
            · identity (x1 ⊗ x2) #⊗ rearrange_prod y1 y2 z1 z2
nner_swap
            · rearrange_prod x1 x2 (y1 ⊗ z1) (y2 ⊗ z2).
nner_swap
  Proof.
nner_swap
  Admitted.
nner_swap

nner_swap
  Lemma rearrange_hexagon'_3 (x y z : V)
nner_swap
    : rearrange_prod x x y y #⊗ identity (z ⊗ z)
nner_swap
        · rearrange_prod (x ⊗ y) (x ⊗ y) z z
nner_swap
        · mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _
nner_swap
      = mon_lassociator _ _ _
nner_swap
            · identity (x ⊗_ x) #⊗ rearrange_prod y y z z
nner_swap
            · rearrange_prod x x (y ⊗ z) (y ⊗ z).
nner_swap
  Proof.
nner_swap
    apply rearrange_hexagon'.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_hexagoninv' (x y z : V)
nner_swap
    : identity (x ⊗ x) #⊗ rearrange_prod y y z z
nner_swap
  · rearrange_prod x x (y ⊗ z) (y ⊗ z)
nner_swap
  · mon_rassociator _ _ _ #⊗ mon_rassociator _ _ _ =
nner_swap
  mon_rassociator _ _ _
nner_swap
  · rearrange_prod x x y y #⊗ identity (z ⊗ z)
nner_swap
  · rearrange_prod (x ⊗ y) (x ⊗ y) z z.
nner_swap
  Proof.
nner_swap
    set (t := rearrange_hexagon' x x y y z z).
nner_swap
    apply pathsinv0.
nner_swap
    use (z_iso_inv_on_left _ _ _ _ (mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _,,
nner_swap
                                      mon_rassociator _ _ _ #⊗ mon_rassociator _ _ _ ,, _)).
nner_swap
    {
nner_swap
      apply (pr2 (is_z_iso_bifunctor_z_iso V
nner_swap
                    (mon_lassociator _ _ _) (mon_lassociator _ _ _)
nner_swap
                    (_ ,, monoidal_associatorisolaw V _ _ _)
nner_swap
                    (_ ,, monoidal_associatorisolaw V _ _ _))).
nner_swap
    }
nner_swap
    cbn.
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      rewrite ! assoc'.
nner_swap
      apply maponpaths.
nner_swap
      rewrite assoc.
nner_swap
      apply (! t).
nner_swap
    }
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      rewrite ! assoc.
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply pathsinv0.
nner_swap
      apply mon_rassociator_lassociator.
nner_swap
    }
nner_swap
    now rewrite id_left.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearrange_commute_with_swap (x1 x2 y1 y2 : V)
nner_swap
    : rearrange_prod x1 x2 y1 y2 · sym_mon_braiding _ x1 y1 #⊗ sym_mon_braiding _ x2 y2
nner_swap
      = sym_mon_braiding _ (x1 ⊗ x2) (y1 ⊗ y2) · rearrange_prod y1 y2 x1 x2.
nner_swap
  Proof.
nner_swap
    unfold rearrange_prod.
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
      apply pathsinv0, sym_mon_tensor_lassociator0.
nner_swap
    }
nner_swap
    unfold monoidal_cat_tensor_mor, mon_lassociator, mon_rassociator.
nner_swap
    cbn.
nner_swap

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
      rewrite (when_bifunctor_becomes_leftwhiskering V).
nner_swap
      etrans.
nner_swap
      2: apply (bifunctor_leftcomp V y1).
nner_swap
      apply maponpaths.
nner_swap
      rewrite ! assoc.
nner_swap
      apply pathsinv0.
nner_swap
      apply sym_mon_hexagon_rassociator0.
nner_swap
    }
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      rewrite ! assoc'.
nner_swap
      do 2 apply maponpaths.
nner_swap
      refine (! sym_mon_hexagon_lassociator1 _ _ _ _ _ @ _).
nner_swap
      now rewrite ! assoc'.
nner_swap
    }
nner_swap

nner_swap
    unfold functoronmorphisms1.
nner_swap
    rewrite ! assoc.
nner_swap
    apply maponpaths_2.
nner_swap
    unfold monoidal_cat_tensor_pt.
nner_swap
    cbn.
nner_swap

nner_swap
    rewrite ! assoc'.
nner_swap
    apply pathsinv0.
nner_swap
    use (z_iso_inv_on_right _ _ _ (mon_lassociator _ _ _ ,, mon_rassociator _ _ _ ,, _)).
nner_swap
    { apply monoidal_associatorisolaw. }
nner_swap
    cbn.
nner_swap

nner_swap
    rewrite (bifunctor_leftcomp V).
nner_swap
    rewrite ! assoc.
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 3 apply maponpaths_2.
nner_swap
      apply pathsinv0.
nner_swap
      apply mon_lassociator_lassociator'.
nner_swap
    }
nner_swap
    rewrite (bifunctor_leftid V).
nner_swap
    rewrite id_right.
nner_swap

nner_swap
    apply pathsinv0.
nner_swap
    use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
nner_swap
    {
nner_swap
      use (is_z_iso_rightwhiskering_z_iso V).
nner_swap
      refine (_ ,, _).
nner_swap
      apply (_ ,, monoidal_braiding_inverses V).
nner_swap
    }
nner_swap
    cbn.
nner_swap

nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0, monoidal_associatornatright.
nner_swap
    }
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
      rewrite <- ! (bifunctor_rightcomp V).
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0, sym_mon_hexagon_rassociator1.
nner_swap
    }
nner_swap

nner_swap
    rewrite ! (bifunctor_rightcomp V).
nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap
    rewrite ! assoc.
nner_swap
    rewrite (bifunctor_leftcomp V).
nner_swap
    rewrite assoc.
nner_swap
    unfold sym_mon_braiding, mon_lassociator, monoidal_cat_tensor_pt.
nner_swap
    cbn.
nner_swap
    rewrite (monoidal_associatornatleftright V).
nner_swap
    rewrite ! assoc'.
nner_swap
    apply maponpaths.
nner_swap
    rewrite assoc.
nner_swap
    apply pathsinv0.
nner_swap
    use (z_iso_inv_on_left _ _ _ _ (mon_lassociator _ _ _ ,, mon_rassociator _ _ _ ,, _)).
nner_swap
    {
nner_swap
      apply monoidal_associatorisolaw.
nner_swap
    }
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
      apply pathsinv0, mon_lassociator_lassociator.
nner_swap
    }
nner_swap
    unfold monoidal_cat_tensor_mor.
nner_swap
    unfold mon_lassociator.
nner_swap
    unfold mon_rassociator.
nner_swap
    unfold monoidal_cat_tensor_pt.
nner_swap
    cbn.
nner_swap
    rewrite ! assoc.
nner_swap
    rewrite (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    rewrite <- (bifunctor_rightcomp V).
nner_swap
    etrans.
nner_swap
    2: {
nner_swap
      do 2 apply maponpaths_2.
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0, (monoidal_associatorisolaw V).
nner_swap
    }
nner_swap
    rewrite (bifunctor_rightid V).
nner_swap
    rewrite id_left.
nner_swap
    now rewrite (when_bifunctor_becomes_leftwhiskering V).
nner_swap
  Qed.
nner_swap

nner_swap
End Rearranging.
