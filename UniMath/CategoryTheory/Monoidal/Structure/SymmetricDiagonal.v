(*
This file contains certain (coherence) properties involving the braiding, of a fixed symmetric monoidal category.
Two coherences, needed somewhere else, are admitted. These holes will be fixed.

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Section Rearranging.

  Context (V : sym_monoidal_cat).

  Definition inner_swap (x y z w : V)
    : V⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
  Proof.
    refine (mon_lassociator _ _ _ · _).
    refine (_ · mon_rassociator _ _ _).
    refine (x ⊗^{V}_{l} _).
    refine (mon_rassociator _ _ _ · _).
    refine (_ · mon_lassociator _ _ _).
    exact (sym_mon_braiding V y z ⊗^{V}_{r} w).
  Defined.

  Definition inner_swap' (x y z w : V)
    : V⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
  Proof.
    refine (mon_lassociator _ _ _ · _).
    refine (_ · mon_rassociator _ _ _).
    refine (x ⊗^{V}_{l} _).
    exact (sym_mon_braiding _ _ _ · mon_lassociator _ _ _ · _ ⊗^{V}_{l} sym_mon_braiding _ _ _).
  Defined.

  Definition inner_swap'' (x y z w : V)
    : V⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
  Proof.
    refine (mon_lassociator _ _ _ · _).
    refine (x ⊗^{V}_{l} _ · _).
    - exact (sym_mon_braiding _ _ _ · mon_lassociator _ _ _).
    - exact (mon_rassociator x z (w ⊗ y) · (x ⊗ z) ⊗^{V}_{l} sym_mon_braiding _ w y).
  Defined.

  Definition inner_swap''' (x y z w : V)
    : V⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
  Proof.
    refine (sym_mon_braiding _ _ _ ⊗^{V}_{r} _  · mon_lassociator _ _ _ · sym_mon_braiding _ _ (_ ⊗ _) · _).
    refine (_ · _ ⊗^{V}_{l} sym_mon_braiding _ _ _).
    refine (_ · mon_rassociator _ _ _).
    refine (_ · x ⊗^{V}_{l} mon_lassociator _ _ _).
    apply mon_lassociator.
  Defined.

  Lemma sym_monoidal_braiding_hexagon1_variant (y z w : V)
    : mon_rassociator y z w · (sym_mon_braiding _ y z ⊗^{V}_{r} w · mon_lassociator z y w)
      = sym_mon_braiding _ _ _ · mon_lassociator _ _ _ · _ ⊗^{V}_{l} sym_mon_braiding _ _ _.
  Proof.
    rewrite assoc.
    apply pathsinv0.
    use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
    {
      use (is_z_iso_leftwhiskering_z_iso V).
      apply is_z_isomorphism_sym_mon_braiding.
    }
    cbn.
    rewrite ! assoc'.
    etrans.
    2: {
      apply maponpaths.
      rewrite assoc.
      refine (sym_mon_hexagon_lassociator V _ _ _ @ _).
      rewrite <- (when_bifunctor_becomes_rightwhiskering V).
      now rewrite <- (when_bifunctor_becomes_leftwhiskering V).
    }
    rewrite ! assoc.
    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply pathsinv0, monoidal_associatorisolaw.
    }
    now rewrite id_left.
  Qed.

  Lemma inner_swap_characterization
    (x y z w : V)
    : inner_swap x y z w = inner_swap' x y z w.
  Proof.
    unfold inner_swap, inner_swap'.
    apply maponpaths.
    apply maponpaths_2.
    apply maponpaths.
    apply sym_monoidal_braiding_hexagon1_variant.
  Qed.

  Lemma inner_swap_characterization' (x y z w : V)
    : inner_swap' x y z w = inner_swap'' x y z w.
  Proof.
    unfold inner_swap', inner_swap''.
    apply maponpaths.
    rewrite ! (bifunctor_leftcomp V).
    rewrite ! assoc'.
    do 2 apply maponpaths.
    apply monoidal_associatorinvnatleft.
  Qed.

  Lemma inner_swap_characterization''
    (x y z w : V)
    : inner_swap x y z w = inner_swap'' x y z w.
  Proof.
    refine (inner_swap_characterization _ _ _ _ @ _).
    apply inner_swap_characterization'.
  Qed.

  Lemma inner_swap_characterization''' (x y z w : V)
    : inner_swap'' x y z w = inner_swap''' x y z w.
  Proof.
    unfold inner_swap'', inner_swap'''.
    rewrite ! assoc.
    do 2 apply maponpaths_2.
    rewrite ! (bifunctor_leftcomp V).
    rewrite ! assoc.
    apply maponpaths_2.
    apply sym_mon_tensor_lassociator1.
  Qed.

  Lemma inner_swap_characterization'''' (x y z w : V)
    : inner_swap x y z w = inner_swap''' x y z w.
  Proof.
    etrans. { apply inner_swap_characterization''. }
    apply inner_swap_characterization'''.
  Qed.

  Lemma precompose_inner_swap
    {x y z w : V}
    {x' y' z' w' : V}
    (fx : V⟦x,x'⟧)
    (fy : V⟦y,y'⟧)
    (fz : V⟦z,z'⟧)
    (fw : V⟦w,w'⟧)
    : inner_swap x y z w · ((fx #⊗ fz) #⊗ (fy #⊗ fw))
      = ((fx #⊗ fy) #⊗ (fz #⊗ fw)) · inner_swap _ _ _ _.
  Proof.
    unfold inner_swap.

    etrans. {
      rewrite ! assoc'.
      do 2 apply maponpaths.
      apply pathsinv0.
      exact (monoidal_associatorinv_nat2 V fx fz (fy #⊗ fw)).
    }

    rewrite ! assoc.
    apply maponpaths_2.
    etrans.
    2: {
      apply maponpaths_2.
      apply associator_nat2.
    }
    rewrite ! assoc'.
    apply maponpaths.

    etrans. {
      apply maponpaths_2.
      apply maponpaths.
      apply (sym_monoidal_braiding_hexagon1_variant y z w).
    }

    rewrite <- ! (when_bifunctor_becomes_leftwhiskering V).
    refine (! tensor_comp_mor _ _ _ _ @ _).
    refine (_ @ tensor_comp_mor _ _ _ _ ).
    rewrite id_left, id_right.
    apply maponpaths.

    etrans.
    2: {
      apply maponpaths.
      exact (! sym_monoidal_braiding_hexagon1_variant y' z' w').
    }

    rewrite ! assoc.
    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply pathsinv0, tensor_sym_mon_braiding.
    }
    rewrite ! assoc'.
    apply maponpaths.
    unfold monoidal_cat_tensor_mor.
    cbn.
    rewrite ! assoc.

    etrans.
    2: {
      apply maponpaths_2.
      apply associator_nat2.
    }
    rewrite ! assoc'.
    apply maponpaths.
    refine (! tensor_comp_mor _ _ _ _ @ _).

    rewrite id_left.
    etrans. {
      apply maponpaths.
      apply pathsinv0, tensor_sym_mon_braiding.
    }
    cbn.
    rewrite <- (when_bifunctor_becomes_leftwhiskering V).
    refine (_ @ tensor_comp_mor _ _ _ _).
    apply maponpaths_2.
    apply pathsinv0, id_right.
  Qed.

  Lemma rearrange_along_unit (x y : V)
    : inner_swap x I_{V} I_{V} y = identity _.
  Proof.
    unfold inner_swap.
    rewrite sym_mon_braiding_id.
    rewrite (bifunctor_rightid V).
    rewrite id_left.
    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply monoidal_associatorisolaw.
    }
    rewrite (bifunctor_leftid V).
    rewrite id_left.
    apply monoidal_associatorisolaw.
  Qed.

  Lemma inner_swap_inv
    (x y z w : V)
    : inner_swap x y z w · inner_swap x z y w = identity _.
  Proof.
    unfold inner_swap.
    apply pathsinv0.
    rewrite ! assoc'.
    use (z_iso_inv_to_left _ _ _ (_ ,, _)).
    {
      apply (_ ,, monoidal_associatorisolaw V _ _ _).
    }
    cbn.
    rewrite ! assoc.
    use (z_iso_inv_on_left _ _ _ _ (mon_lassociator _ _ _ ,, mon_rassociator _ _ _ ,, _)).
    {
      apply (_ ,, monoidal_associatorisolaw _ _ _ _).
    }
    cbn.
    rewrite id_right.
    etrans.
    2: {
      apply pathsinv0.
      apply monoidal_associatorisolaw.
    }
    cbn.

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply monoidal_associatorisolaw.
    }
    rewrite id_right.
    refine (! bifunctor_leftcomp V _ _ _ _ _ _ @ _).
    etrans. {
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      apply monoidal_associatorisolaw.
    }
    rewrite id_left.
    etrans. {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _).
      apply maponpaths.
      apply (monoidal_braiding_inverses V).
    }
    rewrite (bifunctor_rightid V).
    rewrite id_right.
    etrans. {
      apply maponpaths.
      apply monoidal_associatorisolaw.
    }
    apply (bifunctor_leftid V).
  Qed.

  Lemma inner_swap_is_z_isomorphism
    (x y z w : V)
    : is_z_isomorphism (inner_swap x y z w).
  Proof.
    use make_is_z_isomorphism.
    - apply inner_swap.
    - split ; apply inner_swap_inv.
  Defined.

  Lemma mon_lunitor_triangle_transposed (x : V)
    : mon_lunitor (monoidal_unit V ⊗_{V} x)
      = mon_rassociator I_{V} I_{V} x · mon_lunitor I_{V} ⊗^{V}_{r} x.
  Proof.
    rewrite <- (when_bifunctor_becomes_rightwhiskering V).
    etrans.
    2: {
      apply maponpaths, mon_lunitor_triangle.
    }
    rewrite assoc.
    refine (! id_left _ @ _).
    apply maponpaths_2.
    apply pathsinv0.
    apply monoidal_associatorisolaw.
  Qed.

  Lemma rightwhisker_of_lunitor_with_unit (x : V)
    : monoidal_unit V ⊗^{V}_{l} lu^{V}_{x} = lu^{V}_{monoidal_unit V ⊗ x}.
  Proof.
    refine (_ @ ! mon_lunitor_triangle_transposed x).

    use (z_iso_inv_to_left _ _ _ (mon_rassociator _ _ _ ,, mon_lassociator _ _ _ ,, _)).
    {
      split ; apply monoidal_associatorisolaw.
    }

    refine (monoidal_triangleidentity _ _ _ @ _).
    apply maponpaths.
    apply pathsinv0, unitors_coincide_on_unit.
  Qed.

  Lemma whiskering_on_both_sides_with_lunitor_left_unit (x y : V)
    : monoidal_unit V ⊗^{V}_{l} (mon_lunitor x ⊗^{V}_{r} y)
      = monoidal_unit V ⊗^{V}_{l} mon_lassociator _ _ _
          · (mon_rassociator _ _ (x ⊗ y) · mon_lunitor _ ⊗^{V}_{r} (x ⊗ y)).
  Proof.
    refine (Categories.right_whisker_with_lunitor' _ _ _ @ _).
    rewrite (bifunctor_leftcomp V).
    apply maponpaths.
    refine (_ @ mon_lunitor_triangle_transposed _).
    exact (rightwhisker_of_lunitor_with_unit (x ⊗ y)).
  Qed.

  Lemma precompose_inner_swap_with_lunitors_on_right (x y : V)
    : inner_swap (monoidal_unit V) x (monoidal_unit V) y
        · mon_lunitor (monoidal_unit V) ⊗^{V}_{r} (x ⊗ y) · mon_lunitor (x ⊗ y)
      = (mon_lunitor x #⊗ mon_lunitor y).
  Proof.
    unfold inner_swap.

    rewrite ! (bifunctor_leftcomp V).
    etrans. {
      apply maponpaths_2.
      rewrite ! assoc'.
      do 2 apply maponpaths.

      refine (_ @ idpath (monoidal_unit V ⊗^{V}_{l} (mon_runitor x ⊗^{V}_{r} y))).

      apply pathsinv0.
      use (z_iso_inv_to_left _ _ _ (_ ,, _)).
      {
        use is_z_iso_leftwhiskering_z_iso.
        use (is_z_iso_rightwhiskering_z_iso V).
        apply (_ ,, monoidal_braiding_inverses V _ _).
      }
      cbn.
      rewrite <- (bifunctor_leftcomp V).
      etrans. {
        apply maponpaths.
        refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _).
        apply maponpaths.
        apply sym_mon_braiding_runitor.
      }
      apply whiskering_on_both_sides_with_lunitor_left_unit.
    }

    rewrite <- (bifunctor_leftcomp V).
    etrans. {
      apply maponpaths_2.
      do 2 apply maponpaths.
      etrans. {
        apply maponpaths.
        refine (_ @ mon_triangle x y).
        apply pathsinv0, (when_bifunctor_becomes_rightwhiskering V).
      }
      rewrite assoc.
      apply maponpaths_2.
      apply monoidal_associatorisolaw.
    }
    rewrite id_left.
    unfold monoidal_cat_tensor_mor.
    cbn.
    etrans. {
      rewrite assoc'.
      apply maponpaths.
      refine (_ @ tensor_lunitor (identity x #⊗ mon_lunitor y)).
      now rewrite <- (when_bifunctor_becomes_leftwhiskering V).
    }

    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      apply mon_lunitor_triangle.
    }
    apply pathsinv0, tensor_split'.
  Qed.

  Lemma precompose_inner_swap_with_lunitors_and_runitor (x y : V)
    : inner_swap x (monoidal_unit V) y (monoidal_unit V)
        · (x ⊗ y) ⊗^{V}_{l} mon_lunitor (monoidal_unit V) · mon_runitor (x ⊗ y)
      = (mon_runitor x #⊗ mon_runitor y).
  Proof.

    unfold inner_swap.

    rewrite ! (bifunctor_leftcomp V).
    etrans. {
      apply maponpaths_2.
      rewrite ! assoc'.
      do 2 apply maponpaths.
      refine (_ @ idpath (x ⊗^{V}_{l} (mon_lunitor y ⊗^{V}_{r} monoidal_unit V) · mon_rassociator _ _ _)).

      apply pathsinv0.
      use (z_iso_inv_to_left _ _ _ (_ ,, _)).
      {
        use is_z_iso_leftwhiskering_z_iso.
        use (is_z_iso_rightwhiskering_z_iso V).
        apply (_ ,, monoidal_braiding_inverses V _ _).
      }
      cbn.
      rewrite ! assoc.
      rewrite <- (bifunctor_leftcomp V).
      etrans. {
        apply maponpaths_2.
        apply maponpaths.
        refine (! bifunctor_rightcomp V _ _ _ _ _ _ @ _).
        apply maponpaths.
        apply sym_mon_braiding_lunitor.
      }

      etrans. {
        apply maponpaths_2.
        apply maponpaths.
        refine (_ @ mon_triangle _ _).
        apply pathsinv0.
        apply (when_bifunctor_becomes_rightwhiskering V).
      }
      cbn.
      rewrite (bifunctor_leftcomp V).
      rewrite ! assoc'.
      apply maponpaths.
      unfold monoidal_cat_tensor_mor.
      cbn.
      rewrite (when_bifunctor_becomes_leftwhiskering V).
      apply (monoidal_associatorinvnatleft V).
    }

    rewrite ! assoc'.
    etrans. {
      do 3 apply maponpaths.
      apply mon_runitor_triangle.
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    unfold functoronmorphisms1.
    unfold monoidal_cat_tensor_pt.
    cbn.

    rewrite ! assoc.
    apply maponpaths_2.
    rewrite (bifunctor_rightid V).
    rewrite id_right.
    rewrite assoc'.
    rewrite <- (bifunctor_leftcomp V).

    etrans.
    2: {
      refine (! mon_triangle  _ _ @ _).
      apply (when_bifunctor_becomes_rightwhiskering V).
    }

    apply maponpaths.
    rewrite <- (when_bifunctor_becomes_leftwhiskering V).
    apply maponpaths.

    use (z_iso_inv_on_right _ _ _ (mon_lassociator _ _ _ ,, _ ,, _)).
    { apply monoidal_associatorisolaw. }
    cbn.
    rewrite <- (when_bifunctor_becomes_rightwhiskering V).
    apply (! mon_lunitor_triangle _ _).
  Qed.

  Lemma rearrange_hexagon (x1 x2 y1 y2 z1 z2 : V)
    : inner_swap (x1 ⊗ x2) y1 (y2 ⊗ z1) z2
         · (inner_swap x1 x2 y2 z1 ⊗^{V}_{r} (y1 ⊗ z2)
              · mon_lassociator _ _ _)
       = (mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _)
           · (inner_swap x1 (x2 ⊗ y1) y2 (z1 ⊗ z2)
                · (x1 ⊗ y2) ⊗^{V}_{l} inner_swap x2 y1 z1 z2).
  Proof.
  Admitted.

  Lemma rearrange_hexagon_2 (x y : V)
    : inner_swap (x ⊗ x) x (y ⊗ y) y
         · (inner_swap x x y y ⊗^{V}_{r} (x ⊗ y)
              · mon_lassociator _ _ _)
       = mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _
           · (inner_swap x (x ⊗ x) y (y ⊗ y)
                · (x ⊗ y) ⊗^{V}_{l} inner_swap x x y y).
  Proof.
    apply rearrange_hexagon.
  Qed.

  Lemma rearrange_hexagon' (x1 x2 y1 y2 z1 z2 : V)
    : inner_swap x1 x2 y1 y2 #⊗ identity (z1 ⊗ z2)
        · inner_swap (x1 ⊗ y1) (x2 ⊗ y2) z1 z2
        · mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _
      = mon_lassociator _ _ _
            · identity (x1 ⊗ x2) #⊗ inner_swap y1 y2 z1 z2
            · inner_swap x1 x2 (y1 ⊗ z1) (y2 ⊗ z2).
  Proof.
  Admitted.

  Lemma rearrange_hexagon'_3 (x y z : V)
    : inner_swap x x y y #⊗ identity (z ⊗ z)
        · inner_swap (x ⊗ y) (x ⊗ y) z z
        · mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _
      = mon_lassociator _ _ _
            · identity (x ⊗_ x) #⊗ inner_swap y y z z
            · inner_swap x x (y ⊗ z) (y ⊗ z).
  Proof.
    apply rearrange_hexagon'.
  Qed.

  Lemma rearrange_hexagoninv' (x y z : V)
    : identity (x ⊗ x) #⊗ inner_swap y y z z
  · inner_swap x x (y ⊗ z) (y ⊗ z)
  · mon_rassociator _ _ _ #⊗ mon_rassociator _ _ _ =
  mon_rassociator _ _ _
  · inner_swap x x y y #⊗ identity (z ⊗ z)
  · inner_swap (x ⊗ y) (x ⊗ y) z z.
  Proof.
    set (t := rearrange_hexagon' x x y y z z).
    apply pathsinv0.
    use (z_iso_inv_on_left _ _ _ _ (mon_lassociator _ _ _ #⊗ mon_lassociator _ _ _,,
                                      mon_rassociator _ _ _ #⊗ mon_rassociator _ _ _ ,, _)).
    {
      apply (pr2 (is_z_iso_bifunctor_z_iso V
                    (mon_lassociator _ _ _) (mon_lassociator _ _ _)
                    (_ ,, monoidal_associatorisolaw V _ _ _)
                    (_ ,, monoidal_associatorisolaw V _ _ _))).
    }
    cbn.
    etrans.
    2: {
      rewrite ! assoc'.
      apply maponpaths.
      rewrite assoc.
      apply (! t).
    }
    etrans.
    2: {
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      apply pathsinv0.
      apply mon_rassociator_lassociator.
    }
    now rewrite id_left.
  Qed.

  Lemma rearrange_commute_with_swap (x1 x2 y1 y2 : V)
    : inner_swap x1 x2 y1 y2 · sym_mon_braiding _ x1 y1 #⊗ sym_mon_braiding _ x2 y2
      = sym_mon_braiding _ (x1 ⊗ x2) (y1 ⊗ y2) · inner_swap y1 y2 x1 x2.
  Proof.
    unfold inner_swap.
    rewrite ! assoc.

    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply pathsinv0, sym_mon_tensor_lassociator0.
    }
    unfold monoidal_cat_tensor_mor, mon_lassociator, mon_rassociator.
    cbn.

    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite (when_bifunctor_becomes_leftwhiskering V).
      etrans.
      2: apply (bifunctor_leftcomp V y1).
      apply maponpaths.
      rewrite ! assoc.
      apply pathsinv0.
      apply sym_mon_hexagon_rassociator0.
    }

    etrans.
    2: {
      rewrite ! assoc'.
      do 2 apply maponpaths.
      refine (! sym_mon_hexagon_lassociator1 _ _ _ _ _ @ _).
      now rewrite ! assoc'.
    }

    unfold functoronmorphisms1.
    rewrite ! assoc.
    apply maponpaths_2.
    unfold monoidal_cat_tensor_pt.
    cbn.

    rewrite ! assoc'.
    apply pathsinv0.
    use (z_iso_inv_on_right _ _ _ (mon_lassociator _ _ _ ,, mon_rassociator _ _ _ ,, _)).
    { apply monoidal_associatorisolaw. }
    cbn.

    rewrite (bifunctor_leftcomp V).
    rewrite ! assoc.

    etrans.
    2: {
      do 3 apply maponpaths_2.
      apply pathsinv0.
      apply mon_lassociator_lassociator'.
    }
    rewrite (bifunctor_leftid V).
    rewrite id_right.

    apply pathsinv0.
    use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
    {
      use (is_z_iso_rightwhiskering_z_iso V).
      refine (_ ,, _).
      apply (_ ,, monoidal_braiding_inverses V).
    }
    cbn.

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, monoidal_associatornatright.
    }

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- ! (bifunctor_rightcomp V).
      apply maponpaths.
      apply pathsinv0, sym_mon_hexagon_rassociator1.
    }

    rewrite ! (bifunctor_rightcomp V).
    rewrite ! assoc'.
    apply maponpaths.
    rewrite ! assoc.
    rewrite (bifunctor_leftcomp V).
    rewrite assoc.
    unfold sym_mon_braiding, mon_lassociator, monoidal_cat_tensor_pt.
    cbn.
    rewrite (monoidal_associatornatleftright V).
    rewrite ! assoc'.
    apply maponpaths.
    rewrite assoc.
    apply pathsinv0.
    use (z_iso_inv_on_left _ _ _ _ (mon_lassociator _ _ _ ,, mon_rassociator _ _ _ ,, _)).
    {
      apply monoidal_associatorisolaw.
    }
    cbn.
    rewrite assoc'.
    etrans.
    2: {
      apply maponpaths.
      apply pathsinv0, mon_lassociator_lassociator.
    }
    unfold monoidal_cat_tensor_mor.
    unfold mon_lassociator.
    unfold mon_rassociator.
    unfold monoidal_cat_tensor_pt.
    cbn.
    rewrite ! assoc.
    rewrite (when_bifunctor_becomes_rightwhiskering V).
    rewrite <- (bifunctor_rightcomp V).
    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0, (monoidal_associatorisolaw V).
    }
    rewrite (bifunctor_rightid V).
    rewrite id_left.
    now rewrite (when_bifunctor_becomes_leftwhiskering V).
  Qed.

End Rearranging.
