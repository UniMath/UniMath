Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
(* Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions. *)

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
(* Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.MonoidalSections.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub. *)
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.

Import MonoidalNotations.

Section Rearranging.

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

  Definition rearrange_prod (x y z w : C)
    : C ⟦(x ⊗_{ M} y) ⊗_{ M} (z ⊗_{ M} w), (x ⊗_{ M} z) ⊗_{ M} (y ⊗_{ M} w)⟧.
  Proof.
    refine (α _ _ _ · _).
    refine (_ · αinv _ _ _).
    refine (x ⊗l _).
    refine (αinv _ _ _ · _).
    refine (_ · α _ _ _).
    exact (pr1 S y z ⊗r w).
  Defined.

  Lemma TO_BE_MOVED (y z w : C)
    : αinv y z w · (pr1 S y z ⊗^{ M}_{r} w · α z y w)
      = pr1 S _ _ · α _ _ _ · _ ⊗l pr1 S _ _.
  Proof.
    rewrite assoc.
    set (p := pr2 (pr222 S) y w z).
    set (p' := pr1 (pr222 S) y w z).

    apply pathsinv0.
    use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
    {
      use (is_z_iso_leftwhiskering_z_iso M).
      apply (_ ,, pr122 S _ _).
    }
    cbn.
    rewrite ! assoc'.
    etrans.
    2: {
      apply maponpaths.
      rewrite assoc.
      apply (pr1 (pr222 S) _ _ _).
    }
    rewrite ! assoc.
    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply pathsinv0, (monoidal_associatorisolaw M).
    }
    now rewrite id_left.
  Qed.

  Lemma precompose_rearrange_prod
    {x y z w : C}
    {x' y' z' w' : C}
    (fx : C⟦x,x'⟧)
    (fy : C⟦y,y'⟧)
    (fz : C⟦z,z'⟧)
    (fw : C⟦w,w'⟧)
    : rearrange_prod x y z w · ((fx ⊗⊗ fz) ⊗⊗ (fy ⊗⊗ fw))
      = ((fx ⊗⊗ fy) ⊗⊗ (fz ⊗⊗ fw)) · rearrange_prod _ _ _ _.
  Proof.
    unfold rearrange_prod.

    etrans. {
      rewrite ! assoc'.
      do 2 apply maponpaths.
      apply pathsinv0.
      exact (monoidal_associatorinv_nat2 M fx fz (fy ⊗⊗ fw)).
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

    rewrite (TO_BE_MOVED y z w).

    rewrite <- ! (when_bifunctor_becomes_leftwhiskering M).
    rewrite <- ! (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite id_left, id_right.
    apply maponpaths.

    rewrite (TO_BE_MOVED y' z' w').

    rewrite ! assoc.
    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply pathsinv0, (tensor_sym_mon_braiding ((C,,M),,S)).
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
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).

    rewrite id_left.
    etrans. {
      apply maponpaths.
      apply pathsinv0, (tensor_sym_mon_braiding ((C,,M),,S)).
    }
    cbn.
    rewrite <- (when_bifunctor_becomes_leftwhiskering M).
    rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    now rewrite id_right.
  Qed.

  Lemma rearrange_along_unit (x y : C)
    : rearrange_prod x I_{M} I_{M} y = identity _.
  Proof.
    unfold rearrange_prod.
    set (pf := sym_mon_braiding_id ((C,,M),,S)).
    cbn in pf.

    rewrite pf.
    rewrite (bifunctor_rightid M).
    rewrite id_left.
    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      exact (pr2 (monoidal_associatorisolaw M I I y)).
    }
    rewrite (bifunctor_leftid M).
    rewrite id_left.
    exact (pr1 (monoidal_associatorisolaw M _ _ _)).
  Qed.

  Lemma rearrange_prod_inv
    (x y z w : C)
    : rearrange_prod x y z w · rearrange_prod x z y w = identity _.
  Proof.
    unfold rearrange_prod.
    apply pathsinv0.
    rewrite ! assoc'.
    use (z_iso_inv_to_left _ _ _ (_ ,, _)).
    {
      apply (_ ,, monoidal_associatorisolaw M _ _ _).
    }
    cbn.
    rewrite ! assoc.
    use (z_iso_inv_on_left _ _ _ _ (α _ _ _ ,, αinv _ _ _ ,, _)).
    {
      apply (_ ,, monoidal_associatorisolaw M _ _ _).
    }
    cbn.
    rewrite id_right.
    etrans.
    2: {
      apply pathsinv0.
      apply (monoidal_associatorisolaw M).
    }
    cbn.

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply (monoidal_associatorisolaw M).
    }
    rewrite id_right.
    rewrite <- (bifunctor_leftcomp M).
    etrans. {
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      apply (monoidal_associatorisolaw M).
    }
    rewrite id_left.
    etrans. {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- (bifunctor_rightcomp M).
      apply maponpaths.
      apply (monoidal_braiding_inverses S).
    }
    rewrite (bifunctor_rightid M).
    rewrite id_right.
    etrans. {
      apply maponpaths.
      apply (monoidal_associatorisolaw M).
    }
    apply (bifunctor_leftid M).
  Qed.

  Lemma rearrange_prod_is_z_isomorphism
    (x y z w : C)
    : is_z_isomorphism (rearrange_prod x y z w).
  Proof.
    use make_is_z_isomorphism.
    - apply rearrange_prod.
    - split ; apply rearrange_prod_inv.
  Defined.

  Lemma mon_lunitor_triangle_transposed (x : C)
    : lu^{ M }_{ I ⊗_{ M} x}
      = αinv I_{ M} I_{ M} x · lu I_{ M} ⊗^{ M}_{r} x.
  Proof.
    rewrite <- (when_bifunctor_becomes_rightwhiskering M).
    etrans.
    2: {
      apply maponpaths, (mon_lunitor_triangle (V := C,,M) I x).
    }
    rewrite assoc.
    refine (! id_left _ @ _).
    apply maponpaths_2.
    apply pathsinv0.
    apply monoidal_associatorisolaw.
  Qed.

  Lemma TO_BE_MOVED'' (x : C)
    : I_{M} ⊗^{M}_{l} lu^{M}_{x} = lu^{M}_{I ⊗_{ M} x}.
  Proof.
    refine (_ @ ! mon_lunitor_triangle_transposed x).

    use (z_iso_inv_to_left _ _ _ (αinv I_{ M} I_{ M} x ,, α I_{ M} I_{ M} x ,, _)).
    {
      split ; apply monoidal_associatorisolaw.
    }

    refine (monoidal_triangleidentity M I x @ _).
    apply maponpaths.
    apply pathsinv0, unitors_coincide_on_unit.
  Qed.

  Lemma TO_BE_MOVED' (x y : C)
    : I ⊗^{ M}_{l} (lu x ⊗^{ M}_{r} y)
      = I_{ M} ⊗^{ M}_{l} α I_{ M} x y
          · (αinv I_{ M} I_{ M} (x ⊗_{ M} y) · lu I_{ M} ⊗^{ M}_{r} (x ⊗_{ M} y)).
  Proof.
    refine (Categories.right_whisker_with_lunitor' _ _ _ @ _).
    rewrite (bifunctor_leftcomp M).
    apply maponpaths.
    refine (_ @ mon_lunitor_triangle_transposed _).
    exact (TO_BE_MOVED'' (x ⊗ y)).
  Qed.

  Lemma precompose_rearrange_prod_with_lunitors_on_right (x y : C)
    : rearrange_prod I_{ M} x I_{ M} y · lu I_{ M} ⊗^{ M}_{r} (x ⊗_{ M} y) · lu (x ⊗ y)
      = (lu x ⊗⊗ lu y).
  Proof.
    unfold rearrange_prod.

    rewrite ! (bifunctor_leftcomp M).
    etrans. {
      apply maponpaths_2.
      rewrite ! assoc'.
      do 2 apply maponpaths.

      refine (_ @ idpath (I ⊗l (ru x ⊗r y))).

      apply pathsinv0.
      use (z_iso_inv_to_left _ _ _ (_ ,, _)).
      {
        use is_z_iso_leftwhiskering_z_iso.
        use (is_z_iso_rightwhiskering_z_iso M).
        apply (_ ,, monoidal_braiding_inverses S _ _).
      }
      cbn.
      rewrite <- (bifunctor_leftcomp M).
      etrans. {
        apply maponpaths.
        rewrite <- (bifunctor_rightcomp M).
        apply maponpaths.
        apply (sym_mon_braiding_runitor ((C,,M),,S)).
      }
      apply TO_BE_MOVED'.
    }

    rewrite <- (bifunctor_leftcomp M).
    etrans. {
      apply maponpaths_2.
      do 2 apply maponpaths.
      etrans. {
        apply maponpaths.
        refine (_ @ mon_triangle (V := C,,M) x y).
        apply pathsinv0, (when_bifunctor_becomes_rightwhiskering M).
      }
      rewrite assoc.
      apply maponpaths_2.
      apply (monoidal_associatorisolaw M).
    }
    rewrite id_left.
    unfold monoidal_cat_tensor_mor.
    cbn.
    etrans. {
      rewrite assoc'.
      apply maponpaths.
      refine (_ @ tensor_lunitor (V := C,,M) (identity x ⊗^{ M} lu y)).
      now rewrite <- (when_bifunctor_becomes_leftwhiskering M).
    }

    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      apply (mon_lunitor_triangle (V := C,,M)).
    }
    apply pathsinv0, (tensor_split' (V := C,,M)).
  Qed.

  Lemma precompose_rearrange_prod_with_lunitors_and_runitor (x y : C)
    : rearrange_prod x I_{ M} y I_{ M} · (x ⊗_{ M} y) ⊗^{ M}_{l} lu I_{ M} · ru^{ M }_{ x ⊗_{ M} y} = (ru x ⊗⊗ ru y).
  Proof.

    unfold rearrange_prod.

    rewrite ! (bifunctor_leftcomp M).
    etrans. {
      apply maponpaths_2.
      rewrite ! assoc'.
      do 2 apply maponpaths.
      refine (_ @ idpath (x ⊗l (lu y ⊗r I) · αinv _ _ _)).

      apply pathsinv0.
      use (z_iso_inv_to_left _ _ _ (_ ,, _)).
      {
        use is_z_iso_leftwhiskering_z_iso.
        use (is_z_iso_rightwhiskering_z_iso M).
        apply (_ ,, monoidal_braiding_inverses S _ _).
      }
      cbn.
      rewrite ! assoc.
      rewrite <- (bifunctor_leftcomp M).
      etrans. {
        apply maponpaths_2.
        rewrite <- (bifunctor_rightcomp M).
        apply maponpaths.
        apply maponpaths.
        apply (sym_mon_braiding_lunitor ((C,,M),,S)).
      }

      etrans. {
        apply maponpaths_2.
        apply maponpaths.
        refine (_ @ mon_triangle (V := C,,M) y I).
        apply pathsinv0.
        apply (when_bifunctor_becomes_rightwhiskering M).
      }
      cbn.
      rewrite (bifunctor_leftcomp M).
      rewrite ! assoc'.
      apply maponpaths.
      unfold monoidal_cat_tensor_mor.
      cbn.
      rewrite (when_bifunctor_becomes_leftwhiskering M).
      apply (monoidal_associatorinvnatleft M).
    }

    rewrite ! assoc'.
    etrans. {
      do 3 apply maponpaths.
      apply (mon_runitor_triangle (V := C,,M)).
    }
    unfold monoidal_cat_tensor_mor.
    cbn.
    unfold functoronmorphisms1.
    unfold monoidal_cat_tensor_pt.
    cbn.

    rewrite ! assoc.
    apply maponpaths_2.
    rewrite (bifunctor_rightid M).
    rewrite id_right.
    rewrite assoc'.
    rewrite <- (bifunctor_leftcomp M).

    etrans.
    2: {
      refine (! mon_triangle (V := C,,M) _ _ @ _).
      apply (when_bifunctor_becomes_rightwhiskering M).
    }

    apply maponpaths.
    rewrite <- (when_bifunctor_becomes_leftwhiskering M).
    apply maponpaths.

    use (z_iso_inv_on_right _ _ _ (α I y I ,, _ ,, _)).
    { apply monoidal_associatorisolaw. }
    cbn.
    rewrite <- (when_bifunctor_becomes_rightwhiskering M).
    apply (! mon_lunitor_triangle (V := C,,M) y I).
  Qed.

  Lemma composition_rearrange_and_braiding4
    (x1 x2 y1 y2 : C)
    : rearrange_prod x1 x2 y1 y2 · pr1 S x1 y1 ⊗^{ M} pr1 S x2 y2
      = pr1 S (x1 ⊗_{ M} x2) (y1 ⊗_{ M} y2) · rearrange_prod y1 y2 x1 x2.
  Proof.
    unfold rearrange_prod.

    assert (p1 :  αinv x1 y1 (x2 ⊗_{ M} y2) · pr1 S x1 y1 ⊗^{ M} pr1 S x2 y2
                  = x1 ⊗l (y1 ⊗l pr1 S x2 y2) · αinv _ _ _ · pr1 S x1 y1 ⊗r _).
    {
      admit.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      exact p1.
    }
    clear p1.
    rewrite ! assoc.

    Check pr1 (pr222 S) .

    assert (p2 : x1 ⊗^{ M}_{l} (y1 ⊗^{ M}_{l} pr1 S x2 y2) · αinv x1 y1 (y2 ⊗_{ M} x2)
                 = αinv _ _ _ · _ ⊗l pr1 S _ _).
    {
      admit.
    }

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      exact p2.
    }






  Admitted.

  Lemma composition_rearrange_and_braiding
    (x y : C)
    : rearrange_prod x x y y · pr1 S x y ⊗^{ M} pr1 S x y
       = pr1 S (x ⊗_{ M} x) (y ⊗_{ M} y) · rearrange_prod y y x x.
  Proof.
    exact (composition_rearrange_and_braiding4 x x y y).
  Qed.

  Lemma composition_rearrange_and_braiding'
    (x y : C)
    : pr1 S x x ⊗^{ M} pr1 S y y · rearrange_prod x x y y · pr1 S (x ⊗_{ M} y) (x ⊗_{ M} y)
      = rearrange_prod x x y y.
  Proof.

    unfold rearrange_prod.

    set (t := pr112 S).
    unfold braiding_law_naturality_left in t.
    set (s := pr222 S).
    unfold braiding_law_hexagon in s.
    unfold braiding_law_hexagon1 in s.
    unfold braiding_law_hexagon2 in s.

    (* etrans. {
      rewrite ! (bifunctor_leftcomp M).
      rewrite ! assoc'.
      do 4 apply maponpaths.

      rewrite assoc'.
      apply maponpaths.

    use (z_iso_inv_to_right _ _ _ _ (_ ,, _)).
    {
      refine (_ ,, _).
      apply (_ ,, monoidal_braiding_inverses S).
    }
    cbn.



    use (z_iso_inv_to_left _ _ _ (_ ,, _)).
    {
      refine (_ ,, _).
      apply (_ ,, monoidal_braiding_inverses S).
    }*)


  Admitted.

  Lemma rearrange_hexagon (x y : C)
     :  rearrange_prod (x ⊗_{ M} x) x (y ⊗_{ M} y) y
  · (rearrange_prod x x y y ⊗^{ M}_{r} (x ⊗_{ M} y)
       · α^{ M }_{ x ⊗_{ M} y, x ⊗_{ M} y, x ⊗_{ M} y})
        = α^{ M }_{ x, x, x} ⊗^{ M} α^{ M }_{ y, y, y}
                                        · (rearrange_prod x (x ⊗_{ M} x) y (y ⊗_{ M} y)
                                             · (x ⊗_{ M} y) ⊗^{ M}_{l} rearrange_prod x x y y).
  Proof.

  Admitted.

  Lemma rearrange_hexagon' (x y z : C)
    : rearrange_prod x x y y ⊗^{ M} identity (z ⊗_{ M} z)
        · rearrange_prod (x ⊗_{ M} y) (x ⊗_{ M} y) z z
        · α^{ M }_{ x, y, z} ⊗^{ M} α^{ M }_{ x, y, z}
      = α^{ M }_{ x ⊗_{ M} x, y ⊗_{ M} y, z ⊗_{ M} z}
            · identity (x ⊗_{ M} x) ⊗^{ M} rearrange_prod y y z z
            · rearrange_prod x x (y ⊗_{ M} z) (y ⊗_{ M} z).
  Proof.
  Admitted.

  Lemma rearrange_hexagoninv' (x y z : C)
    : identity (x ⊗_{ M} x) ⊗^{ M} rearrange_prod y y z z
  · rearrange_prod x x (y ⊗_{ M} z) (y ⊗_{ M} z)
  · αinv^{ M }_{ x, y, z} ⊗^{ M} αinv^{ M }_{ x, y, z} =
  αinv^{ M }_{ x ⊗_{ M} x, y ⊗_{ M} y, z ⊗_{ M} z}
  · rearrange_prod x x y y ⊗^{ M} identity (z ⊗_{ M} z)
  · rearrange_prod (x ⊗_{ M} y) (x ⊗_{ M} y) z z.
  Proof.
  Admitted.

End Rearranging.
