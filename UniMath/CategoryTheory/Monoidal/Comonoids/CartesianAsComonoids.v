(*
In this file, we show:
   if a symmetric monoidal category is cartesian, the forgetful functor from the category of commutative comonoids is an isomorphism of categories.

The converse of this statement remains to be done.
At this moment, one property remains to be proven. The condition is axiomatized in the context.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.CatIsoDisplayed.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Tensor.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Symmetric.


Import MonoidalNotations.
Import ComonoidNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section CartesianToCartesianAsComonoids.

  Context {M : monoidal_cat} (Ccart : is_cartesian M).
  Let V : sym_monoidal_cat := M,, cartesian_to_symmetric Ccart.

  Let diag (x : V) : V⟦x, x ⊗ x⟧
      := (BinProductArrow _ (is_cartesian_BinProduct Ccart x x) (identity x) (identity x)).

  Let aug (x : V) : V⟦x, monoidal_unit M⟧
      := (semi_cart_to_unit Ccart x).

  Lemma identity_of_lwhisker_with_unit (x : V)
    : monoidal_cat_tensor_mor (aug (monoidal_unit M)) (identity x)
       = identity (_ ⊗ x).
  Proof.
    refine (_ @ tensor_id_id _ _).
    apply maponpaths_2.
    apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Lemma identity_of_rwhisker_with_unit (x : V)
    : monoidal_cat_tensor_mor (identity x) (aug I_{M})
       = identity (x ⊗ I_{V}).
  Proof.
    refine (_ @ tensor_id_id _ _).
    apply maponpaths.
    apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Lemma cartesian_lunitor (x : V)
    : semi_cart_tensor_pr2 (pr1 Ccart) I_{ M} x = mon_lunitor x.
  Proof.
    refine (_ @ id_left _).
    unfold semi_cart_tensor_pr2.
    apply maponpaths_2.
    apply identity_of_lwhisker_with_unit.
  Qed.

  Lemma cartesian_runitor (x : V)
    : semi_cart_tensor_pr1 (pr1 Ccart) x I_{M} = mon_runitor x.
  Proof.
    refine (_ @ id_left _).
    unfold semi_cart_tensor_pr1.
    apply maponpaths_2.
    apply identity_of_rwhisker_with_unit.
  Qed.

  Lemma cartesian_linvunitor (x : V)
    : BinProductArrow V (is_cartesian_BinProduct Ccart I_{ M} x)
        (semi_cart_to_unit Ccart x)
        (identity x)
      = mon_linvunitor x.
  Proof.
    apply pathsinv0.
    use BinProductArrowUnique.
    - apply (semi_cart_to_unit_eq Ccart).
    - etrans. {
        apply maponpaths.
        apply cartesian_lunitor.
      }
      apply monoidal_leftunitorisolaw.
  Qed.

  Lemma cartesian_linvunitor' (x : V)
    : BinProductArrow V (is_cartesian_BinProduct Ccart x x) (identity x) (identity x)
         · semi_cart_to_unit Ccart x ⊗^{M}_{r} x
       = mon_linvunitor x.
  Proof.
    etrans. {
      refine (_ @ postcompWithBinProductArrow _
                (is_cartesian_BinProduct Ccart _ _)
                (is_cartesian_BinProduct Ccart _ _)
                (semi_cart_to_unit Ccart x)
                (identity x)
                (identity x) (identity x)).
      apply maponpaths.
      rewrite <- (when_bifunctor_becomes_rightwhiskering M).
      exact (cartesian_tensor_mor Ccart (semi_cart_to_unit Ccart x) (identity x)).
    }

    do 2 rewrite id_left.
    exact (cartesian_linvunitor x).
  Qed.

  Lemma cartesian_rinvunitor (x : V)
    : BinProductArrow V (is_cartesian_BinProduct Ccart x I_{ M})
        (identity x)
        (semi_cart_to_unit Ccart x)
      = mon_rinvunitor x.
  Proof.
    apply pathsinv0.
    use BinProductArrowUnique.
    - etrans. {
        apply maponpaths.
        apply cartesian_runitor.
      }
      apply monoidal_rightunitorisolaw.
    - apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Lemma cartesian_rinvunitor' (x : V)
    : diag x · x ⊗^{ M}_{l} aug x = mon_rinvunitor x.
  Proof.
    etrans. {
      refine (_ @ postcompWithBinProductArrow _
                (is_cartesian_BinProduct Ccart _ _)
                (is_cartesian_BinProduct Ccart _ _)
                (identity x)
                (semi_cart_to_unit Ccart x)
                (identity x) (identity x)).
      apply maponpaths.
      rewrite <- (when_bifunctor_becomes_leftwhiskering M).
      exact (cartesian_tensor_mor Ccart (identity x) (semi_cart_to_unit Ccart x)).
    }

    do 2 rewrite id_left.
    exact (cartesian_rinvunitor x).
  Qed.

  Lemma cartesian_associator (x y z : V)
    : mon_lassociator x y z
      = BinProductArrow V
          (is_cartesian_BinProduct Ccart _ _)
          (semi_cart_tensor_pr1 Ccart _ _ · semi_cart_tensor_pr1 Ccart _ _)
          (semi_cart_tensor_pr2 Ccart _ _ ⊗^{M}_{r} z).
  Proof.
    use (BinProductArrowUnique _ _ _ (is_cartesian_BinProduct Ccart _ _)).
    - apply (mon_lassociator_pr1 Ccart).
    - refine (mon_lassociator_pr2 Ccart x y z @ _).
      unfold monoidal_cat_tensor_mor.
      now apply (when_bifunctor_becomes_rightwhiskering M).
  Qed.

  Lemma BinProductArrow_as_diag (x y z : V) (f : V⟦x,y⟧) (g : V⟦x,z⟧)
    : diag x · f #⊗ g
      = BinProductArrow V (is_cartesian_BinProduct Ccart y z) f g.
  Proof.
    etrans.
    {
      apply maponpaths.
      apply (cartesian_tensor_mor Ccart).
    }
    etrans.
    {
      apply (postcompWithBinProductArrow _
               (is_cartesian_BinProduct Ccart y z) (is_cartesian_BinProduct Ccart x x)).
    }
    now do 2 rewrite id_left.
  Qed.

  Lemma diag_is_symmetric (x : V)
    : diag x · cartesian_to_braiding_data Ccart x x = diag x.
  Proof.
    apply (BinProductArrowsEq _ _ _ (is_cartesian_BinProduct Ccart x x)).
    - rewrite assoc'.
      etrans.
      { apply maponpaths.
        apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct Ccart x x)). }
      etrans.
      { apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct Ccart x x)). }
      apply pathsinv0, (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct Ccart x x)).
    - rewrite assoc'.
      etrans.
      { apply maponpaths.
        apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct Ccart x x)). }
      etrans.
      { apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct Ccart x x)). }
      apply pathsinv0, (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct Ccart x x)).
  Qed.

  Lemma diagonal_commutes_with_assoc (x : V)
    : diag x · diag x ⊗^{M}_{r} x · mon_lassociator x x x = diag x · x ⊗^{M}_{l} diag x.
  Proof.
    rewrite cartesian_associator.
    etrans.
    { apply cancel_postcomposition.
      etrans.
      { apply maponpaths.
        apply pathsinv0, (when_bifunctor_becomes_rightwhiskering M). }
      apply BinProductArrow_as_diag.
    }
    etrans.
    2: { etrans.
         2: { apply maponpaths.
              apply (when_bifunctor_becomes_leftwhiskering M). }
         apply pathsinv0, BinProductArrow_as_diag.
    }
    etrans.
    { apply (precompWithBinProductArrow _ (is_cartesian_BinProduct Ccart x (x ⊗ x))). }
    apply maponpaths_12.
    - rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct Ccart _ _)). }
      apply (BinProductPr1Commutes _ _ _ (is_cartesian_BinProduct Ccart x x)).
    - etrans.
      { apply maponpaths.
        etrans.
        { apply pathsinv0, (when_bifunctor_becomes_rightwhiskering M). }
        apply (cartesian_tensor_mor Ccart). }
      etrans.
      { apply (postcompWithBinProductArrow _
                 (is_cartesian_BinProduct Ccart x x)
                 (is_cartesian_BinProduct Ccart (is_cartesian_BinProduct Ccart x x) x)). }
      apply maponpaths_12.
      + apply (BinProductPr2Commutes _ _ _ (is_cartesian_BinProduct Ccart _ _)).
      + apply id_left.
  Qed.

  Lemma cartesian_monoidal_has_enough_comonoids_laws
    : ∏ x : V, comonoid_laws M (x ,, diag x ,, aug x).
  Proof.
    repeat split.
    - unfold comonoid_laws_unit_left.
      cbn.
      refine (_ @ mon_linvunitor_lunitor x).
      apply maponpaths_2.
      exact (cartesian_linvunitor' x).
    - unfold comonoid_laws_unit_right.
      cbn.
      refine (_ @ mon_rinvunitor_runitor x).
      apply maponpaths_2.
      exact (cartesian_rinvunitor' x).
    - unfold comonoid_laws_assoc.
      cbn.
      apply diagonal_commutes_with_assoc.
  Qed.

  Definition cartesian_monoidal_has_enough_comonoids
    : ∏ x : V, comonoid M.
  Proof.
    intro x.
    refine (x ,, _ ,, _).
    exact (cartesian_monoidal_has_enough_comonoids_laws x).
  Defined.

  (* Definition cartesian_monoidal_has_enough_commcomonoids
    : ∏ x : V, is_commutative V (cartesian_monoidal_has_enough_comonoids x).
  Proof.
    exact (λ x, diag_is_symmetric x).
  Qed. *)

  Definition cartesian_monoidal_has_enough_comm_comonoids
    : ∏ x : V, disp_cat_of_commutative_comonoids V x.
  Proof.
    intro x.
    exists (pr2 (cartesian_monoidal_has_enough_comonoids x)).
    apply diag_is_symmetric.
  Defined.

  Lemma cartesian_monoidal_has_unique_comonoids
    : ∏ x : V,  iscontr (disp_cat_of_comonoids V x).
  Proof.
    intro x.
    exists (comonoid_to_struct V (cartesian_monoidal_has_enough_comonoids x)).
    intro m.
    use subtypePath.
    { intro ; apply isaprop_comonoid_laws. }

    use total2_paths_f.
    - use (BinProductArrowUnique _ _ _ (is_cartesian_BinProduct Ccart x x)).
      + refine (_ @ comonoid_to_law_unit_right _ (_,,m)).
        cbn.
        unfold semi_cart_tensor_pr1.
        rewrite ! assoc.
        apply maponpaths_2.
        apply maponpaths.
        unfold monoidal_cat_tensor_mor.
        rewrite (when_bifunctor_becomes_leftwhiskering M).
        apply maponpaths.
        apply (semi_cart_to_unit_eq Ccart).
      + refine (_ @ comonoid_to_law_unit_left _ (_,,m)).
        cbn.
        unfold semi_cart_tensor_pr2.
        rewrite ! assoc.
        apply maponpaths_2.
        apply maponpaths.
        unfold monoidal_cat_tensor_mor.
        rewrite (when_bifunctor_becomes_rightwhiskering M).
        apply maponpaths.
        apply (semi_cart_to_unit_eq Ccart).
    - apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Lemma cartesian_monoidal_has_unique_comm_comonoids
    : ∏ x : V,  iscontr (disp_cat_of_commutative_comonoids V x).
  Proof.
    intro x.
    apply iscontraprop1.
    - apply isaproptotal2.
      + intro ; apply homset_property.
      + intro ; intros.
        apply proofirrelevance.
        apply isapropifcontr.
        apply cartesian_monoidal_has_unique_comonoids.
    - apply cartesian_monoidal_has_enough_comm_comonoids.
  Defined.

  Lemma cartesian_monoidal_has_enough_comonoids_mor_comult
    {x y : V} (f : V⟦x, y⟧)
    : is_comonoid_mor_comult V
        (cartesian_monoidal_has_enough_comonoids x)
        (cartesian_monoidal_has_enough_comonoids y)
        f.
  Proof.
    etrans.
    2: {
      apply pathsinv0.
      apply (precompWithBinProductArrow _ (is_cartesian_BinProduct Ccart y y)).
    }
    rewrite id_right.
    etrans. {
      apply maponpaths.
      apply (cartesian_tensor_mor Ccart).
    }

    etrans. {
      apply (postcompWithBinProductArrow _
               (is_cartesian_BinProduct Ccart _ _)
               (is_cartesian_BinProduct Ccart _ _)
               f f
            ).
    }
    now rewrite id_left.
  Qed.

  Definition cartesian_monoidal_has_enough_comonoids_mor
    {x y : V} (f : V⟦x, y⟧)
    : comonoid_mor_struct V
        (cartesian_monoidal_has_enough_comonoids x)
        (cartesian_monoidal_has_enough_comonoids y)
        f.
  Proof.
    use make_is_comonoid_mor.
    - exact (cartesian_monoidal_has_enough_comonoids_mor_comult f).
    - apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Definition cartesian_monoidal_has_enough_comonoids_mor'
    {x y : V} (f : V⟦x, y⟧)
    : diag x · f #⊗ f
      = f · diag y × aug x · identity (monoidal_unit V) = f · aug y.
  Proof.
    split.
    - exact (cartesian_monoidal_has_enough_comonoids_mor_comult f).
    - apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Lemma sigma_with_unit (A : UU)
    : (∑ _ : A, unit) ≃ A.
  Proof.
    use weq_iso.
    - exact pr1.
    - exact (λ x , x ,, tt).
    - intro.
      use subtypePath.
      { intro ; apply isapropunit. }
      apply idpath.
    - intro ; apply idpath.
  Defined.

  Definition cartesian_mon_is_comm_comonoids
    : is_catiso (pr1_category (disp_cat_of_commutative_comonoids V)).
  Proof.
    apply forgetful_is_iso_univ.
    - apply disp_cat_of_commutative_comonoids_is_univalent.
    - apply cartesian_monoidal_has_enough_comm_comonoids.
    - intro ; intros.
      use (iscontrweqb' _ (sigma_with_unit _)).
      use (iscontrweqb' _ (sigma_with_unit _)).
      apply iscontraprop1.
      { apply isapropdirprod ; apply homset_property. }
      split.
      + refine (_ @ cartesian_monoidal_has_enough_comonoids_mor_comult f @ _).
        -- apply maponpaths_2.
           etrans. {
             do 3 apply maponpaths.
             exact (proofirrelevancecontr (cartesian_monoidal_has_unique_comm_comonoids c1) d1 (cartesian_monoidal_has_enough_comm_comonoids c1)).
           }
           apply idpath.
        -- apply maponpaths.
           etrans.
           2: {
             do 3 apply maponpaths.
             exact (! (proofirrelevancecontr (cartesian_monoidal_has_unique_comm_comonoids c2) d2 (cartesian_monoidal_has_enough_comm_comonoids c2))).
           }
           apply idpath.
      + apply (semi_cart_to_unit_eq Ccart).
  Qed.

End CartesianToCartesianAsComonoids.

(* Section CartesianFromComonoidsToCartesian.

  Context {C : category} {M : monoidal C} (S : symmetric M).

  Context (i_i : is_catiso (pr1_category
                              (commutative_comonoids_disp_cat_over_base S))).

  Let inv_i := inv_catiso (_ ,, i_i).
  Let F_i := functor_from_catiso _ _ (_ ,, i_i).

  Definition cartesian_mon_from_comm_comonoids
    : is_cartesian (C,,M).
  Proof.
    use symm_monoidal_is_cartesian_from_comonoid.
    - exact S.
    - intro ; apply (catiso_is_globally_contr i_i).
    - intro ; intros.
      (* apply catiso_is_locally_contr. *)
      admit.
    - admit.
    - intro ; intro.
      admit.
  Admitted.

End CartesianFromComonoidsToCartesian. *)
