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

(* Require Import UniMath.CategoryTheory.Monoidal.Comonoids.CommComonoidsCartesian.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.MonoidalCartesianBuilder. *)


Local Open Scope cat.
Import MonoidalNotations.
Import ComonoidNotations.

Section CartesianToCartesianAsComonoids.

  Context {C : category} {M : monoidal C} (Ccart : is_cartesian (C,,M)).
  Let V : sym_monoidal_cat := (C,,M),, cartesian_to_symmetric Ccart.

  Let diag (x : C) := (BinProductArrow _ (is_cartesian_BinProduct Ccart x x) (identity x) (identity x)).

  Let aug (x : C) := (semi_cart_to_unit Ccart x).

  Lemma aug_of_unit : aug I_{M} = identity I_{M}.
  Proof.
    apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Definition cartesian_monoidal_has_enough_comonoids_data
    : ∏ x : C, comonoid_data M x.
  Proof.
    intro x.
    exists (diag x).
    exact (aug x).
  Defined.

  Lemma identity_of_lwhisker_with_unit (x : C)
    :  monoidal_cat_tensor_mor (aug I_{ M}) (identity x)
       = identity (I_{M} ⊗_{M} x).
  Proof.
    etrans.
    2: {
      apply (bifunctor_distributes_over_id (F := M)) ; apply M.
    }
    apply maponpaths_2.
    apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Lemma identity_of_rwhisker_with_unit (x : C)
    :  monoidal_cat_tensor_mor (V := C,,M) (identity x) (aug I_{ M})
       = identity (x ⊗_{M} I_{M}).
  Proof.
    etrans.
    2: {
      apply (bifunctor_distributes_over_id (F := M)) ; apply M.
    }
    apply maponpaths.
    apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Lemma cartesian_lunitor (x : C)
    : semi_cart_tensor_pr2 (pr1 Ccart) I_{ M} x = lu^{M}_{x}.
  Proof.
    refine (_ @ id_left _).
    unfold semi_cart_tensor_pr2.
    apply maponpaths_2.
    apply identity_of_lwhisker_with_unit.
  Qed.

  Lemma cartesian_runitor (x : C)
    : semi_cart_tensor_pr1 (pr1 Ccart) x I_{M} = ru^{M}_{x}.
  Proof.
    refine (_ @ id_left _).
    unfold semi_cart_tensor_pr1.
    apply maponpaths_2.
    apply identity_of_rwhisker_with_unit.
  Qed.

  Lemma cartesian_linvunitor (x : C)
    : BinProductArrow C (is_cartesian_BinProduct Ccart I_{ M} x)
        (semi_cart_to_unit Ccart x)
        (identity x)
      = luinv^{M}_{x}.
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

  Lemma cartesian_linvunitor' (x : C)
    :  BinProductArrow C (is_cartesian_BinProduct Ccart x x) (identity x) (identity x)
         · semi_cart_to_unit Ccart x ⊗^{ M}_{r} x
       = luinv^{M}_{x}.
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

  Lemma cartesian_rinvunitor (x : C)
    : BinProductArrow C (is_cartesian_BinProduct Ccart x I_{ M})
        (identity x)
        (semi_cart_to_unit Ccart x)
      = ruinv^{M}_{x}.
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

  Lemma cartesian_rinvunitor' (x : C)
    : diag x · x ⊗^{ M}_{l} aug x = ruinv^{M}_{x}.
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

  Lemma cartesian_associator (x y z : C)
    : α^{ M }_{ x, y, z}
      = BinProductArrow C
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

  Lemma BinProductArrow_as_diag (x y z : C) (f : C⟦x,y⟧) (g : C⟦x,z⟧)
    : diag x · f ⊗^{M} g
      = BinProductArrow C (is_cartesian_BinProduct Ccart y z) f g.
  Proof.
    use (BinProductArrowUnique _ _ _ (is_cartesian_BinProduct Ccart _ _)).
    - rewrite assoc'.
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        apply (cartesian_tensor_mor Ccart f g).
      }
      etrans. {
        apply maponpaths.
        apply (BinProductOfArrowsPr1 _ (is_cartesian_BinProduct Ccart _ _)).
      }
      rewrite assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      unfold diag.
      refine ((BinProductPr1Commutes) _ _ _ (is_cartesian_BinProduct Ccart _ _) _ _ _).
    - rewrite assoc'.
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        apply (cartesian_tensor_mor Ccart f g).
      }
      etrans. {
        apply maponpaths.
        apply (BinProductOfArrowsPr2 _ (is_cartesian_BinProduct Ccart _ _)).
      }
      rewrite assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      unfold diag.
      refine ((BinProductPr2Commutes) _ _ _ (is_cartesian_BinProduct Ccart _ _) _ _ _).
  Qed.

  Lemma diag_is_symmetric (x : C)
    :  diag x · cartesian_to_braiding_data Ccart x x = diag x.
  Proof.
    etrans. {
      apply (precompWithBinProductArrow _ (is_cartesian_BinProduct Ccart _ _)).
    }

    etrans. {
      apply maponpaths.
      refine (_ @ idpath (identity x)).
      refine (assoc _ _ _ @ _).
      refine (_ @ mon_rinvunitor_runitor (V := C,,M) x).
      apply maponpaths_2.
      refine (_ @ cartesian_rinvunitor' x).
      apply maponpaths.
      apply (when_bifunctor_becomes_leftwhiskering M).
    }

    apply maponpaths_2.
    unfold semi_cart_tensor_pr2.
    refine (assoc _ _ _ @ _).
    refine (_ @ mon_linvunitor_lunitor (V := C,,M) x).
    apply maponpaths_2.
    refine (_ @ cartesian_linvunitor' x).
    apply maponpaths.
    apply (when_bifunctor_becomes_rightwhiskering M).
  Qed.

  (* Lemma diagonal_commutes_with_assoc (x : C)
    : diag x ⊗^{ M}_{r} x · α^{ M }_{ x, x, x}
      = x ⊗^{ M}_{l} diag x.
  Proof.
` Admitted. *)
  Context (diagonal_commutes_with_assoc
            : ∏ (x : C), diag x · diag x ⊗^{ M}_{r} x · α^{ M }_{ x, x, x}
                         = diag x · x ⊗^{ M}_{l} diag x).

  Lemma cartesian_monoidal_has_enough_comonoids_laws
    : ∏ x : C, comonoid_laws M (cartesian_monoidal_has_enough_comonoids_data x).
  Proof.
    repeat split.
    - unfold comonoid_laws_unit_left.
      cbn.
      refine (_ @ mon_linvunitor_lunitor (V := C,,M) x).
      apply maponpaths_2.
      exact (cartesian_linvunitor' x).
    - unfold comonoid_laws_unit_right.
      cbn.
      refine (_ @ mon_rinvunitor_runitor (V := C,,M) x).
      apply maponpaths_2.
      exact (cartesian_rinvunitor' x).
    - unfold comonoid_laws_assoc.
      cbn.
      apply diagonal_commutes_with_assoc.
  Qed.

  Definition cartesian_monoidal_has_enough_comonoids
    : ∏ x : C, comonoid M x.
  Proof.
    intro x.
    exists (cartesian_monoidal_has_enough_comonoids_data x).
    exact (cartesian_monoidal_has_enough_comonoids_laws x).
  Defined.

  Definition cartesian_monoidal_has_enough_comm_comonoids
    : ∏ x : C, is_commutative
                 (cartesian_to_symmetric Ccart)
                 (cartesian_monoidal_has_enough_comonoids x).
  Proof.
    exact (λ x, diag_is_symmetric x).
  Qed.

  Lemma cartesian_monoidal_has_unique_comonoids
    : ∏ x : C, iscontr (comonoid M x).
  Proof.
    intro x.
    exists (cartesian_monoidal_has_enough_comonoids x).
    intro m.
    use subtypePath.
    { intro ; apply isaprop_comonoid_laws. }

    use total2_paths_f.
    - use (BinProductArrowUnique _ _ _ (is_cartesian_BinProduct Ccart x x)).
      + refine (_ @ pr122 m).
        cbn.
        unfold semi_cart_tensor_pr1.
        rewrite ! assoc.
        apply maponpaths_2.
        apply maponpaths.
        unfold monoidal_cat_tensor_mor.
        rewrite (when_bifunctor_becomes_leftwhiskering M).
        apply maponpaths.
        apply (semi_cart_to_unit_eq Ccart).
      + refine (_ @ pr12 m).
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

  Lemma cartesian_monoidal_has_enough_comonoids_mor_mult
    {x y : C} (f : C⟦x, y⟧)
    : is_comonoid_mor_mult M
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

  Lemma cartesian_monoidal_has_enough_comonoids_mor_unit
    {x y : C} (f : C⟦x, y⟧)
    : is_comonoid_mor_unit M
        (cartesian_monoidal_has_enough_comonoids x)
        (cartesian_monoidal_has_enough_comonoids y)
        f.
  Proof.
    apply (semi_cart_to_unit_eq Ccart).
  Qed.

  Definition cartesian_monoidal_has_enough_comonoids_mor
    {x y : C} (f : C⟦x, y⟧)
    : is_comonoid_mor M
        (cartesian_monoidal_has_enough_comonoids x)
        (cartesian_monoidal_has_enough_comonoids y)
        f.
  Proof.
    exists (cartesian_monoidal_has_enough_comonoids_mor_mult f).
    exact (cartesian_monoidal_has_enough_comonoids_mor_unit f).
  Qed.

  Definition cartesian_monoidal_has_enough_comonoids_mor'
    {x y : C} (f : C⟦x, y⟧)
    : diag x · monoidal_cat_tensor_mor (V := V) f f = f · diag y × aug x · identity I_{ M} = f · aug y.
  Proof.
    split.
    - exact (cartesian_monoidal_has_enough_comonoids_mor_mult f).
    - refine (_ @ ! cartesian_monoidal_has_enough_comonoids_mor_unit f).
      apply id_right.
  Qed.

  Definition cartesian_mon_is_comm_comonoids
    : is_catiso (pr1_category
                   (commutative_comonoids_disp_cat V)).
  Proof.
    use forgetful_is_iso.
    - intro c.
      use unique_exists.
      + apply cartesian_monoidal_has_enough_comonoids.
      + apply cartesian_monoidal_has_enough_comm_comonoids.
      + intro ; apply homset_property.
      + intro ; intro.
        use proofirrelevance.
        apply isapropifcontr.
        apply (cartesian_monoidal_has_unique_comonoids c).
    - intro ; intros.
      use unique_exists.
      + refine (_ ,, tt).
        apply cartesian_monoidal_has_enough_comonoids_mor'.
      + exact tt.
      + exact (λ _, isapropunit).
      + intro ; intro.
        use proofirrelevance.
        simpl.
        use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
        apply (isaprop_total2 (_ ,, homset_property _ _ _ _ _) (λ _ , _ ,, homset_property _ _ _ _ _)).
  Defined.

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
