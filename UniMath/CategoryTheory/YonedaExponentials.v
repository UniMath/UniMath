(**************************************************************************************************

  The Yoneda embedding preserves exponentials

  This file shows that the Yoneda embedding Y preserves exponentials. It does this by first
  establishing isomorphisms between Y(X^Y)(Z) and (Y(X)^Y(Y))(Z) for all Z, and then showing that
  these are equal to the morphisms given by `preserves_exponentials_map`. From this, we conclude
  that `preserves_exponentials_map` is an isomorphism.

  Contents
  1. The Yoneda embedding preserves exponentials [yoneda_preserves_exponentials]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.YonedaBinproducts.

(** The scopes must be in this order, because we use ∘ from weq_scope and not from cat *)
Local Open Scope cat.
Local Open Scope weq_scope.

Section YonedaPreservesExponentials.

  Context {C : category}.
  Context (BP : BinProducts C).
  Context (Exp : Exponentials BP).


  Definition yoneda_exponentials_iso
    (X Y Z : C)
    : z_iso
      ((yoneda C (exp (Exp X) Y) : _ ⟶ _) Z)
      ((exp (Exponentials_PreShv (yoneda C X)) (yoneda C Y) : _ ⟶ _) Z).
  Proof.
    refine (hset_equiv_weq_z_iso _ _ _).
    refine (yoneda_weq _ _ (exp (Exponentials_PreShv _) _) ∘ _).
    refine (adjunction_hom_weq (pr2 (Exponentials_PreShv _)) _ _ ∘ _).
    refine (invweq (z_iso_comp_right_weq (preserves_binproduct_to_z_iso _
      (yoneda_preserves_binproduct _ BP) _ (BinProducts_PreShv _ _)) _) ∘ _).
    refine (weq_from_fully_faithful (yoneda_fully_faithful _) _ _ ∘ _).
    refine (invweq (adjunction_hom_weq (pr2 (Exp X)) _ _) ∘ _).
    refine (invweq (weq_from_fully_faithful (yoneda_fully_faithful _) _ _) ∘ _).
    exact (invweq (yoneda_weq _ _ (yoneda _ _))).
  Defined.

  (** The pr1 is definitionally equal to nat_trans_data_from_nat_trans_funclass,
    but the latter gives an increase of about 5 seconds in yoneda_preserves_exponentials *)
  Lemma yoneda_exponentials_iso_is_preserves_exponentials
    (X Y Z : C)
    : z_iso_mor (yoneda_exponentials_iso X Y Z)
    = pr1 (preserves_exponentials_map _ _ (yoneda_preserves_binproduct _ BP) _ _) Z.
  Proof.
    apply funextsec.
    intro f.
    apply nat_trans_eq_alt.
    intro d.
    apply funextfun.
    intro x.
    cbn.
    do 2 (
      refine (!maponpaths (λ x, _ · BinProductArrow _ _ x _ · _) (id_right (BinProductPr1 _ _)) @ _);
      refine (!maponpaths (λ x, _ · BinProductArrow _ _ _ x · _) (id_right (BinProductPr2 _ _)) @ _);
      refine (maponpaths (λ x, x · _) (postcompWithBinProductArrow _ _ _ _ _ _ _) @ !_)
    ).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ x, x · _) (postcompWithBinProductArrow _ _ _ _ _ _ _) @ _).
    apply (maponpaths (λ x, x · _)).
    refine (
      maponpaths (λ x, BinProductArrow _ (BP X (pr1 (Exp X) Y)) x _) _ @
      maponpaths (λ x, BinProductArrow _ (BP X (pr1 (Exp X) Y)) _ x) _
    ).
    - apply id_right.
    - refine (maponpaths (λ x, x · _) (id_right _) @ _).
      refine (maponpaths (λ x, x · _) (id_right _) @ _).
      refine (maponpaths (λ x, _ · x) (id_left _) @ _).
      exact (!id_right _).
  Qed.

  Definition yoneda_preserves_exponentials
    : preserves_exponentials Exp (Exponentials_PreShv) (yoneda_preserves_binproduct _ BP).
  Proof.
    intros X Y.
    apply nat_trafo_z_iso_if_pointwise_z_iso.
    intro Z.
    use is_z_isomorphism_path.
    - exact (z_iso_mor (yoneda_exponentials_iso X Y Z)).
    - exact (yoneda_exponentials_iso_is_preserves_exponentials X Y Z).
    - apply z_iso_is_z_isomorphism.
  Defined.

End YonedaPreservesExponentials.
