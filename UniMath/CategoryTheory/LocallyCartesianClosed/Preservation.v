(*******************************************************************************************

 Functors between locally Cartesian closed categories

 We define structure preserving functors between locally Cartesian closed categories. We
 phrase this in terms of functors between displayed categories that preserve dependent
 products.

 Contents
 1. Structure preserving functors between LCCCs
 2. The identity is structure preserving
 3. The composition is structure preserving

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRightAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.

Local Open Scope cat.

(** * 1. Structure preserving functors between LCCCs *)
Definition preserves_locally_cartesian_closed
           {C₁ C₂ : category}
           {PB₁ : Pullbacks C₁}
           {PB₂ : Pullbacks C₂}
           {F : C₁ ⟶ C₂}
           (HF : preserves_pullback F)
           (H₁ : is_locally_cartesian_closed PB₁)
           (H₂ : is_locally_cartesian_closed PB₂)
  : UU
  := preserves_dependent_products
       (cartesian_disp_codomain_functor F HF)
       (cod_dependent_products H₁)
       (cod_dependent_products H₂).

Proposition isaprop_preserves_locally_cartesian_closed
            {C₁ C₂ : category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            {F : C₁ ⟶ C₂}
            (HF : preserves_pullback F)
            (H₁ : is_locally_cartesian_closed PB₁)
            (H₂ : is_locally_cartesian_closed PB₂)
  : isaprop (preserves_locally_cartesian_closed HF H₁ H₂).
Proof.
  apply isaprop_preserves_dependent_products.
Qed.

(** * 2. The identity is structure preserving *)
Proposition id_preserves_locally_cartesian_closed
            {C : category}
            {PB : Pullbacks C}
            (H : is_locally_cartesian_closed PB)
  : preserves_locally_cartesian_closed (identity_preserves_pullback C) H H.
Proof.
  unfold preserves_locally_cartesian_closed.
  refine (transportf
            (λ z, preserves_dependent_products z _ _)
            _
            (id_preserves_dependent_products (cod_dependent_products H))).
  use subtypePath.
  {
    intro.
    apply isaprop_is_cartesian_disp_functor.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_disp_functor_axioms.
  }
  use total2_paths_f.
  - apply idpath.
  - cbn.
    repeat (use funextsec ; intro).
    use eq_cod_mor ; cbn.
    apply idpath.
Qed.

(** * 3. The composition is structure preserving *)
Proposition comp_preserves_locally_cartesian_closed
            {C₁ C₂ C₃ : category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            {PB₃ : Pullbacks C₃}
            {H₁ : is_locally_cartesian_closed PB₁}
            {H₂ : is_locally_cartesian_closed PB₂}
            {H₃ : is_locally_cartesian_closed PB₃}
            {F : C₁ ⟶ C₂}
            {HF : preserves_pullback F}
            (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
            {G : C₂ ⟶ C₃}
            {HG : preserves_pullback G}
            (HGG : preserves_locally_cartesian_closed HG H₂ H₃)
  : preserves_locally_cartesian_closed
      (composition_preserves_pullback HF HG)
      H₁
      H₃.
Proof.
  unfold preserves_locally_cartesian_closed.
  refine (transportf
            (λ z, preserves_dependent_products z _ _)
            _
            (comp_preserves_dependent_products HFF HGG)).
  use subtypePath.
  {
    intro.
    apply isaprop_is_cartesian_disp_functor.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_disp_functor_axioms.
  }
  use total2_paths_f.
  - apply idpath.
  - cbn.
    repeat (use funextsec ; intro).
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    cbn.
    apply idpath.
Qed.
