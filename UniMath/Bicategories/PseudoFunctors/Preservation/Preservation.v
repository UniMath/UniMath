(***********************************************************************

 Preservation of limits and colimits

 In this file, we look at the preservation of some limits and colimits.
 Our main focus is on final and initial objects and on products and
 coproducts.

 Contents:
 1. Basic definitions
 2. The identity pseudofunctor preserves (co)limits
 3. Preservation of the composition
 4. Preservation of chosen (co)limits

 ***********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Inserters.
Require Import UniMath.Bicategories.Limits.Equifiers.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.

Local Open Scope cat.

(**
 1. Basic definitions
 *)
Section Preserves.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂).

  Definition preserves_bifinal
    : UU
    := ∏ (x : B₁),
       is_bifinal x
       →
       is_bifinal (F x).

  Definition preserves_biinitial
    : UU
    := ∏ (x : B₁),
       is_biinitial x
       →
       is_biinitial (F x).

  Definition psfunctor_binprod_cone
             {x y : B₁}
             (p : binprod_cone x y)
    : binprod_cone (F x) (F y)
    := make_binprod_cone
         (F p)
         (#F (binprod_cone_pr1 p))
         (#F (binprod_cone_pr2 p)).

  Definition preserves_binprods
    : UU
    := ∏ (x y : B₁)
         (p : binprod_cone x y),
       has_binprod_ump p
       →
       has_binprod_ump (psfunctor_binprod_cone p).

  Definition psfunctor_bincoprod_cocone
             {x y : B₁}
             (p : bincoprod_cocone x y)
    : bincoprod_cocone (F x) (F y)
    := make_bincoprod_cocone
         (F p)
         (#F (bincoprod_cocone_inl p))
         (#F (bincoprod_cocone_inr p)).

  Definition preserves_bincoprods
    : UU
    := ∏ (x y : B₁)
         (p : bincoprod_cocone x y),
       has_bincoprod_ump p
       →
       has_bincoprod_ump (psfunctor_bincoprod_cocone p).

  Definition psfunctor_inserter_cone
             {x y : B₁}
             {f g : x --> y}
             (p : inserter_cone f g)
    : inserter_cone (#F f) (#F g)
    := make_inserter_cone
         (F p)
         (#F (inserter_cone_pr1 p))
         (psfunctor_comp F (inserter_cone_pr1 p) f
          • ##F (inserter_cone_cell p)
          • (psfunctor_comp F (inserter_cone_pr1 p) g)^-1).

  Definition preserves_inserters
    : UU
    := ∏ (x y : B₁)
         (f g : x --> y)
         (p : inserter_cone f g),
       has_inserter_ump p
       →
       has_inserter_ump (psfunctor_inserter_cone p).

  Definition psfunctor_equifier_cone
             {x y : B₁}
             {f g : x --> y}
             {α β : f ==> g}
             (p : equifier_cone f g α β)
    : equifier_cone (#F f) (#F g) (##F α) (##F β).
  Proof.
    refine (make_equifier_cone
              (F p)
              (#F (equifier_cone_pr1 p))
              _).
    abstract
      (pose (maponpaths
               (λ z, psfunctor_comp F (equifier_cone_pr1 p) f
                     • ##F z
                     • (psfunctor_comp F (equifier_cone_pr1 p) g)^-1)
               (equifier_cone_eq p)) as q ;
       cbn -[psfunctor_comp] in q ;
       rewrite !psfunctor_lwhisker in q ;
       rewrite !vassocl in q ;
       rewrite !vcomp_rinv in q ;
       rewrite !id2_right in q ;
       exact q).
  Defined.

  Definition preserves_equifiers
    : UU
    := ∏ (x y : B₁)
         (f g : x --> y)
         (α β : f ==> g)
         (p : equifier_cone f g α β),
       has_equifier_ump p
       →
       has_equifier_ump (psfunctor_equifier_cone p).
End Preserves.

(**
 2. The identity pseudofunctor preserves (co)limits
 *)
Definition identity_preserves_bifinal
           (B : bicat)
  : preserves_bifinal (id_psfunctor B)
  := λ x Hx, Hx.

Definition identity_preserves_biinitial
           (B : bicat)
  : preserves_biinitial (id_psfunctor B)
  := λ x Hx, Hx.

Definition identity_preserves_binprods
           (B : bicat)
  : preserves_binprods (id_psfunctor B)
  := λ x y p Hp, Hp.

Definition identity_preserves_bincoprods
           (B : bicat)
  : preserves_bincoprods (id_psfunctor B)
  := λ x y p Hp, Hp.

(**
 3. Preservation of the composition
 *)
Definition comp_psfunctor_preserves_bifinal
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           (HF : preserves_bifinal F)
           (HG : preserves_bifinal G)
  : preserves_bifinal (comp_psfunctor G F)
  := λ x Hx, HG _ (HF _ Hx).

Definition comp_psfunctor_preserves_biinitial
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           (HF : preserves_biinitial F)
           (HG : preserves_biinitial G)
  : preserves_biinitial (comp_psfunctor G F)
  := λ x Hx, HG _ (HF _ Hx).

Definition comp_psfunctor_preserves_binprods
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           (HF : preserves_binprods F)
           (HG : preserves_binprods G)
  : preserves_binprods (comp_psfunctor G F)
  := λ x y p Hp, HG _ _ _ (HF _ _ _ Hp).

Definition comp_psfunctor_preserves_bincoprods
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           (HF : preserves_bincoprods F)
           (HG : preserves_bincoprods G)
  : preserves_bincoprods (comp_psfunctor G F)
  := λ x y p Hp, HG _ _ _ (HF _ _ _ Hp).

(**
 4. Preservation of chosen (co)limits
 *)
Definition preserves_chosen_biinitial
           (B₁ : bicat_with_biinitial)
           {B₂ : bicat}
           (F : psfunctor B₁ B₂)
  : UU
  := is_biinitial (F (pr1 (biinitial_of B₁))).

Definition preserves_chosen_biinitial_to_preserve_biinitial
           (B₁ : bicat_with_biinitial)
           {B₂ : bicat}
           (F : psfunctor B₁ B₂)
           (HF : preserves_chosen_biinitial B₁ F)
  : preserves_biinitial F.
Proof.
  intros x Hx.
  refine (equiv_from_biinitial
            _
            (psfunctor_preserves_adjequiv'
               F
               (biinitial_unique_adj_eqv
                  Hx
                  (pr2 (biinitial_of B₁))))).
  apply HF.
Defined.
