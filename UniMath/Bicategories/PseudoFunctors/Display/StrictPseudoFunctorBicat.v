(** This is the third and final layer of the construction of the bicategory of strict pseudofunctors.
    Here we add the laws.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictIdentitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictCompositor.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.

Local Open Scope cat.

Section StrictPseudoFunctorData.
  Variable (C D : bicat).

  Definition strict_psfunctor_data_disp : disp_bicat (map1cells C D)
    := disp_dirprod_bicat
         (map2cells_disp_cat C D)
         (disp_dirprod_bicat
            (strict_identitor_disp_cat C D)
            (strict_compositor_disp_cat C D)).

  Definition strict_psfunctor_data_bicat : bicat
    := total_bicat strict_psfunctor_data_disp.

  Definition strict_psfunctor_data : UU
    := strict_psfunctor_data_bicat.

  Definition strict_psfunctor_data_is_univalent_2_1
             (HD_2_1 : is_univalent_2_1 D)
    : is_univalent_2_1 strict_psfunctor_data_bicat.
  Proof.
    apply is_univalent_2_1_total_dirprod.
    - apply map1cells_is_univalent_2_1.
      exact HD_2_1.
    - apply map2cells_is_disp_univalent_2_1.
    - apply is_univalent_2_1_dirprod_bicat.
      + apply strict_identitor_is_disp_univalent_2_1.
      + apply strict_compositor_is_disp_univalent_2_1.
  Defined.

  Definition strict_psfunctor_data_is_univalent_2_0
             (HD : is_univalent_2 D)
    : is_univalent_2_0 strict_psfunctor_data_bicat.
  Proof.
    pose (HD_2_1 := pr2 HD).
    apply is_univalent_2_0_total_dirprod.
    - apply map1cells_is_univalent_2; assumption.
    - apply map2cells_is_disp_univalent_2; assumption.
    - apply is_univalent_2_dirprod_bicat.
      + apply map1cells_is_univalent_2_1; assumption.
      + apply strict_identitor_is_disp_univalent_2; assumption.
      + apply strict_compositor_is_disp_univalent_2; assumption.
  Defined.

  Definition strict_psfunctor_data_is_univalent_2
             (HD : is_univalent_2 D)
    : is_univalent_2 strict_psfunctor_data_bicat.
  Proof.
    split.
    - apply strict_psfunctor_data_is_univalent_2_0; assumption.
    - apply strict_psfunctor_data_is_univalent_2_1.
      exact (pr2 HD).
  Defined.
End StrictPseudoFunctorData.

Coercion functor_data_from_bifunctor_ob_mor_cell
         {C D : bicat}
         (F: strict_psfunctor_data C D)
  : functor_data C D
  := pr1 F.

Definition strict_psfunctor_on_cells
           {C D : bicat}
           (F : strict_psfunctor_data C D)
           {a b : C}
           {f g : a --> b}
           (x : f ==> g)
  : #F f ==> #F g
  := pr12 F a b f g x.

Local Notation "'##'" := (strict_psfunctor_on_cells).

Definition strict_psfunctor_id
           {C D : bicat}
           (F : strict_psfunctor_data C D)
           (a : C)
  : identity (F a) = #F (identity a)
  := pr122 F a.

Definition strict_psfunctor_comp
           {C D : bicat}
           (F : strict_psfunctor_data C D)
           {a b c : C}
           (f : a --> b)
           (g : b --> c)
  : #F f · #F g = #F (f · g)
  := pr222 F a b c f g.

Definition strict_psfunctor_id_cell
           {C D : bicat}
           (F : strict_psfunctor_data C D)
           (a : C)
  : invertible_2cell (id₁ (F a)) (# F (id₁ a))
  := idtoiso_2_1 _ _ (strict_psfunctor_id F a).

Definition strict_psfunctor_comp_cell
           {C D : bicat}
           (F : strict_psfunctor_data C D)
           {a b c : C}
           (f : a --> b)
           (g : b --> c)
  : invertible_2cell (# F f · # F g) (# F (f · g))
  := idtoiso_2_1 _ _ (strict_psfunctor_comp F f g).

Section FunctorLaws.
  Context {C D : bicat}.
  Variable (F : strict_psfunctor_data C D).

  Definition strict_psfunctor_id2_law
    : UU
    := ∏ (a b : C) (f : a --> b), ##F (id2 f) = id2 _.

  Definition strict_psfunctor_vcomp2_law : UU
    := ∏ (a b : C) (f g h: C⟦a, b⟧) (η : f ==> g) (φ : g ==> h),
       ##F (η • φ) = ##F η • ##F φ.

  Definition strict_psfunctor_lunitor_law : UU
    := ∏ (a b : C) (f : C⟦a, b⟧),
       lunitor (#F f)
       =
       (strict_psfunctor_id_cell F a ▹ #F f)
         • strict_psfunctor_comp_cell F (identity a) f
         • ##F (lunitor f).

  Definition strict_psfunctor_runitor_law : UU
    := ∏ (a b : C) (f : C⟦a, b⟧),
       runitor (#F f)
       =
       (#F f ◃ strict_psfunctor_id_cell F b)
         • strict_psfunctor_comp_cell F f (identity b)
         • ##F (runitor f).

  Definition strict_psfunctor_lassociator_law : UU
    := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
       (#F f ◃ strict_psfunctor_comp_cell F g h)
         • strict_psfunctor_comp_cell F f (g · h)
         • ##F (lassociator f g h)
       =
       (lassociator (#F f) (#F g) (#F h))
         • (strict_psfunctor_comp_cell F f g ▹ #F h)
         • strict_psfunctor_comp_cell F (f · g) h.

  Definition strict_psfunctor_lwhisker_law : UU
    := ∏ (a b c : C) (f : C⟦a, b⟧) (g₁ g₂ : C⟦b, c⟧) (η : g₁ ==> g₂),
       strict_psfunctor_comp_cell F f g₁ • ##F (f ◃ η)
       =
       #F f ◃ ##F η • strict_psfunctor_comp_cell F f g₂.

  Definition strict_psfunctor_rwhisker_law : UU
    := ∏ (a b c : C) (f₁ f₂ : C⟦a, b⟧) (g : C⟦b, c⟧) (η : f₁ ==> f₂),
       strict_psfunctor_comp_cell F f₁ g • ##F (η ▹ g)
       =
       ##F η ▹ #F g • strict_psfunctor_comp_cell F f₂ g.

  Definition is_strict_psfunctor : UU
    := strict_psfunctor_id2_law
         × strict_psfunctor_vcomp2_law
         × strict_psfunctor_lunitor_law
         × strict_psfunctor_runitor_law
         × strict_psfunctor_lassociator_law
         × strict_psfunctor_lwhisker_law
         × strict_psfunctor_rwhisker_law.

  Definition is_strict_psfunctor_isaprop
    : isaprop is_strict_psfunctor.
  Proof.
    repeat (apply isapropdirprod) ; repeat (apply impred ; intro)
    ; apply D.
  Qed.
End FunctorLaws.

Section StrictPseudoFunctorBicat.
  Variable (C D : bicat).

  Definition strict_psfunctor_bicat
    : bicat
    := fullsubbicat (strict_psfunctor_data_bicat C D) is_strict_psfunctor.

  Definition strict_psfunctor_bicat_is_univalent_2_1
             (HD_2_1 : is_univalent_2_1 D)
    : is_univalent_2_1 strict_psfunctor_bicat.
  Proof.
    apply is_univalent_2_1_fullsubbicat.
    apply strict_psfunctor_data_is_univalent_2_1.
    exact HD_2_1.
  Defined.

  Definition strict_psfunctor_bicat_is_univalent_2_0
             (HD : is_univalent_2 D)
    : is_univalent_2_0 strict_psfunctor_bicat.
  Proof.
    apply is_univalent_2_0_fullsubbicat.
    - apply strict_psfunctor_data_is_univalent_2; assumption.
    - intro.
      apply is_strict_psfunctor_isaprop.
  Defined.

  Definition strict_psfunctor_bicat_is_univalent_2
             (HD : is_univalent_2 D)
    : is_univalent_2 strict_psfunctor_bicat.
  Proof.
    split.
    - apply strict_psfunctor_bicat_is_univalent_2_0; assumption.
    - apply strict_psfunctor_bicat_is_univalent_2_1.
      exact (pr2 HD).
  Defined.
End StrictPseudoFunctorBicat.
