(** This is the third and final layer of the construction of the bicategory of pseudofunctors.
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
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.

Local Open Scope cat.

Section PseudoFunctorData.
  Variable (C D : bicat).

  Definition psfunctor_data_disp : disp_bicat (map1cells C D)
    := disp_dirprod_bicat
         (map2cells_disp_cat C D)
         (disp_dirprod_bicat
            (identitor_disp_cat C D)
            (compositor_disp_cat C D)).

  Definition psfunctor_data_bicat : bicat
    := total_bicat psfunctor_data_disp.

  Definition psfunctor_data : UU
    := psfunctor_data_bicat.

  Definition psfunctor_data_is_univalent_2_1
             (HD_2_1 : is_univalent_2_1 D)
    : is_univalent_2_1 psfunctor_data_bicat.
  Proof.
    apply is_univalent_2_1_total_dirprod.
    - apply map1cells_is_univalent_2_1.
      exact HD_2_1.
    - apply map2cells_is_disp_univalent_2_1.
    - apply is_univalent_2_1_dirprod_bicat.
      + apply identitor_is_disp_univalent_2_1.
      + apply compositor_is_disp_univalent_2_1.
  Defined.

  Definition psfunctor_data_is_univalent_2_0
             (HD : is_univalent_2 D)
    : is_univalent_2_0 psfunctor_data_bicat.
  Proof.
    pose (HD_2_1 := pr2 HD).
    apply is_univalent_2_0_total_dirprod.
    - apply map1cells_is_univalent_2; assumption.
    - apply map2cells_is_disp_univalent_2; assumption.
    - apply is_univalent_2_dirprod_bicat.
      + apply map1cells_is_univalent_2_1; assumption.
      + apply identitor_is_disp_univalent_2; assumption.
      + apply compositor_is_disp_univalent_2; assumption.
  Defined.

  Definition psfunctor_data_is_univalent_2
             (HD : is_univalent_2 D)
    : is_univalent_2 psfunctor_data_bicat.
  Proof.
    split.
    - apply psfunctor_data_is_univalent_2_0; assumption.
    - apply psfunctor_data_is_univalent_2_1.
      exact (pr2 HD).
  Defined.

End PseudoFunctorData.

Coercion functor_data_from_bifunctor_ob_mor_cell
         {C D : bicat}
         (F: psfunctor_data C D)
  : functor_data C D
  := pr1 F.

Definition psfunctor_on_cells
           {C D : bicat}
           (F : psfunctor_data C D)
           {a b : C}
           {f g : a --> b}
           (x : f ==> g)
  : #F f ==> #F g
  := pr12 F a b f g x.

Local Notation "'##'" := (psfunctor_on_cells).

Definition psfunctor_id
           {C D : bicat}
           (F : psfunctor_data C D)
           (a : C)
  : identity (F a) ==> #F (identity a)
  := pr122 F a.

Definition psfunctor_comp
           {C D : bicat}
           (F : psfunctor_data C D)
           {a b c : C}
           (f : a --> b)
           (g : b --> c)
  : #F f · #F g ==> #F (f · g)
  := pr222 F a b c f g.

Section FunctorLaws.
  Context {C D : bicat}.
  Variable (F : psfunctor_data C D).

  Definition psfunctor_id2_law
    : UU
    := ∏ (a b : C) (f : a --> b), ##F (id2 f) = id2 _.

  Definition psfunctor_vcomp2_law : UU
    := ∏ (a b : C) (f g h: C⟦a, b⟧) (η : f ==> g) (φ : g ==> h),
       ##F (η • φ) = ##F η • ##F φ.

  Definition psfunctor_lunitor_law : UU
    := ∏ (a b : C) (f : C⟦a, b⟧),
       lunitor (#F f)
       =
       (psfunctor_id F a ▹ #F f)
         • psfunctor_comp F (identity a) f
         • ##F (lunitor f).

  Definition psfunctor_runitor_law : UU
    := ∏ (a b : C) (f : C⟦a, b⟧),
       runitor (#F f)
       =
       (#F f ◃ psfunctor_id F b)
         • psfunctor_comp F f (identity b)
         • ##F (runitor f).

  Definition psfunctor_lassociator_law : UU
    := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
       (#F f ◃ psfunctor_comp F g h)
         • psfunctor_comp F f (g · h)
         • ##F (lassociator f g h)
       =
       (lassociator (#F f) (#F g) (#F h))
         • (psfunctor_comp F f g ▹ #F h)
         • psfunctor_comp F (f · g) h.

  Definition psfunctor_lwhisker_law : UU
    := ∏ (a b c : C) (f : C⟦a, b⟧) (g₁ g₂ : C⟦b, c⟧) (η : g₁ ==> g₂),
       psfunctor_comp F f g₁ • ##F (f ◃ η)
       =
       #F f ◃ ##F η • psfunctor_comp F f g₂.

  Definition psfunctor_rwhisker_law : UU
    := ∏ (a b c : C) (f₁ f₂ : C⟦a, b⟧) (g : C⟦b, c⟧) (η : f₁ ==> f₂),
       psfunctor_comp F f₁ g • ##F (η ▹ g)
       =
       ##F η ▹ #F g • psfunctor_comp F f₂ g.

  Definition psfunctor_laws : UU
    := psfunctor_id2_law
         × psfunctor_vcomp2_law
         × psfunctor_lunitor_law
         × psfunctor_runitor_law
         × psfunctor_lassociator_law
         × psfunctor_lwhisker_law
         × psfunctor_rwhisker_law.

  Definition invertible_cells
    : UU
    := (∏ (a : C),
        is_invertible_2cell (psfunctor_id F a))
     ×
       (∏ (a b c : C) (f : a --> b) (g : b --> c),
        is_invertible_2cell (psfunctor_comp F f g)).

  Definition is_psfunctor : UU
    := psfunctor_laws × invertible_cells.

  Definition is_psfunctor_isaprop
    : isaprop is_psfunctor.
  Proof.
    repeat (apply isapropdirprod) ; repeat (apply impred ; intro)
    ; try (apply D) ; try (apply isaprop_is_invertible_2cell).
  Qed.
End FunctorLaws.

Section LaxFunctorBicat.
  Variable (C D : bicat).

  Definition laxfunctor_bicat
    : bicat
    := fullsubbicat (psfunctor_data_bicat C D) psfunctor_laws.

  Definition laxfunctor_bicat_is_univalent_2_1
             (HD_2_1 : is_univalent_2_1 D)
    : is_univalent_2_1 laxfunctor_bicat.
  Proof.
    apply is_univalent_2_1_fullsubbicat.
    apply psfunctor_data_is_univalent_2_1.
    exact HD_2_1.
  Defined.

  Definition laxfunctor_bicat_is_univalent_2_0
             (HD : is_univalent_2 D)
    : is_univalent_2_0 laxfunctor_bicat.
  Proof.
    apply is_univalent_2_0_fullsubbicat.
    - apply psfunctor_data_is_univalent_2; assumption.
    - intro.
      repeat (apply isapropdirprod) ; repeat (apply impred ; intro)
      ; try (apply D).
  Defined.

  Definition laxfunctor_bicat_is_univalent_2
             (HD : is_univalent_2 D)
    : is_univalent_2 laxfunctor_bicat.
  Proof.
    split.
    - apply laxfunctor_bicat_is_univalent_2_0; assumption.
    - apply laxfunctor_bicat_is_univalent_2_1.
      exact (pr2 HD).
  Defined.

End LaxFunctorBicat.

Section PseudoFunctorBicat.
  Variable (C D : bicat).

  Definition psfunctor_bicat
    : bicat
    := fullsubbicat (psfunctor_data_bicat C D) is_psfunctor.

  Definition psfunctor_bicat_is_univalent_2_1
             (HD_2_1 : is_univalent_2_1 D)
    : is_univalent_2_1 psfunctor_bicat.
  Proof.
    apply is_univalent_2_1_fullsubbicat.
    apply psfunctor_data_is_univalent_2_1.
    exact HD_2_1.
  Defined.

  Definition psfunctor_bicat_is_univalent_2_0
             (HD : is_univalent_2 D)
    : is_univalent_2_0 psfunctor_bicat.
  Proof.
    apply is_univalent_2_0_fullsubbicat.
    - apply psfunctor_data_is_univalent_2; assumption.
    - intro.
      apply is_psfunctor_isaprop.
  Defined.

  Definition psfunctor_bicat_is_univalent_2
             (HD : is_univalent_2 D)
    : is_univalent_2 psfunctor_bicat.
  Proof.
    split.
    - apply psfunctor_bicat_is_univalent_2_0; assumption.
    - apply psfunctor_bicat_is_univalent_2_1.
      exact (pr2 HD).
  Defined.

End PseudoFunctorBicat.
