Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Domain.
Require Import UniMath.Bicategories.DisplayedBicats.FiberBicategory.
Require Import UniMath.Bicategories.DisplayedBicats.FiberCategory.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.DomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.FiberBicategory.FunctorFromCleaving.

Local Open Scope cat.

Section DomainFiber.
  Context {B : bicat}
          (c a : B).

  Let fib : category
    := discrete_fiber_category
         (dom_disp_bicat B a)
         (dom_disp_2cells_isaprop B a)
         (dom_disp_univalent_2_1 B a)
         (dom_local_iso_cleaving a)
         c.

  Let homc : category
    := hom c a.

  Definition hom_to_domain_fib_data
    : functor_data homc fib.
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - exact (λ f g α, α • linvunitor _).
  Defined.

  Definition hom_to_domain_fib_is_functor
    : is_functor hom_to_domain_fib_data.
  Proof.
    split.
    - intro f ; cbn.
      apply id2_left.
    - intros f g h α β ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply linvunitor_natural.
      }
      rewrite <- lwhisker_hcomp.
      apply maponpaths.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      refine (!(id2_right _) @ _).
      apply maponpaths.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rwhisker.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply idpath.
  Qed.

  Definition hom_to_domain_fib
    : homc ⟶ fib.
  Proof.
    use make_functor.
    - exact hom_to_domain_fib_data.
    - exact hom_to_domain_fib_is_functor.
  Defined.

  Definition domain_fib_to_hom_data
    : functor_data fib homc.
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - exact (λ f g α, α • lunitor _).
  Defined.

  Definition domain_fib_to_hom_is_functor
    : is_functor domain_fib_to_hom_data.
  Proof.
    split.
    - intros f ; cbn.
      apply linvunitor_lunitor.
    - intros f g h α β ; cbn.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      apply lunitor_triangle.
  Qed.

  Definition domain_fib_to_hom
    : fib ⟶ homc.
  Proof.
    use make_functor.
    - exact domain_fib_to_hom_data.
    - exact domain_fib_to_hom_is_functor.
  Defined.

  Definition equiv_domain_fib_hom_unit
    : functor_identity fib
      ⟹
      domain_fib_to_hom ∙ hom_to_domain_fib.
  Proof.
    use make_nat_trans.
    - exact (λ f, linvunitor f).
    - abstract
        (intros f g α ; cbn ;
         do 2 apply maponpaths_2 ;
         rewrite !vassocl ;
         rewrite lunitor_linvunitor ;
         rewrite id2_right ;
         rewrite !lwhisker_hcomp ;
         rewrite <- linvunitor_natural ;
         rewrite <- lwhisker_hcomp ;
         apply maponpaths ;
         rewrite linvunitor_assoc ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         rewrite lwhisker_hcomp, rwhisker_hcomp ;
         apply triangle_r_inv).
  Defined.

  Definition equiv_domain_fib_hom_counit
    : hom_to_domain_fib ∙ domain_fib_to_hom
      ⟹
      functor_identity homc.
  Proof.
    use make_nat_trans.
    - exact (λ f, id₂ f).
    - abstract
        (intros f g α ; cbn ;
         rewrite id2_left, id2_right ;
         rewrite !vassocl ;
         rewrite linvunitor_lunitor ;
         apply id2_right).
  Defined.

  Definition equiv_domain_fib_hom
    : equivalence_of_cats fib homc.
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact domain_fib_to_hom.
      + exact hom_to_domain_fib.
      + exact equiv_domain_fib_hom_unit.
      + exact equiv_domain_fib_hom_counit.
    - split.
      + intro f.
        apply is_z_iso_discrete_fiber.
        apply dom_invertible_2cell_is_left_disp_adj_equiv.
        cbn.
        is_iso.
      + intro f ; cbn.
        apply is_inv2cell_to_is_z_iso.
        is_iso.
  Defined.

  Definition adj_equivalence_domain_fib_to_hom
    : adj_equivalence_of_cats domain_fib_to_hom
    := adjointificiation equiv_domain_fib_hom.

  Definition adj_equiv_domain_fib_hom
    : adj_equiv fib homc
    := _ ,, adj_equivalence_domain_fib_to_hom.
End DomainFiber.

Section DomainSubFiber.
  Context {B : bicat}
          (a : B)
          {c₁ c₂ : B}
          (f : c₁ --> c₂).

  Let fib₁ : category
    := discrete_fiber_category
         (dom_disp_bicat B a)
         (dom_disp_2cells_isaprop B a)
         (dom_disp_univalent_2_1 B a)
         (dom_local_iso_cleaving a)
         c₁.

  Let fib₂ : category
    := discrete_fiber_category
         (dom_disp_bicat B a)
         (dom_disp_2cells_isaprop B a)
         (dom_disp_univalent_2_1 B a)
         (dom_local_iso_cleaving a)
         c₂.

  Definition functor_from_dom_cleaving_nat_trans
    : functor_from_cleaving
        (dom_disp_bicat B a)
        (dom_disp_2cells_isaprop B a)
        (dom_disp_univalent_2_1 B a)
        (dom_global_cleaving a)
        (dom_local_iso_cleaving a)
        f
      ⟹
      domain_fib_to_hom _ _
      ∙ pre_comp a f
      ∙ hom_to_domain_fib _ _.
  Proof.
    use make_nat_trans.
    - exact (λ g, linvunitor _).
    - abstract
        (intros g₁ g₂ α ; cbn in * ;
         rewrite lwhisker_id2 ;
         rewrite id2_left, id2_right ;
         rewrite <- !lwhisker_vcomp ;
         rewrite !vassocr ;
         do 3 apply maponpaths_2 ;
         rewrite !vassocl ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocl ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite runitor_rwhisker ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite <- vcomp_whisker ;
         rewrite linvunitor_assoc ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite <- lwhisker_lwhisker_rassociator ;
         rewrite !lwhisker_vcomp ;
         apply idpath).
  Defined.

  Definition functor_from_dom_cleaving_nat_z_iso
    : nat_z_iso
        (functor_from_cleaving
           (dom_disp_bicat B a)
           (dom_disp_2cells_isaprop B a)
           (dom_disp_univalent_2_1 B a)
           (dom_global_cleaving a)
           (dom_local_iso_cleaving a)
           f)
        (domain_fib_to_hom _ _
         ∙ pre_comp a f
         ∙ hom_to_domain_fib _ _).
  Proof.
    use make_nat_z_iso.
    - exact functor_from_dom_cleaving_nat_trans.
    - intro g.
      apply is_z_iso_discrete_fiber.
      apply dom_invertible_2cell_is_left_disp_adj_equiv.
      cbn.
      is_iso.
  Defined.
End DomainSubFiber.
