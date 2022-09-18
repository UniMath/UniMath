(*************************************************************************

 Inclusion into the monad bicategory

 We show that we have a pseudofunctor from `B` to `mnd B`. Each object
 is sent to the identity monad on that object

 Contents
 1. The identity monad
 2. Section of bicategory of monads
 3. Left biadjoint to the inclusion

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicatSection.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EndoMap.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.

Local Open Scope cat.

(**
 1. The identity monad
 *)
Section IdMonad.
  Context {B : bicat}
          (x : B).

  Definition id_monad_data
    : disp_mnd_data B x
    := id₁ x ,, id₂ _ ,, lunitor _.

  Definition is_mnd_id_monad_data
    : is_mnd B (x,, id_monad_data).
  Proof.
    repeat split ; cbn.
    - rewrite id2_rwhisker.
      rewrite id2_right.
      apply linvunitor_lunitor.
    - rewrite lwhisker_id2.
      rewrite id2_right.
      rewrite lunitor_runitor_identity.
      apply rinvunitor_runitor.
    - apply maponpaths_2.
      rewrite lunitor_lwhisker.
      rewrite runitor_lunitor_identity.
      apply idpath.
  Qed.

  Definition id_monad
    : disp_mnd B x
    := id_monad_data ,, is_mnd_id_monad_data.
End IdMonad.

(**
 2. Section of bicategory of monads
 *)
Definition id_monad_mor
           {B : bicat}
           {x y : B}
           (f : x --> y)
  : id_monad x -->[ f ] id_monad y.
Proof.
  simple refine ((runitor _ • linvunitor _ ,, _) ,, tt) ; cbn.
  repeat split.
  - abstract
      (cbn ;
       rewrite id2_rwhisker, lwhisker_id2 ;
       rewrite !id2_right ;
       rewrite !vassocr ;
       rewrite rinvunitor_runitor ;
       rewrite id2_left ;
       apply idpath).
  - abstract
      (cbn ;
       rewrite !vassocl ;
       rewrite lunitor_runitor_identity ;
       rewrite <- lunitor_lwhisker ;
       rewrite !(maponpaths (λ z, _ • (_ • (_ • (_ • z)))) (vassocr _ _ _)) ;
       rewrite lassociator_rassociator ;
       rewrite id2_left ;
       rewrite lwhisker_vcomp ;
       rewrite !vassocl ;
       rewrite linvunitor_lunitor ;
       rewrite id2_right ;
       rewrite runitor_triangle ;
       rewrite vcomp_runitor ;
       rewrite !vassocr ;
       do 2 apply maponpaths_2 ;
       rewrite <- runitor_triangle ;
       rewrite !vassocr ;
       rewrite lassociator_rassociator ;
       rewrite id2_left ;
       rewrite runitor_lunitor_identity ;
       apply idpath).
Defined.

Definition id_monad_cell
           {B : bicat}
           {x y : B}
           {f g : x --> y}
           (τ : f ==> g)
  : id_monad_mor f ==>[ τ ] id_monad_mor g.
Proof.
  simple refine ((_ ,, (tt ,, tt)) ,, tt) ; cbn.
  rewrite !vassocr.
  rewrite vcomp_runitor.
  rewrite !vassocl.
  apply maponpaths.
  rewrite linvunitor_natural.
  rewrite lwhisker_hcomp.
  apply idpath.
Qed.

Definition id_monad_id
           {B : bicat}
           (x : B)
  : id_disp _ ==>[ id2 _ ] id_monad_mor (id₁ x).
Proof.
  simple refine ((_ ,, (tt ,, tt)) ,, tt) ; cbn.
  rewrite lwhisker_id2, id2_rwhisker.
  rewrite id2_left, id2_right.
  rewrite lunitor_runitor_identity.
  rewrite lunitor_V_id_is_left_unit_V_id.
  apply idpath.
Qed.

Definition id_monad_comp
           {B : bicat}
           {x y z : B}
           (f : x --> y)
           (g : y --> z)
  : id_monad_mor f ;; id_monad_mor g ==>[ id2 _ ] id_monad_mor (f · g).
Proof.
  simple refine ((_ ,, (tt ,, tt)) ,, tt) ; cbn.
  rewrite id2_rwhisker, id2_left.
  rewrite lwhisker_id2, id2_right.
  rewrite <- runitor_triangle.
  rewrite !vassocl.
  apply maponpaths.
  rewrite <- !lwhisker_vcomp.
  rewrite !vassocl.
  apply maponpaths.
  rewrite linvunitor_assoc.
  rewrite !vassocr.
  apply maponpaths_2.
  rewrite lwhisker_hcomp.
  rewrite triangle_l_inv.
  rewrite <- rwhisker_hcomp.
  rewrite rwhisker_vcomp.
  rewrite !vassocr.
  rewrite rinvunitor_runitor.
  rewrite id2_left.
  apply idpath.
Qed.

Definition mnd_section_disp_bicat
           (B : bicat)
  : section_disp_bicat (disp_mnd B).
Proof.
  use make_section_disp_bicat.
  - apply disp_2cells_isaprop_disp_mnd.
  - apply disp_locally_groupoid_disp_mnd.
  - exact (λ x, id_monad x).
  - exact (λ _ _ f, id_monad_mor f).
  - exact (λ _ _ _ _ τ, id_monad_cell τ).
  - exact (λ x, id_monad_id x).
  - exact (λ _ _ _ f g, id_monad_comp f g).
Defined.

Definition mnd_incl
           (B : bicat)
  : psfunctor B (mnd B)
  := section_to_psfunctor (mnd_section_disp_bicat B).

(**
 3. Left biadjoint to the inclusion
 *)
Definition mnd_to_mnd_incl_data
           {B : bicat}
           (m : mnd B)
  : mnd_mor_data m (mnd_incl B (ob_of_mnd m)).
Proof.
  use make_mnd_mor_data.
  - exact (id₁ _).
  - exact (runitor _ • unit_of_mnd m • rinvunitor _).
Defined.

Definition mnd_to_mnd_incl_laws
           {B : bicat}
           (m : mnd B)
  : mnd_mor_laws (mnd_to_mnd_incl_data m).
Proof.
  split.
  - cbn.
    rewrite lwhisker_id2.
    rewrite id2_right.
    rewrite !vassocr.
    rewrite rinvunitor_runitor.
    rewrite id2_left.
    use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
    rewrite lunitor_runitor_identity.
    rewrite !vassocr.
    rewrite <- vcomp_runitor.
    rewrite !vassocl.
    rewrite runitor_rinvunitor.
    rewrite id2_right.
    apply idpath.
  - cbn.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite rwhisker_hcomp.
    rewrite !vassocr.
    rewrite <- triangle_r.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite rwhisker_hcomp.
      rewrite !vassocr.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      rewrite runitor_lunitor_identity.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite <- vcomp_runitor.
    rewrite !vassocl.
    rewrite runitor_rinvunitor.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      apply idpath.
    }
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
    rewrite id2_left.
    refine (_ @ id2_right _).
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    rewrite !vassocr.
    exact (pr1 (pr222 m)).
Qed.

Definition mnd_to_mnd_incl
           {B : bicat}
           (m : mnd B)
  : m --> mnd_incl B (ob_of_mnd m).
Proof.
  use make_mnd_mor.
  - exact (mnd_to_mnd_incl_data m).
  - exact (mnd_to_mnd_incl_laws m).
Defined.

Definition mnd_incl_hom_functor_data
           {B : bicat}
           (m : mnd B)
           (x : B)
  : functor_data
      (hom m (mnd_incl B x))
      (hom (ob_of_mnd m) x).
Proof.
  use make_functor_data.
  - exact (λ f, pr1 f).
  - exact (λ f₁ f₂ τ, pr1 τ).
Defined.

Definition mnd_incl_hom_functor_is_functor
           {B : bicat}
           (m : mnd B)
           (x : B)
  : is_functor (mnd_incl_hom_functor_data m x).
Proof.
  split.
  - intro ; cbn.
    apply idpath.
  - intro ; intros ; cbn.
    apply idpath.
Qed.

Definition mnd_incl_hom_functor
           {B : bicat}
           (m : mnd B)
           (x : B)
  : hom m (mnd_incl B x) ⟶ hom (ob_of_mnd m) x.
Proof.
  use make_functor.
  - exact (mnd_incl_hom_functor_data m x).
  - exact (mnd_incl_hom_functor_is_functor m x).
Defined.

Definition mnd_incl_unit_data
           {B : bicat}
           (m : mnd B)
           (x : B)
  : nat_trans_data
      (functor_identity _)
      (left_universal_arrow_functor (mnd_incl B) m x mnd_to_mnd_incl
       ∙ mnd_incl_hom_functor m x)
  := λ f, linvunitor f.

Definition mnd_incl_unit_is_nat_trans
           {B : bicat}
           (m : mnd B)
           (x : B)
  : is_nat_trans
      _ _
      (mnd_incl_unit_data m x).
Proof.
  intros f₁ f₂ τ ; unfold mnd_incl_unit_data ; cbn.
  rewrite linvunitor_natural.
  rewrite <- lwhisker_hcomp.
  apply idpath.
Qed.

Definition mnd_incl_unit
           {B : bicat}
           (m : mnd B)
           (x : B)
  : functor_identity _
    ⟹
    left_universal_arrow_functor (mnd_incl B) m x mnd_to_mnd_incl
    ∙ mnd_incl_hom_functor m x.
Proof.
  use make_nat_trans.
  - exact (mnd_incl_unit_data m x).
  - exact (mnd_incl_unit_is_nat_trans m x).
Defined.

Definition mnd_incl_counit_mnd_cell_data
           {B : bicat}
           (m : mnd B)
           (x : B)
           (f : m --> mnd_incl B x)
  : mnd_cell_data
      ((mnd_incl_hom_functor m x
        ∙ left_universal_arrow_functor (mnd_incl B) m x mnd_to_mnd_incl) f)
      (functor_identity (hom_data m (mnd_incl B x)) f)
  := lunitor _.

Definition mnd_incl_counit_is_mnd_cell
           {B : bicat}
           (m : mnd B)
           (x : B)
           (f : m --> mnd_incl B x)
  : is_mnd_cell (mnd_incl_counit_mnd_cell_data m x f).
Proof.
  unfold is_mnd_cell, mnd_incl_counit_mnd_cell_data ; cbn.
  rewrite <- !lwhisker_vcomp.
  rewrite <- !rwhisker_vcomp.
  rewrite !vassocl.
  use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
  rewrite !vassocr.
  rewrite lunitor_triangle.
  rewrite !vassocl.
  etrans.
  {
    apply maponpaths.
    rewrite lwhisker_hcomp.
    rewrite !vassocr.
    rewrite triangle_l_inv.
    rewrite <- rwhisker_hcomp.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite !vassocl.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    rewrite id2_rwhisker.
    apply id2_right.
  }
  use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
  rewrite !vassocr.
  rewrite lwhisker_hcomp.
  rewrite <- linvunitor_natural.
  rewrite !vassocl.
  etrans.
  {
    apply maponpaths.
    apply (pr1 (pr212 f)).
  }
  cbn.
  rewrite !vassocr.
  rewrite runitor_rinvunitor.
  rewrite lwhisker_id2.
  rewrite !id2_left.
  apply idpath.
Qed.

Definition mnd_incl_counit_data
           {B : bicat}
           (m : mnd B)
           (x : B)
  : nat_trans_data
      (mnd_incl_hom_functor m x
       ∙ left_universal_arrow_functor (mnd_incl B) m x mnd_to_mnd_incl)
      (functor_identity _).
Proof.
  intro f.
  use make_mnd_cell.
  - exact (mnd_incl_counit_mnd_cell_data m x f).
  - exact (mnd_incl_counit_is_mnd_cell m x f).
Defined.

Definition mnd_incl_counit_is_nat_trans
           {B : bicat}
           (m : mnd B)
           (x : B)
  : is_nat_trans
      _ _
      (mnd_incl_counit_data m x).
Proof.
  intros f₁ f₂ τ.
  use eq_mnd_cell ; cbn.
  unfold mnd_incl_counit_mnd_cell_data ; cbn.
  rewrite vcomp_lunitor.
  apply idpath.
Qed.

Definition mnd_incl_counit
           {B : bicat}
           (m : mnd B)
           (x : B)
  : mnd_incl_hom_functor m x
    ∙ left_universal_arrow_functor (mnd_incl B) m x mnd_to_mnd_incl
    ⟹
    functor_identity _.
Proof.
  use make_nat_trans.
  - exact (mnd_incl_counit_data m x).
  - exact (mnd_incl_counit_is_nat_trans m x).
Defined.

Definition is_z_isomorphism_mnd_incl_unit
           {B : bicat}
           {m : mnd B}
           {x : B}
           (f : ob_of_mnd m --> x)
  : is_z_isomorphism (mnd_incl_unit_data m x f).
Proof.
  use is_inv2cell_to_is_z_iso.
  unfold mnd_incl_unit_data.
  is_iso.
Defined.

Definition is_z_isomorphism_mnd_incl_counit
           {B : bicat}
           {m : mnd B}
           {x : B}
           (f : m --> mnd_incl B x)
  : is_z_isomorphism (mnd_incl_counit_data m x f).
Proof.
  use is_inv2cell_to_is_z_iso.
  use is_invertible_mnd_2cell.
  unfold mnd_incl_counit_data, mnd_incl_counit_mnd_cell_data ; cbn.
  is_iso.
Defined.

Definition mnd_incl_left_universal_arrow
           (B : bicat)
  : left_universal_arrow (mnd_incl B).
Proof.
  use make_left_universal_arrow.
  - exact (λ m, ob_of_mnd m).
  - exact (λ m, mnd_to_mnd_incl m).
  - exact (λ m x, mnd_incl_hom_functor m x).
  - exact (λ m x, mnd_incl_unit m x).
  - exact (λ m x, mnd_incl_counit m x).
  - exact (λ m x f, is_z_isomorphism_mnd_incl_unit f).
  - exact (λ m x f, is_z_isomorphism_mnd_incl_counit f).
Defined.
