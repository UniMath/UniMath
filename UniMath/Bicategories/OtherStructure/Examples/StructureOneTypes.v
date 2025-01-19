(**
 Duality involutions of bicategories

 Contents:
 1. Duality involution on locally groupoidal bicategory
 2. 1-Types are cartesian closed
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Examples.OneTypesLimits.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Op2OfPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.ConstProduct.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.OtherStructure.DualityInvolution.
Require Import UniMath.Bicategories.OtherStructure.Exponentials.

Local Open Scope cat.

(**
 1. Duality involution on locally groupoidal bicategory
 *)
Section DualityInvolutionLocallyGroupoidal.
  Context (B : bicat)
          (inv_B : locally_groupoid B).

  Definition op_locally_groupoid_data
    : psfunctor_data (op2_bicat B) B.
  Proof.
    use make_psfunctor_data.
    - exact (λ z, z).
    - exact (λ _ _ f, f).
    - exact (λ _ _ _ _ α, (inv_B _ _ _ _ α)^-1).
    - exact (λ _, id2 _).
    - exact (λ _ _ _ _ _, id2 _).
  Defined.

  Definition op_locally_groupoid_laws
    : psfunctor_laws op_locally_groupoid_data.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - refine (!(id2_right _) @ _).
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      apply idpath.
    - use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite lunitor_linvunitor.
      rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite runitor_rinvunitor.
      rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - rewrite lwhisker_id2, id2_rwhisker.
      rewrite !id2_left, !id2_right.
      refine (!(id2_right _) @ _).
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite rassociator_lassociator.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_left, id2_right.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_left, id2_right.
      apply idpath.
  Qed.

  Definition op_locally_groupoid_invertible_cells
    : invertible_cells op_locally_groupoid_data.
  Proof.
    split ; intro ; intros ; cbn ; is_iso.
  Defined.

  Definition op_locally_groupoid
    : psfunctor (op2_bicat B) B.
  Proof.
    use make_psfunctor.
    - exact op_locally_groupoid_data.
    - exact op_locally_groupoid_laws.
    - exact op_locally_groupoid_invertible_cells.
  Defined.

  Definition locally_groupoid_duality_involution_unit_data
    : pstrans_data
        (id_psfunctor B)
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid)).
  Proof.
    use make_pstrans_data.
    - exact (λ x, id₁ _).
    - exact (λ _ _ f,
             comp_of_invertible_2cell
               (lunitor_invertible_2cell _)
               (rinvunitor_invertible_2cell _)).
  Defined.

  Definition locally_groupoid_duality_involution_unit_is_pstrans
    : is_pstrans locally_groupoid_duality_involution_unit_data.
  Proof.
    repeat split.
    - intros x y f g α ; cbn.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - intro x ; cbn.
      rewrite !id2_left.
      rewrite id2_rwhisker, id2_right.
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros x y z f g ; cbn.
      rewrite id2_left.
      rewrite id2_rwhisker, id2_right.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_l_inv.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition locally_groupoid_duality_involution_unit
    : pstrans
        (id_psfunctor B)
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid)).
  Proof.
    use make_pstrans.
    - exact locally_groupoid_duality_involution_unit_data.
    - exact locally_groupoid_duality_involution_unit_is_pstrans.
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_data
    : pstrans_data
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid))
        (id_psfunctor B).
  Proof.
    use make_pstrans_data.
    - exact (λ _, id₁ _).
    - exact (λ _ _ f,
             comp_of_invertible_2cell
               (lunitor_invertible_2cell _)
               (rinvunitor_invertible_2cell _)).
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_is_pstrans
    : is_pstrans locally_groupoid_duality_involution_unit_inv_data.
  Proof.
    repeat split.
    - intros x y f g α ; cbn.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite vcomp_rinv.
      apply id2_right.
    - intro x ; cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite id2_left.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros x y z f g ; cbn.
      rewrite lwhisker_id2, !id2_left.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_l_inv.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition locally_groupoid_duality_involution_unit_inv
    : pstrans
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid))
        (id_psfunctor B).
  Proof.
    use make_pstrans.
    - exact locally_groupoid_duality_involution_unit_inv_data.
    - exact locally_groupoid_duality_involution_unit_inv_is_pstrans.
  Defined.

  Definition locally_groupoid_duality_involution_unit_unit_inv_data
    : invertible_modification_data
        (id₁ (id_psfunctor B))
        (locally_groupoid_duality_involution_unit
         · locally_groupoid_duality_involution_unit_inv).
  Proof.
    intro x ; cbn.
    exact (linvunitor_invertible_2cell _).
  Defined.

  Definition locally_groupoid_duality_involution_unit_unit_inv_is_modif
    : is_modification
        locally_groupoid_duality_involution_unit_unit_inv_data.
  Proof.
    intros x y f ; cbn.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocl.
    rewrite (rwhisker_hcomp _ (rinvunitor f)).
    rewrite <- triangle_r_inv.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite lunitor_V_id_is_left_unit_V_id.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_l_inv.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_vcomp.
    rewrite !vassocr.
    rewrite linvunitor_lunitor.
    rewrite id2_left.
    rewrite !vassocl.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    apply idpath.
  Qed.

  Definition locally_groupoid_duality_involution_unit_unit_inv
    : invertible_modification
        (id₁ (id_psfunctor B))
        (locally_groupoid_duality_involution_unit
         · locally_groupoid_duality_involution_unit_inv).
  Proof.
    use make_invertible_modification.
    - exact locally_groupoid_duality_involution_unit_unit_inv_data.
    - exact locally_groupoid_duality_involution_unit_unit_inv_is_modif.
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_unit_data
    : invertible_modification_data
        (locally_groupoid_duality_involution_unit_inv
         · locally_groupoid_duality_involution_unit)
        (id₁ _).
  Proof.
    intro x ; cbn.
    exact (lunitor_invertible_2cell _).
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_unit_is_modif
    : is_modification
        locally_groupoid_duality_involution_unit_inv_unit_data.
  Proof.
    intros x y f ; cbn.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite !vassocl.
    rewrite runitor_lunitor_identity.
    apply maponpaths.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    apply idpath.
  Qed.

  Definition locally_groupoid_duality_involution_unit_inv_unit
    : invertible_modification
        (locally_groupoid_duality_involution_unit_inv
         · locally_groupoid_duality_involution_unit)
        (id₁ _).
  Proof.
    use make_invertible_modification.
    - exact locally_groupoid_duality_involution_unit_inv_unit_data.
    - exact locally_groupoid_duality_involution_unit_inv_unit_is_modif.
  Defined.

  Definition locally_groupoid_duality_involution_triangle
             (x : B)
    : invertible_2cell (id₁ x) (id₁ x)
    := id2_invertible_2cell _.

  Definition locally_groupoid_duality_involution_data
    : duality_involution_data op_locally_groupoid
    := make_duality_involution_data
         op_locally_groupoid
         locally_groupoid_duality_involution_unit
         locally_groupoid_duality_involution_unit_inv
         locally_groupoid_duality_involution_unit_unit_inv
         locally_groupoid_duality_involution_unit_inv_unit
         locally_groupoid_duality_involution_triangle.

  Definition locally_groupoid_duality_involution_laws_coh
             (x : B)
    : lunitor (id₁ x)
      • rinvunitor (id₁ x)
      • (id₁ x ◃ id₂ (id₁ x))
      =
      id₁ x ◃ (inv_B x x (id₁ x) (id₁ x) (id₂ (id₁ x)))^-1.
  Proof.
    rewrite lunitor_runitor_identity.
    rewrite runitor_rinvunitor.
    rewrite lwhisker_id2.
    rewrite !id2_left.
    refine (_ @ id2_right _).
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    rewrite lwhisker_id2.
    apply id2_left.
  Qed.

  Proposition locally_groupoid_duality_involution_triangle_law
              {x y : B}
              (f : x --> y)
    : (id₂ (id₁ x) ▹ f)
      • id₂ (id₁ x · f)
      =
      (((lunitor f • rinvunitor f)
      • (f ◃ id₂ (id₁ y)))
      • id₂ (f · id₁ y))
      • (inv_B x y (id₁ x · f) (f · id₁ y) (lunitor f • rinvunitor f))^-1.
  Proof.
    rewrite id2_rwhisker, lwhisker_id2.
    rewrite !id2_left, !id2_right.
    use vcomp_move_L_pM ; [ is_iso | ].
    cbn.
    rewrite id2_right.
    refine (_ @ id2_right _).
    use vcomp_move_L_pM ; [ is_iso | ].
    cbn.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_runitor.
      apply id2_left.
    }
    apply lunitor_linvunitor.
  Qed.

  Definition locally_groupoid_duality_involution_laws
    : duality_involution_laws locally_groupoid_duality_involution_data.
  Proof.
    split.
    - exact locally_groupoid_duality_involution_laws_coh.
    - exact @locally_groupoid_duality_involution_triangle_law.
  Qed.

  Definition locally_groupoid_duality_involution
    : duality_involution op_locally_groupoid
    := locally_groupoid_duality_involution_data
       ,,
       locally_groupoid_duality_involution_laws.
End DualityInvolutionLocallyGroupoidal.

(**
 2. 1-Types are cartesian closed
*)
Definition one_types_pair_2cell
           {X₁ X₂ Y₁ Y₂ : one_type}
           {f₁ f₂ : X₁ → Y₁}
           {g₁ g₂ : X₂ → Y₂}
           (p : f₁ ~ f₂)
           (q : g₁ ~ g₂)
           (x₁ : X₁)
           (x₂ : X₂)
  : @pair_2cell
      (_ ,, has_binprod_one_types)
      X₁ X₂ Y₁ Y₂
      f₁ f₂
      g₁ g₂
      p
      q
      (x₁ ,, x₂)
    =
    pathsdirprod
      (p x₁)
      (q x₂).
Proof.
  refine (pathsdirprod_eta _ @ _).
  use paths_pathsdirprod.
  - pose (@pair_2cell_pr1
            (_ ,, has_binprod_one_types)
            X₁ X₂ Y₁ Y₂
            f₁ f₂
            g₁ g₂
            p
            q)
      as r.
    etrans.
    {
      apply (eqtohomot r (x₁ ,, x₂)).
    }
    apply pathscomp0rid.
  - pose (@pair_2cell_pr2
            (_ ,, has_binprod_one_types)
            X₁ X₂ Y₁ Y₂
            f₁ f₂
            g₁ g₂
            p
            q)
      as r.
    etrans.
    {
      apply (eqtohomot r (x₁ ,, x₂)).
    }
    apply pathscomp0rid.
Qed.

Definition is_cartesian_closed_one_types
  : is_cartesian_closed_bicat (_ ,, has_binprod_one_types).
Proof.
  use make_is_cartesian_closed_bicat.
  - exact one_types_is_univalent_2_1.
  - intros X Y.
    exact (HLevel_fun X Y).
  - exact (λ X Y fx, app_fun fx).
  - exact (λ X Y₁ Y₂ f g p, app_homot p).
  - abstract
      (simpl ; intros X Y₁ Y₂ f g p ;
       cbn in p ;
       unfold homotsec in p ;
       cbn -[pair_2cell] ;
       unfold homotfun ;
       use funextsec ;
       intro yx ;
       etrans ;
       [ apply maponpaths ;
         exact (@one_types_pair_2cell
                  Y₁ X (HLevel_fun X Y₂) X
                  f g (idfun X) (idfun X)
                  (app_homot p) (homotrefl _)
                  (pr1 yx) (pr2 yx))
       | ] ;
       rewrite maponpaths_app_fun ;
       etrans ;
       [ do 2 apply maponpaths ;
         apply maponpaths_pr2_pathsdirprod
       | ] ;
       etrans ;
       [ apply maponpaths_2 ;
         apply maponpaths ;
         apply maponpaths_pr1_pathsdirprod
       | ] ;
       cbn ;
       rewrite pathscomp0rid ;
       apply maponpaths_app_homot).
  - abstract
      (simpl ; intros X Y₁ Y₂ f g p q₁ q₂ r₁ r₂ ;
       simpl in r₁ ;
       use funextsec ;
       intro y ;
       use path_path_fun ;
       intro x ;
       refine (_ @ eqtohomot r₁ (y ,, x) @ !(eqtohomot r₂ (y ,, x)) @ _) ;
       [ cbn -[pair_2cell] ;
         unfold homotfun, homotrefl ;
         rewrite one_types_pair_2cell ;
         rewrite maponpaths_app_fun ;
         refine (!_) ;
         etrans ;
         [ do 2 apply maponpaths ;
           apply maponpaths_pr2_pathsdirprod
         | ] ;
         etrans ;
         [ apply maponpaths_2 ;
           apply maponpaths ;
           apply maponpaths_pr1_pathsdirprod
         | ] ;
         apply pathscomp0rid
       | cbn -[pair_2cell] ;
         unfold homotfun, homotrefl ;
         rewrite one_types_pair_2cell ;
         rewrite maponpaths_app_fun ;
         etrans ;
         [ do 2 apply maponpaths ;
           apply maponpaths_pr2_pathsdirprod
         | ] ;
         etrans ;
         [ apply maponpaths_2 ;
           apply maponpaths ;
           apply maponpaths_pr1_pathsdirprod
         | ] ;
         cbn ;
         apply pathscomp0rid ]).
  - exact (λ X Y₁ Y₂ f y x, f (y ,, x)).
  - simpl ; intros X Y₁ Y₂ f.
    use make_invertible_2cell.
    + apply homotrefl.
    + apply one_type_2cell_iso.
Defined.
