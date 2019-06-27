(* ******************************************************************************* *)
(** The inclusion of pseudofunctors into strict pseudofunctors for locally univalent
bicategories
 ********************************************************************************* *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.StrictIdentitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.StrictCompositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Import PseudoFunctor.Notations.
Import StrictPseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.StrictToPseudo.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.

Local Open Scope cat.

Definition idtoiso_2_1_isotoid_2_1
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {a b : B}
           {f g : a --> b}
           (α : invertible_2cell f g)
  : idtoiso_2_1 _ _ (isotoid_2_1 HB α) = α.
Proof.
  unfold isotoid_2_1.
  exact (homotweqinvweq (make_weq (idtoiso_2_1 f g) (HB _ _ f g)) α).
Defined.

Definition isotoid_2_1_idtoiso_2_1
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {a b : B}
           {f g : a --> b}
           (p : f = g)
  : isotoid_2_1 HB (idtoiso_2_1 _ _ p) = p.
Proof.
  unfold isotoid_2_1.
  exact (homotinvweqweq (make_weq (idtoiso_2_1 f g) (HB _ _ f g)) p).
Defined.

Definition strict_modification_eq
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           {m m' : σ ==> τ}
           (p : ∏ (X : B), pr111 m X = pr111 m' X)
  : m = m'.
Proof.
  use subtypeEquality.
  { intro. simpl.
    exact isapropunit.
  }
  use subtypeEquality.
  { intro. simpl.
    repeat (apply isapropdirprod) ; apply isapropunit.
  }
  use subtypeEquality.
  { intro. simpl.
    repeat (apply impred ; intro).
    apply B'.
  }
  use funextsec.
  exact p.
Qed.

Definition make_strict_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : ∏ (X : B), pr111 σ X ==> pr111 τ X)
           (Hm : ∏ (X Y : B) (f : X --> Y),
                 pr211 σ _ _ f • (m Y ▻ #F f)
                 =
                 #G f ◅ m X • pr211 τ _ _ f)
  : σ ==> τ
  := (((m ,, Hm) ,, (tt ,, tt ,, tt)),, tt).

Definition make_is_invertible_strict_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : σ ==> τ)
           (Hm : ∏ (X : B), is_invertible_2cell (pr111 m X))
  : is_invertible_2cell m.
Proof.
  use make_is_invertible_2cell.
  - use make_strict_modification.
    + exact (λ X, (Hm X)^-1).
    + intros X Y f.
      simpl.
      use vcomp_move_R_Mp.
      { is_iso. }
      simpl.
      rewrite <- vassocr.
      use vcomp_move_L_pM.
      { is_iso. }
      symmetry.
      simpl.
      exact (pr211 m X Y f).
  - use strict_modification_eq.
    intro X.
    cbn.
    exact (vcomp_rinv (Hm X)).
  - use strict_modification_eq.
    intro X.
    cbn.
    exact (vcomp_lid (Hm X)).
Defined.

Section Strictify.
  Variable (B₁ B₂ : bicat)
           (HB₂_2_1 : is_univalent_2_1 B₂).

  Local Arguments idtoiso_2_1 {_} {_} {_} {_} {_} _.
  Local Arguments isotoid_2_1 {_} _ {_} {_} {_} {_} _.

  Definition strictify_ob
    : psfunctor B₁ B₂ → strict_psfunctor_bicat B₁ B₂.
  Proof.
    intros F.
    use make_strict_psfunctor.
    - use make_strict_psfunctor_data.
      + exact (λ X, F X).
      + exact (λ _ _ f, #F f).
      + intros a b f g α ; cbn.
        exact (psfunctor_on_cells F α).
      + intro a ; cbn.
        exact (isotoid_2_1 HB₂_2_1 (psfunctor_id F a)).
      + intros a b c f g; cbn.
        exact (isotoid_2_1 HB₂_2_1 (psfunctor_comp F f g)).
    - repeat split ; try (apply F)
      ; abstract (intro ; intros ; cbn ;
             unfold StrictPseudoFunctorBicat.strict_psfunctor_id_cell,
             StrictPseudoFunctorBicat.strict_psfunctor_comp_cell ;
             cbn ;
             rewrite !idtoiso_2_1_isotoid_2_1 ;
             apply F).
  Defined.

  Definition strictify_mor
             (F G : psfunctor_bicat B₁ B₂)
    : pstrans F G → strictify_ob F --> strictify_ob G.
  Proof.
    intros η.
    use tpair.
    - use tpair.
      + use tpair ; cbn.
        * exact (λ X, η X).
        * exact (λ X Y f, psnaturality_of η f).
      + refine (_ ,, (_ ,, _)).
        * intro ; intros ; cbn.
          apply (psnaturality_natural η).
        * abstract (intro ; intros ; cbn
                    ; unfold StrictPseudoFunctorBicat.strict_psfunctor_id_cell,
                      StrictPseudoFunctorBicat.strict_psfunctor_comp_cell
                    ; cbn
                    ; rewrite !idtoiso_2_1_isotoid_2_1
                    ; apply (pstrans_id η)).
        * abstract (intro ; intros ; cbn
                    ; unfold StrictPseudoFunctorBicat.strict_psfunctor_id_cell,
                      StrictPseudoFunctorBicat.strict_psfunctor_comp_cell
                    ; cbn
                    ; rewrite !idtoiso_2_1_isotoid_2_1
                    ; apply (pstrans_comp η)).
    - exact tt.
  Defined.

  Definition strictify_cell
             (F G : psfunctor_bicat B₁ B₂)
             (η₁ η₂ : pstrans F G)
    : modification η₁ η₂
      →
      (strictify_mor _ _ η₁)
        ==>
        strictify_mor _ _ η₂
    := λ m, m.

  Definition strictify_identitor
             (F : psfunctor B₁ B₂)
    : (id₁ (strictify_ob F))
      ==>
        strictify_mor F F (id₁ F).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (λ X, id₂ _).
        * intros X Y f ; cbn.
          abstract (rewrite lwhisker_id2, id2_rwhisker, id2_left, id2_right
                    ; reflexivity).
      + exact (tt ,, tt ,, tt).
    - exact tt.
  Defined.

  Definition strictify_compositor
             (F₁ F₂ F₃ : psfunctor B₁ B₂)
             (η₁ : F₁ --> F₂)
             (η₂ : F₂ --> F₃)
    : (strictify_mor _ _ η₁)
        · strictify_mor _ _ η₂
        ==>
        strictify_mor _ _ (η₁ · η₂).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (λ X, id₂ _).
        * intros X Y f ; cbn.
          abstract (rewrite lwhisker_id2, id2_rwhisker, id2_left, id2_right
                    ; reflexivity).
      + exact (tt ,, tt ,, tt).
    - exact tt.
  Defined.

  Definition strictify_data
    : psfunctor_data (psfunctor_bicat B₁ B₂) (strict_psfunctor_bicat B₁ B₂).
  Proof.
    use make_psfunctor_data.
    - exact strictify_ob.
    - exact strictify_mor.
    - exact strictify_cell.
    - exact strictify_identitor.
    - exact strictify_compositor.
  Defined.

  Definition strictify_laws
    : psfunctor_laws strictify_data.
  Proof.
    refine (_ ,, (_ ,, (_ ,, (_ ,, (_ ,, (_ ,, _))))))
    ; intro ; intros ; use strict_modification_eq ; intro ; cbn.
    - exact (idpath _).
    - exact (idpath _).
    - rewrite id2_rwhisker, !id2_left.
      exact (idpath _).
    - rewrite lwhisker_id2, !id2_left.
      exact (idpath _).
    - rewrite id2_rwhisker, lwhisker_id2, !id2_right, id2_left.
      exact (idpath _).
    - rewrite id2_left, id2_right.
      exact (idpath _).
    - rewrite id2_left, id2_right.
      exact (idpath _).
  Qed.

  Definition strictify
    : psfunctor (psfunctor_bicat B₁ B₂) (strict_psfunctor_bicat B₁ B₂).
  Proof.
    use make_psfunctor.
    - exact strictify_data.
    - exact strictify_laws.
    - split ; intros ; apply make_is_invertible_strict_modification
      ; intros ; cbn ; is_iso.
  Defined.

  Definition TODO {A : UU} : A.
  Admitted.

  Definition strictify_counit_comp_comp
             (F : psfunctor B₁ B₂)
    : pstrans_data (strict_psfunctor_to_psfunctor_map B₁ B₂ (strictify_ob F)) F.
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - simple refine (λ X Y f, make_invertible_2cell _) ; cbn.
      + exact (lunitor (# F f) • rinvunitor (# F f)).
      + is_iso.
  Defined.

  Definition strictify_counit_comp_is_pstrans
             (F : psfunctor B₁ B₂)
    : is_pstrans (strictify_counit_comp_comp F).
  Proof.
    repeat split.
    - intros X Y f g α ; simpl.
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        rewrite !vassocl.
        rewrite rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      apply idpath.
    - intros X ; simpl.
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        rewrite !vassocl.
        rewrite rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite lunitor_runitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      do 2 apply maponpaths.
      unfold strict_psfunctor_id_cell, strict_psfunctor_id.
      cbn.
      rewrite idtoiso_2_1_isotoid_2_1.
      apply idpath.
    - intros X Y Z f g ; simpl.
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        rewrite !vassocl.
        rewrite rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite <- rwhisker_vcomp.
          rewrite !vassocr.
          rewrite lunitor_triangle.
          apply idpath.
        }
        rewrite !vassocl.
        rewrite rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- lwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite lwhisker_vcomp.
        rewrite !vassocr.
        rewrite linvunitor_lunitor, id2_left.
        apply idpath.
      }
      rewrite rinvunitor_triangle.
      apply maponpaths.
      unfold strict_psfunctor_comp_cell, strict_psfunctor_comp.
      cbn.
      rewrite idtoiso_2_1_isotoid_2_1.
      apply idpath.
  Qed.

  Definition strictify_counit_comp
             (F : psfunctor B₁ B₂)
    : pstrans (strict_psfunctor_to_psfunctor_map B₁ B₂ (strictify_ob F)) F.
  Proof.
    use make_pstrans.
    - exact (strictify_counit_comp_comp F).
    - exact (strictify_counit_comp_is_pstrans F).
  Defined.

  Definition strict_counit_data_help
             (F G : psfunctor B₁ B₂)
             (α : pstrans F G)
             (X Y : B₁)
             (f : X --> Y)
    : (rassociator (id₁ (F X)) ((pr111 α) X) (#G f))
        • (id₁ (F X) ◃ (psnaturality_of α f))
        • (lassociator (id₁ (F X)) (#F f) (α Y))
        • (((lunitor (# F f) • rinvunitor (# F f)) ▹ α Y))
        • (rassociator (# F f) (id₁ (F Y)) (α Y))
        • (# F f ◃ (lunitor (α Y) • rinvunitor (α Y)))
      =
      ((lunitor ((pr111 α) X) • rinvunitor (α X)) ▹ # G f)
        • (rassociator (α X) (id₁ (G X)) (# G f))
        • ((α X ◃ (lunitor (# G f) • rinvunitor (# G f))))
        • (lassociator (α X) (# G f) (id₁ (G Y)))
        • ((psnaturality_of α f ▹ id₁ (G Y)))
        • rassociator (# F f) (α Y) (id₁ (G Y)).
  Proof.
    refine (!_).
    etrans.
    {
      do 4 apply maponpaths_2.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      rewrite !rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- rwhisker_hcomp, <- lwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite vassocl.
      rewrite <- left_unit_inv_assoc.
      apply idpath.
    }
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite lunitor_triangle.
      rewrite rwhisker_hcomp.
      etrans.
      {
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite <- triangle_r_inv.
        rewrite <- lwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor, lwhisker_id2, id2_right.
      apply idpath.
    }
    rewrite vcomp_lunitor.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite <- lunitor_triangle.
    rewrite !vassocr.
    rewrite rassociator_lassociator.
    apply id2_left.
  Qed.

  Definition strictify_counit_data
    : pstrans_data
        (ps_comp (strict_psfunctor_to_psfunctor B₁ B₂) strictify)
        (ps_id_functor (psfunctor_bicat B₁ B₂)).
  Proof.
    use make_pstrans_data.
    - exact strictify_counit_comp.
    - intros F G α.
      use make_invertible_modification.
      + intros Z ; cbn.
        use make_invertible_2cell.
        * exact (lunitor _ • rinvunitor _).
        * is_iso.
      + abstract (intros X Y f ; cbn ;
                  rewrite !vassocr ;
                  apply strict_counit_data_help).
  Defined.

  Definition strictify_counit_is_pstrans
    : is_pstrans strictify_counit_data.
  Proof.
     exact TODO.
  Qed.
  (*
    refine (_ ,, (_ ,, _)).
    - intros F₁ F₂ α β m.
      (*
      pose ((pr1 strictify_counit_data F₁ ◃ psfunctor_on_cells (ps_id_functor (psfunctor_bicat B₁ B₂)) m)
              • pr2 strictify_counit_data F₁ F₂ β) as r₁.
      pose (pr2 strictify_counit_data F₁ F₂ α
                • (psfunctor_on_cells (ps_comp (strict_psfunctor_to_psfunctor B₁ B₂) strictify) m
                      ▹ pr1 strictify_counit_data F₂)) as r₂.
      assert UU.
      {
        refine (modification
                  _
                  (pr211 (ps_comp (strict_psfunctor_to_psfunctor B₁ B₂) strictify) F₁ F₂ β)).
        pose (pr1 strictify_counit_data F₁ · # (ps_id_functor (psfunctor_bicat B₁ B₂)) α) as p.
        cbn -[psfunctor_bicat] in p.
      use modification_eq.
      intros X ; cbn.
       *)
      apply TODO.
    - intros F.
      (*use modification_eq.
      intros X ; cbn.
      *)apply TODO.
    - intros.
      (*use modification_eq.
      intros X ; cbn.
       *)
      apply TODO.
  Qed.*)

  Definition strictify_counit
    : pstrans
        (ps_comp (strict_psfunctor_to_psfunctor B₁ B₂) strictify)
        (ps_id_functor _).
  Proof.
    use make_pstrans.
    - exact strictify_counit_data.
    - exact strictify_counit_is_pstrans.
  Defined.

  Definition strictify_counit_inv_data_comp
             (F : psfunctor B₁ B₂)
    : pstrans_data F (strict_psfunctor_to_psfunctor_map B₁ B₂ (strictify_ob F)).
  Proof.
    use make_pstrans_data.
    - exact (λ X, id₁ (F X)).
    - simple refine (λ X Y f, make_invertible_2cell _) ; cbn.
      + exact (lunitor (# F f) • rinvunitor (# F f)).
      + is_iso.
  Defined.

  Definition strictify_counit_inv_data_is_pstrans
             (F : psfunctor B₁ B₂)
    : is_pstrans (strictify_counit_inv_data_comp F).
  Proof.
    repeat split.
    - intros X Y f g α ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        rewrite !vassocl.
        rewrite rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite vassocl.
      apply idpath.
    - intros X ; cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        rewrite !vassocl.
        rewrite rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite vassocl.
      rewrite lunitor_runitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      do 2 apply maponpaths.
      unfold strict_psfunctor_id_cell, strict_psfunctor_id.
      cbn.
      rewrite idtoiso_2_1_isotoid_2_1.
      apply idpath.
    - intros X Y Z f g ; simpl.
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_lunitor.
        rewrite !vassocl.
        rewrite rinvunitor_natural.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite <- rwhisker_vcomp.
          rewrite !vassocr.
          rewrite lunitor_triangle.
          apply idpath.
        }
        rewrite !vassocl.
        rewrite rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- lwhisker_hcomp.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite lwhisker_vcomp.
        rewrite !vassocr.
        rewrite linvunitor_lunitor, id2_left.
        apply idpath.
      }
      rewrite rinvunitor_triangle.
      apply maponpaths.
      unfold strict_psfunctor_comp_cell, strict_psfunctor_comp.
      cbn.
      rewrite idtoiso_2_1_isotoid_2_1.
      apply idpath.
  Qed.

  Definition strictify_counit_inv_data
    : pstrans_data
        (ps_id_functor (psfunctor_bicat B₁ B₂))
        (ps_comp (strict_psfunctor_to_psfunctor B₁ B₂) strictify).
  Proof.
    use make_pstrans_data.
    - intro F.
      use make_pstrans.
      + exact (strictify_counit_inv_data_comp F).
      + exact (strictify_counit_inv_data_is_pstrans F).
    - intros F₁ F₂ α.
      use make_invertible_modification.
      + intros X.
        use make_invertible_2cell ; cbn.
        * exact (lunitor _ • rinvunitor _).
        * is_iso.
      + abstract (intros X Y f ; cbn ;
                  rewrite !vassocr ;
                  apply strict_counit_data_help).
  Defined.

  Definition strictify_counit_inv
    : pstrans
        (ps_id_functor _)
        (ps_comp (strict_psfunctor_to_psfunctor B₁ B₂) strictify).
  Proof.
    use make_pstrans.
    - exact strictify_counit_inv_data.
    - apply TODO.
  Defined.

  Local Definition modifications_help
        (F : functor_data B₁ B₂)
        (X Y : B₁)
        (f : X --> Y)
    : (rassociator (id₁ (F X)) (id₁ (F X)) (#F f))
        • (id₁ (F X) ◃ (lunitor (# F f) • rinvunitor (# F f)))
        • lassociator (id₁ (F X)) (# F f) (id₁ (F Y))
        • ((lunitor (# F f) • rinvunitor (# F f)) ▹ id₁ (F Y))
        • rassociator (#F f) (id₁ (F Y)) (id₁ (F Y))
        • (# F f ◃ lunitor (id₁ (F Y)))
      =
      (lunitor (id₁ (F X)) ▹ # F f)
        • lunitor (#F f)
        • rinvunitor (#F f).
  Proof.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite !vassocl.
    rewrite runitor_lunitor_identity.
    apply maponpaths.
    rewrite !vassocr.
    rewrite rinvunitor_triangle.
    rewrite !vassocl.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    rewrite rinvunitor_runitor, id2_right.
    rewrite rinvunitor_natural.
    rewrite rwhisker_hcomp.
    apply idpath.
  Qed.

  Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

  Definition modification_help_alt
             (F₁ F₂ : functor_data B₁ B₂)
             (α : nat_trans_data F₁ F₂)
             (X : B₁)
    : (rassociator (id₁ (F₁ X)) (id₁ (F₁ X)) (α X))
        • (id₁ (F₁ X) ◃ (lunitor (α X) • rinvunitor (α X)))
        • lassociator (id₁ (F₁ X)) (α X) (id₁ (F₂ X))
        • ((lunitor (α X) • rinvunitor (α X)) ▹ id₁ (F₂ X))
        • rassociator (α X) (id₁ (F₂ X)) (id₁ (F₂ X))
        • (α X ◃ lunitor (id₁ (F₂ X)))
      =
      (lunitor (id₁ (F₁ X)) ▹ α X)
        • lunitor (α X)
        • rinvunitor (α X).
  Proof.
    rewrite !vassocl.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    rewrite rinvunitor_runitor, id2_right.
    refine (!_).
    etrans.
    {
      rewrite rinvunitor_natural, <- rwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    rewrite rinvunitor_triangle.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite lunitor_lwhisker.
    rewrite runitor_lunitor_identity.
    apply idpath.
  Qed.

  Local Definition psfunctor_to_functor_data
        (F : psfunctor B₁ B₂)
    : functor_data B₁ B₂.
  Proof.
    use make_functor_data.
    - exact (λ X, F X).
    - exact (λ _ _ f, #F f).
  Defined.

  Local Definition strict_psfunctor_to_functor_data
        (F : strict_psfunctor B₁ B₂)
    : functor_data B₁ B₂.
  Proof.
    use make_functor_data.
    - exact (λ X, F X).
    - exact (λ _ _ f, #F f).
  Defined.

  Local Definition pstrans_to_nattrans_data
        {F₁ F₂ : psfunctor B₁ B₂}
        (α : pstrans F₁ F₂)
    : nat_trans_data
        (psfunctor_to_functor_data F₁)
        (psfunctor_to_functor_data F₂)
    := λ X, α X.

  Local Definition strict_pstrans_to_nattrans_data
        {F₁ F₂ : strict_psfunctor_bicat B₁ B₂}
        (α : F₁ --> F₂)
    : nat_trans_data
        (strict_psfunctor_to_functor_data F₁)
        (strict_psfunctor_to_functor_data F₂)
    := λ X, pr111 α X.

  Definition strictify_counit_inv_strictify_counit
    : invertible_modification
        (comp_trans
           strictify_counit_inv
           strictify_counit)
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - intros F.
      use make_invertible_modification.
      + intro X ; cbn.
        use make_invertible_2cell.
        * exact (lunitor (id₁ _)).
        * is_iso.
      + abstract (intros X Y f ; cbn ;
                  rewrite !vassocr ;
                  apply (modifications_help (psfunctor_to_functor_data F) X Y f)).
    - abstract (intros F₁ F₂ α ;
                apply modification_eq ;
                intros X ; cbn ;
                rewrite !vassocr ;
                apply (modification_help_alt
                         (psfunctor_to_functor_data F₁)
                         (psfunctor_to_functor_data F₂)
                         (pstrans_to_nattrans_data α))).
  Defined.

  Definition strictify_counit_strictify_counit_inv
    : invertible_modification
        (comp_trans
           strictify_counit
           strictify_counit_inv)
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - intros F.
      use make_invertible_modification.
      + intro X ; cbn.
        use make_invertible_2cell.
        * exact (lunitor (id₁ _)).
        * is_iso.
      + abstract (intros X Y f ; cbn ;
                  rewrite !vassocr ;
                  apply (modifications_help (psfunctor_to_functor_data F) X Y f)).
    - abstract (intros F₁ F₂ α ;
                apply modification_eq ;
                intros X ; cbn ;
                rewrite !vassocr ;
                apply (modification_help_alt
                         (psfunctor_to_functor_data F₁)
                         (psfunctor_to_functor_data F₂)
                         (pstrans_to_nattrans_data α))).
  Defined.

  Definition strictify_unit_data_help1
             (F : strict_psfunctor B₁ B₂)
             (X Y : B₁)
             (f g : B₁ ⟦ X, Y ⟧)
             (α : f ==> g)
    : (id₁ (F X) ◃ ## F α)
        • lunitor (# F g)
        • rinvunitor (# F g)
      =
      (lunitor (# F f) • rinvunitor (# F f))
        • (##F α ▹ id₁ ((pr111 F) Y)).
  Proof.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite rinvunitor_natural.
    rewrite rwhisker_hcomp.
    apply idpath.
  Qed.

  Definition strictify_unit_data_help2
             (F : strict_psfunctor B₁ B₂)
             (X : B₁)
    : (id₁ (F X) ◃ psfunctor_id (strict_psfunctor_to_psfunctor_map B₁ B₂ F) X)
        • lunitor (# F (id₁ X))
        • rinvunitor (# F (id₁ X))
      =
      (runitor (id₁ (F X)) • linvunitor (id₁ (F X)))
        • (idtoiso_2_1 (strict_psfunctor_id F X) ▹ id₁ (F X)).
  Proof.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite rinvunitor_natural.
    rewrite rwhisker_hcomp.
    rewrite lunitor_runitor_identity.
    rewrite lunitor_V_id_is_left_unit_V_id.
    apply idpath.
  Qed.

  Definition strictify_unit_data_help3
             (F : strict_psfunctor B₁ B₂)
             (X Y Z : B₁)
             (f : X --> Y)
             (g : Y --> Z)
    : ((id₁ ((pr111 F) X) ◃ psfunctor_comp (strict_psfunctor_to_psfunctor_map B₁ B₂ F) f g)
         • lunitor (# F (f · g))) • rinvunitor (# F (f · g))
      =
      (lassociator (id₁ ((pr111 F) X)) (# F f) (# F g))
        • ((lunitor (# F f) • rinvunitor (# F f)) ▹ # F g)
        • rassociator (#F f) (id₁ (F Y)) (# F g)
        • (# F f ◃ (lunitor (# F g) • rinvunitor (# F g)))
        • lassociator (#F f) (#F g) (id₁ ((pr111 F) Z))
        • (idtoiso_2_1 ((pr222 (pr1 F)) X Y Z f g) ▹ id₁ ((pr111 F) Z)).
  Proof.
    rewrite vcomp_lunitor.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_triangle.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_r_inv.
    rewrite <- lwhisker_hcomp.
    rewrite lwhisker_vcomp.
    rewrite !vassocr.
    rewrite linvunitor_lunitor, id2_left.
    rewrite rinvunitor_triangle.
    rewrite rinvunitor_natural.
    rewrite rwhisker_hcomp.
    apply idpath.
  Qed.

  Definition strictify_unit_data_help4
             (F₁ F₂ : strict_psfunctor B₁ B₂)
             (α : strict_psfunctor_bicat B₁ B₂ ⟦ F₁ , F₂ ⟧)
             (X Y : B₁)
             (f : X --> Y)
    : (rassociator (id₁ ((pr111 F₁) X)) ((pr111 α) X) (# F₂ f))
        • (id₁ ((pr111 F₁) X) ◃ (pr211 α) X Y f)
        • lassociator (id₁ (F₁ X)) (# F₁ f) ((pr111 α) Y)
        • ((lunitor (# F₁ f) • rinvunitor (# F₁ f)) ▹ (pr111 α) Y)
        • rassociator (#F₁ f) (id₁ (F₁ Y)) ((pr111 α) Y)
        • (# F₁ f ◃ (lunitor ((pr111 α) Y) • rinvunitor ((pr111 α) Y)))
      =
      ((lunitor ((pr111 α) X) • rinvunitor ((pr111 α) X)) ▹ # F₂ f)
        • rassociator ((pr111 α) X) (id₁ (F₂ X)) (# F₂ f)
        • ((pr111 α) X ◃ (lunitor (# F₂ f) • rinvunitor (# F₂ f)))
        • lassociator ((pr111 α) X) ((pr211 F₂) X Y f) (id₁ (F₂ Y))
        • ((pr211 α) X Y f ▹ id₁ ((pr111 F₂) Y))
        • rassociator (#F₁ f) ((pr111 α) Y) (id₁ (F₂ Y)).
  Proof.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            rewrite <- rwhisker_vcomp.
            rewrite !vassocl.
            rewrite !rwhisker_hcomp.
            rewrite <- triangle_r_inv.
            rewrite <- rwhisker_hcomp, <- lwhisker_hcomp.
            apply idpath.
          }
          rewrite !vassocl.
          rewrite lwhisker_vcomp.
          apply maponpaths.
          rewrite !vassocr.
          rewrite linvunitor_lunitor, id2_left.
          apply idpath.
        }
        rewrite !vassocl.
        rewrite rinvunitor_triangle.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite !rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocl.
      rewrite <- left_unit_inv_assoc.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite !vassocl.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    etrans.
    {
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor, id2_right.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      apply idpath.
    }
    apply maponpaths_2.
    use vcomp_move_R_pM.
    { is_iso. }
    rewrite lunitor_triangle.
    apply idpath.
  Qed.

  Definition strictify_unit_data
    : pstrans_data
        (ps_id_functor (strict_psfunctor_bicat B₁ B₂))
        (ps_comp strictify (strict_psfunctor_to_psfunctor B₁ B₂)).
  Proof.
    use make_pstrans_data.
    - intros F.
      simple refine (((_ ,, _)  ,, (_ ,, _ ,, _)) ,, tt).
      + exact (λ X, id₁ (pr111 F X)).
      + intros X Y f ; cbn.
        use make_invertible_2cell.
        * exact (lunitor _ • rinvunitor _).
        * is_iso.
      + abstract (intros X Y f g α ; cbn ;
                  rewrite !vassocr ;
                  apply strictify_unit_data_help1).
      + abstract (intros X ; cbn ;
                  rewrite idtoiso_2_1_isotoid_2_1 ;
                  rewrite !vassocr ;
                  apply strictify_unit_data_help2).
      + abstract (intros X Y Z f g ; cbn ;
                  rewrite idtoiso_2_1_isotoid_2_1 ;
                  rewrite !vassocr ;
                  apply strictify_unit_data_help3).
    - intros F₁ F₂ α.
      use make_invertible_2cell.
      + use make_strict_modification.
        * intros Z ; cbn.
          exact (lunitor _ • rinvunitor _).
        * abstract (intros X Y f ; cbn ;
                    rewrite !vassocr ;
                    apply strictify_unit_data_help4).
      + use make_is_invertible_strict_modification.
        intros X ; cbn.
        is_iso.
  Defined.

  Definition strictify_unit
    : pstrans
        (ps_id_functor _)
        (ps_comp strictify (strict_psfunctor_to_psfunctor B₁ B₂)).
  Proof.
    use make_pstrans.
    - exact strictify_unit_data.
    - apply TODO.
  Defined.

  Definition strictify_unit_inv_data
    : pstrans_data
        (ps_comp strictify (strict_psfunctor_to_psfunctor B₁ B₂))
        (ps_id_functor _).
  Proof.
    use make_pstrans_data.
    - intros F.
      simple refine (((_ ,, _)  ,, (_ ,, _ ,, _)) ,, tt).
      + exact (λ X, id₁ (pr111 F X)).
      + intros X Y f ; cbn.
        use make_invertible_2cell.
        * exact (lunitor _ • rinvunitor _).
        * is_iso.
      + abstract (intros X Y f g α ; cbn ;
                  rewrite !vassocr ;
                  apply strictify_unit_data_help1).
      + abstract (intros X ; cbn ;
                  rewrite idtoiso_2_1_isotoid_2_1 ;
                  rewrite !vassocr ;
                  apply strictify_unit_data_help2).
      + abstract (intros X Y Z f g ; cbn ;
                  rewrite idtoiso_2_1_isotoid_2_1 ;
                  rewrite !vassocr ;
                  apply strictify_unit_data_help3).
    - intros F₁ F₂ α.
      use make_invertible_2cell.
      + use make_strict_modification.
        * intros Z ; cbn.
          exact (lunitor _ • rinvunitor _).
        * abstract (intros X Y f ; cbn ;
                    rewrite !vassocr ;
                    apply strictify_unit_data_help4).
      + use make_is_invertible_strict_modification.
        intros X ; cbn.
        is_iso.
  Defined.

  Definition strictify_unit_inv
    : pstrans
        (ps_comp strictify (strict_psfunctor_to_psfunctor B₁ B₂))
        (ps_id_functor _).
  Proof.
    use make_pstrans.
    - exact strictify_unit_inv_data.
    - apply TODO.
  Defined.

  Definition strictify_unit_strictify_unit_inv
    : invertible_modification
        (comp_trans
           strictify_unit
           strictify_unit_inv)
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - intros F.
      use make_invertible_2cell.
      + use make_strict_modification.
        * intro X ; cbn.
          exact (lunitor (id₁ _)).
        * abstract
            (intros X Y f ; cbn ;
             rewrite !vassocr ;
             apply (modifications_help (strict_psfunctor_to_functor_data F) X Y f)).
      + use make_is_invertible_strict_modification.
        intro X ; cbn.
        is_iso.
    - abstract (intros F₁ F₂ α ;
                apply strict_modification_eq ;
                intros X ; cbn ;
                rewrite !vassocr ;
                apply (modification_help_alt
                         (strict_psfunctor_to_functor_data F₁)
                         (strict_psfunctor_to_functor_data F₂)
                         (strict_pstrans_to_nattrans_data α))).
  Defined.

  Definition strictify_unit_inv_strictify_unit
    : invertible_modification
        (comp_trans
           strictify_unit_inv
           strictify_unit)
        (id_trans _).
  Proof.
    use make_invertible_modification.
    - intros F.
      use make_invertible_2cell.
      + use make_strict_modification.
        * intro X ; cbn.
          exact (lunitor (id₁ _)).
        * abstract
            (intros X Y f ; cbn ;
             rewrite !vassocr ;
             apply (modifications_help (strict_psfunctor_to_functor_data F) X Y f)).
      + use make_is_invertible_strict_modification.
        intro X ; cbn.
        is_iso.
    - abstract (intros F₁ F₂ α ;
                apply strict_modification_eq ;
                intros X ; cbn ;
                rewrite !vassocr ;
                apply (modification_help_alt
                         (strict_psfunctor_to_functor_data F₁)
                         (strict_psfunctor_to_functor_data F₂)
                         (strict_pstrans_to_nattrans_data α))).
  Defined.
End Strictify.
