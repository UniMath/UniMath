(************************************************************************************

 Techniques for proving displayed univalence

 This file collects techniques for proving displayed univalence of bicategories.

 One way to prove displayed univalence for a displayed bicategory, is by constructing
 a displayed pseudofunctor to another displayed bicategory and showing that the
 action on objects, 1-cells and 2-cells of that pseudofunctor are equivalences. Note
 that this displayed pseudofunctor does not need to live over an isomorphism: it can
 lie over any pseudofunctor.

 Contents
 1. Univalence along displayed pseudofunctors that are isomorphisms
 1.1. Notion of isomorphism for displayed pseudofunctors
 1.2. Invertible 2-cells
 1.3. Local univalence
 1.4. Adjoint equivalences
 1.5. Global univalence

 ************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.Initial.
Require Import UniMath.Bicategories.Core.Examples.Final.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransportLaws.

Local Open Scope cat.

(**
 1. Univalence along displayed pseudofunctors
 *)

(**
 1.1. Notion of isomorphism for displayed pseudofunctors
 *)
Definition disp_psfunctor_iso
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := (∏ (x : B₁), isweq (FF x))
     ×
     (∏ (x y : B₁)
        (f : x --> y)
        (xx : D₁ x)
        (yy : D₁ y),
      isweq (λ (ff : xx -->[ f ] yy), disp_psfunctor_mor _ _ _ FF ff))
     ×
     (∏ (x y : B₁)
        (f g : x --> y)
        (τ : f ==> g)
        (xx : D₁ x) (yy : D₁ y)
        (ff : xx -->[ f ] yy)
        (gg : xx -->[ g ] yy),
      isweq (λ (ττ : ff ==>[ τ ] gg), disp_psfunctor_cell _ _ _ FF ττ)).

Section PseudofunctorIsos.
  Context {B₁ B₂ : bicat}
          {F : psfunctor B₁ B₂}
          {D₁ : disp_bicat B₁}
          {D₂ : disp_bicat B₂}
          {FF : disp_psfunctor D₁ D₂ F}
          (HF : disp_psfunctor_iso FF).

  Definition disp_psfunctor_iso_ob_weq
             (x : B₁)
    : D₁ x ≃ D₂ (F x)
    := make_weq (FF x) (pr1 HF x).

  Definition disp_psfunctor_iso_mor_weq
             {x y : B₁}
             (f : x --> y)
             (xx : D₁ x)
             (yy : D₁ y)
    : xx -->[ f ] yy ≃ FF x xx -->[ # F f ] FF y yy
    := make_weq _ (pr12 HF x y f xx yy).

  Definition disp_psfunctor_iso_cell_weq
             {x y : B₁}
             {f g : x --> y}
             (τ : f ==> g)
             {xx : D₁ x} {yy : D₁ y}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : ff ==>[ τ ] gg
      ≃
      disp_psfunctor_mor D₁ D₂ F FF ff ==>[ ## F τ] disp_psfunctor_mor D₁ D₂ F FF gg
    := make_weq _ (pr22 HF x y f g τ xx yy ff gg).

  Definition disp_psfunctor_iso_invmap_2
             {x y : B₁}
             {f : x --> y}
             {xx : D₁ x}
             {yy : D₁ y}
             {ff gg : xx -->[ f ] yy}
             (ττ : disp_psfunctor_mor D₁ D₂ F FF ff
                   ==>[ ## F (id2 f)]
                   disp_psfunctor_mor D₁ D₂ F FF gg)
    : ff ==>[ id2 f ] gg
    := invmap (disp_psfunctor_iso_cell_weq (id2 f) ff gg) ττ.

  Proposition disp_psfunctor_iso_invmap_2_eq_1
              {x y : B₁}
              {f : x --> y}
              {xx : D₁ x}
              {yy : D₁ y}
              {ff gg : xx -->[ f ] yy}
              (ττ : disp_psfunctor_mor D₁ D₂ F FF ff
                    ==>[ ## F (id2 f)]
                    disp_psfunctor_mor D₁ D₂ F FF gg)
    : disp_psfunctor_cell _ _ _ FF (disp_psfunctor_iso_invmap_2 ττ) = ττ.
  Proof.
    apply (homotweqinvweq (disp_psfunctor_iso_cell_weq (id2 f) ff gg)).
  Qed.

  Proposition disp_psfunctor_iso_invmap_2_eq_2
              {x y : B₁}
              {f : x --> y}
              {xx : D₁ x}
              {yy : D₁ y}
              {ff gg : xx -->[ f ] yy}
              (ττ : ff ==>[ id2 f ] gg)
    : disp_psfunctor_iso_invmap_2 (disp_psfunctor_cell _ _ _ FF ττ) = ττ.
  Proof.
    apply (homotinvweqweq (disp_psfunctor_iso_cell_weq (id2 f) ff gg)).
  Qed.

  Proposition disp_psfunctor_iso_invmap_2_id2
              {x y : B₁}
              {f : x --> y}
              {xx : D₁ x}
              {yy : D₁ y}
              {ff : xx -->[ f ] yy}
              (p : id₂ (# F f) = ## F (id₂ f))
    : disp_psfunctor_iso_invmap_2
        (transportf
           (λ z, _ ==>[ z ] _)
           p
           (disp_id2 (disp_psfunctor_mor D₁ D₂ F FF ff)))
      =
      disp_id2 _.
  Proof.
    refine (_ @ disp_psfunctor_iso_invmap_2_eq_2 (disp_id2 ff)).
    apply maponpaths.
    rewrite (disp_psfunctor_id2 _ _ _ FF (pr2 FF)).
    unfold transportb.
    apply maponpaths_2.
    apply cellset_property.
  Qed.

  Proposition disp_psfunctor_iso_invmap_2_vcomp
              {x y : B₁}
              {f : x --> y}
              {xx : D₁ x}
              {yy : D₁ y}
              {ff gg hh : xx -->[ f ] yy}
              (ττ : disp_psfunctor_mor D₁ D₂ F FF ff
                    ==>[ ## F (id2 f)]
                    disp_psfunctor_mor D₁ D₂ F FF gg)
              (θθ : disp_psfunctor_mor D₁ D₂ F FF gg
                    ==>[ ## F (id2 f)]
                    disp_psfunctor_mor D₁ D₂ F FF hh)
    : disp_psfunctor_iso_invmap_2 ττ •• disp_psfunctor_iso_invmap_2 θθ
      =
      transportb
        (λ z, _ ==>[ z ] _)
        (id2_left _)
        (disp_psfunctor_iso_invmap_2
           (transportb
              (λ z, _ ==>[ z ] _)
              (maponpaths (λ h, ##F h) (!(id2_left _)) @ psfunctor_vcomp F _ _)
              (ττ •• θθ))).
  Proof.
    simple refine (!(transportfbinv
                       (λ z, _ ==>[ z ] _)
                       (!(id2_left _))
                       (disp_psfunctor_iso_invmap_2 ττ •• disp_psfunctor_iso_invmap_2 θθ))
                     @ _).
    unfold transportb.
    apply maponpaths.
    etrans.
    {
      exact (!(disp_psfunctor_iso_invmap_2_eq_2 _)).
    }
    apply maponpaths.
    etrans.
    {
      apply disp_psfunctor_cell_transportf.
    }
    etrans.
    {
      apply maponpaths.
      apply (disp_psfunctor_vcomp2 _ _ _ FF (pr2 FF)).
    }
    unfold transportb.
    rewrite transport_f_f.
    rewrite !disp_psfunctor_iso_invmap_2_eq_1.
    apply maponpaths_2.
    apply cellset_property.
  Qed.

  Section OverId.
    Context (HB₂ : is_univalent_2_1 B₂).

    Definition disp_psfunctor_iso_id_mor_weq
               {x : B₁}
               (xx yy : D₁ x)
      : xx -->[ id₁ x ] yy ≃ FF x xx -->[ id₁ (F x) ] FF x yy.
    Proof.
      refine (_ ∘ disp_psfunctor_iso_mor_weq (id₁ x) xx yy)%weq.
      use weq_iso.
      - refine (λ f, transportb (λ z, _ -->[ z ] _) _ f).
        exact (isotoid_2_1 HB₂ (psfunctor_id F x)).
      - refine (λ f, transportf (λ z, _ -->[ z ] _) _ f).
        exact (isotoid_2_1 HB₂ (psfunctor_id F x)).
      - abstract
          (intro f ; cbn ;
           rewrite transportfbinv ;
           apply idpath).
      - abstract
          (intro f ; cbn ;
           rewrite transportbfinv ;
           apply idpath).
    Defined.

    Definition disp_psfunctor_invmap_1
               {x : B₁}
               {xx yy : D₁ x}
               (f : FF x xx -->[ id₁ (F x) ] FF x yy)
      : xx -->[ id₁ x ] yy.
    Proof.
      exact (invmap (disp_psfunctor_iso_id_mor_weq xx yy) f).
    Defined.

    Definition disp_psfunctor_invmap_1_id_eq
               (HD₂ : disp_univalent_2_1 D₂)
               {x : B₁}
               (xx : D₁ x)
      : disp_psfunctor_invmap_1 (id_disp (FF x xx))
        =
        id_disp xx.
    Proof.
      unfold disp_psfunctor_invmap_1.
      use (invmaponpathsweq (disp_psfunctor_iso_id_mor_weq xx xx)).
      etrans.
      {
        apply homotweqinvweq.
      }
      refine (!_).
      cbn.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        pose (disp_psfunctor_id _ _ _ FF xx) as p.
        rewrite <- (idtoiso_2_1_isotoid_2_1 HB₂ (psfunctor_id F x)) in p.
        exact (disp_isotoid_2_1 _ HD₂ _ _ _ p).
      }
      rewrite transportbfinv.
      apply idpath.
    Qed.

    Definition disp_psfunctor_invmap_1_id
               (HD₂ : disp_univalent_2_1 D₂)
               {x : B₁}
               (xx : D₁ x)
      : disp_invertible_2cell
          (id2_invertible_2cell _)
          (disp_psfunctor_invmap_1 (id_disp (FF x xx)))
          (id_disp xx).
    Proof.
      exact (disp_idtoiso_2_1 _ (idpath _) _ _ (disp_psfunctor_invmap_1_id_eq HD₂ xx)).
    Qed.

    Definition disp_psfunctor_invmap_1_inv2cell_eq
               (HD₂ : disp_univalent_2_1 D₂)
               {x : B₁}
               {xx yy : D₁ x}
               {f g : FF x xx -->[ id₁ (F x) ] FF x yy}
               (τ : disp_invertible_2cell (id2_invertible_2cell _) f g)
      : disp_psfunctor_invmap_1 f = disp_psfunctor_invmap_1 g.
    Proof.
      assert (f = g) as p.
      {
        exact (disp_isotoid_2_1 _ HD₂ (idpath _) f g τ).
      }
      rewrite p.
      apply idpath.
    Qed.

    Definition disp_psfunctor_invmap_1_inv2cell
               (HD₂ : disp_univalent_2_1 D₂)
               {x : B₁}
               {xx yy : D₁ x}
               {f g : FF x xx -->[ id₁ (F x) ] FF x yy}
               (τ : disp_invertible_2cell (id2_invertible_2cell _) f g)
      : disp_invertible_2cell
          (id2_invertible_2cell _)
          (disp_psfunctor_invmap_1 f)
          (disp_psfunctor_invmap_1 g).
    Proof.
      exact (disp_idtoiso_2_1 _ (idpath _) _ _ (disp_psfunctor_invmap_1_inv2cell_eq HD₂ τ)).
    Qed.

    Definition disp_psfunctor_invmap_1_is_inv2cell
               (HD₂ : disp_univalent_2_1 D₂)
               {x : B₁}
               {xx yy : D₁ x}
               {f g : FF x xx -->[ id₁ (F x) ] FF x yy}
               (τ : f ==>[ id2 _ ] g)
               (Hτ : is_disp_invertible_2cell (id2_invertible_2cell _) τ)
      : disp_invertible_2cell
          (id2_invertible_2cell _)
          (disp_psfunctor_invmap_1 f)
          (disp_psfunctor_invmap_1 g).
    Proof.
      exact (disp_psfunctor_invmap_1_inv2cell HD₂ (τ ,, Hτ)).
    Qed.

    Definition disp_psfunctor_invmap_1_comp_eq
               (HB₁ : is_univalent_2_1 B₁)
               (HD₂ : disp_univalent_2_1 D₂)
               {x : B₁}
               {xx yy zz : D₁ x}
               (f : FF x xx -->[ id₁ (F x) ] FF x yy)
               (g : FF x yy -->[ id₁ (F x) ] FF x zz)
      : transportf
          (λ z, _ -->[ z ] _)
          (isotoid_2_1 HB₁ (linvunitor_invertible_2cell (id₁ _)))
          (disp_psfunctor_invmap_1
             (transportf
                (λ z, _ -->[ z ] _)
                (isotoid_2_1 HB₂ (lunitor_invertible_2cell (id₁ _)))
                (f ;; g)%mor_disp))
        =
        (disp_psfunctor_invmap_1 f ;; disp_psfunctor_invmap_1 g)%mor_disp.
    Proof.
      use transportf_transpose_left.
      use (invmaponpathsweq (disp_psfunctor_iso_id_mor_weq xx zz)).
      etrans.
      {
        apply homotweqinvweq.
      }
      cbn -[disp_psfunctor_invmap_1].
      rewrite disp_psfunctor_mor_transportb.
      rewrite transport_b_b.
      refine (!_).
      pose (disp_psfunctor_comp
              _ _ _
              FF
              (disp_psfunctor_invmap_1 f) (disp_psfunctor_invmap_1 g))
        as p.
      rewrite <- (idtoiso_2_1_isotoid_2_1 HB₂ (psfunctor_comp F (id₁ x) (id₁ x))) in p.
      pose (disp_isotoid_2_1 _ HD₂ _ _ _ p) as q.
      rewrite <- q ; clear q.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply (homotweqinvweq (disp_psfunctor_iso_mor_weq _ yy zz)).
        }
        apply maponpaths_2.
        apply (homotweqinvweq (disp_psfunctor_iso_mor_weq _ xx yy)).
      }
      cbn.
      rewrite transportf_postwhisker_1cell.
      rewrite transportf_prewhisker_1cell.
      rewrite !transport_f_f.
      apply maponpaths_2.
      use (invmaponpathsweq (_ ,, HB₂ _ _ _ _)).
      cbn.
      use subtypePath.
      {
        intro.
        apply isaprop_is_invertible_2cell.
      }
      rewrite !idtoiso_2_1_concat.
      cbn.
      rewrite <- idtoiso_2_1_lwhisker.
      rewrite <- idtoiso_2_1_rwhisker.
      rewrite idtoiso_2_1_inv.
      rewrite !idtoiso_2_1_concat.
      cbn -[psfunctor_id psfunctor_comp].
      rewrite (idtoiso_2_1_psfunctor F).
      rewrite !idtoiso_2_1_isotoid_2_1.
      cbn -[psfunctor_id psfunctor_comp].
      rewrite psfunctor_F_lunitor.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite vcomp_rinv.
      rewrite id2_left.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite vcomp_rinv.
      apply id2_right.
    Qed.

    Definition disp_psfunctor_invmap_1_comp
               (HB₁ : is_univalent_2_1 B₁)
               (HD₂ : disp_univalent_2_1 D₂)
               {x : B₁}
               {xx yy zz : D₁ x}
               (f : FF x xx -->[ id₁ (F x) ] FF x yy)
               (g : FF x yy -->[ id₁ (F x) ] FF x zz)
      : disp_invertible_2cell
          (id2_invertible_2cell _)
          (transportf
             (λ z, _ -->[ z ] _)
             (isotoid_2_1 HB₁ (linvunitor_invertible_2cell (id₁ _)))
             (disp_psfunctor_invmap_1
                (transportf
                   (λ z, _ -->[ z ] _)
                   (isotoid_2_1 HB₂ (lunitor_invertible_2cell (id₁ _)))
                   (f ;; g)%mor_disp)))
          (disp_psfunctor_invmap_1 f ;; disp_psfunctor_invmap_1 g).
    Proof.
      exact (disp_idtoiso_2_1 _ (idpath _) _ _ (disp_psfunctor_invmap_1_comp_eq HB₁ HD₂ f g)).
    Qed.
  End OverId.

End PseudofunctorIsos.

Section UnivalenceIso.
  Context {B₁ B₂ : bicat}
          {F : psfunctor B₁ B₂}
          {D₁ : disp_bicat B₁}
          {D₂ : disp_bicat B₂}
          (FF : disp_psfunctor D₁ D₂ F)
          (HF : disp_psfunctor_iso FF).

  (**
   1.2. Invertible 2-cells
   *)
  Section DispInvertibles.
    Context {x y : B₁}
            {f : x --> y}
            {xx : D₁ x}
            {yy : D₁ y}
            (ff gg : xx -->[ f ] yy).

    Definition disp_invertible_2cell_weq_along_iso_left
               (τ : disp_invertible_2cell
                      (id2_invertible_2cell (# F f))
                      (disp_psfunctor_mor _ _ _ FF ff)
                      (disp_psfunctor_mor _ _ _ FF gg))
      : disp_invertible_2cell (id2_invertible_2cell f) ff gg.
    Proof.
      simple refine (_ ,, _ ,, _ ,, _).
      - refine (disp_psfunctor_iso_invmap_2
                  HF
                  (transportb (λ z, _ ==>[ z ] _) _ (pr1 τ))).
        abstract
          (rewrite psfunctor_id2 ;
           apply idpath).
      - refine (disp_psfunctor_iso_invmap_2
                  HF
                  (transportb (λ z, _ ==>[ z ] _) _ (pr12 τ))).
        abstract
          (cbn ;
           rewrite psfunctor_id2 ;
           apply idpath).
      - abstract
          (refine (disp_psfunctor_iso_invmap_2_vcomp _ _ _ @ _) ;
           unfold transportb ;
           rewrite disp_mor_transportf_prewhisker ;
           rewrite disp_mor_transportf_postwhisker ;
           rewrite !transport_f_f ;
           etrans ;
           [ do 3 apply maponpaths ;
             apply (pr2 τ)
           | ] ;
           unfold transportb ;
           rewrite transport_f_f ;
           rewrite disp_psfunctor_iso_invmap_2_id2 ;
           apply maponpaths_2 ;
           apply cellset_property).
      - abstract
          (refine (disp_psfunctor_iso_invmap_2_vcomp _ _ _ @ _) ;
           unfold transportb ;
           rewrite disp_mor_transportf_prewhisker ;
           rewrite disp_mor_transportf_postwhisker ;
           rewrite !transport_f_f ;
           etrans ;
           [ do 3 apply maponpaths ;
             apply (pr2 τ)
           | ] ;
           unfold transportb ;
           rewrite transport_f_f ;
           rewrite disp_psfunctor_iso_invmap_2_id2 ;
           apply maponpaths_2 ;
           apply cellset_property).
    Defined.

    Definition disp_invertible_2cell_weq_along_iso_right
               (τ : disp_invertible_2cell (id2_invertible_2cell f) ff gg)
          : disp_invertible_2cell
              (id2_invertible_2cell (# F f))
              (disp_psfunctor_mor _ _ _ FF ff)
              (disp_psfunctor_mor _ _ _ FF gg).
    Proof.
      simple refine (_ ,, _ ,, _ ,, _).
      - refine (transportb
                  (λ z, _ ==>[ z ] _)
                  _
                  (disp_psfunctor_cell _ _ _ FF (pr1 τ))).
        abstract
          (cbn ;
           rewrite psfunctor_id2 ;
           apply idpath).
      - refine (transportb
                  (λ z, _ ==>[ z ] _)
                  _
                  (disp_psfunctor_cell _ _ _ FF (pr12 τ))).
        abstract
          (cbn ;
           rewrite psfunctor_id2 ;
           apply idpath).
      - abstract
          (cbn ;
           unfold transportb ;
           rewrite disp_mor_transportf_prewhisker ;
           rewrite disp_mor_transportf_postwhisker ;
           rewrite transport_f_f ;
           etrans ;
           [ apply maponpaths ;
             refine (!_) ;
             apply (disp_psfunctor_vcomp2_alt _ _ _ FF (pr2 FF))
           | ] ;
           rewrite transport_f_f ;
           etrans ;
           [ do 2 apply maponpaths ;
             apply (pr2 τ)
           | ] ;
           etrans ;
           [ apply maponpaths ;
             apply disp_psfunctor_cell_transportb
           | ] ;
           unfold transportb ;
           rewrite transport_f_f ;
           rewrite (disp_psfunctor_id2 _ _ _ FF (pr2 FF)) ;
           unfold transportb ;
           rewrite transport_f_f ;
           apply maponpaths_2 ;
           apply cellset_property).
      - abstract
          (cbn ;
           unfold transportb ;
           rewrite disp_mor_transportf_prewhisker ;
           rewrite disp_mor_transportf_postwhisker ;
           rewrite transport_f_f ;
           etrans ;
           [ apply maponpaths ;
             refine (!_) ;
             apply (disp_psfunctor_vcomp2_alt _ _ _ FF (pr2 FF))
           | ] ;
           rewrite transport_f_f ;
           etrans ;
           [ do 2 apply maponpaths ;
             apply (pr2 τ)
           | ] ;
           etrans ;
           [ apply maponpaths ;
             apply disp_psfunctor_cell_transportb
           | ] ;
           unfold transportb ;
           rewrite transport_f_f ;
           rewrite (disp_psfunctor_id2 _ _ _ FF (pr2 FF)) ;
           unfold transportb ;
           rewrite transport_f_f ;
           apply maponpaths_2 ;
           apply cellset_property).
    Defined.

    Definition disp_invertible_2cell_along_iso_weq
      : disp_invertible_2cell
          (id2_invertible_2cell (# F f))
          (disp_psfunctor_mor _ _ _ FF ff)
          (disp_psfunctor_mor _ _ _ FF gg)
        ≃
        disp_invertible_2cell (id2_invertible_2cell f) ff gg.
    Proof.
      use weq_iso.
      - exact disp_invertible_2cell_weq_along_iso_left.
      - exact disp_invertible_2cell_weq_along_iso_right.
      - abstract
          (intros τ ;
           use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
           cbn ;
           rewrite disp_psfunctor_iso_invmap_2_eq_1 ;
           rewrite transport_b_b ;
           unfold transportb ;
           refine (_ @ idpath_transportf (λ z, _ ==>[ z ] _) _) ;
           apply maponpaths_2 ;
           apply cellset_property).
      - abstract
          (intros τ ;
           use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
           cbn ;
           rewrite transport_b_b ;
           refine (_ @ disp_psfunctor_iso_invmap_2_eq_2 HF τ) ;
           apply maponpaths ;
           unfold transportb ;
           refine (_ @ idpath_transportf (λ z, _ ==>[ z ] _) _) ;
           apply maponpaths_2 ;
           apply cellset_property).
    Defined.
  End DispInvertibles.

  (**
   1.3. Local univalence
   *)
  Context (HD₂ : disp_univalent_2_1 D₂).

  Definition disp_univalent_2_1_along_iso
    : disp_univalent_2_1 D₁.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros x y f xx yy ff gg.
    use weqhomot.
    - exact (disp_invertible_2cell_along_iso_weq ff gg
             ∘ make_weq _ (HD₂ _ _ _ _ (idpath (#F f)) (FF x xx) (FF y yy) _ _)
             ∘ make_weq
                 _
                 (isweqonpathsincl
                    _
                    (isinclweq
                       _ _ _
                       (pr2 (disp_psfunctor_iso_mor_weq HF f xx yy)))
                    ff gg))%weq.
    - abstract
        (intro p ; cbn in p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
         cbn ;
         refine (_ @ disp_psfunctor_iso_invmap_2_eq_2 HF _) ;
         apply maponpaths ;
         rewrite (disp_psfunctor_id2 _ _ _ FF (pr2 FF)) ;
         apply maponpaths_2 ;
         apply cellset_property).
  Defined.

  (**
   1.4. Adjoint equivalences
   *)
  Context (HB₁ : is_univalent_2_1 B₁)
          (HB₂ : is_univalent_2_1 B₂).

  Section DispAdjEquivs.
    Context {x : B₁}
            (xx yy : D₁ x).

    Definition disp_adjequiv_along_iso_weq_left_equiv
               (ff : disp_adjoint_equivalence
                       (internal_adjoint_equivalence_identity (F x))
                       (FF x xx) (FF x yy))
      : disp_left_equivalence
          (internal_adjoint_equivalence_identity x)
          (disp_psfunctor_invmap_1 HF HB₂ (pr1 ff)).
    Proof.
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      - exact (disp_psfunctor_invmap_1 HF HB₂ (pr112 ff)).
      - simple refine (transportf
                         (λ z, _ ==>[ z ] _)
                         _
                         (inverse_of_disp_invertible_2cell
                            (disp_psfunctor_invmap_1_id HF HB₂ HD₂ xx)
                          •• disp_psfunctor_invmap_1_is_inv2cell
                               HF HB₂ HD₂
                               (transportf
                                  (λ z, _ ==>[ z ] _)
                                  _
                                  (pr1 (pr212 ff)
                                   •• transportf_disp_2cell
                                        (pr1 ff ;; pr112 ff)%mor_disp
                                        _))
                               _
                          •• transportf_disp_2cell _ _
                          •• disp_psfunctor_invmap_1_comp HF HB₂ HB₁ HD₂ _ _)).
        + abstract
            (cbn ;
             rewrite idtoiso_2_1_isotoid_2_1 ;
             rewrite !id2_left, !id2_right ;
             apply idpath).
        + abstract
            (cbn ;
             rewrite idtoiso_2_1_isotoid_2_1 ;
             apply linvunitor_lunitor).
        + use transportf_is_disp_invertible_2cell.
          * cbn.
            is_iso.
            apply property_from_invertible_2cell.
          * pose (pr1 (pr212 ff) ,, pr1 (pr222 ff)
                     : disp_invertible_2cell
                         (left_equivalence_unit_iso (internal_adjoint_equivalence_identity _))
                         (id_disp _)
                         (pr1 ff ;; pr112 ff))
              as p.
            exact (pr2 (vcomp_disp_invertible
                          p
                          (transportf_disp_2cell _ _))).
      - simpl.
        simple refine (transportf
                         (λ z, _ ==>[ z ] _)
                         _
                         (inverse_of_disp_invertible_2cell
                            (disp_psfunctor_invmap_1_comp HF HB₂ HB₁ HD₂ _ _)
                          •• inverse_of_disp_invertible_2cell
                               (transportf_disp_2cell _ _)
                          •• disp_psfunctor_invmap_1_is_inv2cell
                               HF HB₂ HD₂
                               (transportf
                                  (λ z, _ ==>[ z ] _)
                                  _
                                  (inverse_of_disp_invertible_2cell
                                     (transportf_disp_2cell _ _)
                                   •• pr2 (pr212 ff)))
                               _
                          •• disp_psfunctor_invmap_1_id HF HB₂ HD₂ yy)).
        + abstract
            (cbn ;
             rewrite id2_left, !id2_right ;
             rewrite idtoiso_2_1_isotoid_2_1 ; cbn ;
             apply idpath).
        + abstract
            (cbn ;
             rewrite idtoiso_2_1_isotoid_2_1 ; cbn ;
             apply linvunitor_lunitor).
        + use transportf_is_disp_invertible_2cell.
          * cbn.
            is_iso.
          * pose (pr2 (pr212 ff) ,, pr2 (pr222 ff)
                 : disp_invertible_2cell
                     (left_equivalence_counit_iso (internal_adjoint_equivalence_identity _))
                     (pr112 ff ;; pr1 ff)
                     (id_disp _))
              as p.
            exact (pr2 (vcomp_disp_invertible
                          (inverse_of_disp_invertible_2cell
                             (transportf_disp_2cell _ _))
                          p)).
      - simpl.
        use transportf_is_disp_invertible_2cell.
        + is_iso.
          apply property_from_invertible_2cell.
        + exact (pr2 (vcomp_disp_invertible
                        (vcomp_disp_invertible
                           (vcomp_disp_invertible
                              (inverse_of_disp_invertible_2cell
                                 (disp_psfunctor_invmap_1_id HF HB₂ HD₂ xx))
                              (disp_psfunctor_invmap_1_is_inv2cell _ _ _ _ _))
                           (transportf_disp_2cell _ _))
                        (disp_psfunctor_invmap_1_comp HF HB₂ HB₁ HD₂ _ _))).
      - simpl.
        use transportf_is_disp_invertible_2cell.
        + is_iso.
        + exact (pr2 (vcomp_disp_invertible
                        (vcomp_disp_invertible
                           (vcomp_disp_invertible
                              (inverse_of_disp_invertible_2cell
                                 (disp_psfunctor_invmap_1_comp HF HB₂ HB₁ HD₂ _ _))
                              (inverse_of_disp_invertible_2cell
                                 (transportf_disp_2cell _ _)))
                           (disp_psfunctor_invmap_1_is_inv2cell _ _ _ _ _))
                        (disp_psfunctor_invmap_1_id HF HB₂ HD₂ yy))).
    Qed.

    Definition disp_adjequiv_along_iso_weq_left
               (ff : disp_adjoint_equivalence
                       (internal_adjoint_equivalence_identity (F x))
                       (FF x xx) (FF x yy))
      : disp_adjoint_equivalence
          (internal_adjoint_equivalence_identity x)
          xx yy.
    Proof.
      simple refine (_ ,, _).
      - exact (disp_psfunctor_invmap_1 HF HB₂ (pr1 ff)).
      - use (disp_left_equivalence_to_left_adjoint_equivalence_over_id HB₁).
        exact (disp_adjequiv_along_iso_weq_left_equiv ff).
    Defined.

    Definition disp_adjequiv_along_iso_weq_right_equiv
               (ff : disp_adjoint_equivalence
                       (internal_adjoint_equivalence_identity x)
                       xx yy)
      : disp_left_equivalence
          (internal_adjoint_equivalence_identity (F x))
          (disp_psfunctor_iso_id_mor_weq HF HB₂ xx yy (pr1 ff)).
    Proof.
      simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
      - exact (disp_psfunctor_iso_id_mor_weq HF HB₂ _ _ (pr112 ff)).
      - refine (transportf
                  (λ z, _ ==>[ z ] _)
                  _
                  (disp_psfunctor_id _ _ _ FF xx
                   •• disp_psfunctor_cell _ _ _ FF (pr1 (pr212 ff))
                   •• pr12 (disp_psfunctor_comp _ _ _ FF (pr1 ff) (pr112 ff))
                   •• (_ ◃◃ transportf_disp_2cell _ _)
                   •• (transportf_disp_2cell _ _ ▹▹ _))).
        abstract
          (cbn -[psfunctor_id psfunctor_comp] ;
           rewrite idtoiso_2_1_inv ;
           rewrite !idtoiso_2_1_isotoid_2_1 ;
           rewrite psfunctor_linvunitor ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)) ;
           rewrite vcomp_rinv ;
           rewrite id2_left ;
           rewrite <- vcomp_whisker ;
           rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
           rewrite rwhisker_vcomp ;
           cbn -[psfunctor_id psfunctor_comp] ;
           rewrite vcomp_rinv ;
           rewrite id2_rwhisker ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite linvunitor_natural ;
           rewrite <- lwhisker_hcomp ;
           rewrite !vassocl ;
           rewrite lwhisker_vcomp ;
           rewrite vcomp_rinv ;
           rewrite lwhisker_id2 ;
           apply id2_right).
      - cbn.
        refine (transportf
                  (λ z, _ ==>[ z ] _)
                  _
                  ((_ ◃◃ pr12 (transportf_disp_2cell _ _))
                   •• (pr12 (transportf_disp_2cell _ _) ▹▹ _)
                   •• disp_psfunctor_comp _ _ _ FF (pr112 ff) (pr1 ff)
                   •• disp_psfunctor_cell _ _ _ FF (pr2 (pr212 ff))
                   •• pr12 (disp_psfunctor_id _ _ _ FF yy))).
        abstract
          (cbn -[psfunctor_id psfunctor_comp] ;
           rewrite idtoiso_2_1_inv ;
           rewrite !idtoiso_2_1_isotoid_2_1 ;
           rewrite psfunctor_F_lunitor ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
           rewrite vcomp_rinv ;
           rewrite id2_left ;
           cbn -[psfunctor_id psfunctor_comp] ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite rwhisker_vcomp ;
           rewrite vcomp_rinv ;
           rewrite id2_rwhisker ;
           rewrite id2_left ;
           rewrite !vassocr ;
           rewrite vcomp_lunitor ;
           rewrite !vassocl ;
           rewrite vcomp_rinv ;
           apply id2_right).
      - cbn -[psfunctor_id psfunctor_comp].
        use transportf_is_disp_invertible_2cell.
        + is_iso.
          * apply property_from_invertible_2cell.
          * exact (psfunctor_is_iso F (linvunitor_invertible_2cell _)).
          * apply property_from_invertible_2cell.
          * apply property_from_invertible_2cell.
        + pose (pr1 (pr212 ff) ,, pr1 (pr222 ff)
                  : disp_invertible_2cell
                      (left_equivalence_unit_iso (internal_adjoint_equivalence_identity x))
                      (id_disp xx)
                      (pr1 ff ;; pr112 ff))
            as p.
          exact (pr2 (vcomp_disp_invertible
                        (vcomp_disp_invertible
                           (vcomp_disp_invertible
                              (vcomp_disp_invertible
                                 (disp_psfunctor_id _ _ _ FF xx)
                                 (disp_psfunctor_invertible_2cell FF p))
                              (inverse_of_disp_invertible_2cell
                                 (disp_psfunctor_comp _ _ _ FF (pr1 ff) (pr112 ff))))
                           (disp_invertible_2cell_lwhisker
                              _
                              (transportf_disp_2cell _ _)))
                        (disp_invertible_2cell_rwhisker
                           _
                           (transportf_disp_2cell _ _)))).
      - cbn -[psfunctor_id psfunctor_comp].
        use transportf_is_disp_invertible_2cell.
        + is_iso.
          * apply property_from_invertible_2cell.
          * exact (psfunctor_is_iso F (lunitor_invertible_2cell _)).
        + cbn.
          pose (pr2 (pr212 ff) ,, pr2 (pr222 ff)
                 : disp_invertible_2cell
                     (left_equivalence_counit_iso (internal_adjoint_equivalence_identity x))
                     (pr112 ff ;; pr1 ff)
                     (id_disp yy))
            as p.
          exact (pr2 (vcomp_disp_invertible
                        (vcomp_disp_invertible
                           (vcomp_disp_invertible
                              (vcomp_disp_invertible
                                 (disp_invertible_2cell_lwhisker
                                    _
                                    (inverse_of_disp_invertible_2cell
                                       (transportf_disp_2cell _ _)))
                                 (disp_invertible_2cell_rwhisker
                                    _
                                    (inverse_of_disp_invertible_2cell
                                       (transportf_disp_2cell _ _))))
                              (disp_psfunctor_comp _ _ _ FF _ _))
                           (disp_psfunctor_invertible_2cell FF p))
                        (inverse_of_disp_invertible_2cell
                           (disp_psfunctor_id D₁ D₂ F FF yy)))).
    Qed.

    Definition disp_adjequiv_along_iso_weq_right
               (ff : disp_adjoint_equivalence
                       (internal_adjoint_equivalence_identity x)
                       xx yy)
      : disp_adjoint_equivalence
          (internal_adjoint_equivalence_identity (F x))
          (FF x xx) (FF x yy).
    Proof.
      simple refine (_ ,, _).
      - exact (disp_psfunctor_iso_id_mor_weq HF HB₂ _ _ (pr1 ff)).
      - use (disp_left_equivalence_to_left_adjoint_equivalence_over_id HB₂).
        exact (disp_adjequiv_along_iso_weq_right_equiv ff).
    Defined.

    Definition disp_adjequiv_along_iso_weq
      : disp_adjoint_equivalence
          (internal_adjoint_equivalence_identity (F x))
          (FF x xx) (FF x yy)
        ≃
        disp_adjoint_equivalence
          (internal_adjoint_equivalence_identity x)
          xx yy.
    Proof.
      use weq_iso.
      - exact disp_adjequiv_along_iso_weq_left.
      - exact disp_adjequiv_along_iso_weq_right.
      - abstract
          (intros f ;
           use subtypePath ;
           [ intro ;
             exact (isaprop_disp_left_adjoint_equivalence
                      _ _
                      HB₂
                      HD₂)
           | ] ;
           cbn -[disp_psfunctor_iso_id_mor_weq disp_psfunctor_invmap_1] ;
           apply homotweqinvweq).
      - abstract
          (intros f ;
           use subtypePath ;
           [ intro ;
             exact (isaprop_disp_left_adjoint_equivalence
                      _ _
                      HB₁
                      disp_univalent_2_1_along_iso)
           | ] ;
           cbn -[disp_psfunctor_iso_id_mor_weq disp_psfunctor_invmap_1] ;
           apply homotinvweqweq).
    Defined.
  End DispAdjEquivs.

  (**
   1.5. Global univalence
   *)
  Definition disp_univalent_2_0_along_iso
             (HD₂' : disp_univalent_2_0 D₂)
    : disp_univalent_2_0 D₁.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x xx yy.
    use weqhomot.
    - exact (disp_adjequiv_along_iso_weq xx yy
             ∘ make_weq _ (HD₂' _ _ (idpath _) _ _)
             ∘ make_weq
                 _
                 (isweqonpathsincl
                    _
                    (isinclweq
                       _ _ _
                       (pr2 (disp_psfunctor_iso_ob_weq HF x)))
                    xx yy))%weq.
    - abstract
        (intro p ;
         cbn in p ;
         induction p ;
         use subtypePath ;
         [ intro ;
           exact (isaprop_disp_left_adjoint_equivalence
                    _ _
                    HB₁
                    disp_univalent_2_1_along_iso)
         | ] ;
         cbn -[disp_psfunctor_iso_id_mor_weq disp_psfunctor_invmap_1] ;
         exact (disp_psfunctor_invmap_1_id_eq HF HB₂ HD₂ xx)).
  Defined.

  Definition disp_univalent_2_along_iso
             (HD₂' : disp_univalent_2_0 D₂)
    : disp_univalent_2 D₁.
  Proof.
    split.
    - exact (disp_univalent_2_0_along_iso HD₂').
    - exact disp_univalent_2_1_along_iso.
  Defined.
End UnivalenceIso.
