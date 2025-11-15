(**

 Reindexing of displayed bicategories

 Suppose that we have a displayed bicategory `D` over a bicategory `B₂` and that we have
 a pseudofunctor `F` from `B₁` to `B₂`. Our goal is to construct a displayed bicategory,
 called the reindexed of `D` along `F`, over `B₁`. This reindexed displayed bicategory
 represents the pullback of `D` along `F`, although this needs to be defined in a suitable
 tricategorical sense.

 There are some subtleties in this definition, and to understand those, let us look at how
 the reindexed is defined.
 - Objects over `x : B₁` are defined to be objects over `F x : B₂` in `D`
 - Morphisms over `f : x --> y` in `B₁` from `xx : D(F x)` to `yy : D(F y)` are defined to
   be morphisms from `xx` to `yy` over `#F f`
 - 2-cells over `τ : F ==> g` in `B₁` from `ff : xx -->[ #F f ] yy` to `gg : xx -->[ #F g ] yy`
   are defined to be 2-cells over `##F τ` from `ff` to `gg` in `D`.
 All of this is similar to how reindexing is defined for displayed categories: objects,
 morphisms, and cells in the reindexed displayed bicategory are defined to be objects,
 morphisms, and cells respectively in the given displayed bicategory over the image under `F`.

 However, the subtlety arises when we try to define the identity morphism. Given an object
 `x : B₁` and `xx : D(F x)`, our goal is to define a morphism `xx -->[ #F (id₁ x) xx ] xx`,
 which would give the identity in the reindexed displayed bicategory. However, the identity
 in the original displayed bicategory lies over `id₁ (F x)` rather than `#F (id₁ x`)`, and
 hence, the identity `disp_id xx` does not give the desired identity, because it lives over
 the incorrect 1-cell in the base. For composition, we meet a similar problem: we need to
 construct a morphism over `#F(f · g)`, whereas composition in the given displayed bicategory
 gives us a morphism over `#F f · #F g`.

 To solve this problem, we need to be able to transport morphisms in the displayed bicategory.
 Since we only assume `F` to be a pseudofunctor rather, we need to be able to transport along
 invertible 2-cells, since we only have invertible 2-cells between `id₁ (F x)` and `#F (id₁ x`),
 and between `#F(f · g)` and `#F f · #F g`. For this reason, we assume that `D` is equipped
 with a local isocleaving. A local isocleaving allows us to do what we want: we can transport
 displayed 1-cells along invertible 2-cells.

 The requirement that a displayed bicategory is equipped with a local isocleaving, is quite
 natural. For instance, if some displayed bicategory lives over a locally univalent bicategory,
 then we can equip it with a local isocleaving. This is because every invertible 2-cell gives
 rise to an identity, and path induction allows us to find the desired lifts. In addition, in
 the construction of the fiber category (see FiberCategory.v), we assume not only that every
 displayed 2-cell with the same source and target are equal and that the displayed bicategory
 is locally univalent, but also that it comes equipped with a local isocleaving. The reason for
 this requirement is exactly the same as what we saw before: local isocleavings allow us to
 transport displayed 1-cells along invertible 2-cells in the base.

 Finally, we also make a simplifying assumption in the construction, namely that all displayed
 2-cells with the same source and target in `D` are equal. The reason is purely to simplify
 the proof of the bicategorical laws.

 Contents
 1. The reindexed displayed bicategory
 2. Invertible 2-cells in the reindexed displayed bicategory
 3. Local univalence
 4. Displayed adjoint equivalences in the reindexed displayed bicategory
 5. Global univalence
 6. Reindexing displayed bicategories over locally univalent bicategories

                                                                                        *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.

Local Open Scope cat.

Section Reindex.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          (D : disp_bicat B₂)
          (HD : local_iso_cleaving D)
          (Dprop : disp_2cells_isaprop D).

  (** * 1. The reindexed displayed bicategory *)
  Definition reindex_disp_cat_ob_mor
    : disp_cat_ob_mor B₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, D (F x)).
    - exact (λ (x y : B₁) (xx : D (F x)) (yy : D (F y)) (f : x --> y),
             xx -->[ #F f ] yy).
  Defined.

  Definition reindex_disp_cat_id_comp
    : disp_cat_id_comp B₁ reindex_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (x : B₁) (xx : D (F x)),
             local_iso_cleaving_1cell
               HD
               (id_disp xx)
               (inv_of_invertible_2cell (psfunctor_id F x))).
    - exact (λ (x y z : B₁)
               (f : x --> y) (g : y --> z)
               (xx : D (F x))
               (yy : D (F y))
               (zz : D (F z))
               (ff : xx -->[ #F f ] yy)
               (gg : yy -->[ #F g ] zz),
             local_iso_cleaving_1cell
               HD
               (ff ;; gg)%mor_disp
               (inv_of_invertible_2cell (psfunctor_comp F f g))).
  Defined.

  Definition reindex_disp_cat_data
    : disp_cat_data B₁.
  Proof.
    simple refine (_ ,, _).
    - exact reindex_disp_cat_ob_mor.
    - exact reindex_disp_cat_id_comp.
  Defined.

  Definition reindex_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B₁.
  Proof.
    simple refine (_ ,, _).
    - exact reindex_disp_cat_data.
    - exact (λ (x y : B₁)
               (f g : x --> y)
               (τ : f ==> g)
               (xx : D (F x))
               (yy : D (F y))
               (ff : xx -->[ #F f ] yy)
               (gg : xx -->[ #F g ] yy),
             ff ==>[ ##F τ ] gg).
  Defined.

  Definition reindex_disp_prebicat_ops
    : disp_prebicat_ops reindex_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - refine (λ (x y : B₁)
                (f : x --> y)
                (xx : D (F x))
                (yy : D (F y))
                (ff : xx -->[ #F f ] yy),
              transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_id2 ff)).
      abstract
        (exact (!(psfunctor_id2 F f))).
    - refine (λ (x y : B₁)
                (f : x --> y)
                (xx : D (F x))
                (yy : D (F y))
                (ff : xx -->[ #F f ] yy),
              transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_local_iso_cleaving_invertible_2cell _ _ _
                 •• (disp_local_iso_cleaving_invertible_2cell _ _ _ ▹▹ _)
                 •• disp_lunitor ff)).
      abstract
        (exact (!(psfunctor_F_lunitor F f))).
    - refine (λ (x y : B₁)
                (f : x --> y)
                (xx : D (F x))
                (yy : D (F y))
                (ff : xx -->[ #F f ] yy),
              transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_local_iso_cleaving_invertible_2cell _ _ _
                 •• (_ ◃◃ disp_local_iso_cleaving_invertible_2cell _ _ _)
                 •• disp_runitor ff)).
      abstract
        (exact (!(psfunctor_F_runitor F f))).
    - refine (λ (x y : B₁)
                (f : x --> y)
                (xx : D (F x))
                (yy : D (F y))
                (ff : xx -->[ #F f ] yy),
              transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_linvunitor ff
                 •• (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _) ▹▹ _)
                 •• disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _))).
      abstract
        (exact (!(psfunctor_linvunitor F f))).
    - refine (λ (x y : B₁)
                (f : x --> y)
                (xx : D (F x))
                (yy : D (F y))
                (ff : xx -->[ #F f ] yy),
              transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_rinvunitor ff
                 •• (_ ◃◃ disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _))
                 •• disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _))).
      abstract
        (exact (!(psfunctor_rinvunitor F f))).
    - refine (λ (w x y z : B₁)
                (f : w --> x)
                (g : x --> y)
                (h : y --> z)
                (ww : D (F w))
                (xx : D (F x))
                (yy : D (F y))
                (zz : D (F z))
                (ff : ww -->[ #F f ] xx)
                (gg : xx -->[ #F g ] yy)
                (hh : yy -->[ #F h ] zz),
              transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_local_iso_cleaving_invertible_2cell _ _ _
                 •• (disp_local_iso_cleaving_invertible_2cell _ _ _ ▹▹ _)
                 •• disp_rassociator ff gg hh
                 •• (_ ◃◃ disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _))
                 •• disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _))).
      abstract
        (cbn -[psfunctor_comp psfunctor_id] ;
         rewrite !vassocl ;
         refine (!_) ;
         use vcomp_move_L_pV ;
         use (vcomp_move_L_pV
                _ _ _
                (rwhisker_of_invertible_2cell (#F h) (psfunctor_comp F f g))) ;
         rewrite !vassocr ;
         exact (psfunctor_rassociator F f g h)).
    - refine (λ (w x y z : B₁)
                (f : w --> x)
                (g : x --> y)
                (h : y --> z)
                (ww : D (F w))
                (xx : D (F x))
                (yy : D (F y))
                (zz : D (F z))
                (ff : ww -->[ #F f ] xx)
                (gg : xx -->[ #F g ] yy)
                (hh : yy -->[ #F h ] zz),
              transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_local_iso_cleaving_invertible_2cell _ _ _
                 •• (_ ◃◃ disp_local_iso_cleaving_invertible_2cell _ _ _)
                 •• disp_lassociator ff gg hh
                 •• (disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _) ▹▹ _)
                 •• disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _))).
      abstract
        (cbn -[psfunctor_comp psfunctor_id] ;
         rewrite !vassocl ;
         refine (!_) ;
         use vcomp_move_L_pV ;
         use (vcomp_move_L_pV
                _ _ _
                (lwhisker_of_invertible_2cell (#F f) (psfunctor_comp F g h))) ;
         rewrite !vassocr ;
         exact (psfunctor_lassociator F f g h)).
    - refine (λ (x y : B₁)
                (f g h : x --> y)
                (τ : f ==> g)
                (θ : g ==> h)
                (xx : D (F x))
                (yy : D (F y))
                (ff : xx -->[ #F f ] yy)
                (gg : xx -->[ #F g ] yy)
                (hh : xx -->[ #F h ] yy)
                (ττ : ff ==>[ ## F τ ] gg)
                (θθ : gg ==>[ ## F θ ] hh),
              transportf
                (λ z, _ ==>[ z ] _)
                _
                (ττ •• θθ)).
      abstract
        (exact (!(psfunctor_vcomp F τ θ))).
    - refine (λ (x y z : B₁)
                (f : x --> y)
                (g₁ g₂ : y --> z)
                (τ : g₁ ==> g₂)
                (xx : D (F x))
                (yy : D (F y))
                (zz : D (F z))
                (ff : xx -->[ #F f ] yy)
                (gg₁ : yy -->[ #F g₁ ] zz)
                (gg₂ : yy -->[ #F g₂ ] zz)
                (ττ : gg₁ ==>[ ## F τ ] gg₂),
               transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_local_iso_cleaving_invertible_2cell _ _ _
                 •• (ff ◃◃ ττ)
                 •• disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _))).
      abstract
        (cbn -[psfunctor_comp] ;
         rewrite !vassocl ;
         refine (!_) ;
         use vcomp_move_L_pV ;
         rewrite psfunctor_lwhisker ;
         apply idpath).
    - refine (λ (x y z : B₁)
                (f₁ f₂ : x --> y)
                (g : y --> z)
                (τ : f₁ ==> f₂)
                (xx : D (F x))
                (yy : D (F y))
                (zz : D (F z))
                (ff₁ : xx -->[ #F f₁ ] yy)
                (ff₂ : xx -->[ #F f₂ ] yy)
                (gg : yy -->[ #F g ] zz)
                (ττ : ff₁ ==>[ ## F τ ] ff₂),
               transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_local_iso_cleaving_invertible_2cell _ _ _
                 •• (ττ ▹▹ gg)
                 •• disp_inv_cell (disp_local_iso_cleaving_invertible_2cell _ _ _))).
      abstract
        (cbn -[psfunctor_comp] ;
         rewrite !vassocl ;
         refine (!_) ;
         use vcomp_move_L_pV ;
         rewrite psfunctor_rwhisker ;
         apply idpath).
  Defined.

  Definition reindex_disp_prebicat_data
    : disp_prebicat_data B₁.
  Proof.
    simple refine (_ ,, _).
    - exact reindex_disp_prebicat_1_id_comp_cells.
    - exact reindex_disp_prebicat_ops.
  Defined.

  Proposition transportf_reindex_disp_bicat
              {x y : B₁}
              {f g : x --> y}
              {τ τ': f ==> g}
              (p : τ = τ')
              {xx : reindex_disp_prebicat_data x}
              {yy : reindex_disp_prebicat_data y}
              {ff : xx -->[ f ] yy}
              {gg : xx -->[ g ] yy}
              (ττ : ff ==>[ τ ] gg)
    : transportf (λ (z : f ==> g), ff ==>[ ##F z ] gg) p ττ
      =
      transportf (λ (z : #F f ==> #F g), _ ==>[ z ] _) (maponpaths (λ z, ##F z) p) ττ.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition reindex_disp_prebicat_laws
    : disp_prebicat_laws reindex_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply Dprop.
  Qed.

  Definition reindex_disp_prebicat
    : disp_prebicat B₁.
  Proof.
    simple refine (_ ,, _).
    - exact reindex_disp_prebicat_data.
    - exact reindex_disp_prebicat_laws.
  Defined.

  Definition reindex_disp_bicat
    : disp_bicat B₁.
  Proof.
    simple refine (_ ,, _).
    - exact reindex_disp_prebicat.
    - abstract
        (intros x y f g τ xx yy ff gg ;
         apply disp_cellset_property).
  Defined.

  Proposition disp_2cells_iscontr_reindex_disp_bicat
              (Dcontr : disp_2cells_iscontr D)
    : disp_2cells_iscontr reindex_disp_bicat.
  Proof.
    intro ; intros.
    apply Dcontr.
  Qed.

  (** * 2. Invertible 2-cells in the reindexed displayed bicategory *)
  Definition to_disp_invertible_2cell_reindex
             {x y : B₁}
             {f : x --> y}
             {xx : reindex_disp_bicat x}
             {yy : reindex_disp_bicat y}
             {ff gg : xx -->[ f ] yy}
             (ττ : disp_invertible_2cell
                     (id2_invertible_2cell (# F f))
                     ff
                     gg)
    : disp_invertible_2cell (id2_invertible_2cell f) ff gg.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (pr1 ττ)).
      abstract
        (cbn ;
         rewrite psfunctor_id2 ;
         apply idpath).
    - refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (pr12 ττ)).
      abstract
        (cbn ;
         rewrite psfunctor_id2 ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite disp_mor_transportf_prewhisker ;
         rewrite disp_mor_transportf_postwhisker ;
         refine (_ @ !(transportf_reindex_disp_bicat _ _)) ;
         rewrite !transport_f_f ;
         refine (maponpaths _ (pr122 ττ) @ _) ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply cellset_property).
    - abstract
        (cbn ;
         rewrite disp_mor_transportf_prewhisker ;
         rewrite disp_mor_transportf_postwhisker ;
         refine (_ @ !(transportf_reindex_disp_bicat _ _)) ;
         rewrite !transport_f_f ;
         refine (maponpaths _ (pr222 ττ) @ _) ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply cellset_property).
  Defined.

  Definition from_disp_invertible_2cell_reindex
             {x y : B₁}
             {f : x --> y}
             {xx : reindex_disp_bicat x}
             {yy : reindex_disp_bicat y}
             {ff gg : xx -->[ f ] yy}
             (ττ : disp_invertible_2cell (id2_invertible_2cell f) ff gg)
    : disp_invertible_2cell
        (id2_invertible_2cell (# F f))
        ff
        gg.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (pr1 ττ : ff ==>[ ##F _ ] gg)).
      abstract
        (cbn ;
         rewrite psfunctor_id2 ;
         apply idpath).
    - refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (pr12 ττ : gg ==>[ ##F _ ] ff)).
      abstract
        (cbn ;
         rewrite psfunctor_id2 ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite disp_mor_transportf_prewhisker ;
         rewrite disp_mor_transportf_postwhisker ;
         rewrite transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           refine (!_ @ maponpaths _ (pr122 ττ)) ;
           apply (transportbfinv (λ z, _ ==>[ z ] _))
         | ] ;
         unfold transportb ;
         cbn ;
         rewrite transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           apply transportf_reindex_disp_bicat
         | ] ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply cellset_property).
    - abstract
        (cbn ;
         rewrite disp_mor_transportf_prewhisker ;
         rewrite disp_mor_transportf_postwhisker ;
         rewrite transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           refine (!_ @ maponpaths _ (pr222 ττ)) ;
           apply (transportbfinv (λ z, _ ==>[ z ] _))
         | ] ;
         unfold transportb ;
         cbn ;
         rewrite transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           apply transportf_reindex_disp_bicat
         | ] ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply cellset_property).
  Defined.

  Definition disp_invertible_2cell_reindex_weq
             {x y : B₁}
             {f : x --> y}
             {xx : reindex_disp_bicat x}
             {yy : reindex_disp_bicat y}
             (ff gg : xx -->[ f ] yy)
    : disp_invertible_2cell (D := D) (id2_invertible_2cell (#F f)) ff gg
      ≃
      disp_invertible_2cell (D := reindex_disp_bicat) (id2_invertible_2cell f) ff gg.
  Proof.
    use weq_iso.
    - apply to_disp_invertible_2cell_reindex.
    - apply from_disp_invertible_2cell_reindex.
    - abstract
        (intro ττ ;
         use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
         cbn ;
         rewrite transport_f_f ;
         use (transportf_set (λ z, _ ==>[ z ] _)) ;
         apply cellset_property).
    - abstract
        (intro ττ ;
         use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
         cbn ;
         rewrite transport_f_f ;
         use (transportf_set (λ z, _ ==>[ z ] _)) ;
         apply cellset_property).
  Defined.

  (** * 3. Local univalence *)
  Proposition disp_univalent_2_1_reindex_disp_bicat
              (univ_D : disp_univalent_2_1 D)
    : disp_univalent_2_1 reindex_disp_bicat.
  Proof.
    use fiberwise_local_univalent_is_univalent_2_1.
    intros x y f xx yy ff gg.
    use weqhomot.
    - exact (disp_invertible_2cell_reindex_weq ff gg
             ∘ make_weq _ (univ_D (F x) (F y) (#F f) (#F f) (idpath _) xx yy ff gg))%weq.
    - intros p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_disp_invertible_2cell.
      }
      cbn in p.
      induction p.
      cbn.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Context (Dgrpd : disp_locally_groupoid D).

  Definition disp_locally_groupoid_reindex
             (HB₁ : is_univalent_2_1 B₁)
    : disp_locally_groupoid reindex_disp_bicat.
  Proof.
    use (make_disp_locally_groupoid_univalent_2_1 _ _ HB₁).
    intros x y f xx yy ff gg ττ.
    cbn in xx, yy, ff, gg, ττ.
    pose (H := Dgrpd
                 (F x) (F y)
                 (#F f) (#F f)
                 (id2_invertible_2cell _)
                 xx yy
                 ff gg
                 (transportf (λ z, _ ==>[ z ] _) (psfunctor_id2 F f) ττ)).
    refine (transportf
              (is_disp_invertible_2cell _)
              _
              (pr2 (to_disp_invertible_2cell_reindex (_ ,, H)))).
    cbn.
    rewrite transport_f_f.
    use (transportf_set (λ z, _ ==>[ z ] _)).
    apply cellset_property.
  Qed.

  (** * 4. Displayed adjoint equivalences in the reindexed displayed bicategory *)
  Section ToAdjEquiv.
    Context (HB₁ : is_univalent_2_1 B₁)
            {x : B₁}
            {xx yy : reindex_disp_bicat x}
            (ττ : disp_adjoint_equivalence
                    (D := D)
                    (internal_adjoint_equivalence_identity (F x))
                    xx yy).

    Definition to_disp_adjoint_equivalence_reindex_mor
      : xx -->[ identity _ ] yy
      := local_iso_cleaving_1cell
           HD
           (pr1 ττ)
           (inv_of_invertible_2cell (psfunctor_id F x)).

    Let ff : (xx : D (F x)) -->[ # F (id₁ x) ] yy
      := to_disp_adjoint_equivalence_reindex_mor.

    Definition to_disp_adjoint_equivalence_reindex_inv
      : yy -->[ identity _ ] xx
      := local_iso_cleaving_1cell
           HD
           (pr112 ττ)
           (inv_of_invertible_2cell (psfunctor_id F x)).

    Let gg : (yy : D (F x)) -->[ # F (id₁ x) ] xx
      := to_disp_adjoint_equivalence_reindex_inv.

    Definition to_disp_adjoint_equivalence_reindex_unit
      : id_disp xx
        ==>[ left_adjoint_unit (internal_adjoint_equivalence_identity x) ]
        to_disp_adjoint_equivalence_reindex_mor ;; to_disp_adjoint_equivalence_reindex_inv.
    Proof.
      refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_local_iso_cleaving_invertible_2cell
                   HD
                   (id_disp (xx : D (F x)))
                   (inv_of_invertible_2cell (psfunctor_id F x))
                 •• pr1 (pr212 ττ)
                 •• (_ ◃◃ disp_inv_cell
                            (disp_local_iso_cleaving_invertible_2cell HD
                               (pr112 ττ)
                               (inv_of_invertible_2cell (psfunctor_id F x))))
                 •• (disp_inv_cell
                       (disp_local_iso_cleaving_invertible_2cell HD
                          (pr1 ττ)
                          (inv_of_invertible_2cell (psfunctor_id F x))) ▹▹ _)
                 •• disp_inv_cell
                      (disp_local_iso_cleaving_invertible_2cell HD
                         (ff ;; gg)
                         (inv_of_invertible_2cell (psfunctor_comp F (id₁ x) (id₁ x)))))).
      cbn -[psfunctor_id psfunctor_comp].
      rewrite psfunctor_linvunitor.
      do 2 apply maponpaths_2.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      apply id2_right.
    Qed.

    Definition to_disp_adjoint_equivalence_reindex_counit
      : to_disp_adjoint_equivalence_reindex_inv ;; to_disp_adjoint_equivalence_reindex_mor
        ==>[ left_adjoint_counit (internal_adjoint_equivalence_identity x) ]
        id_disp yy.
    Proof.
      cbn.
      refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_local_iso_cleaving_invertible_2cell HD
                   (gg ;; ff)
                   (inv_of_invertible_2cell (psfunctor_comp F (id₁ x) (id₁ x)))
                 •• (disp_local_iso_cleaving_invertible_2cell HD
                       (pr112 ττ)
                       (inv_of_invertible_2cell (psfunctor_id F x)) ▹▹ _)
                 •• (_ ◃◃ disp_local_iso_cleaving_invertible_2cell HD
                            (pr1 ττ)
                            (inv_of_invertible_2cell (psfunctor_id F x)))
                 •• pr2 (pr212 ττ)
                 •• disp_inv_cell
                      (disp_local_iso_cleaving_invertible_2cell
                         HD
                         (id_disp (yy : D (F x)))
                         (inv_of_invertible_2cell (psfunctor_id F x))))).
      cbn -[psfunctor_id psfunctor_comp].
      rewrite psfunctor_F_lunitor.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- vcomp_lunitor.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      apply id2_left.
    Qed.

    Definition to_disp_adjoint_equivalence_reindex_data
      : disp_left_adjoint_data
          (internal_adjoint_equivalence_identity x)
          to_disp_adjoint_equivalence_reindex_mor.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact to_disp_adjoint_equivalence_reindex_inv.
      - exact to_disp_adjoint_equivalence_reindex_unit.
      - exact to_disp_adjoint_equivalence_reindex_counit.
    Defined.

    Definition to_disp_adjoint_equivalence_reindex
      : disp_adjoint_equivalence
          (D := reindex_disp_bicat)
          (internal_adjoint_equivalence_identity x)
          xx yy.
    Proof.
      simple refine (_ ,, (_ ,, _ ,, _)).
      - exact to_disp_adjoint_equivalence_reindex_mor.
      - exact to_disp_adjoint_equivalence_reindex_data.
      - abstract
          (split ; apply Dprop).
      - abstract
          (split ; apply (disp_locally_groupoid_reindex HB₁)).
    Defined.
  End ToAdjEquiv.

  Section FromAdjEquiv.
    Context {x : B₁}
            {xx yy : reindex_disp_bicat x}
            (ττ : disp_adjoint_equivalence
                    (D := reindex_disp_bicat)
                    (internal_adjoint_equivalence_identity x)
                    xx yy).

    Definition from_disp_adjoint_equivalence_reindex_mor
      : (xx : D (F x)) -->[ id₁ _ ] yy
      := local_iso_cleaving_1cell
           HD
           (pr1 ττ)
           (psfunctor_id F x).

    Definition from_disp_adjoint_equivalence_reindex_inv
      : (yy : D (F x)) -->[ id₁ _ ] xx
      := local_iso_cleaving_1cell
           HD
           (pr112 ττ)
           (psfunctor_id F x).

    Definition from_disp_adjoint_equivalence_reindex_unit
      : id_disp _
        ==>[ left_adjoint_unit (internal_adjoint_equivalence_identity (F x)) ]
        from_disp_adjoint_equivalence_reindex_mor
        ;; from_disp_adjoint_equivalence_reindex_inv.
    Proof.
      pose (pr1 ττ) as m₁.
      pose (pr112 ττ) as m₂.
      cbn in m₁, m₂.
      refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_inv_cell
                   (disp_local_iso_cleaving_invertible_2cell
                      HD
                      (id_disp (xx : D(F x)))
                      (inv_of_invertible_2cell (psfunctor_id F x)))
                 •• pr1 (pr212 ττ)
                 •• disp_local_iso_cleaving_invertible_2cell
                      HD
                      (m₁ ;; m₂)
                      (inv_of_invertible_2cell (psfunctor_comp F (id₁ x) (id₁ x)))
                 •• (_ ◃◃ disp_inv_cell
                            (disp_local_iso_cleaving_invertible_2cell
                               HD
                               (pr112 ττ)
                               (psfunctor_id F x)))
                 •• (disp_inv_cell
                       (disp_local_iso_cleaving_invertible_2cell
                          HD
                          (pr1 ττ)
                          (psfunctor_id F x)) ▹▹ _))).
      cbn -[psfunctor_id psfunctor_comp].
      rewrite psfunctor_linvunitor.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_rinv.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite id2_rwhisker.
        apply id2_right.
      }
      rewrite !vassocr.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_right.
    Qed.

    Definition from_disp_adjoint_equivalence_reindex_counit
      : from_disp_adjoint_equivalence_reindex_inv
        ;; from_disp_adjoint_equivalence_reindex_mor
        ==>[ left_adjoint_counit (internal_adjoint_equivalence_identity (F x)) ]
        id_disp _.
    Proof.
      pose (pr1 ττ) as m₁.
      pose (pr112 ττ) as m₂.
      cbn in m₁, m₂.
      refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                ((_ ◃◃ disp_local_iso_cleaving_invertible_2cell
                         HD
                         (pr1 ττ)
                         (psfunctor_id F x))
                 •• (disp_local_iso_cleaving_invertible_2cell
                          HD
                          (pr112 ττ)
                          (psfunctor_id F x) ▹▹ _)
                 •• disp_inv_cell
                      (disp_local_iso_cleaving_invertible_2cell
                         HD
                         (m₂ ;; m₁)
                         (inv_of_invertible_2cell (psfunctor_comp F (id₁ x) (id₁ x))))
                 •• pr2 (pr212 ττ)
                 •• disp_local_iso_cleaving_invertible_2cell
                      HD
                      (id_disp (yy : D(F x)))
                      (inv_of_invertible_2cell (psfunctor_id F x)))).
      cbn -[psfunctor_id psfunctor_comp].
      rewrite psfunctor_F_lunitor.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_rinv.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite vcomp_rinv.
      apply id2_right.
    Qed.

    Definition from_disp_adjoint_equivalence_reindex_data
      : disp_left_adjoint_data
          (internal_adjoint_equivalence_identity (F x))
          from_disp_adjoint_equivalence_reindex_mor.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact from_disp_adjoint_equivalence_reindex_inv.
      - exact from_disp_adjoint_equivalence_reindex_unit.
      - exact from_disp_adjoint_equivalence_reindex_counit.
    Defined.

    Definition from_disp_adjoint_equivalence_reindex
      : disp_adjoint_equivalence
          (D := D)
          (internal_adjoint_equivalence_identity (F x))
          xx yy.
    Proof.
      simple refine (_ ,, (_ ,, _ ,, _)).
      - exact from_disp_adjoint_equivalence_reindex_mor.
      - exact from_disp_adjoint_equivalence_reindex_data.
      - abstract (split ; apply Dprop).
      - abstract (split ; apply Dgrpd).
    Defined.
  End FromAdjEquiv.

  Proposition disp_adjoint_equivalence_reindex_weq_left
              (HB₁ : is_univalent_2_1 B₁)
              (HB₂ : is_univalent_2_1 B₂)
              (univ_D_1 : disp_univalent_2_1 D)
              {x : B₁}
              {xx yy : reindex_disp_bicat x}
              (ττ : disp_adjoint_equivalence
                      (D := D)
                      (internal_adjoint_equivalence_identity (F x))
                      xx yy)
    : from_disp_adjoint_equivalence_reindex (to_disp_adjoint_equivalence_reindex HB₁ ττ)
      =
      ττ.
  Proof.
    use subtypePath.
    {
      intro.
      use (isaprop_disp_left_adjoint_equivalence _ _ HB₂).
      exact univ_D_1.
    }
    use (disp_isotoid_2_1 _ univ_D_1 (idpath _)).
    cbn.
    refine (transportf
              (λ z, disp_invertible_2cell z _ _)
              _
              (vcomp_disp_invertible
                 (disp_local_iso_cleaving_invertible_2cell
                    HD
                    (to_disp_adjoint_equivalence_reindex_mor ττ)
                    (psfunctor_id F x))
                 (disp_local_iso_cleaving_invertible_2cell
                    HD
                    (pr1 ττ)
                    (inv_of_invertible_2cell (psfunctor_id F x))))).
    use cell_from_invertible_2cell_eq.
    cbn -[psfunctor_id].
    apply vcomp_rinv.
  Qed.

  Proposition disp_adjoint_equivalence_reindex_weq_right
              (HB₁ : is_univalent_2_1 B₁)
              (HB₂ : is_univalent_2_1 B₂)
              (univ_D_1 : disp_univalent_2_1 D)
              {x : B₁}
              {xx yy : reindex_disp_bicat x}
              (ττ : disp_adjoint_equivalence
                      (internal_adjoint_equivalence_identity x)
                      xx yy)
    : to_disp_adjoint_equivalence_reindex HB₁ (from_disp_adjoint_equivalence_reindex ττ)
      =
      ττ.
  Proof.
    use subtypePath.
    {
      intro.
      use (isaprop_disp_left_adjoint_equivalence _ _ HB₁).
      use disp_univalent_2_1_reindex_disp_bicat.
      exact univ_D_1.
    }
    use (disp_isotoid_2_1 _ univ_D_1 (idpath _)).
    cbn.
    refine (transportf
              (λ z, disp_invertible_2cell z _ _)
              _
              (vcomp_disp_invertible
                 (disp_local_iso_cleaving_invertible_2cell
                    HD
                    (from_disp_adjoint_equivalence_reindex_mor ττ)
                    (inv_of_invertible_2cell (psfunctor_id F x)))
                 (disp_local_iso_cleaving_invertible_2cell
                    HD
                    (pr1 ττ)
                    (psfunctor_id F x)))).
    use cell_from_invertible_2cell_eq.
    cbn -[psfunctor_id].
    apply vcomp_linv.
  Qed.

  Definition disp_adjoint_equivalence_reindex_weq
             (HB₁ : is_univalent_2_1 B₁)
             (HB₂ : is_univalent_2_1 B₂)
             (univ_D_1 : disp_univalent_2_1 D)
             {x : B₁}
             (xx yy : reindex_disp_bicat x)
    : disp_adjoint_equivalence
        (D := D)
        (internal_adjoint_equivalence_identity (F x))
        xx yy
      ≃
      disp_adjoint_equivalence
        (D := reindex_disp_bicat)
        (internal_adjoint_equivalence_identity x)
        xx yy.
  Proof.
    use weq_iso.
    - exact (to_disp_adjoint_equivalence_reindex HB₁).
    - exact from_disp_adjoint_equivalence_reindex.
    - intro ττ.
      exact (disp_adjoint_equivalence_reindex_weq_left HB₁ HB₂ univ_D_1 ττ).
    - intro ττ.
      exact (disp_adjoint_equivalence_reindex_weq_right HB₁ HB₂ univ_D_1 ττ).
  Defined.

  (** * 5. Global univalence *)
  Proposition disp_univalent_2_0_reindex_disp_bicat
              (HB₁ : is_univalent_2_1 B₁)
              (HB₂ : is_univalent_2_1 B₂)
              (univ_D_0 : disp_univalent_2_0 D)
              (univ_D_1 : disp_univalent_2_1 D)
    : disp_univalent_2_0 reindex_disp_bicat.
  Proof.
    use fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x xx yy.
    use weqhomot.
    - exact (disp_adjoint_equivalence_reindex_weq HB₁ HB₂ univ_D_1 xx yy
             ∘ make_weq _ (univ_D_0 (F x) (F x) (idpath _) xx yy))%weq.
    - intro p.
      use subtypePath.
      {
        intro.
        apply (isaprop_disp_left_adjoint_equivalence _ _ HB₁).
        use disp_univalent_2_1_reindex_disp_bicat.
        exact univ_D_1.
      }
      cbn in p.
      induction p.
      apply idpath.
  Qed.

  Proposition disp_univalent_2_reindex_disp_bicat
              (HB₁ : is_univalent_2_1 B₁)
              (HB₂ : is_univalent_2_1 B₂)
              (univ_D_0 : disp_univalent_2_0 D)
              (univ_D_1 : disp_univalent_2_1 D)
    : disp_univalent_2 reindex_disp_bicat.
  Proof.
    split.
    - exact (disp_univalent_2_0_reindex_disp_bicat HB₁ HB₂ univ_D_0 univ_D_1).
    - exact (disp_univalent_2_1_reindex_disp_bicat univ_D_1).
  Qed.
End Reindex.

(** * 6. Reindexing displayed bicategories over locally univalent bicategories *)
Definition reindex_disp_bicat_univ
           {B₁ B₂ : bicat}
           (HB₂ : is_univalent_2_1 B₂)
           (F : psfunctor B₁ B₂)
           (D : disp_bicat B₂)
           (Dprop : disp_2cells_isaprop D)
  : disp_bicat B₁.
Proof.
  refine (reindex_disp_bicat F D _ Dprop).
  use univalent_2_1_to_local_iso_cleaving.
  exact HB₂.
Defined.
