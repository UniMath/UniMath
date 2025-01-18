(**********************************************************************************

 Reindexing two-sided displayed categories

 Suppose, we have a two-sided displayed category `D` over `C₁'` and `C₂'`. Suppose
 that we also have functors `F : C₁ ⟶ C₁'` and `G : C₂ ⟶ C₂'`. Then we can
 construct a two-sided displayed category over `C₁` and `C₂`.

 Contents
 1. Transport lemmas
 2. The definition
 3. Isomorphisms
 4. The univalence
 5. Discreteness

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.

Local Open Scope cat.

Section Reindexing.
  Context {C₁ C₁' C₂ C₂' : category}
          (F : C₁ ⟶ C₁')
          (G : C₂ ⟶ C₂')
          (D : twosided_disp_cat C₁' C₂').

  (**
   1. Transport lemmas
   *)
  Definition twosided_prod_transport_reindex
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D (F x₁) (G y₁)}
             {xy₂ : D (F x₂) (G y₂)}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ g₂ : y₁ --> y₂}
             (fg : xy₁ -->[ #F f₁ ][ #G g₁ ] xy₂)
             (p : f₁ = f₂)
             (q : g₁ = g₂)
    : transportf
        (λ z, _ -->[ #F z ][ _ ] _)
        p
        (transportf
           (λ z, _ -->[ _ ][ #G z ] _)
           q
           fg)
      =
      transportf
        (λ z, _ -->[ pr1 z ][ dirprod_pr2 z ] _)
        (pathsdirprod
           (maponpaths (λ z, #F z) p)
           (maponpaths (λ z, #G z) q))
        fg.
  Proof.
    induction p ; induction q.
    apply idpath.
  Qed.

  Definition twosided_prod_transport_alt
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D (F x₁) (G y₁)}
             {xy₂ : D (F x₂) (G y₂)}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ g₂ : y₁ --> y₂}
             (fg : xy₁ -->[ #F f₁ ][ #G g₁ ] xy₂)
             (p : f₁ = f₂)
             (q : g₁ = g₂)
    : transportf
        (λ z, _ -->[ _ ][ #G z ] _)
        q
        (transportf
           (λ z, _ -->[ #F z ][ _ ] _)
           p
           fg)
      =
      transportf
        (λ z, _ -->[ pr1 z ][ dirprod_pr2 z ] _)
        (pathsdirprod
           (maponpaths (λ z, #F z) p)
           (maponpaths (λ z, #G z) q))
        fg.
  Proof.
    induction p ; induction q.
    apply idpath.
  Qed.

  (**
   2. The definition
   *)
  Definition reindex_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, D (F x) (G y)).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g, xy₁ -->[ #F f ][ #G g ] xy₂).
  Defined.

  Definition reindex_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp reindex_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y xy,
             transportb
               (λ z, _ -->[ z ][ _] _)
               (functor_id _ _)
               (transportb
                  (λ z, _ -->[ _ ][ z ] _)
                  (functor_id _ _)
                  (id_two_disp _))).
    - exact (λ x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ fg₁ fg₂,
             transportb
               (λ z, _ -->[ z ][ _] _)
               (functor_comp _ _ _)
               (transportb
                  (λ z, _ -->[ _ ][ z ] _)
                  (functor_comp _ _ _)
                  (fg₁ ;;2 fg₂))).
  Defined.

  Definition reindex_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact reindex_twosided_disp_cat_ob_mor.
    - exact reindex_twosided_disp_cat_id_comp.
  Defined.

  Definition reindex_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms reindex_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg ; cbn.
      unfold transportb_disp_mor2, transportf_disp_mor2, transportb ; cbn.
      etrans.
      {
        apply twosided_prod_transport.
      }
      etrans.
      {
        apply maponpaths.
        rewrite two_disp_pre_whisker_left.
        rewrite two_disp_pre_whisker_right.
        etrans.
        {
          apply twosided_prod_transport.
        }
        etrans.
        {
          apply maponpaths.
          apply id_two_disp_left.
        }
        unfold transportb.
        apply maponpaths.
        apply twosided_prod_transport.
      }
      rewrite !transport_f_f.
      rewrite twosided_prod_transport_reindex.
      apply maponpaths_2.
      apply isaset_dirprod ; apply homset_property.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg ; cbn.
      unfold transportb_disp_mor2, transportf_disp_mor2, transportb ; cbn.
      etrans.
      {
        apply twosided_prod_transport.
      }
      etrans.
      {
        apply maponpaths.
        rewrite two_disp_post_whisker_left.
        rewrite two_disp_post_whisker_right.
        etrans.
        {
          apply twosided_prod_transport.
        }
        etrans.
        {
          apply maponpaths.
          apply id_two_disp_right.
        }
        unfold transportb.
        apply maponpaths.
        apply twosided_prod_transport.
      }
      rewrite !transport_f_f.
      rewrite twosided_prod_transport_reindex.
      apply maponpaths_2.
      apply isaset_dirprod ; apply homset_property.
    - intros x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ xy₁ xy₂ xy₃ xy₄ f₁ f₂ f₃ g₁ g₂ g₃ fg₁ fg₂ fg₃.
      cbn.
      unfold transportb_disp_mor2, transportf_disp_mor2, transportb ; cbn.
      etrans.
      {
        apply twosided_prod_transport.
      }
      etrans.
      {
        apply maponpaths.
        rewrite two_disp_post_whisker_left.
        rewrite two_disp_post_whisker_right.
        etrans.
        {
          apply twosided_prod_transport.
        }
        etrans.
        {
          apply maponpaths.
          apply assoc_two_disp.
        }
        unfold transportb.
        apply maponpaths.
        apply twosided_prod_transport.
      }
      rewrite !transport_f_f.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply twosided_prod_transport.
        }
        apply maponpaths.
        rewrite two_disp_pre_whisker_left.
        rewrite two_disp_pre_whisker_right.
        apply twosided_prod_transport.
      }
      rewrite !twosided_prod_transport_reindex.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply isaset_dirprod ; apply homset_property.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g.
      apply isaset_disp_mor.
  Qed.

  Definition reindex_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact reindex_twosided_disp_cat_data.
    - exact reindex_twosided_disp_cat_axioms.
  Defined.

  (**
   3. Isomorphisms
   *)
  Section MakeReindexIso.
    Context {x₁ x₂ : C₁}
            {y₁ y₂ : C₂}
            {f : x₁ --> x₂}
            (Hf : is_z_isomorphism f)
            {g : y₁ --> y₂}
            (Hg : is_z_isomorphism g)
            {xy₁ : D (F x₁) (G y₁)}
            {xy₂ : D (F x₂) (G y₂)}
            {fg : xy₁ -->[ #F f ][ #G g ] xy₂}
            (Hfg : is_iso_twosided_disp
                     (functor_on_is_z_isomorphism F Hf)
                     (functor_on_is_z_isomorphism G Hg)
                     fg).

    Definition is_iso_reindex_twosided_disp_cat
      : @is_iso_twosided_disp
           _ _
           reindex_twosided_disp_cat
           _ _ _ _ _ _ _ _
           Hf
           Hg
           fg.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact (iso_inv_twosided_disp Hfg).
      - abstract
          (cbn ; unfold transportb_disp_mor2, transportf_disp_mor2, transportb ; cbn ;
           etrans ; [ apply twosided_prod_transport | ] ;
           etrans ; [ apply maponpaths ; exact (inv_after_iso_twosided_disp Hfg) | ] ;
           etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
           rewrite transport_f_f ;
           refine (!_) ;
           etrans ; [ do 2 apply maponpaths ; apply twosided_prod_transport | ] ;
           etrans ; [ apply twosided_prod_transport_reindex | ] ;
           rewrite transport_f_f ;
           apply maponpaths_2 ;
           apply isaset_dirprod ; apply homset_property).
      - abstract
          (cbn ; unfold transportb_disp_mor2, transportf_disp_mor2, transportb ; cbn ;
           etrans ; [ apply twosided_prod_transport | ] ;
           etrans ; [ apply maponpaths ; exact (iso_after_inv_twosided_disp Hfg) | ] ;
           etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
           rewrite transport_f_f ;
           refine (!_) ;
           etrans ; [ do 2 apply maponpaths ; apply twosided_prod_transport | ] ;
           etrans ; [ apply twosided_prod_transport_reindex | ] ;
           rewrite transport_f_f ;
           apply maponpaths_2 ;
           apply isaset_dirprod ; apply homset_property).
    Defined.

    Definition iso_reindex_twosided_disp_cat
      : @iso_twosided_disp
          _ _
          reindex_twosided_disp_cat
          _ _ _ _
          (f ,, Hf)
          (g ,, Hg)
          xy₁
          xy₂
      := (fg ,, is_iso_reindex_twosided_disp_cat).
  End MakeReindexIso.

  Section FromReindexIso.
    Context {x₁ x₂ : C₁}
            {y₁ y₂ : C₂}
            {f : x₁ --> x₂}
            (Hf : is_z_isomorphism f)
            {g : y₁ --> y₂}
            (Hg : is_z_isomorphism g)
            {xy₁ : D (F x₁) (G y₁)}
            {xy₂ : D (F x₂) (G y₂)}
            {fg : xy₁ -->[ #F f ][ #G g ] xy₂}
            (Hfg : @is_iso_twosided_disp
                      _ _
                      reindex_twosided_disp_cat
                      _ _ _ _ _ _ _ _
                      Hf
                      Hg
                      fg).

    Definition from_is_iso_reindex_twosided_disp_cat
      : is_iso_twosided_disp
          (functor_on_is_z_isomorphism F Hf)
          (functor_on_is_z_isomorphism G Hg)
          fg.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact (iso_inv_twosided_disp Hfg).
      - abstract
          (cbn ; unfold transportb ;
           pose (p := inv_after_iso_twosided_disp Hfg) ;
           cbn in p ;
           rewrite twosided_prod_transportb in p ;
           pose (@transportf_transpose_right
                   _
                   (λ z, _ -->[ pr1 z ][ dirprod_pr2 z ] _)
                   _ _
                   (pathsdirprod _ _)
                   _ _
                   p)
             as p' ;
           refine (p' @ _) ;
           unfold transportb_disp_mor2, transportf_disp_mor2, transportb ; cbn ;
           rewrite twosided_prod_transport_reindex ;
           rewrite !twosided_prod_transport ;
           rewrite !transport_f_f ;
           apply maponpaths_2 ;
           apply isaset_dirprod ; apply homset_property).
      - abstract
          (cbn ; unfold transportb ;
           pose (p := iso_after_inv_twosided_disp Hfg) ;
           cbn in p ;
           rewrite twosided_prod_transportb in p ;
           pose (@transportf_transpose_right
                   _
                   (λ z, _ -->[ pr1 z ][ dirprod_pr2 z ] _)
                   _ _
                   (pathsdirprod _ _)
                   _ _
                   p)
             as p' ;
           refine (p' @ _) ;
           unfold transportb_disp_mor2, transportf_disp_mor2, transportb ; cbn ;
           rewrite twosided_prod_transport_reindex ;
           rewrite !twosided_prod_transport ;
           rewrite !transport_f_f ;
           apply maponpaths_2 ;
           apply isaset_dirprod ; apply homset_property).
    Defined.

    Definition iso_from_is_iso_reindex_twosided_disp_cat
      : @iso_twosided_disp
          _ _
          D
          _ _ _ _
          (#F f ,, functor_on_is_z_isomorphism F Hf)
          (#G g ,, functor_on_is_z_isomorphism G Hg)
          xy₁
          xy₂
      := (fg ,, from_is_iso_reindex_twosided_disp_cat).
  End FromReindexIso.

  Definition iso_weq_reindex_twosided_disp_cat
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : x₁ --> x₂}
             (Hf : is_z_isomorphism f)
             {g : y₁ --> y₂}
             (Hg : is_z_isomorphism g)
             (xy₁ : D (F x₁) (G y₁))
             (xy₂ : D (F x₂) (G y₂))
    : @iso_twosided_disp
         _ _
         D
         _ _ _ _
         (#F f ,, functor_on_is_z_isomorphism F Hf)
         (#G g ,, functor_on_is_z_isomorphism G Hg)
         xy₁
         xy₂
      ≃
      @iso_twosided_disp
         _ _
         reindex_twosided_disp_cat
         _ _ _ _
         (f ,, Hf)
         (g ,, Hg)
         xy₁
         xy₂.
  Proof.
    use weq_iso.
    - exact (λ fg, iso_reindex_twosided_disp_cat Hf Hg (pr2 fg)).
    - exact (λ fg, iso_from_is_iso_reindex_twosided_disp_cat Hf Hg (pr2 fg)).
    - abstract
        (intro fg ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
    - abstract
        (intro fg ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
  Defined.

  Definition is_univalent_reindex_twosided_disp_cat_help_to
             {x₁ : C₁}
             {y₁ : C₂}
             (xy₁ xy₂ : reindex_twosided_disp_cat x₁ y₁)
             (fg : iso_twosided_disp
                     (identity_z_iso (F x₁))
                     (identity_z_iso (G y₁)) xy₁ xy₂)
    : iso_twosided_disp
        (_ ,, functor_on_is_z_isomorphism F (identity_is_z_iso x₁))
        (_ ,, functor_on_is_z_isomorphism G (identity_is_z_iso y₁))
        xy₁ xy₂.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (transportb
               (λ z, _ -->[ z ][ _] _)
               (functor_id _ _)
               (transportb
                  (λ z, _ -->[ _ ][ z ] _)
                  (functor_id _ _)
                  (pr1 fg))).
    - exact (transportb
               (λ z, _ -->[ z ][ _] _)
               (functor_id _ _)
               (transportb
                  (λ z, _ -->[ _ ][ z ] _)
                  (functor_id _ _)
                  (iso_inv_twosided_disp (pr2 fg)))).
    - abstract
        (cbn ;
         unfold transportb ;
         rewrite two_disp_pre_whisker_left ;
         rewrite two_disp_pre_whisker_right ;
         rewrite two_disp_post_whisker_left ;
         rewrite two_disp_post_whisker_right ;
         etrans ; [ apply twosided_prod_transport | ] ;
         etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
         rewrite transport_f_f ;
         etrans ; [ apply maponpaths ;apply (inv_after_iso_twosided_disp (pr2 fg)) | ] ;
         unfold transportb ;
         etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
         rewrite transport_f_f ;
         refine (!_) ;
         etrans ; [ apply twosided_prod_transport | ] ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
    - abstract
        (cbn ;
         unfold transportb ;
         rewrite two_disp_pre_whisker_left ;
         rewrite two_disp_pre_whisker_right ;
         rewrite two_disp_post_whisker_left ;
         rewrite two_disp_post_whisker_right ;
         etrans ; [ apply twosided_prod_transport | ] ;
         etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
         rewrite transport_f_f ;
         etrans ; [ apply maponpaths ;apply (iso_after_inv_twosided_disp (pr2 fg)) | ] ;
         unfold transportb ;
         etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
         rewrite transport_f_f ;
         refine (!_) ;
         etrans ; [ apply twosided_prod_transport | ] ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
  Defined.

  (**
   4. The univalence
   *)
  Definition is_univalent_reindex_twosided_disp_cat_help_from
             {x₁ : C₁}
             {y₁ : C₂}
             (xy₁ xy₂ : reindex_twosided_disp_cat x₁ y₁)
             (fg : iso_twosided_disp
                     (_ ,, functor_on_is_z_isomorphism F (identity_is_z_iso x₁))
                     (_ ,, functor_on_is_z_isomorphism G (identity_is_z_iso y₁))
                     xy₁ xy₂)
    : iso_twosided_disp
        (identity_z_iso (F x₁))
        (identity_z_iso (G y₁))
        xy₁ xy₂.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (transportf
               (λ z, _ -->[ z ][ _] _)
               (functor_id _ _)
               (transportf
                  (λ z, _ -->[ _ ][ z ] _)
                  (functor_id _ _)
                  (pr1 fg))).
    - exact (transportf
               (λ z, _ -->[ z ][ _] _)
               (functor_id _ _)
               (transportf
                  (λ z, _ -->[ _ ][ z ] _)
                  (functor_id _ _)
                  (iso_inv_twosided_disp (pr2 fg)))).
    - abstract
        (cbn ;
         rewrite two_disp_pre_whisker_left ;
         rewrite two_disp_pre_whisker_right ;
         rewrite two_disp_post_whisker_left ;
         rewrite two_disp_post_whisker_right ;
         etrans ; [ apply twosided_prod_transport | ] ;
         etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
         rewrite transport_f_f ;
         etrans ; [ apply maponpaths ;apply (inv_after_iso_twosided_disp (pr2 fg)) | ] ;
         unfold transportb ;
         etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
         rewrite transport_f_f ;
         refine (!_) ;
         etrans ; [ apply twosided_prod_transport | ] ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
    - abstract
        (cbn ;
         unfold transportb ;
         rewrite two_disp_pre_whisker_left ;
         rewrite two_disp_pre_whisker_right ;
         rewrite two_disp_post_whisker_left ;
         rewrite two_disp_post_whisker_right ;
         etrans ; [ apply twosided_prod_transport | ] ;
         etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
         rewrite transport_f_f ;
         etrans ; [ apply maponpaths ;apply (iso_after_inv_twosided_disp (pr2 fg)) | ] ;
         unfold transportb ;
         etrans ; [ apply maponpaths ; apply twosided_prod_transport | ] ;
         rewrite transport_f_f ;
         refine (!_) ;
         etrans ; [ apply twosided_prod_transport | ] ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
  Defined.

  Definition is_univalent_reindex_twosided_disp_cat_help_weq
             {x₁ : C₁}
             {y₁ : C₂}
             (xy₁ xy₂ : reindex_twosided_disp_cat x₁ y₁)
    : iso_twosided_disp (identity_z_iso (F x₁)) (identity_z_iso (G y₁)) xy₁ xy₂
      ≃
      iso_twosided_disp
        (_ ,, functor_on_is_z_isomorphism F (identity_is_z_iso x₁))
        (_ ,, functor_on_is_z_isomorphism G (identity_is_z_iso y₁))
        xy₁ xy₂.
  Proof.
    use weq_iso.
    - exact (is_univalent_reindex_twosided_disp_cat_help_to xy₁ xy₂).
    - exact (is_univalent_reindex_twosided_disp_cat_help_from xy₁ xy₂).
    - abstract
        (intros f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         cbn in * ; unfold transportb ;
         rewrite !twosided_prod_transport ;
         rewrite transport_f_f ;
         refine (_ @ @idpath_transportf
                        _
                        (λ z, xy₁ -->[ pr1 z ][ dirprod_pr2 z ] xy₂)
                        (_ ,, _)
                        (pr1 f)) ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
    - abstract
        (intros f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         cbn in * ; unfold transportb ;
         rewrite !twosided_prod_transport ;
         rewrite transport_f_f ;
         refine (_ @ @idpath_transportf
                        _
                        (λ z, xy₁ -->[ pr1 z ][ dirprod_pr2 z ] xy₂)
                        (_ ,, _)
                        (pr1 f)) ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
  Defined.

  Definition is_univalent_reindex_twosided_disp_cat
             (HD : is_univalent_twosided_disp_cat D)
    : is_univalent_twosided_disp_cat reindex_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p q xy₁ xy₂.
    induction p ; induction q.
    use weqhomot.
    - exact (iso_weq_reindex_twosided_disp_cat _ _ xy₁ xy₂
             ∘ is_univalent_reindex_twosided_disp_cat_help_weq xy₁ xy₂
             ∘ make_weq _ (HD _ _ _ _ (idpath _) (idpath _) xy₁ xy₂))%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
  Defined.

  (**
   5. Discreteness
   *)
  Definition isaprop_disp_twosided_mor_reindex_twosided_disp_cat
             (HD₁ : isaprop_disp_twosided_mor D)
    : isaprop_disp_twosided_mor reindex_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg fg'.
    apply HD₁.
  Qed.

  Definition all_disp_mor_iso_reindex_twosided_disp_cat
             (HD : all_disp_mor_iso D)
    : all_disp_mor_iso reindex_twosided_disp_cat.
  Proof.
    intro ; intros.
    apply is_iso_reindex_twosided_disp_cat.
    apply HD.
  Qed.

  Definition discrete_reindex_twosided_disp_cat
             (HD : discrete_twosided_disp_cat D)
    : discrete_twosided_disp_cat reindex_twosided_disp_cat.
  Proof.
    repeat split.
    - apply isaprop_disp_twosided_mor_reindex_twosided_disp_cat.
      apply HD.
    - apply all_disp_mor_iso_reindex_twosided_disp_cat.
      apply HD.
    - apply is_univalent_reindex_twosided_disp_cat.
      apply HD.
  Defined.
End Reindexing.
