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
      unfold transportb.
      admit.
  Admitted.

  Definition reindex_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact reindex_twosided_disp_cat_data.
    - exact reindex_twosided_disp_cat_axioms.
  Defined.

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
    Admitted.

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
    Admitted.

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

  Definition TODO { A : UU } : A.
  Admitted.

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
    simple refine (_ ,, _).
    - exact (transportb
               (λ z, _ -->[ z ][ _] _)
               (functor_id _ _)
               (transportb
                  (λ z, _ -->[ _ ][ z ] _)
                  (functor_id _ _)
                  (pr1 fg))).
    - apply TODO.
  Defined.

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
    simple refine (_ ,, _).
    - exact (transportf
               (λ z, _ -->[ z ][ _] _)
               (functor_id _ _)
               (transportf
                  (λ z, _ -->[ _ ][ z ] _)
                  (functor_id _ _)
                  (pr1 fg))).
    - apply TODO.
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
    - apply TODO.
    - apply TODO.
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
