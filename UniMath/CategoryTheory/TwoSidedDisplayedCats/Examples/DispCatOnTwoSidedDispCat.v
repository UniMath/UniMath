(**********************************************************************************

 Composing a two-sided displayed category with a displayed category

 We show how to compose a two-sided displayed category with a displayed category.
 The idea is basically as follows: a two-sided displayed category represents a
 span and a displayed category represents a functor. Both legs of the span get
 composed with this functor to obtain a new span.

 More precisely, we have a two-sided displayed category and a displayed category
 over the total category of that two-sided displayed category. This displayed
 category represents structures/properties to be added to our two-sided displayed
 category. We then form a new two-sided displayed category by taking sigma-types.

 Contents
 1. The definition
 2. Isomorphisms
 3. Univalence and discreteness

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.

Local Open Scope cat.

Definition transportf_hset_eq
           {X : UU}
           {Y : X → UU}
           (Xisaset : isaset X)
           {x₁ x₂ : X}
           (p q : x₁ = x₂)
           (y : Y x₁)
  : transportf Y p y = transportf Y q y.
Proof.
  apply maponpaths_2.
  apply Xisaset.
Qed.

Section DispCatOnTwoSidedDispCat.
  Context {C₁ C₂ : category}
          (D₁ : twosided_disp_cat C₁ C₂)
          (D₂ : disp_cat (total_twosided_disp_category D₁)).

  (**
   1. The definition
   *)
  Definition sigma_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, ∑ (xy : D₁ x y), D₂ (x ,, y ,, xy)).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g,
             ∑ (fg : pr1 xy₁ -->[ f ][ g ] pr1 xy₂),
             pr2 xy₁ -->[ f ,, g ,, fg ] pr2 xy₂).
  Defined.

  Definition sigma_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp sigma_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - simple refine (λ x y xy, id_two_disp (pr1 xy) ,, _).
      apply (@id_disp (total_twosided_disp_category D₁) D₂).
    - exact (λ x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ fg₁ fg₂,
             pr1 fg₁ ;;2 pr1 fg₂
             ,,
             (pr2 fg₁ ;; pr2 fg₂)%mor_disp).
  Defined.

  Definition sigma_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact sigma_twosided_disp_cat_ob_mor.
    - exact sigma_twosided_disp_cat_id_comp.
  Defined.

  Definition sigma_twosided_disp_cat_mor_eq
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {xy₁ : sigma_twosided_disp_cat_data x₁ y₁}
             {xy₂ : sigma_twosided_disp_cat_data x₂ y₂}
             (fg₁ : xy₁ -->[ f ][ g ] xy₂)
             (fg₂ : xy₁ -->[ f ][ g ] xy₂)
             (p : pr1 fg₁ = pr1 fg₂)
             (q : transportf
                    (λ z, pr2 xy₁ -->[ z ] pr2 xy₂)
                    (maponpaths (λ z, f ,, g ,, z) p)
                    (pr2 fg₁)
                  =
                  pr2 fg₂)
    : fg₁ = fg₂.
  Proof.
    induction fg₁ as [ fg₁ fg₁' ].
    induction fg₂ as [ fg₂ fg₂' ].
    cbn in *.
    induction p.
    cbn in q.
    induction q.
    apply idpath.
  Qed.

  Section SigmaLeft.
    Context {x₁ x₂ : C₁}
            {f : x₁ --> x₂}
            {y₁ y₂ : C₂}
            {g₁ g₂ : y₁ --> y₂}
            (p : g₂ = g₁)
            {xy₁ : sigma_twosided_disp_cat_data x₁ y₁}
            {xy₂ : sigma_twosided_disp_cat_data x₂ y₂}
            (fg : xy₁ -->[ f ][ g₂ ] xy₂).

    Let q₁ : total_twosided_disp_category D₁ := x₁ ,, y₁ ,, pr1 xy₁.
    Let q₂ : total_twosided_disp_category D₁ := x₂ ,, y₂ ,, pr1 xy₂.
    Let h₁ : q₁ --> q₂ := f ,, g₂ ,, pr1 fg.
    Let h₂ : q₁ --> q₂ := f ,, g₁ ,, transportf (λ z, _ -->[ f ][ z ] _) p (pr1 fg).

    Definition sigma_transportf_left_path
      : h₁ = h₂.
    Proof.
      induction p.
      apply idpath.
    Defined.
  End SigmaLeft.

  Definition sigma_transportf_left
             {x₁ x₂ : C₁}
             {f : x₁ --> x₂}
             {y₁ y₂ : C₂}
             {g₁ g₂ : y₁ --> y₂}
             (p : g₂ = g₁)
             {xy₁ : sigma_twosided_disp_cat_data x₁ y₁}
             {xy₂ : sigma_twosided_disp_cat_data x₂ y₂}
             (fg : xy₁ -->[ f ][ g₂ ] xy₂)
    : transportf
        (λ z, xy₁ -->[ f ][ z ] xy₂)
        p
        fg
      =
      transportf
        (λ z, _ -->[ f ][ z ] _)
        p
        (pr1 fg)
      ,,
      transportf
        (λ z, @mor_disp _ D₂ _ _ (pr2 xy₁) (pr2 xy₂) z)
        (sigma_transportf_left_path p fg)
        (pr2 fg).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Section SigmaRight.
    Context {x₁ x₂ : C₁}
            {f₁ f₂ : x₁ --> x₂}
            (p : f₂ = f₁)
            {y₁ y₂ : C₂}
            {g : y₁ --> y₂}
            {xy₁ : sigma_twosided_disp_cat_data x₁ y₁}
            {xy₂ : sigma_twosided_disp_cat_data x₂ y₂}
            (fg : xy₁ -->[ f₂ ][ g ] xy₂).

    Let q₁ : total_twosided_disp_category D₁ := x₁ ,, y₁ ,, pr1 xy₁.
    Let q₂ : total_twosided_disp_category D₁ := x₂ ,, y₂ ,, pr1 xy₂.
    Let h₁ : q₁ --> q₂ := f₂ ,, g ,, pr1 fg.
    Let h₂ : q₁ --> q₂ := f₁ ,, g ,, transportf (λ z, _ -->[ z ][ g ] _) p (pr1 fg).

    Definition sigma_transportf_right_path
      : h₁ = h₂.
    Proof.
      induction p.
      apply idpath.
    Defined.
  End SigmaRight.

  Definition sigma_transportf_right
             {x₁ x₂ : C₁}
             {f₁ f₂ : x₁ --> x₂}
             (p : f₂ = f₁)
             {y₁ y₂ : C₂}
             {g : y₁ --> y₂}
             {xy₁ : sigma_twosided_disp_cat_data x₁ y₁}
             {xy₂ : sigma_twosided_disp_cat_data x₂ y₂}
             (fg : xy₁ -->[ f₂ ][ g ] xy₂)
    : transportf
        (λ z, xy₁ -->[ z ][ g ] xy₂)
        p
        fg
      =
      transportf
        (λ z, _ -->[ z ][ g ] _)
        p
        (pr1 fg)
      ,,
      transportf
        (λ z, @mor_disp _ D₂ _ _ (pr2 xy₁) (pr2 xy₂) z)
        (sigma_transportf_right_path p fg)
        (pr2 fg).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Definition sigma_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms sigma_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg.
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite sigma_transportf_left.
      rewrite sigma_transportf_right.
      use sigma_twosided_disp_cat_mor_eq.
      + apply id_two_disp_left.
      + cbn.
        unfold twosided_disp_cat_ob_mor_to_mor.
        etrans.
        {
          apply maponpaths.
          exact (@id_left_disp _ D₂ _ _ _ _ _ (pr2 fg)).
        }
        unfold transportb.
        rewrite !transport_f_f.
        apply transportf_hset_eq.
        apply (total_twosided_disp_category D₁).
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg.
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite sigma_transportf_left.
      rewrite sigma_transportf_right.
      use sigma_twosided_disp_cat_mor_eq.
      + apply id_two_disp_right.
      + cbn.
        unfold twosided_disp_cat_ob_mor_to_mor.
        etrans.
        {
          apply maponpaths.
          exact (@id_right_disp _ D₂ _ _ _ _ _ (pr2 fg)).
        }
        unfold transportb.
        rewrite !transport_f_f.
        apply transportf_hset_eq.
        apply (total_twosided_disp_category D₁).
    - intros x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ xy₁ xy₂ xy₃ xy₄ f₁ f₂ f₃ g₁ g₂ g₃ fg₁ fg₂ fg₃.
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite sigma_transportf_left.
      rewrite sigma_transportf_right.
      use sigma_twosided_disp_cat_mor_eq.
      + apply assoc_two_disp.
      + cbn.
        unfold twosided_disp_cat_ob_mor_to_mor.
        etrans.
        {
          apply maponpaths.
          apply (@assoc_disp _ D₂ _ _ _ _ _ _ _ _ _ _ _ (pr2 fg₁) (pr2 fg₂) (pr2 fg₃)).
        }
        unfold transportb.
        rewrite !transport_f_f.
        apply transportf_hset_eq.
        apply (total_twosided_disp_category D₁).
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g.
      use isaset_total2.
      + apply isaset_disp_mor.
      + intro.
        apply homsets_disp.
  Qed.

  Definition sigma_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact sigma_twosided_disp_cat_data.
    - exact sigma_twosided_disp_cat_axioms.
  Defined.

  Definition sigma_mor_eq
             {x : C₁}
             {y : C₂}
             {xy : sigma_twosided_disp_cat x y}
             {f : x --> x}
             {g : y --> y}
             {fg₁ fg₂ : xy -->[ f ][ g ] xy}
             (p : fg₁ = fg₂)
    : pr2 fg₁
      =
      transportb
        (λ z, _ -->[ z ] _)
        (maponpaths _ (maponpaths (λ z, _ ,, z) (maponpaths pr1 p)))
        (pr2 fg₂).
  Proof.
    induction p.
    apply idpath.
  Qed.

  (**
   2. Isomorphisms
   *)
  Definition to_iso_sigma_of_twosided_disp_cat
             {x : C₁}
             {y : C₂}
             {xy₁ : sigma_twosided_disp_cat x y}
             {xy₂ : sigma_twosided_disp_cat x y}
             (f : iso_twosided_disp
                    (identity_z_iso x) (identity_z_iso y)
                    (pr1 xy₁) (pr1 xy₂))
             (g : z_iso_disp
                    (make_z_iso_total_twosided_disp_cat _ f)
                    (pr2 xy₁) (pr2 xy₂))
    : @iso_twosided_disp
        _ _
        sigma_twosided_disp_cat
        _ _ _ _
        (identity_z_iso x)
        (identity_z_iso y)
        xy₁
        xy₂.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr1 f ,, pr1 g).
    - exact (pr12 f ,, inv_mor_disp_from_z_iso g).
    - abstract
        (unfold transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite sigma_transportf_left ;
         rewrite sigma_transportf_right ;
         use sigma_twosided_disp_cat_mor_eq ; [ exact (pr122 f) | ] ;
         etrans ;
         [ apply maponpaths ;
           exact (inv_mor_after_z_iso_disp g)
         | ] ;
         unfold transportb ; cbn ;
         rewrite !transport_f_f ;
         apply transportf_hset_eq ;
         apply (total_twosided_disp_category D₁)).
    - abstract
        (unfold transportb_disp_mor2, transportf_disp_mor2 ;
         rewrite sigma_transportf_left ;
         rewrite sigma_transportf_right ;
         use sigma_twosided_disp_cat_mor_eq ; [ exact (pr222 f) | ] ;
         etrans ;
         [ apply maponpaths ;
           exact (z_iso_disp_after_inv_mor g)
         | ] ;
         unfold transportb ; cbn ;
         rewrite !transport_f_f ;
         apply transportf_hset_eq ;
         apply (total_twosided_disp_category D₁)).
  Defined.

  Section FromSigmaIso.
    Context {x : C₁}
            {y : C₂}
            {xy₁ : sigma_twosided_disp_cat x y}
            {xy₂ : sigma_twosided_disp_cat x y}
            (f : @iso_twosided_disp
                    _ _
                    sigma_twosided_disp_cat
                    _ _ _ _
                    (identity_z_iso x)
                    (identity_z_iso y)
                    xy₁
                    xy₂).

    Let h : pr1 xy₁ -->[ identity_z_iso x ][ identity_z_iso y] pr1 xy₂ := pr11 f.
    Let hinv : pr1 xy₂ -->[ identity_z_iso x ][ identity_z_iso y] pr1 xy₁ := pr112 f.

    Local Lemma from_iso_sigma_of_twosided_disp_cat_inv₁
      : h ;;2 hinv
        =
        transportb
          (λ z, _ -->[ z ][ identity _ · identity _] _)
          (z_iso_inv_after_z_iso (identity_z_iso _))
          (transportb
             (λ z, _ -->[ identity x ][ z ] _)
             (z_iso_inv_after_z_iso (identity_z_iso _))
             (id_two_disp _)).
    Proof.
      refine (maponpaths pr1 (pr122 f) @ _).
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite sigma_transportf_left.
      rewrite sigma_transportf_right.
      apply idpath.
    Qed.

    Local Lemma from_iso_sigma_of_twosided_disp_cat_inv₂
      : hinv ;;2 h
        =
        transportb
          (λ z, _ -->[ z ][ identity _ · identity _] _)
          (z_iso_inv_after_z_iso (identity_z_iso _))
          (transportb
             (λ z, _ -->[ identity x ][ z ] _)
             (z_iso_inv_after_z_iso (identity_z_iso _))
             (id_two_disp _)).
    Proof.
      refine (maponpaths pr1 (pr222 f) @ _).
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite sigma_transportf_left.
      rewrite sigma_transportf_right.
      apply idpath.
    Qed.

    Definition from_iso_sigma_of_twosided_disp_cat_pr1
      : @iso_twosided_disp
          _ _
          D₁
          _ _ _ _
          (identity_z_iso x)
          (identity_z_iso y)
          (pr1 xy₁)
          (pr1 xy₂).
    Proof.
      simple refine (_ ,, _ ,, _ ,, _).
      - exact h.
      - exact hinv.
      - exact from_iso_sigma_of_twosided_disp_cat_inv₁.
      - exact from_iso_sigma_of_twosided_disp_cat_inv₂.
    Defined.

    Local Arguments transportf {_} _ {_ _ _} _.

    Definition from_iso_sigma_of_twosided_disp_cat_pr2
      : z_iso_disp
          (make_z_iso_total_twosided_disp_cat D₁
             from_iso_sigma_of_twosided_disp_cat_pr1)
          (pr2 xy₁)
          (pr2 xy₂).
    Proof.
      simple refine (_ ,, _ ,, _ ,, _).
      - exact (pr21 f).
      - exact (pr212 f).
      - abstract
          (assert (p := pr222 f
                        @ maponpaths _ (sigma_transportf_left _ _)
                        @ sigma_transportf_right _ _) ;
           cbn in p ;
           rewrite transport_f_f in p ;
           refine (sigma_mor_eq p @ _) ;
           cbn ;
           unfold transportb ;
           rewrite transport_f_f ;
           apply transportf_hset_eq ;
           apply (total_twosided_disp_category D₁)).
      - abstract
          (assert (p := pr122 f
                        @ maponpaths _ (sigma_transportf_left _ _)
                        @ sigma_transportf_right _ _) ;
           cbn in p ;
           rewrite transport_f_f in p ;
           refine (sigma_mor_eq p @ _) ;
           cbn ;
           unfold transportb ;
           rewrite transport_f_f ;
           apply transportf_hset_eq ;
           apply (total_twosided_disp_category D₁)).
    Defined.
  End FromSigmaIso.

  Definition weq_iso_sigma_of_twosided_disp_cat_help_eq
             {x : C₁}
             {y : C₂}
             {xy₁ : sigma_twosided_disp_cat x y}
             {xy₂ : sigma_twosided_disp_cat x y}
             (h₁ h₂ : ∑ (f : iso_twosided_disp
                               (identity_z_iso x) (identity_z_iso y)
                               (pr1 xy₁) (pr1 xy₂)),
                      z_iso_disp
                        (make_z_iso_total_twosided_disp_cat _ f)
                        (pr2 xy₁) (pr2 xy₂))
             (p : pr11 h₁ = pr11 h₂)
             (q : pr12 h₁
                  =
                  transportb
                    (λ z, pr2 xy₁ -->[ z ] pr2 xy₂)
                    (maponpaths
                       (λ (z : pr1 xy₁ -->[ identity _ ][ identity _ ] pr1 xy₂),
                        _ ,, _ ,, z)
                       p)
                    (pr12 h₂))
    : h₁ = h₂.
  Proof.
    induction h₁ as [ h₁ k₁ ].
    induction h₁ as [ h₁ Hh₁ ].
    induction k₁ as [ k₁ Hk₁ ].
    induction h₂ as [ h₂ k₂ ].
    induction h₂ as [ h₂ Hh₂ ].
    induction k₂ as [ k₂ Hk₂ ].
    cbn in *.
    induction p.
    cbn in q.
    induction q.
    assert (Hh₁ = Hh₂) as p.
    {
      apply isaprop_is_iso_twosided_disp.
    }
    induction p.
    do 2 apply maponpaths.
    apply (@isaprop_is_z_iso_disp _ D₂).
  Qed.

  Definition weq_iso_sigma_of_twosided_disp_cat
             {x : C₁}
             {y : C₂}
             (xy₁ : sigma_twosided_disp_cat x y)
             (xy₂ : sigma_twosided_disp_cat x y)
    : (∑ (f : iso_twosided_disp
                (identity_z_iso x) (identity_z_iso y)
                (pr1 xy₁) (pr1 xy₂)),
          z_iso_disp
            (make_z_iso_total_twosided_disp_cat _ f)
            (pr2 xy₁) (pr2 xy₂))
      ≃
      @iso_twosided_disp
         _ _
         sigma_twosided_disp_cat
         _ _ _ _
         (identity_z_iso x)
         (identity_z_iso y)
         xy₁
         xy₂.
  Proof.
    use weq_iso.
    - exact (λ f, to_iso_sigma_of_twosided_disp_cat (pr1 f) (pr2 f)).
    - intro f.
      simple refine (_ ,, _).
      + exact (from_iso_sigma_of_twosided_disp_cat_pr1 f).
      + exact (from_iso_sigma_of_twosided_disp_cat_pr2 f).
    - intro f.
      use weq_iso_sigma_of_twosided_disp_cat_help_eq ; apply idpath.
    - abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
  Defined.

  (**
   3. Univalence and discreteness
   *)
  Definition is_univalent_sigma_of_twosided_disp_cat_help
             (HD₂ : is_univalent_disp D₂)
             {x₁ : C₁}
             {y₁ : C₂}
             (xy₁ xy₂ : sigma_twosided_disp_cat x₁ y₁)
             (p : pr1 xy₁ = pr1 xy₂)
    : (transportf (λ z, D₂ (x₁ ,, y₁ ,, z)) p (pr2 xy₁) = pr2 xy₂)
      ≃
      z_iso_disp
        (@make_z_iso_total_twosided_disp_cat
           _ _ D₁
           _ _ _ _ _ _
           _ _
           (idtoiso_twosided_disp (idpath _) (idpath _) p))
        (pr2 xy₁)
        (pr2 xy₂).
  Proof.
    induction xy₁ as [ z₁ z₂ ].
    induction xy₂ as [ z₃ z₄ ].
    cbn in *.
    induction p ; cbn.
    refine (_ ∘ (_ ,, HD₂ _ _ (idpath _) z₂ z₄))%weq.
    use weq_iso.
    - intro f.
      simple refine (pr1 f ,, pr12 f ,, _ ,, _).
      + abstract
          (refine (pr122 f @ _) ;
           apply transportf_hset_eq ;
           apply homset_property).
      + abstract
          (refine (pr222 f @ _) ;
           apply transportf_hset_eq ;
           apply homset_property).
    - intro f.
      simple refine (pr1 f ,, pr12 f ,, _ ,, _).
      + abstract
          (refine (pr122 f @ _) ;
           apply transportf_hset_eq ;
           apply (total_twosided_disp_category D₁)).
      + abstract
          (refine (pr222 f @ _) ;
           apply transportf_hset_eq ;
           apply (total_twosided_disp_category D₁)).
    - abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         apply idpath).
    - abstract
        (intro f ;
         use subtypePath ; [ intro ; apply (@isaprop_is_z_iso_disp _ D₂) | ] ;
         apply idpath).
  Defined.

  Definition is_univalent_sigma_of_twosided_disp_cat
             (HD₁ : is_univalent_twosided_disp_cat D₁)
             (HD₂ : is_univalent_disp D₂)
    : is_univalent_twosided_disp_cat sigma_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂.
    use weqhomot.
    - exact (weq_iso_sigma_of_twosided_disp_cat _ _
             ∘ weqtotal2
                 (make_weq _ (HD₁ x₁ x₁ y₁ y₁ (idpath _) (idpath _) (pr1 xy₁) (pr1 xy₂)))
                 (is_univalent_sigma_of_twosided_disp_cat_help HD₂ xy₁ xy₂)
             ∘ total2_paths_equiv _ _ _)%weq.
    - intro p.
      induction p.
      use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ; cbn.
      apply idpath.
  Defined.

  Definition isaprop_disp_twosided_mor_sigma_twosided_disp_cat
             (HD₁ : isaprop_disp_twosided_mor D₁)
             (HD₂ : locally_propositional D₂)
    : isaprop_disp_twosided_mor sigma_twosided_disp_cat.
  Proof.
    intro ; intros.
    use total2_paths_f.
    - apply HD₁.
    - apply HD₂.
  Qed.

  Definition discrete_sigma_twosided_disp_cat
             (HD₁ : discrete_twosided_disp_cat D₁)
             (HD₂ : is_univalent_disp D₂)
             (HD₃ : locally_propositional D₂)
             (HD₄ : groupoidal_disp_cat D₂)
    : discrete_twosided_disp_cat sigma_twosided_disp_cat.
  Proof.
    use make_discrete_twosided_disp_cat.
    - use isaprop_disp_twosided_mor_sigma_twosided_disp_cat.
      + apply HD₁.
      + exact HD₃.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g Hf Hg fg ; cbn.
      simple refine (_ ,, _).
      + apply HD₁.
        exact (pr1 fg).
      + cbn.
        pose (h := @make_z_iso_total_twosided_disp_cat
                      _ _
                      D₁
                      x₁ x₂
                      y₁ y₂
                      (pr1 xy₁) (pr1 xy₂)
                      (f ,, Hf) (g ,, Hg)
                      (pr1 fg ,, pr12 HD₁ _ _ _ _ _ _ _ _ _ _ _)).
        apply (HD₄ _ _ h (pr2 h)).
        apply fg.
    - use is_univalent_sigma_of_twosided_disp_cat.
      + apply HD₁.
      + exact HD₂.
  Qed.
End DispCatOnTwoSidedDispCat.
