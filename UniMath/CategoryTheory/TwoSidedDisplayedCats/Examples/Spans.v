(**********************************************************************************

 The two-sided displayed category of spans

 A span in a category `C` is a diagram `x₁ <-- y --> x₂`. We construct a two-sided
 displayed category whose displayed objects are spans. We also give the spans that
 are necessary to construct the double category of spans.

 Contents
 1. The definition
 2. The univalence
 3. Builders and accessors
 4. Isomorphisms of spans
 5. The identity spans
 6. The composition of spans
 7. The left unitor of spans
 8. The right unitor of spans
 9. The associator of spans
 10. Companions and conjoints

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.

Local Open Scope cat.

Section Spans.
  Context (C : category).

  (** * 1. The definition *)
  Definition spans_ob
    : twosided_disp_cat C C
    := constant_twosided_disp_cat C C C.

  Definition spans_mor_left_ob_mor
    : disp_cat_ob_mor (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xyz, pr22 xyz --> pr1 xyz).
    - exact (λ xyz₁ xyz₂ l₁ l₂ fgh,
             l₁ · pr1 fgh
             =
             pr22 fgh · l₂).
  Defined.

  Definition spans_mor_left_id_comp
    : disp_cat_id_comp
        (total_twosided_disp_category spans_ob)
        spans_mor_left_ob_mor.
  Proof.
    split.
    - intros xyz fgh ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros xyz₁ xyz₂ xyz₃ fgh₁ fgh₂ h₁ h₂ h₃ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      apply idpath.
  Qed.

  Definition spans_mor_left_data
    : disp_cat_data (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact spans_mor_left_ob_mor.
    - exact spans_mor_left_id_comp.
  Defined.

  Definition spans_mor_left_axioms
    : disp_cat_axioms
        (total_twosided_disp_category spans_ob)
        spans_mor_left_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply isasetaprop.
      apply homset_property.
  Qed.

  Definition spans_mor_left
    : disp_cat (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact spans_mor_left_data.
    - exact spans_mor_left_axioms.
  Defined.

  Definition spans_mor_right_ob_mor
    : disp_cat_ob_mor (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xyz, pr22 xyz --> pr12 xyz).
    - exact (λ xyz₁ xyz₂ l₁ l₂ fgh,
             l₁ · pr12 fgh
             =
             pr22 fgh · l₂).
  Defined.

  Definition spans_mor_right_id_comp
    : disp_cat_id_comp
        (total_twosided_disp_category spans_ob)
        spans_mor_right_ob_mor.
  Proof.
    split.
    - intros xyz fgh ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros xyz₁ xyz₂ xyz₃ fgh₁ fgh₂ h₁ h₂ h₃ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      apply idpath.
  Qed.

  Definition spans_mor_right_data
    : disp_cat_data (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact spans_mor_right_ob_mor.
    - exact spans_mor_right_id_comp.
  Defined.

  Definition spans_mor_right_axioms
    : disp_cat_axioms
        (total_twosided_disp_category spans_ob)
        spans_mor_right_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply isasetaprop.
      apply homset_property.
  Qed.

  Definition spans_mor_right
    : disp_cat (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact spans_mor_right_data.
    - exact spans_mor_right_axioms.
  Defined.

  Definition spans_mors
    : disp_cat (total_twosided_disp_category spans_ob)
    := dirprod_disp_cat
         spans_mor_left
         spans_mor_right.

  Definition twosided_disp_cat_of_spans
    : twosided_disp_cat C C
    := sigma_twosided_disp_cat _ spans_mors.

  (** * 2. The univalence *)
  Definition is_univalent_disp_spans_mor_left
    : is_univalent_disp spans_mor_left.
  Proof.
    intros x y p l₁ l₂.
    induction p.
    use isweqimplimpl.
    - intro f ; cbn in *.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_left, id_right in p.
      exact p.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_disp_spans_mor_right
    : is_univalent_disp spans_mor_right.
  Proof.
    intros x y p l₁ l₂.
    induction p.
    use isweqimplimpl.
    - intro f ; cbn in *.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_left, id_right in p.
      exact p.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_spans_twosided_disp_cat
             (HC : is_univalent C)
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_spans.
  Proof.
    use is_univalent_sigma_of_twosided_disp_cat.
    - use is_univalent_constant_twosided_disp_cat.
      exact HC.
    - use dirprod_disp_cat_is_univalent.
      + exact is_univalent_disp_spans_mor_left.
      + exact is_univalent_disp_spans_mor_right.
  Defined.

  Definition is_strict_spans_twosided_disp_cat
             (HC : is_setcategory C)
    : is_strict_twosided_disp_cat twosided_disp_cat_of_spans.
  Proof.
    intros x y ; cbn.
    use isaset_total2.
    - apply HC.
    - intro z.
      use isasetdirprod.
      + apply homset_property.
      + apply homset_property.
  Qed.

  (** * 3. Builders and accessors *)
  Definition span
             (a b : C)
    : UU
    := twosided_disp_cat_of_spans a b.

  Definition make_span
             {a b x : C}
             (l : x --> a)
             (r : x --> b)
    : span a b
    :=  x ,, l ,, r.

  Definition ob_of_span
             {a b : C}
             (s : span a b)
    : C
    := pr1 s.

  Definition mor_left_of_span
             {a b : C}
             (s : span a b)
    : ob_of_span s --> a
    := pr12 s.

  Definition mor_right_of_span
             {a b : C}
             (s : span a b)
    : ob_of_span s --> b
    := pr22 s.

  Definition span_sqr
             {a₁ a₂ b₁ b₂ : C}
             (f : a₁ --> a₂)
             (g : b₁ --> b₂)
             (s₁ : span a₁ b₁)
             (s₂ : span a₂ b₂)
    : UU
    := s₁ -->[ f ][ g ] s₂.

  Definition span_laws
             {a₁ a₂ b₁ b₂ : C}
             (f : a₁ --> a₂)
             (g : b₁ --> b₂)
             (s₁ : span a₁ b₁)
             (s₂ : span a₂ b₂)
             (φ : ob_of_span s₁ --> ob_of_span s₂)
    : UU
    := (mor_left_of_span s₁ · f
        =
        φ · mor_left_of_span s₂)
       ×
       (mor_right_of_span s₁ · g
        =
        φ · mor_right_of_span s₂).

  Definition make_span_sqr
             {a₁ a₂ b₁ b₂ : C}
             {f : a₁ --> a₂}
             {g : b₁ --> b₂}
             {s₁ : span a₁ b₁}
             {s₂ : span a₂ b₂}
             (φ : ob_of_span s₁ --> ob_of_span s₂)
             (Hφ : span_laws f g _ _ φ)
    : span_sqr f g s₁ s₂
    := φ ,, Hφ.

  Definition span_sqr_ob_mor
             {a₁ a₂ b₁ b₂ : C}
             {f : a₁ --> a₂}
             {g : b₁ --> b₂}
             {s₁ : span a₁ b₁}
             {s₂ : span a₂ b₂}
             (sq : span_sqr f g s₁ s₂)
    : ob_of_span s₁ --> ob_of_span s₂
    := pr1 sq.

  Proposition span_sqr_mor_left
              {a₁ a₂ b₁ b₂ : C}
              {f : a₁ --> a₂}
              {g : b₁ --> b₂}
              {s₁ : span a₁ b₁}
              {s₂ : span a₂ b₂}
              (sq : span_sqr f g s₁ s₂)
    : mor_left_of_span s₁ · f
      =
      span_sqr_ob_mor sq · mor_left_of_span s₂.
  Proof.
    exact (pr12 sq).
  Qed.

  Proposition span_sqr_mor_right
              {a₁ a₂ b₁ b₂ : C}
              {f : a₁ --> a₂}
              {g : b₁ --> b₂}
              {s₁ : span a₁ b₁}
              {s₂ : span a₂ b₂}
              (sq : span_sqr f g s₁ s₂)
    : mor_right_of_span s₁ · g
      =
      span_sqr_ob_mor sq · mor_right_of_span s₂.
  Proof.
    exact (pr22 sq).
  Qed.

  Proposition span_sqr_eq
              {a₁ a₂ b₁ b₂ : C}
              {f : a₁ --> a₂}
              {g : b₁ --> b₂}
              {s₁ : span a₁ b₁}
              {s₂ : span a₂ b₂}
              (sq₁ sq₂ : span_sqr f g s₁ s₂)
              (p : span_sqr_ob_mor sq₁
                   =
                   span_sqr_ob_mor sq₂)
    : sq₁ = sq₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    exact p.
  Qed.

  (** * 4. Isomorphisms of spans *)
  Proposition transportf_disp_mor2_span
              {a₁ a₂ b₁ b₂ : C}
              {f f' : a₁ --> a₂}
              (p : f = f')
              {g g' : b₁ --> b₂}
              (q : g = g')
              {s₁ : span a₁ b₁}
              {s₂ : span a₂ b₂}
              (sq : span_sqr f g s₁ s₂)
    : span_sqr_ob_mor
        (transportf_disp_mor2
           p
           q
           sq)
      =
      span_sqr_ob_mor sq.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_disp_mor2_span
              {a₁ a₂ b₁ b₂ : C}
              {f f' : a₁ --> a₂}
              (p : f' = f)
              {g g' : b₁ --> b₂}
              (q : g' = g)
              {s₁ : span a₁ b₁}
              {s₂ : span a₂ b₂}
              (sq : span_sqr f g s₁ s₂)
    : span_sqr_ob_mor
        (transportb_disp_mor2
           p
           q
           sq)
      =
      span_sqr_ob_mor sq.
  Proof.
    apply transportf_disp_mor2_span.
  Qed.

  Section IsoSpan.
    Context {a b : C}
            {s₁ : span a b}
            {s₂ : span a b}
            (sq : span_sqr (identity _) (identity _) s₁ s₂)
            (Hsq : is_z_isomorphism (span_sqr_ob_mor sq)).

    Let i : z_iso (ob_of_span s₁) (ob_of_span s₂)
      := make_z_iso _ _ Hsq.

    Proposition is_iso_twosided_disp_span_sqr_inv_laws
      : span_laws
          (identity a) (identity b)
          s₂ s₁
          (inv_from_z_iso i).
    Proof.
      split.
      - rewrite id_right.
        refine (!_).
        use z_iso_inv_on_right.
        refine (_ @ span_sqr_mor_left sq).
        rewrite id_right.
        apply idpath.
      - rewrite id_right.
        refine (!_).
        use z_iso_inv_on_right.
        refine (_ @ span_sqr_mor_right sq).
        rewrite id_right.
        apply idpath.
    Qed.

    Definition is_iso_twosided_disp_span_sqr_inv
      : span_sqr (identity _) (identity _) s₂ s₁.
    Proof.
      use make_span_sqr.
      - exact (inv_from_z_iso i).
      - exact is_iso_twosided_disp_span_sqr_inv_laws.
    Defined.

    Definition is_iso_twosided_disp_span_sqr
      : is_iso_twosided_disp
          (identity_is_z_iso _)
          (identity_is_z_iso _)
          sq.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact is_iso_twosided_disp_span_sqr_inv.
      - abstract
          (use span_sqr_eq ;
           rewrite transportb_disp_mor2_span ; cbn ;
           exact (z_iso_inv_after_z_iso i)).
      - abstract
          (use span_sqr_eq ;
           rewrite transportb_disp_mor2_span ; cbn ;
           exact (z_iso_after_z_iso_inv i)).
    Defined.
  End IsoSpan.

  (** * 5. The identity spans *)
  Definition id_span
             (a : C)
    : span a a.
  Proof.
    use make_span.
    - exact a.
    - exact (identity _).
    - exact (identity _).
  Defined.

  Proposition id_span_mor_laws
              {x y : C}
              (f : x --> y)
    : span_laws
        f f
        (id_span x) (id_span y)
        f.
  Proof.
    split ; cbn.
    - rewrite id_left, id_right.
      apply idpath.
    - rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition id_span_mor
             {x y : C}
             (f : x --> y)
    : span_sqr f f (id_span x) (id_span y).
  Proof.
    use make_span_sqr.
    - exact f.
    - apply id_span_mor_laws.
  Defined.

  Context (PC : Pullbacks C).

  (** * 6. The composition of spans *)
  Section CompSpan.
    Context {x y z : C}
            (s : span x y)
            (t : span y z).

    Definition comp_span_Pullback
      : Pullback (mor_right_of_span s) (mor_left_of_span t)
      := PC _ _ _ (mor_right_of_span s) (mor_left_of_span t).

    Definition comp_span
      : span x z.
    Proof.
      use make_span.
      - exact comp_span_Pullback.
      - exact (PullbackPr1 _ · mor_left_of_span s).
      - exact (PullbackPr2 _ · mor_right_of_span t).
    Defined.
  End CompSpan.

  Section CompSpanMor.
    Context {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : x₁ --> x₂} {v₂ : y₁ --> y₂} {v₃ : z₁ --> z₂}
            {h₁ : span x₁ y₁}
            {h₂ : span y₁ z₁}
            {k₁ : span x₂ y₂}
            {k₂ : span y₂ z₂}
            (s₁ : span_sqr v₁ v₂ h₁ k₁)
            (s₂ : span_sqr v₂ v₃ h₂ k₂).

    Definition mor_of_comp_span_mor
      : comp_span_Pullback h₁ h₂ --> comp_span_Pullback k₁ k₂.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _ · span_sqr_ob_mor s₁).
      - exact (PullbackPr2 _ · span_sqr_ob_mor s₂).
      - abstract
          (rewrite !assoc' ;
           rewrite <- span_sqr_mor_left, <- span_sqr_mor_right ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply PullbackSqrCommutes).
    Defined.

    Proposition comp_span_mor_laws
      : span_laws
          v₁ v₃
          (comp_span h₁ h₂) (comp_span k₁ k₂)
          mor_of_comp_span_mor.
    Proof.
      split ; cbn.
      - unfold mor_of_comp_span_mor.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr1.
        rewrite !assoc'.
        apply maponpaths.
        apply span_sqr_mor_left.
      - unfold mor_of_comp_span_mor.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr2.
        rewrite !assoc'.
        apply maponpaths.
        apply span_sqr_mor_right.
    Qed.

    Definition comp_span_mor
      : span_sqr
          v₁ v₃
          (comp_span h₁ h₂) (comp_span k₁ k₂).
    Proof.
      use make_span_sqr.
      - exact mor_of_comp_span_mor.
      - exact comp_span_mor_laws.
    Defined.
  End CompSpanMor.

  (** * 7. The left unitor of spans *)
  Section SpanLunitor.
    Context {x y : C}
            (h : span x y).

    Definition span_lunitor_mor
      : comp_span_Pullback (id_span x) h --> ob_of_span h
      := PullbackPr2 _.

    Definition span_linvunitor
      : ob_of_span h --> comp_span_Pullback (id_span x) h.
    Proof.
      use PullbackArrow.
      - exact (mor_left_of_span h).
      - exact (identity _).
      - abstract
          (cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Proposition is_z_iso_span_lunitor_mor_eqs
      : is_inverse_in_precat
          span_lunitor_mor
          span_linvunitor.
    Proof.
      split ; unfold span_lunitor_mor, span_linvunitor ; cbn.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite id_left.
          rewrite <- PullbackSqrCommutes.
          apply id_right.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          rewrite id_left, id_right.
          apply idpath.
      - apply PullbackArrow_PullbackPr2.
    Qed.

    Definition is_z_iso_span_lunitor_mor
      : is_z_isomorphism span_lunitor_mor.
    Proof.
      use make_is_z_isomorphism.
      - exact span_linvunitor.
      - exact is_z_iso_span_lunitor_mor_eqs.
    Defined.

    Proposition span_lunitor_laws
      : span_laws
          (identity x) (identity y)
          (comp_span (id_span x) h) h
          span_lunitor_mor.
    Proof.
      split ; cbn ; unfold span_lunitor_mor.
      - rewrite !id_right.
        rewrite <- PullbackSqrCommutes ; cbn.
        rewrite id_right.
        apply idpath.
      - rewrite id_right.
        apply idpath.
    Qed.

    Definition span_lunitor
      : span_sqr
          (identity _) (identity _)
          (comp_span (id_span _) h)
          h.
    Proof.
      use make_span_sqr.
      - exact span_lunitor_mor.
      - exact span_lunitor_laws.
    Defined.
  End SpanLunitor.

  (** * 8. The right unitor of spans *)
  Section SpanRunitor.
    Context {x y : C}
            (h : span x y).

    Definition span_runitor_mor
      : comp_span_Pullback h (id_span y) --> ob_of_span h
      := PullbackPr1 _.

    Definition span_rinvunitor
      : ob_of_span h --> comp_span_Pullback h (id_span y).
    Proof.
      use PullbackArrow.
      - exact (identity _).
      - exact (mor_right_of_span h).
      - abstract
          (cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Proposition is_z_iso_span_runitor_mor_eqs
      : is_inverse_in_precat
          span_runitor_mor
          span_rinvunitor.
    Proof.
      split ; unfold span_runitor_mor, span_rinvunitor ; cbn.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite id_left.
          apply id_right.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          rewrite id_left.
          rewrite PullbackSqrCommutes.
          apply id_right.
      - apply PullbackArrow_PullbackPr1.
    Qed.

    Definition is_z_iso_span_runitor_mor
      : is_z_isomorphism span_runitor_mor.
    Proof.
      use make_is_z_isomorphism.
      - exact span_rinvunitor.
      - exact is_z_iso_span_runitor_mor_eqs.
    Defined.

    Proposition span_runitor_laws
      : span_laws
          (identity x) (identity y)
          (comp_span h (id_span y)) h
          span_runitor_mor.
    Proof.
      split ; cbn ; unfold span_runitor_mor.
      - rewrite id_right.
        apply idpath.
      - rewrite !id_right.
        rewrite PullbackSqrCommutes ; cbn.
        rewrite id_right.
        apply idpath.
    Qed.

    Definition span_runitor
      : span_sqr
          (identity _) (identity _)
          (comp_span h (id_span _))
          h.
    Proof.
      use make_span_sqr.
      - exact span_runitor_mor.
      - exact span_runitor_laws.
    Defined.
  End SpanRunitor.

  (** * 9. The associator of spans *)
  Section SpanAssociator.
    Context {w x y z : C}
            (h₁ : span w x)
            (h₂ : span x y)
            (h₃ : span y z).

    Definition span_associator_mor
      : comp_span_Pullback h₁ (comp_span h₂ h₃)
        -->
        comp_span_Pullback (comp_span h₁ h₂) h₃.
    Proof.
      use PullbackArrow.
      - use PullbackArrow.
        + exact (PullbackPr1 _).
        + exact (PullbackPr2 _ · PullbackPr1 _).
        + abstract
            (rewrite !assoc' ;
             rewrite PullbackSqrCommutes ;
             apply idpath).
      - exact (PullbackPr2 _ · PullbackPr2 _).
      - abstract
          (cbn ;
           rewrite !assoc ;
           rewrite PullbackArrow_PullbackPr2 ;
           rewrite !assoc' ;
           rewrite PullbackSqrCommutes ;
           apply idpath).
    Defined.

    Definition span_associator_mor_inv
      : comp_span_Pullback (comp_span h₁ h₂) h₃
        -->
        comp_span_Pullback h₁ (comp_span h₂ h₃).
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _ · PullbackPr1 _).
      - use PullbackArrow.
        + exact (PullbackPr1 _ · PullbackPr2 _).
        + exact (PullbackPr2 _).
        + abstract
            (rewrite !assoc' ;
             rewrite PullbackSqrCommutes ;
             apply idpath).
      - abstract
          (cbn ;
           rewrite !assoc ;
           rewrite PullbackArrow_PullbackPr1 ;
           rewrite !assoc' ;
           rewrite PullbackSqrCommutes ;
           apply idpath).
    Defined.

    Proposition is_iso_span_associator_mor_eq
      : is_inverse_in_precat
          span_associator_mor
          span_associator_mor_inv.
    Proof.
      split.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
        + rewrite id_left.
          unfold span_associator_mor_inv.
          rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          unfold span_associator_mor.
          rewrite !assoc.
          rewrite !PullbackArrow_PullbackPr1.
          apply idpath.
        + rewrite id_left.
          unfold span_associator_mor_inv.
          rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
          * rewrite !assoc'.
            rewrite PullbackArrow_PullbackPr1.
            unfold span_associator_mor.
            rewrite !assoc.
            rewrite PullbackArrow_PullbackPr1.
            rewrite PullbackArrow_PullbackPr2.
            apply idpath.
          * rewrite !assoc'.
            unfold span_associator_mor.
            rewrite !PullbackArrow_PullbackPr2.
            apply idpath.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
        + rewrite id_left.
          unfold span_associator_mor.
          rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
          * rewrite !assoc'.
            rewrite !PullbackArrow_PullbackPr1.
            unfold span_associator_mor_inv.
            rewrite PullbackArrow_PullbackPr1.
            apply idpath.
          * rewrite !assoc'.
            rewrite !PullbackArrow_PullbackPr2.
            unfold span_associator_mor_inv.
            rewrite !assoc.
            rewrite PullbackArrow_PullbackPr2.
            rewrite PullbackArrow_PullbackPr1.
            apply idpath.
        + rewrite !assoc'.
          unfold span_associator_mor.
          rewrite PullbackArrow_PullbackPr2.
          unfold span_associator_mor_inv.
          rewrite !assoc.
          rewrite !PullbackArrow_PullbackPr2.
          rewrite id_left.
          apply idpath.
    Qed.

    Definition is_z_iso_span_associator_mor
      : is_z_isomorphism span_associator_mor.
    Proof.
      use make_is_z_isomorphism.
      - exact span_associator_mor_inv.
      - exact is_iso_span_associator_mor_eq.
    Defined.

    Proposition span_associator_laws
      : span_laws
          (identity _) (identity _)
          (comp_span h₁ (comp_span h₂ h₃))
          (comp_span (comp_span h₁ h₂) h₃)
          span_associator_mor.
    Proof.
      split ; cbn.
      - rewrite id_right.
        unfold span_associator_mor.
        rewrite !assoc.
        rewrite !PullbackArrow_PullbackPr1.
        apply idpath.
      - rewrite id_right.
        unfold span_associator_mor.
        rewrite !assoc.
        rewrite !PullbackArrow_PullbackPr2.
        apply idpath.
    Qed.

    Definition span_associator
      : span_sqr
          (identity _) (identity _)
          (comp_span h₁ (comp_span h₂ h₃))
          (comp_span (comp_span h₁ h₂) h₃).
    Proof.
      use make_span_sqr.
      - exact span_associator_mor.
      - exact span_associator_laws.
    Defined.
  End SpanAssociator.

  (** * 10. Companions and conjoints *)
  Section CompanionsAndConjoints.
    Context {x y : C}
            (f : x --> y).

    Definition span_companion
      : span x y.
    Proof.
      use make_span.
      - exact x.
      - exact (identity x).
      - exact f.
    Defined.

    Definition span_companion_unit
      : span_sqr f (identity y) span_companion (id_span y).
    Proof.
      use make_span_sqr.
      - exact f.
      - abstract
          (split ; cbn ; [ | apply idpath ] ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition span_companion_counit
      : span_sqr (identity x) f (id_span x) span_companion.
    Proof.
      use make_span_sqr.
      - exact (identity x).
      - abstract
          (split ; apply idpath).
    Defined.

    Definition span_conjoint
      : span y x.
    Proof.
      use make_span.
      - exact x.
      - exact f.
      - exact (identity x).
    Defined.

    Definition span_conjoint_unit
      : span_sqr f (identity x) (id_span x) span_conjoint.
    Proof.
      use make_span_sqr.
      - exact (identity x).
      - abstract
          (split ; apply idpath).
    Defined.

    Definition span_conjoint_counit
      : span_sqr (identity y) f span_conjoint (id_span y).
    Proof.
      use make_span_sqr.
      - exact f.
      - abstract
          (split ; cbn ; [ apply idpath | ] ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.
  End CompanionsAndConjoints.
End Spans.
