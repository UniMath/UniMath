(**********************************************************************************

 Structured cospans

 In this file, we define the 2-sided displayed category of structured cospans. Our
 definition is based on Theorem 3.1 in Structured Versus Decorated Cospans by Baez,
 Courser, and Vasilakopoulou. Note that even though they define a monoidal double
 category, the definition in this file only consists of the horizontal and vertical
 morphisms, and the squares. For that reason, we don't need to assume the existence
 of pushouts in any of the involved categories and we also don't need to assume
 that the functor `L` preserves pushouts, We also prove that the obtained 2-sided
 displayed category is univalent.

 Fix categories `A` and `X` and a functor `A ⟶ X`. The construction of the 2-sided
 displayed category is done in multiple steps. In this 2-sided displayed category,
 the objects describe what a structured cospan between objects `a` and `b` in `A`.
 Such a cospan consists of an object `x` in `X` and morphisms `L a --> x` and
 `L b --> x`. Each part of this definition is put in its own 2-sided displayed
 category:
 - We add the object `x` in [struct_cospans_ob]
 - The morphism `L a --> x` is added in [struct_cospans_mor_left], which is a
   displayed category on the total category of [struct_cospans_ob].
 - The morphism `L b --> x` is added in [struct_cospans_mor_right], which is a
   displayed category on the total category of [struct_cospans_ob].
 Combining these together by taking products and a sigma, we obtain the 2-sided
 displayed category of structured cospans.

 We also characterize global isomorphism squares (i.e., those squares of which the
 vertical sides are identities) of structured cospans. In addition, we give some
 standard structured cospans. Furthermore, we define an action of functors on
 structured cospans, and we show that this gives rise to a functor between
 2-sided displayed categories.

 Contents
 1. The 2-sided displayed category of structured cospans
 2. Builders and accessors for structured cospans
 3. The univalence of the 2-sided displayed category of structured cospans
 4. Isos of structured cospans
 5. The identity structured cospans
 6. The composition of structured cospans
 7. The left unitor of structured cospans
 8. The right unitor of structured cospans
 9. The associator of structured cospans
 10. Companions and conjoints
 11. Functors on structured cospans

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.

Local Open Scope cat.

Section StructuredCospans.
  Context {A X : category}
          (L : A ⟶ X).

  (** * 1. The 2-sided displayed category of structured cospans *)
  Definition struct_cospans_ob
    : twosided_disp_cat A A
    := constant_twosided_disp_cat A A X.

  Definition struct_cospans_mor_left_ob_mor
    : disp_cat_ob_mor (total_twosided_disp_category struct_cospans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xyz, L (pr1 xyz) --> pr22 xyz).
    - exact (λ xyz₁ xyz₂ l₁ l₂ fgh,
             l₁ · pr22 fgh
             =
             #L (pr1 fgh) · l₂).
  Defined.

  Definition struct_cospans_mor_left_id_comp
    : disp_cat_id_comp _ struct_cospans_mor_left_ob_mor.
  Proof.
    split.
    - intros xyz fgh ; cbn.
      rewrite id_right.
      rewrite functor_id, id_left.
      apply idpath.
    - intros xyz₁ xyz₂ xyz₃ fgh₁ fgh₂ h₁ h₂ h₃ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      rewrite !assoc.
      rewrite <- functor_comp.
      apply idpath.
  Qed.

  Definition struct_cospans_mor_left_data
    : disp_cat_data (total_twosided_disp_category struct_cospans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact struct_cospans_mor_left_ob_mor.
    - exact struct_cospans_mor_left_id_comp.
  Defined.

  Definition struct_cospans_mor_left_axioms
    : disp_cat_axioms _ struct_cospans_mor_left_data.
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

  Definition struct_cospans_mor_left
    : disp_cat (total_twosided_disp_category struct_cospans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact struct_cospans_mor_left_data.
    - exact struct_cospans_mor_left_axioms.
  Defined.

  Definition struct_cospans_mor_right_ob_mor
    : disp_cat_ob_mor (total_twosided_disp_category struct_cospans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xyz, L(pr12 xyz) --> pr22 xyz).
    - exact (λ xyz₁ xyz₂ l₁ l₂ fgh,
             l₁ · pr22 fgh
             =
             #L(pr12 fgh) · l₂).
  Defined.

  Definition struct_cospans_mor_right_id_comp
    : disp_cat_id_comp
        (total_twosided_disp_category struct_cospans_ob)
        struct_cospans_mor_right_ob_mor.
  Proof.
    split.
    - intros xyz fgh ; cbn.
      rewrite id_right.
      rewrite functor_id, id_left.
      apply idpath.
    - intros xyz₁ xyz₂ xyz₃ fgh₁ fgh₂ h₁ h₂ h₃ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      rewrite !assoc.
      rewrite <- functor_comp.
      apply idpath.
  Qed.

  Definition struct_cospans_mor_right_data
    : disp_cat_data (total_twosided_disp_category struct_cospans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact struct_cospans_mor_right_ob_mor.
    - exact struct_cospans_mor_right_id_comp.
  Defined.

  Definition struct_cospans_mor_right_axioms
    : disp_cat_axioms _ struct_cospans_mor_right_data.
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

  Definition struct_cospans_mor_right
    : disp_cat (total_twosided_disp_category struct_cospans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact struct_cospans_mor_right_data.
    - exact struct_cospans_mor_right_axioms.
  Defined.

  Definition struct_cospans_mors
    : disp_cat (total_twosided_disp_category struct_cospans_ob)
    := dirprod_disp_cat
         struct_cospans_mor_left
         struct_cospans_mor_right.

  Definition twosided_disp_cat_of_struct_cospans
    : twosided_disp_cat A A
    := sigma_twosided_disp_cat _ struct_cospans_mors.

  (** * 2. Builders and accessors for structured cospans *)
  Definition struct_cospan
             (a b : A)
    : UU
    := twosided_disp_cat_of_struct_cospans a b.

  Definition make_struct_cospan
             {a b : A}
             (x : X)
             (l : L a --> x)
             (r : L b --> x)
    : struct_cospan a b
    :=  x ,, l ,, r.

  Definition ob_of_struct_cospan
             {a b : A}
             (s : struct_cospan a b)
    : X
    := pr1 s.

  Definition mor_left_of_struct_cospan
             {a b : A}
             (s : struct_cospan a b)
    : L a --> ob_of_struct_cospan s
    := pr12 s.

  Definition mor_right_of_struct_cospan
             {a b : A}
             (s : struct_cospan a b)
    : L b --> ob_of_struct_cospan s
    := pr22 s.

  Definition struct_cospan_sqr
             {a₁ a₂ b₁ b₂ : A}
             (f : a₁ --> a₂)
             (g : b₁ --> b₂)
             (s₁ : struct_cospan a₁ b₁)
             (s₂ : struct_cospan a₂ b₂)
    : UU
    := s₁ -->[ f ][ g ] s₂.

  Definition struct_cospan_laws
             {a₁ a₂ b₁ b₂ : A}
             (f : a₁ --> a₂)
             (g : b₁ --> b₂)
             (s₁ : struct_cospan a₁ b₁)
             (s₂ : struct_cospan a₂ b₂)
             (φ : ob_of_struct_cospan s₁ --> ob_of_struct_cospan s₂)
    : UU
    := (mor_left_of_struct_cospan s₁ · φ
        =
        #L f · mor_left_of_struct_cospan s₂)
       ×
       (mor_right_of_struct_cospan s₁ · φ
        =
        #L g · mor_right_of_struct_cospan s₂).

  Definition make_struct_cospan_sqr
             {a₁ a₂ b₁ b₂ : A}
             {f : a₁ --> a₂}
             {g : b₁ --> b₂}
             {s₁ : struct_cospan a₁ b₁}
             {s₂ : struct_cospan a₂ b₂}
             (φ : ob_of_struct_cospan s₁ --> ob_of_struct_cospan s₂)
             (Hφ : struct_cospan_laws f g _ _ φ)
    : struct_cospan_sqr f g s₁ s₂
    := φ ,, pr1 Hφ ,, pr2 Hφ.

  Definition struct_cospan_sqr_ob_mor
             {a₁ a₂ b₁ b₂ : A}
             {f : a₁ --> a₂}
             {g : b₁ --> b₂}
             {s₁ : struct_cospan a₁ b₁}
             {s₂ : struct_cospan a₂ b₂}
             (sq : struct_cospan_sqr f g s₁ s₂)
    : ob_of_struct_cospan s₁ --> ob_of_struct_cospan s₂
    := pr1 sq.

  Proposition struct_cospan_sqr_mor_left
              {a₁ a₂ b₁ b₂ : A}
              {f : a₁ --> a₂}
              {g : b₁ --> b₂}
              {s₁ : struct_cospan a₁ b₁}
              {s₂ : struct_cospan a₂ b₂}
              (sq : struct_cospan_sqr f g s₁ s₂)
    : mor_left_of_struct_cospan s₁ · struct_cospan_sqr_ob_mor sq
      =
      #L f · mor_left_of_struct_cospan s₂.
  Proof.
    exact (pr12 sq).
  Qed.

  Proposition struct_cospan_sqr_mor_right
              {a₁ a₂ b₁ b₂ : A}
              {f : a₁ --> a₂}
              {g : b₁ --> b₂}
              {s₁ : struct_cospan a₁ b₁}
              {s₂ : struct_cospan a₂ b₂}
              (sq : struct_cospan_sqr f g s₁ s₂)
    : mor_right_of_struct_cospan s₁ · struct_cospan_sqr_ob_mor sq
      =
      #L g · mor_right_of_struct_cospan s₂.
  Proof.
    exact (pr22 sq).
  Qed.

  Proposition struct_cospan_sqr_eq
              {a₁ a₂ b₁ b₂ : A}
              {f : a₁ --> a₂}
              {g : b₁ --> b₂}
              {s₁ : struct_cospan a₁ b₁}
              {s₂ : struct_cospan a₂ b₂}
              (sq₁ sq₂ : struct_cospan_sqr f g s₁ s₂)
              (p : struct_cospan_sqr_ob_mor sq₁
                   =
                   struct_cospan_sqr_ob_mor sq₂)
    : sq₁ = sq₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    exact p.
  Qed.

  (** * 3. The univalence of the 2-sided displayed category of structured cospans *)
  Definition is_univalent_disp_struct_cospans_mor_left
    : is_univalent_disp struct_cospans_mor_left.
  Proof.
    intros x y p l₁ l₂.
    induction p.
    use isweqimplimpl.
    - intro f ; cbn in *.
      pose (p := pr1 f) ; cbn in p.
      rewrite functor_id, id_left, id_right in p.
      exact p.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_disp_struct_cospans_mor_right
    : is_univalent_disp struct_cospans_mor_right.
  Proof.
    intros x y p l₁ l₂.
    induction p.
    use isweqimplimpl.
    - intro f ; cbn in *.
      pose (p := pr1 f) ; cbn in p.
      rewrite functor_id, id_left, id_right in p.
      exact p.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_struct_cospans_twosided_disp_cat
             (HX : is_univalent X)
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_struct_cospans.
  Proof.
    use is_univalent_sigma_of_twosided_disp_cat.
    - use is_univalent_constant_twosided_disp_cat.
      exact HX.
    - use dirprod_disp_cat_is_univalent.
      + exact is_univalent_disp_struct_cospans_mor_left.
      + exact is_univalent_disp_struct_cospans_mor_right.
  Defined.

  Definition is_strict_struct_cospans_twosided_disp_cat
             (HX : is_setcategory X)
    : is_strict_twosided_disp_cat twosided_disp_cat_of_struct_cospans.
  Proof.
    intros x y ; cbn.
    use isaset_total2.
    - apply HX.
    - intro z.
      use isasetdirprod.
      + apply homset_property.
      + apply homset_property.
  Qed.

  (** * 4. Isos of structured cospans *)
  Proposition transportf_disp_mor2_struct_cospan
              {a₁ a₂ b₁ b₂ : A}
              {f f' : a₁ --> a₂}
              (p : f = f')
              {g g' : b₁ --> b₂}
              (q : g = g')
              {s₁ : struct_cospan a₁ b₁}
              {s₂ : struct_cospan a₂ b₂}
              (sq : struct_cospan_sqr f g s₁ s₂)
    : struct_cospan_sqr_ob_mor
        (transportf_disp_mor2
           p
           q
           sq)
      =
      struct_cospan_sqr_ob_mor sq.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_disp_mor2_struct_cospan
              {a₁ a₂ b₁ b₂ : A}
              {f f' : a₁ --> a₂}
              (p : f' = f)
              {g g' : b₁ --> b₂}
              (q : g' = g)
              {s₁ : struct_cospan a₁ b₁}
              {s₂ : struct_cospan a₂ b₂}
              (sq : struct_cospan_sqr f g s₁ s₂)
    : struct_cospan_sqr_ob_mor
        (transportb_disp_mor2
           p
           q
           sq)
      =
      struct_cospan_sqr_ob_mor sq.
  Proof.
    apply transportf_disp_mor2_struct_cospan.
  Qed.

  Section IsoStructCospan.
    Context {a b : A}
            {s₁ : struct_cospan a b}
            {s₂ : struct_cospan a b}
            (sq : struct_cospan_sqr (identity _) (identity _) s₁ s₂)
            (Hsq : is_z_isomorphism (struct_cospan_sqr_ob_mor sq)).

    Let i : z_iso (ob_of_struct_cospan s₁) (ob_of_struct_cospan s₂)
      := make_z_iso _ _ Hsq.

    Proposition is_iso_twosided_disp_struct_cospan_sqr_inv_laws
      : struct_cospan_laws
          (identity a) (identity b)
          s₂ s₁
          (inv_from_z_iso i).
    Proof.
      split.
      - rewrite functor_id, id_left.
        refine (!_).
        use z_iso_inv_on_left.
        refine (_ @ !(struct_cospan_sqr_mor_left sq)).
        rewrite functor_id, id_left.
        apply idpath.
      - rewrite functor_id, id_left.
        refine (!_).
        use z_iso_inv_on_left.
        refine (_ @ !(struct_cospan_sqr_mor_right sq)).
        rewrite functor_id, id_left.
        apply idpath.
    Qed.

    Definition is_iso_twosided_disp_struct_cospan_sqr_inv
      : struct_cospan_sqr (identity _) (identity _) s₂ s₁.
    Proof.
      use make_struct_cospan_sqr.
      - exact (inv_from_z_iso i).
      - exact is_iso_twosided_disp_struct_cospan_sqr_inv_laws.
    Defined.

    Definition is_iso_twosided_disp_struct_cospan_sqr
      : is_iso_twosided_disp
          (identity_is_z_iso _)
          (identity_is_z_iso _)
          sq.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact is_iso_twosided_disp_struct_cospan_sqr_inv.
      - abstract
          (use struct_cospan_sqr_eq ;
           rewrite transportb_disp_mor2_struct_cospan ; cbn ;
           exact (z_iso_inv_after_z_iso i)).
      - abstract
          (use struct_cospan_sqr_eq ;
           rewrite transportb_disp_mor2_struct_cospan ; cbn ;
           exact (z_iso_after_z_iso_inv i)).
    Defined.
  End IsoStructCospan.
End StructuredCospans.

Section StandardCospans.
  Context {A X : category}
          (L : A ⟶ X).

  (** * 5. The identity structured cospans *)
  Definition id_struct_cospan
             (a : A)
    : struct_cospan L a a.
  Proof.
    use make_struct_cospan.
    - exact (L a).
    - exact (identity _).
    - exact (identity _).
  Defined.

  Proposition id_struct_cospan_mor_laws
              {x y : A}
              (f : x --> y)
    : struct_cospan_laws
        L
        f f
        (id_struct_cospan x) (id_struct_cospan y)
        (# L f).
  Proof.
    split ; cbn.
    - rewrite id_left, id_right.
      apply idpath.
    - rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition id_struct_cospan_mor
             {x y : A}
             (f : x --> y)
    : struct_cospan_sqr L f f (id_struct_cospan x) (id_struct_cospan y).
  Proof.
    use make_struct_cospan_sqr.
    - exact (#L f).
    - apply id_struct_cospan_mor_laws.
  Defined.

  Context (PX : Pushouts X).

  (** * 6. The composition of structured cospans *)
  Section CompCospan.
    Context {x y z : A}
            (s : struct_cospan L x y)
            (t : struct_cospan L y z).

    Definition comp_struct_cospan_Pushout
      : Pushout (mor_right_of_struct_cospan L s) (mor_left_of_struct_cospan L t)
      := PX _ _ _ (mor_right_of_struct_cospan L s) (mor_left_of_struct_cospan L t).

    Definition comp_struct_cospan
      : struct_cospan L x z.
    Proof.
      use make_struct_cospan.
      - exact comp_struct_cospan_Pushout.
      - exact (mor_left_of_struct_cospan L s · PushoutIn1 _).
      - exact (mor_right_of_struct_cospan L t · PushoutIn2 _).
    Defined.
  End CompCospan.

  Section CompCospanMor.
    Context {x₁ x₂ y₁ y₂ z₁ z₂ : A}
            {v₁ : x₁ --> x₂} {v₂ : y₁ --> y₂} {v₃ : z₁ --> z₂}
            {h₁ : struct_cospan L x₁ y₁}
            {h₂ : struct_cospan L y₁ z₁}
            {k₁ : struct_cospan L x₂ y₂}
            {k₂ : struct_cospan L y₂ z₂}
            (s₁ : struct_cospan_sqr L v₁ v₂ h₁ k₁)
            (s₂ : struct_cospan_sqr L v₂ v₃ h₂ k₂).

    Definition mor_of_comp_struct_cospan_mor
      : comp_struct_cospan_Pushout h₁ h₂ --> comp_struct_cospan_Pushout k₁ k₂.
    Proof.
      use PushoutArrow.
      - exact (struct_cospan_sqr_ob_mor _ s₁ · PushoutIn1 _).
      - exact (struct_cospan_sqr_ob_mor _ s₂ · PushoutIn2 _).
      - abstract
          (rewrite !assoc ;
           rewrite struct_cospan_sqr_mor_right ;
           rewrite struct_cospan_sqr_mor_left ;
           rewrite !assoc' ;
           apply maponpaths ;
           apply PushoutSqrCommutes).
    Defined.

    Proposition comp_struct_cospan_mor_laws
      : struct_cospan_laws
          L
          v₁ v₃
          (comp_struct_cospan h₁ h₂) (comp_struct_cospan k₁ k₂)
          mor_of_comp_struct_cospan_mor.
    Proof.
      split ; cbn.
      - unfold mor_of_comp_struct_cospan_mor.
        rewrite !assoc'.
        rewrite PushoutArrow_PushoutIn1.
        rewrite !assoc.
        apply maponpaths_2.
        apply struct_cospan_sqr_mor_left.
      - unfold mor_of_comp_struct_cospan_mor.
        rewrite !assoc'.
        rewrite PushoutArrow_PushoutIn2.
        rewrite !assoc.
        apply maponpaths_2.
        apply struct_cospan_sqr_mor_right.
    Qed.

    Definition comp_struct_cospan_mor
      : struct_cospan_sqr
          L
          v₁ v₃
          (comp_struct_cospan h₁ h₂) (comp_struct_cospan k₁ k₂).
    Proof.
      use make_struct_cospan_sqr.
      - exact mor_of_comp_struct_cospan_mor.
      - exact comp_struct_cospan_mor_laws.
    Defined.
  End CompCospanMor.

  (** * 7. The left unitor of structured cospans *)
  Section CospanLunitor.
    Context {x y : A}
            (h : struct_cospan L x y).

    Definition struct_cospan_lunitor_mor
      : comp_struct_cospan_Pushout (id_struct_cospan x) h --> ob_of_struct_cospan L h.
    Proof.
      use PushoutArrow.
      - exact (mor_left_of_struct_cospan L h).
      - exact (identity _).
      - abstract
          (cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Proposition is_z_iso_struct_cospan_lunitor_mor_eqs
      : is_inverse_in_precat
          struct_cospan_lunitor_mor
          (PushoutIn2 (comp_struct_cospan_Pushout (id_struct_cospan x) h)).
    Proof.
      split.
      - unfold struct_cospan_lunitor_mor.
        use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
        + rewrite !assoc.
          rewrite PushoutArrow_PushoutIn1.
          rewrite <- PushoutSqrCommutes.
          rewrite id_left, id_right.
          apply idpath.
        + rewrite !assoc.
          rewrite PushoutArrow_PushoutIn2.
          rewrite id_left, id_right.
          apply idpath.
      - unfold struct_cospan_lunitor_mor.
        rewrite PushoutArrow_PushoutIn2.
        apply idpath.
    Qed.

    Definition is_z_iso_struct_cospan_lunitor_mor
      : is_z_isomorphism struct_cospan_lunitor_mor.
    Proof.
      use make_is_z_isomorphism.
      - exact (PushoutIn2 _).
      - exact is_z_iso_struct_cospan_lunitor_mor_eqs.
    Defined.

    Proposition struct_cospan_lunitor_laws
      : struct_cospan_laws
          L
          (identity x) (identity y)
          (comp_struct_cospan (id_struct_cospan x) h) h
          struct_cospan_lunitor_mor.
    Proof.
      split ; cbn ; unfold struct_cospan_lunitor_mor.
      - rewrite functor_id.
        rewrite !id_left.
        rewrite PushoutArrow_PushoutIn1.
        apply idpath.
      - rewrite functor_id.
        rewrite id_left.
        rewrite !assoc'.
        rewrite PushoutArrow_PushoutIn2.
        rewrite id_right.
        apply idpath.
    Qed.

    Definition struct_cospan_lunitor
      : struct_cospan_sqr
          L
          (identity _) (identity _)
          (comp_struct_cospan (id_struct_cospan _) h)
          h.
    Proof.
      use make_struct_cospan_sqr.
      - exact struct_cospan_lunitor_mor.
      - exact struct_cospan_lunitor_laws.
    Defined.
  End CospanLunitor.

  (** * 8. The right unitor of structured cospans *)
  Section CospanRunitor.
    Context {x y : A}
            (h : struct_cospan L x y).

    Definition struct_cospan_runitor_mor
      : comp_struct_cospan_Pushout h (id_struct_cospan y) --> ob_of_struct_cospan L h.
    Proof.
      use PushoutArrow.
      - exact (identity _).
      - exact (mor_right_of_struct_cospan L h).
      - abstract
          (cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Proposition is_z_iso_struct_cospan_runitor_mor_eqs
      : is_inverse_in_precat
          struct_cospan_runitor_mor
          (PushoutIn1 (comp_struct_cospan_Pushout h (id_struct_cospan y))).
    Proof.
      split.
      - unfold struct_cospan_runitor_mor.
        use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
        + rewrite !assoc.
          rewrite PushoutArrow_PushoutIn1.
          rewrite id_left, id_right.
          apply idpath.
        + rewrite !assoc.
          rewrite PushoutArrow_PushoutIn2.
          rewrite PushoutSqrCommutes.
          rewrite id_left, id_right.
          apply idpath.
      - unfold struct_cospan_runitor_mor.
        rewrite PushoutArrow_PushoutIn1.
        apply idpath.
    Qed.

    Definition is_z_iso_struct_cospan_runitor_mor
      : is_z_isomorphism struct_cospan_runitor_mor.
    Proof.
      use make_is_z_isomorphism.
      - exact (PushoutIn1 _).
      - exact is_z_iso_struct_cospan_runitor_mor_eqs.
    Defined.

    Proposition struct_cospan_runitor_laws
      : struct_cospan_laws
          L
          (identity x) (identity y)
          (comp_struct_cospan h (id_struct_cospan y)) h
          struct_cospan_runitor_mor.
    Proof.
      split ; cbn ; unfold struct_cospan_runitor_mor.
      - rewrite functor_id.
        rewrite id_left.
        rewrite !assoc'.
        rewrite PushoutArrow_PushoutIn1.
        rewrite id_right.
        apply idpath.
      - rewrite functor_id.
        rewrite !id_left.
        rewrite PushoutArrow_PushoutIn2.
        apply idpath.
    Qed.

    Definition struct_cospan_runitor
      : struct_cospan_sqr
          L
          (identity _) (identity _)
          (comp_struct_cospan h (id_struct_cospan _))
          h.
    Proof.
      use make_struct_cospan_sqr.
      - exact struct_cospan_runitor_mor.
      - exact struct_cospan_runitor_laws.
    Defined.
  End CospanRunitor.

  (** * 9. The associator of structured cospans *)
  Section CospanAssociator.
    Context {w x y z : A}
            (h₁ : struct_cospan L w x)
            (h₂ : struct_cospan L x y)
            (h₃ : struct_cospan L y z).

    Definition struct_cospan_associator_mor
      : comp_struct_cospan_Pushout h₁ (comp_struct_cospan h₂ h₃)
        -->
        comp_struct_cospan_Pushout (comp_struct_cospan h₁ h₂) h₃.
    Proof.
      use PushoutArrow.
      - exact (PushoutIn1 _ · PushoutIn1 _).
      - use PushoutArrow.
        + exact (PushoutIn2 _ · PushoutIn1 _).
        + exact (PushoutIn2 _).
        + abstract
            (rewrite !assoc ;
             rewrite PushoutSqrCommutes ;
             apply idpath).
      - abstract
          (cbn ;
           rewrite !assoc' ;
           rewrite PushoutArrow_PushoutIn1 ;
           rewrite !assoc ;
           rewrite PushoutSqrCommutes ;
           apply idpath).
    Defined.

    Definition struct_cospan_associator_mor_inv
      : comp_struct_cospan_Pushout (comp_struct_cospan h₁ h₂) h₃
        -->
        comp_struct_cospan_Pushout h₁ (comp_struct_cospan h₂ h₃).
    Proof.
      use PushoutArrow.
      - use PushoutArrow.
        + exact (PushoutIn1 _).
        + exact (PushoutIn1 _ · PushoutIn2 _).
        + abstract
            (rewrite !assoc ;
             rewrite PushoutSqrCommutes ;
             apply idpath).
      - exact (PushoutIn2 _ · PushoutIn2 _).
      - abstract
          (cbn ;
           rewrite !assoc' ;
           rewrite PushoutArrow_PushoutIn2 ;
           rewrite !assoc ;
           rewrite PushoutSqrCommutes ;
           apply idpath).
    Defined.

    Proposition is_iso_struct_cospan_associator_mor_eq
      : is_inverse_in_precat
          struct_cospan_associator_mor
          struct_cospan_associator_mor_inv.
    Proof.
      split.
      - use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
        + rewrite id_right.
          unfold struct_cospan_associator_mor.
          rewrite !assoc.
          rewrite PushoutArrow_PushoutIn1.
          unfold struct_cospan_associator_mor_inv.
          rewrite !assoc'.
          rewrite !PushoutArrow_PushoutIn1.
          apply idpath.
        + rewrite id_right.
          unfold struct_cospan_associator_mor.
          rewrite !assoc.
          rewrite PushoutArrow_PushoutIn2.
          use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
          * rewrite !assoc.
            rewrite PushoutArrow_PushoutIn1.
            unfold struct_cospan_associator_mor_inv.
            rewrite !assoc'.
            rewrite !PushoutArrow_PushoutIn1.
            rewrite !PushoutArrow_PushoutIn2.
            apply idpath.
          * rewrite !assoc.
            rewrite PushoutArrow_PushoutIn2.
            unfold struct_cospan_associator_mor_inv.
            rewrite !PushoutArrow_PushoutIn2.
            apply idpath.
      - use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
        + rewrite id_right.
          unfold struct_cospan_associator_mor_inv.
          rewrite !assoc.
          rewrite PushoutArrow_PushoutIn1.
          use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX _ _ _ _ _))) ; cbn.
          * rewrite !assoc.
            rewrite PushoutArrow_PushoutIn1.
            unfold struct_cospan_associator_mor.
            rewrite !PushoutArrow_PushoutIn1.
            apply idpath.
          * rewrite !assoc.
            rewrite PushoutArrow_PushoutIn2.
            unfold struct_cospan_associator_mor.
            rewrite !assoc'.
            rewrite PushoutArrow_PushoutIn2.
            rewrite PushoutArrow_PushoutIn1.
            apply idpath.
        + rewrite id_right.
          unfold struct_cospan_associator_mor_inv.
          rewrite !assoc.
          rewrite PushoutArrow_PushoutIn2.
          unfold struct_cospan_associator_mor.
          rewrite !assoc'.
          rewrite !PushoutArrow_PushoutIn2.
          apply idpath.
    Qed.

    Definition is_z_iso_struct_cospan_associator_mor
      : is_z_isomorphism struct_cospan_associator_mor.
    Proof.
      use make_is_z_isomorphism.
      - exact struct_cospan_associator_mor_inv.
      - exact is_iso_struct_cospan_associator_mor_eq.
    Defined.

    Proposition struct_cospan_associator_laws
      : struct_cospan_laws
          L
          (identity _) (identity _)
          (comp_struct_cospan h₁ (comp_struct_cospan h₂ h₃))
          (comp_struct_cospan (comp_struct_cospan h₁ h₂) h₃)
          struct_cospan_associator_mor.
    Proof.
      split ; cbn.
      - rewrite functor_id, id_left.
        unfold struct_cospan_associator_mor.
        rewrite !assoc'.
        rewrite PushoutArrow_PushoutIn1.
        apply idpath.
      - rewrite functor_id, id_left.
        unfold struct_cospan_associator_mor.
        rewrite !assoc'.
        rewrite !PushoutArrow_PushoutIn2.
        apply idpath.
    Qed.

    Definition struct_cospan_associator
      : struct_cospan_sqr
          L
          (identity _) (identity _)
          (comp_struct_cospan h₁ (comp_struct_cospan h₂ h₃))
          (comp_struct_cospan (comp_struct_cospan h₁ h₂) h₃).
    Proof.
      use make_struct_cospan_sqr.
      - exact struct_cospan_associator_mor.
      - exact struct_cospan_associator_laws.
    Defined.
  End CospanAssociator.

  (** * 10. Companions and conjoints *)
  Section CompanionsAndConjoints.
    Context {x y : A}
            (f : x --> y).

    Definition struct_cospan_companion
      : struct_cospan L x y.
    Proof.
      use make_struct_cospan.
      - exact (L y).
      - exact (#L f).
      - apply identity.
    Defined.

    Definition struct_cospan_companion_unit
      : struct_cospan_sqr
          L
          f (identity y)
          struct_cospan_companion (id_struct_cospan y).
    Proof.
      use make_struct_cospan_sqr.
      - apply identity.
      - abstract
          (split ; cbn ; [ apply idpath | ] ;
           rewrite (functor_id L) ;
           apply idpath).
    Defined.

    Definition struct_cospan_companion_counit
      : struct_cospan_sqr
          L
          (identity x) f
          (id_struct_cospan x) struct_cospan_companion.
    Proof.
      use make_struct_cospan_sqr.
      - exact (#L f).
      - abstract
          (split ; cbn ;
           [ rewrite (functor_id L), !id_left ; apply idpath | ] ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition struct_cospan_conjoint
      : struct_cospan L y x.
    Proof.
      use make_struct_cospan.
      - exact (L y).
      - apply identity.
      - exact (#L f).
    Defined.

    Definition struct_cospan_conjoint_unit
      : struct_cospan_sqr
          L
          f (identity x)
          (id_struct_cospan x) struct_cospan_conjoint.
    Proof.
      use make_struct_cospan_sqr.
      - exact (#L f).
      - abstract
          (split ; cbn ; [ rewrite id_left, id_right ; apply idpath | ] ;
           rewrite (functor_id L) ;
           apply idpath).
    Defined.

    Definition struct_cospan_conjoint_counit
      : struct_cospan_sqr
          L
          (identity y) f
          struct_cospan_conjoint (id_struct_cospan y).
    Proof.
      use make_struct_cospan_sqr.
      - apply identity.
      - abstract
          (split ; cbn ; [ rewrite (functor_id L) ; apply idpath | ] ;
           apply idpath).
    Defined.
  End CompanionsAndConjoints.
End StandardCospans.

(** * 11. Functors on structured cospans *)
Section FunctorOnCospans.
  Context {A₁ A₂ X₁ X₂ : category}
          {L₁ : A₁ ⟶ X₁}
          {L₂ : A₂ ⟶ X₂}
          {FA : A₁ ⟶ A₂}
          {FX : X₁ ⟶ X₂}
          (α : FA ∙ L₂ ⟹ L₁ ∙ FX).

  Definition functor_on_struct_cospan
             {x y : A₁}
             (f : struct_cospan L₁ x y)
    : struct_cospan L₂ (FA x) (FA y).
  Proof.
    use make_struct_cospan.
    - exact (FX (ob_of_struct_cospan _ f)).
    - exact (α x · #FX (mor_left_of_struct_cospan _ f)).
    - exact (α y · #FX (mor_right_of_struct_cospan _ f)).
  Defined.

  Definition functor_on_struct_cospan_sqr
             {x₁ x₂ y₁ y₂ : A₁}
             {f₁ : struct_cospan L₁ x₁ y₁}
             {f₂ : struct_cospan L₁ x₂ y₂}
             {vx : x₁ --> x₂}
             {vy : y₁ --> y₂}
             (sq : struct_cospan_sqr L₁ vx vy f₁ f₂)
    : struct_cospan_sqr
        L₂
        (#FA vx) (#FA vy)
        (functor_on_struct_cospan f₁) (functor_on_struct_cospan f₂).
  Proof.
    use make_struct_cospan_sqr.
    - exact (#FX (struct_cospan_sqr_ob_mor _ sq)).
    - abstract
        (split ; cbn ;
         [ rewrite !assoc' ;
           rewrite <- functor_comp ;
           rewrite struct_cospan_sqr_mor_left ;
           rewrite functor_comp ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           exact (!(nat_trans_ax α _ _ vx))
         | rewrite !assoc' ;
           rewrite <- functor_comp ;
           rewrite struct_cospan_sqr_mor_right ;
           rewrite functor_comp ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           exact (!(nat_trans_ax α _ _ vy)) ]).
  Defined.

  Definition twosided_disp_cat_of_struct_cospans_functor_data
    : twosided_disp_functor_data
        FA FA
        (twosided_disp_cat_of_struct_cospans L₁)
        (twosided_disp_cat_of_struct_cospans L₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y f, functor_on_struct_cospan f).
    - exact (λ _ _ _ _ _ _ _ _ sq, functor_on_struct_cospan_sqr sq).
  Defined.

  Proposition twosided_disp_cat_of_struct_cospans_functor_laws
    : twosided_disp_functor_laws
        FA FA
        (twosided_disp_cat_of_struct_cospans L₁)
        (twosided_disp_cat_of_struct_cospans L₂)
        twosided_disp_cat_of_struct_cospans_functor_data.
  Proof.
    split.
    - intros x y f.
      use struct_cospan_sqr_eq.
      rewrite transportb_disp_mor2_struct_cospan ; cbn.
      apply functor_id.
    - intro ; intros.
      use struct_cospan_sqr_eq.
      rewrite transportb_disp_mor2_struct_cospan ; cbn.
      apply functor_comp.
  Qed.

  Definition twosided_disp_cat_of_struct_cospans_functor
    : twosided_disp_functor
        FA FA
        (twosided_disp_cat_of_struct_cospans L₁)
        (twosided_disp_cat_of_struct_cospans L₂).
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_struct_cospans_functor_data.
    - exact twosided_disp_cat_of_struct_cospans_functor_laws.
  Defined.
End FunctorOnCospans.
