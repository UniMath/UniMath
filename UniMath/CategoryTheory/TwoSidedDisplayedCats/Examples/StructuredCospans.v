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

 Contents
 1. The 2-sided displayed category of structured cospans
 2. Builders and accessors for structured cospans
 3. The univalence of the 2-sided displayed category of structured cospans

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.

Local Open Scope cat.

Section StructuredCospans.
  Context {A X : category}
          (L : A ⟶ X).

  (**
   1. The 2-sided displayed category of structured cospans
   *)
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

  (**
   2. Builders and accessors for structured cospans
   *)
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

  (**
   3. The univalence of the 2-sided displayed category of structured cospans
   *)
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
End StructuredCospans.
