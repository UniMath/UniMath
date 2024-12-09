Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.

Local Open Scope cat.

(** * *)
Definition is_disp_setgrpd
           {C : category}
           (D : disp_cat C)
  : UU
  := (∏ (x : C), isaset (D x))
     ×
     groupoidal_disp_cat D.

Definition disp_setgrpd
           (C : category)
  : UU
  := ∑ (D : disp_cat C), is_disp_setgrpd D.

Coercion disp_setgrpd_to_disp_cat
         {C : category}
         (D : disp_setgrpd C)
  : disp_cat C
  := pr1 D.

Proposition isaset_ob_disp_set_grpd
            {C : category}
            (D : disp_setgrpd C)
            (x : C)
  : isaset (D x).
Proof.
  exact (pr12 D x).
Qed.

Definition is_z_iso_disp_set_grpd
           {C : category}
           (D : disp_setgrpd C)
           {x y : C}
           {f : x --> y}
           (Hf : is_z_isomorphism f)
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : is_z_iso_disp (make_z_iso' f Hf) ff
  := pr22 D x y f Hf xx yy ff.



Definition disp_cat_ob_mor_of_disp_setgrpd
  : disp_cat_ob_mor cat_of_setgroupoid.
Proof.
  simple refine (_ ,, _).
  - exact (λ (G : setgroupoid), disp_setgrpd G).
  - exact (λ (G₁ G₂ : setgroupoid)
             (D₁ : disp_setgrpd G₁)
             (D₂ : disp_setgrpd G₂)
             (F : G₁ --> G₂),
           disp_functor (pr1 F) D₁ D₂).
Defined.

Definition disp_cat_id_comp_of_disp_setgrpd
  : disp_cat_id_comp
      cat_of_setgroupoid
      disp_cat_ob_mor_of_disp_setgrpd.
Proof.
  simple refine (_ ,, _).
  - exact (λ (G : setgroupoid)
             (D : disp_setgrpd G),
           disp_functor_identity D).
  - exact (λ (G₁ G₂ G₃ : setgroupoid)
             (F₁ : G₁ --> G₂)
             (F₂ : G₂ --> G₃)
             (D₁ : disp_setgrpd G₁)
             (D₂ : disp_setgrpd G₂)
             (D₃ : disp_setgrpd G₃)
             (FF₁ : disp_functor (pr1 F₁) D₁ D₂)
             (FF₂ : disp_functor (pr1 F₂) D₂ D₃),
           disp_functor_composite FF₁ FF₂).
Defined.

Definition disp_cat_data_of_disp_setgrpd
  : disp_cat_data cat_of_setgroupoid.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_of_disp_setgrpd.
  - exact disp_cat_id_comp_of_disp_setgrpd.
Defined.

Proposition transportb_disp_setgrpd_ob_help
            {G₁ G₂ : setgroupoid}
            {F F' : G₁ --> G₂}
            (p : F = F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
            (x : ob G₁)
            (xx : pr1 D₁ x)
  : pr11 (transportb (mor_disp D₁ D₂) p FF) x xx
    =
    transportb (pr1 D₂) (maponpaths (λ H, pr111 H x) p) (pr1 FF x xx).
Proof.
  induction p.
  apply idpath.
Qed.

Proposition transportb_disp_setgrpd
            {G₁ G₂ : setgroupoid}
            {FD : functor_data G₁ G₂}
            {HF₁ HF₂ : is_functor FD}
            {t₁ t₂ : unit}
            (F := ((FD ,, HF₁) ,, t₁) : G₁ --> G₂)
            (F' := ((FD ,, HF₂) ,, t₂) : G₁ --> G₂)
            (p : F = F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
  : pr1 (transportb (mor_disp D₁ D₂) p FF) = pr1 FF.
Proof.
  use total2_paths_f.
  - use funextsec ; intro x.
    use funextsec ; intro xx.
    etrans.
    {
      apply transportb_disp_setgrpd_ob_help.
    }

Admitted.

Proposition isaset_disp_functor
            {G₁ G₂ : setgroupoid}
            (F : G₁ --> G₂)
            (D₁ : disp_cat_data_of_disp_setgrpd G₁)
            (D₂ : disp_cat_data_of_disp_setgrpd G₂)
  : isaset (D₁ -->[ F ] D₂).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + do 2 (use impred_isaset ; intro).
      apply isaset_ob_disp_set_grpd.
    + intro.
      do 6 (use impred_isaset ; intro).
      apply homsets_disp.
  - intro.
    apply isasetaprop.
    apply isaprop_disp_functor_axioms.
Qed.

Proposition disp_cat_axioms_of_disp_setgrpd
  : disp_cat_axioms
      cat_of_setgroupoid
      disp_cat_data_of_disp_setgrpd.
Proof.
  repeat split.
  - intros G₁ G₂ F D₁ D₂ FF.
    use disp_functor_eq.
    refine (!_).
    etrans.
    {
      apply transportb_disp_setgrpd.
    }
    apply idpath.
  - intros G₁ G₂ F D₁ D₂ FF.
    use disp_functor_eq.
    refine (!_).
    etrans.
    {
      apply transportb_disp_setgrpd.
    }
    apply idpath.
  - intros G₁ G₂ G₃ G₄ F₁ F₂ F₃ D₁ D₂ D₃ D₄ FF₁ FF₂ FF₃.
    use disp_functor_eq.
    refine (!_).
    etrans.
    {
      apply transportb_disp_setgrpd.
    }
    apply idpath.
  - intros G₁ G₂ F D₁ D₂.
    apply isaset_disp_functor.
Qed.

Definition disp_cat_of_disp_setgrpd
  : disp_cat cat_of_setgroupoid.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_of_disp_setgrpd.
  - exact disp_cat_axioms_of_disp_setgrpd.
Defined.
