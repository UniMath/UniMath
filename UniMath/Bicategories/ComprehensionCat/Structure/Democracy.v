Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.

Local Open Scope cat.

Definition z_iso_disp_codomain
           {C : category}
           {x y : C}
           {f : z_iso x y}
           {h₁ : disp_codomain C x}
           {h₂ : disp_codomain C y}
           (g : z_iso (pr1 h₁) (pr1 h₂))
           (p : g · pr2 h₂ = pr2 h₁ · f)
  : z_iso_disp f h₁ h₂.
Proof.
  use make_z_iso_disp.
  - exact (pr1 g ,, p).
  - simple refine (_ ,, _ ,, _).
    + refine (inv_from_z_iso g ,, _).
      abstract
        (use z_iso_inv_on_right ;
         rewrite !assoc ;
         use z_iso_inv_on_left ;
         exact p).
    + abstract
        (use eq_cod_mor ;
         rewrite transportb_cod_disp ;
         cbn ;
         apply z_iso_after_z_iso_inv).
    + abstract
        (use eq_cod_mor ;
         rewrite transportb_cod_disp ;
         cbn ;
         apply z_iso_inv_after_z_iso).
Defined.

Section DispFunctorReflectIso.
  Context {C₁ C₂ : category}
          {F : C₁ ⟶ C₂}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          (FF : disp_functor F D₁ D₂)
          (HFF : disp_functor_ff FF)
          {x y : C₁}
          {f : z_iso x y}
          {xx : D₁ x}
          {yy : D₁ y}
          (Fff : z_iso_disp
                  (functor_on_z_iso F f)
                  (FF x xx)
                  (FF y yy)).

  Local Open Scope mor_disp.

  Let ff : xx -->[ f ] yy
    := disp_functor_ff_inv FF HFF Fff.
  Let gg : yy -->[ inv_from_z_iso f] xx
    := disp_functor_ff_inv FF HFF (inv_mor_disp_from_z_iso Fff).

  Lemma disp_functor_ff_reflect_disp_iso_left
    : gg ;; ff
      =
      transportb (mor_disp yy yy) (z_iso_after_z_iso_inv f) (id_disp yy).
  Proof.
    unfold ff, gg.
    rewrite <- disp_functor_ff_inv_compose.
    etrans.
    {
      do 2 apply maponpaths.
      exact (z_iso_disp_after_inv_mor Fff).
    }
    unfold transportb.
    rewrite <- (disp_functor_ff_inv_identity FF HFF).
    rewrite <- disp_functor_ff_inv_transportf.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Lemma disp_functor_ff_reflect_disp_iso_right
    : ff ;; gg
      =
      transportb (mor_disp xx xx) (z_iso_inv_after_z_iso f) (id_disp xx).
  Proof.
    unfold ff, gg.
    rewrite <- disp_functor_ff_inv_compose.
    etrans.
    {
      do 2 apply maponpaths.
      exact (inv_mor_after_z_iso_disp Fff).
    }
    unfold transportb.
    rewrite <- (disp_functor_ff_inv_identity FF HFF).
    rewrite <- disp_functor_ff_inv_transportf.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition disp_functor_ff_reflect_disp_iso
    : z_iso_disp f xx yy.
  Proof.
    use make_z_iso_disp.
    - exact ff.
    - simple refine (_ ,, _ ,, _).
      + exact gg.
      + exact disp_functor_ff_reflect_disp_iso_left.
      + exact disp_functor_ff_reflect_disp_iso_right.
  Defined.
End DispFunctorReflectIso.


Notation "'[]'" := (empty_context _).

Definition comp_cat_ty
           {C : full_comp_cat}
           (Γ : C)
  : UU
  := disp_cat_of_types C Γ.

Notation "'ty'" := comp_cat_ty.

Definition comp_cat_ext
           {C : full_comp_cat}
           (Γ : C)
           (A : ty Γ)
  : C
  := comprehension_functor_ob (comp_cat_comprehension C) A.

Notation "Γ '&' A" := (comp_cat_ext Γ A) (at level 20).

Definition comp_cat_proj
           {C : full_comp_cat}
           (Γ : C)
           (A : ty Γ)
  : Γ & A --> Γ
  := comprehension_functor_cod_mor (comp_cat_comprehension C) A.

Notation "'π'" := (comp_cat_proj _).

Definition comp_cat_comp_mor
           {C : full_comp_cat}
           {Γ : C}
           {A B : ty Γ}
           (s : A -->[ identity _ ] B)
  : Γ & A --> Γ & B
  := comprehension_functor_mor (comp_cat_comprehension C) s.

Definition subst_ty
           {C : full_comp_cat}
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A : ty Δ)
  : ty Γ
  := cleaving_ob (cleaving_of_types C) s A.

Notation "A '[[' s ']]'" := (subst_ty s A) (at level 20).



Definition is_democratic
           (C : full_comp_cat)
  : UU
  := ∏ (Γ : C),
     ∑ (A : ty []),
     z_iso Γ ([] & A).

Definition is_democratic_ty
           {C : full_comp_cat}
           (D : is_democratic C)
           (Γ : C)
  : ty []
  := pr1 (D Γ).

Definition is_democratic_iso
           {C : full_comp_cat}
           (D : is_democratic C)
           (Γ : C)
  : z_iso Γ ([] & is_democratic_ty D Γ)
  := pr2 (D Γ).

Proposition transportf_dem
            {C : full_comp_cat}
            {Γ : C}
            {A₁ A₂ : ty (empty_context C)}
            (p : A₁ = A₂)
            (s : Γ --> [] & A₁)
  : transportf (λ A, Γ --> [] & A) p s
    =
    s · comp_cat_comp_mor (idtoiso_disp (idpath _) p).
Proof.
  induction p ; cbn.
  unfold comp_cat_comp_mor.
  rewrite comprehension_functor_mor_id.
  rewrite id_right.
  apply idpath.
Qed.

Proposition eq_is_democratic
            {C : full_comp_cat}
            {D₁ D₂ : is_democratic C}
            (p : ∏ (Γ : C), is_democratic_ty D₁ Γ = is_democratic_ty D₂ Γ)
            (q : ∏ (Γ : C),
                 is_democratic_iso D₁ Γ
                 · comp_cat_comp_mor (idtoiso_disp (idpath _) (p Γ))
                 =
                 is_democratic_iso D₂ Γ)
  : D₁ = D₂.
Proof.
  use funextsec ; intro Γ.
  use total2_paths_f.
  - exact (p Γ).
  - use subtypePath.
    {
      intro.
      apply isaprop_is_z_isomorphism.
    }
    unfold z_iso.
    rewrite pr1_transportf.
    rewrite transportf_dem.
    exact (q Γ).
Qed.

Definition isaprop_is_democratic
           (C : full_comp_cat)
  : isaprop (is_democratic C).
Proof.
  use invproofirrelevance.
  intros D₁ D₂.
  use eq_is_democratic.
  - intro Γ.
    use (isotoid_disp
           (disp_univalent_category_is_univalent_disp _)
           (idpath _)
           _).
    use (disp_functor_ff_reflect_disp_iso
           _
           (full_comp_cat_comprehension_fully_faithful C)).
    use z_iso_disp_codomain.
    + exact (z_iso_comp
               (z_iso_inv (is_democratic_iso D₁ Γ))
               (is_democratic_iso D₂ Γ)).
    + use TerminalArrowEq.
  - intro Γ.
    cbn -[idtoiso_disp].
    rewrite idtoiso_isotoid_disp.
    cbn.
    etrans.
    {
      apply maponpaths.
      exact (maponpaths
               pr1
               (FF_disp_functor_ff_inv
                  (full_comp_cat_comprehension_fully_faithful C)
                  _)).
    }
    cbn.
    rewrite !assoc.
    rewrite z_iso_inv_after_z_iso.
    apply id_left.
Qed.

Definition is_democratic_functor
           {C₁ C₂ : full_comp_cat}
           (D₁ : is_democratic C₁)
           (D₂ : is_democratic C₂)
           (F : full_comp_cat_functor C₁ C₂)
  : UU.
Proof.
Admitted.

Proposition isaprop_is_democratic_functor
            {C₁ C₂ : full_comp_cat}
            (D₁ : is_democratic C₁)
            (D₂ : is_democratic C₂)
            (F : full_comp_cat_functor C₁ C₂)
  : isaprop (is_democratic_functor D₁ D₂ F).
Proof.
Admitted.

Proposition identity_is_democratic
            {C : full_comp_cat}
            (D : is_democratic C)
  : is_democratic_functor D D (id₁ C).
Proof.
Admitted.

Proposition comp_is_democratic
            {C₁ C₂ C₃ : full_comp_cat}
            {D₁ : is_democratic C₁}
            {D₂ : is_democratic C₂}
            {D₃ : is_democratic C₃}
            {F : full_comp_cat_functor C₁ C₂}
            {G : full_comp_cat_functor C₂ C₃}
            (HF : is_democratic_functor D₁ D₂ F)
            (HG : is_democratic_functor D₂ D₃ G)
  : is_democratic_functor D₁ D₃ (F · G).
Proof.
Admitted.

Definition disp_bicat_of_democracy
  : disp_bicat bicat_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact (λ (C : full_comp_cat), is_democratic C).
  - exact (λ (C₁ C₂ : full_comp_cat)
             (D₁ : is_democratic C₁)
             (D₂ : is_democratic C₂)
             (F : full_comp_cat_functor C₁ C₂),
           is_democratic_functor D₁ D₂ F).
  - abstract
      (exact @identity_is_democratic).
  - abstract
      (exact @comp_is_democratic).
Defined.

Definition univalent_2_1_disp_bicat_of_democracy
  : disp_univalent_2_1 disp_bicat_of_democracy.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ D₁ D₂ F.
  apply isaprop_is_democratic_functor.
Qed.

Definition univalent_2_0_disp_bicat_of_democracy
  : disp_univalent_2_0 disp_bicat_of_democracy.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_full_comp_cat.
  - intro C.
    apply isaprop_is_democratic.
  - intros C₁ C₂ D₁ D₂ F.
    apply isaprop_is_democratic_functor.
Qed.

Definition univalent_2_disp_bicat_of_democracy
  : disp_univalent_2 disp_bicat_of_democracy.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_democracy.
  - exact univalent_2_1_disp_bicat_of_democracy.
Defined.
