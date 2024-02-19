(*******************************************************************************************

 Democratic full comprehension categories

 In this file, we define democratic comprehension categories. Our notion of democracy is
 taken from the work by Clairambault and Dybjer. More specifically, a full comprehension
 category is called democratic if for every context `Γ` there is a type `A` in the empty
 context `[]` such `Γ` is isomorphic to the context extension `[] & A`. One could also
 formulate this requirement using the comprehension functor. More specifically, a full
 comprehension category is said to be democratic if the comprehension functor is split
 essentially surjective on the fiber of the empty context (compare to Proposition 2.8 in
 'The biequivalence of locally cartesian closed categories and Martin-Löf type theories'
 and the corresponding statement [is_democratic_weq_split_essentially_surjective]).

 Note that we only define democracy for full comprehension categories. The reason to do so,
 comes from the fact that for full comprehension categories, there is a unique proof of
 democracy. We can understand this from the second and more concise formulation of democracy.
 If a functor `F` between univalent categories is fully faithful, then the type that `F`
 is split essentially surjective is a proposition. The reason for that is that due to the
 fully faithfulness of `F` essential surjectivity is equivalent to split essential
 surjectivity.

 The fact that being democratic is a proposition for full comprehension categories, allows
 us to define the bicategory of democratic full comprehension categories as a subbicategory
 of the bicategory of comprehension categories. Univalence then follows directly from the
 univalence of the subbicategory.

 References
 - 'The biequivalence of locally cartesian closed categories and Martin-Löf type theories'
   by Clairambault and Dybjer.

 Contents
 1. Democratic full comprehension categories
 2. Functors that preserve democracy
 3. The displayed bicategory of democratic full comprehension categories
 4. The univalence of this displayed bicategory

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.FullyFaithfulDispFunctor.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Democratic full comprehension categories *)
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

Definition is_democratic_mor
           {C : full_comp_cat}
           (D : is_democratic C)
           (Γ : C)
  : Γ --> [] & is_democratic_ty D Γ
  := pr1 (is_democratic_iso D Γ).

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

Definition is_democratic_weq_split_essentially_surjective
           (C : full_comp_cat)
  : is_democratic C
    ≃
    split_essentially_surjective (fiber_functor (comp_cat_comprehension C) []).
Proof.
  use weqimplimpl.
  - intros D Γ.
    refine (is_democratic_ty D (pr1 Γ) ,, _).
    use make_z_iso.
    + refine (inv_from_z_iso (is_democratic_iso D (pr1 Γ)) ,, _).
      apply TerminalArrowEq.
    + refine (pr1 (is_democratic_iso D (pr1 Γ)) ,, _).
      apply TerminalArrowEq.
    + split.
      * use eq_cod_mor ; cbn.
        rewrite transportf_cod_disp ; cbn.
        apply z_iso_after_z_iso_inv.
      * use eq_cod_mor ; cbn.
        rewrite transportf_cod_disp ; cbn.
        apply z_iso_inv_after_z_iso.
  - intros H Γ.
    pose ((Γ ,, TerminalArrow _ Γ) : (disp_codomain C)[{functor_identity C []}])
      as Γ'.
    pose (A := pr1 (H Γ')).
    pose (i := pr2 (H Γ')).
    refine (A ,, _).
    use make_z_iso.
    + exact (pr1 (inv_from_z_iso i)).
    + exact (pr11 i).
    + split.
      * refine (_ @ maponpaths pr1 (z_iso_after_z_iso_inv i)).
        cbn.
        rewrite transportf_cod_disp.
        apply idpath.
      * refine (_ @ maponpaths pr1 (z_iso_inv_after_z_iso i)).
        cbn.
        rewrite transportf_cod_disp.
        apply idpath.
  - apply isaprop_is_democratic.
  - use isaprop_split_essentially_surjective.
    + use is_univalent_fiber.
      use disp_univalent_category_is_univalent_disp.
    + use fiber_functor_ff.
      apply full_comp_cat_comprehension_fully_faithful.
Qed.

(** * 2. Functors that preserve democracy *)
Definition democratic_functor_data
           {C₁ C₂ : full_comp_cat}
           (D₁ : is_democratic C₁)
           (D₂ : is_democratic C₂)
           (F : full_comp_cat_functor C₁ C₂)
  : UU
  := ∏ (Γ : C₁),
     let A₁ := comp_cat_type_functor F [] (is_democratic_ty D₁ Γ) in
     let A₂ := is_democratic_ty D₂ (F Γ) in
     A₁ [[ comp_cat_functor_empty_context_arrow F [] ]] -->[ identity _ ] A₂.

Definition democratic_functor_laws
           {C₁ C₂ : full_comp_cat}
           {D₁ : is_democratic C₁}
           {D₂ : is_democratic C₂}
           {F : full_comp_cat_functor C₁ C₂}
           (d : democratic_functor_data D₁ D₂ F)
  : UU.
Proof.
  refine (∏ (Γ : C₁),
          is_democratic_mor D₂ (F Γ)
          =
          #F (is_democratic_mor D₁ Γ)
          · comp_cat_functor_extension F [] (is_democratic_ty D₁ Γ)
          · comp_cat_comp_mor _
          · _
         ).
  - pose (d Γ).
    cbn in m.
Admitted.

Definition is_democratic_functor
           {C₁ C₂ : full_comp_cat}
           (D₁ : is_democratic C₁)
           (D₂ : is_democratic C₂)
           (F : full_comp_cat_functor C₁ C₂)
  : UU
  := ∑ (d : democratic_functor_data D₁ D₂ F),
     democratic_functor_laws d.

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

(** * 3. The displayed bicategory of democratic full comprehension categories *)
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

(** * 4. The univalence of this displayed bicategory *)
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
