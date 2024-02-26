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

 Another important thing to notice is what morphisms of democratic comprehension categories
 are. In the paper by Clairambault and Dybjer morphisms are required to preserve democracy.
 However, this requirement is automatic. If one stares at the diagram of Definition 3.6 in
 that paper, then one can see (after some pondering) that all morphisms in that diagram are
 isomorphisms. As such, there must be a unique `d_Γ` that makes this diagram commute. Note
 that we need to use pseudo morphisms here, because otherwise, context extension is not
 necessarily preserved up to isomorphism. Note that in the proof we make use of the fact
 that our comprehension category is full. Since fully faithful displayed functors reflect
 isomorphisms, we can construct the desired isomorphism (of types) by constructing an
 isomorphism in the slice category (where it is fixed by the diagram). The corresponding
 statement in the formalization is stated as 'the type that a functor is democratic, is
 contractible' ([iscontr_is_democratic_functor]).

 This allows us to define the bicategory of democratic comprehension categories as a full
 subbicategory of the bicategory of full comprehension categories.

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
     z_iso_disp
       (identity_z_iso _)
       (comp_cat_type_functor F [] (is_democratic_ty D₁ Γ))
       ((is_democratic_ty D₂ (F Γ)) [[ TerminalArrow _ _ ]]).

Definition democratic_functor_laws_mor
           {C₁ C₂ : full_comp_cat}
           {D₁ : is_democratic C₁}
           {D₂ : is_democratic C₂}
           {F : full_comp_cat_functor C₁ C₂}
           (d : democratic_functor_data D₁ D₂ F)
           (Γ : C₁)
  : z_iso (F Γ) ([] & is_democratic_ty D₂ (F Γ))
  := z_iso_comp
       (functor_on_z_iso F (is_democratic_iso D₁ Γ))
       (z_iso_comp
          (comp_cat_functor_extension F [] (is_democratic_ty D₁ Γ))
          (z_iso_comp
             (comp_cat_comp_z_iso (d Γ))
             (comp_cat_extend_over_iso
                _
                _
                (comp_cat_functor_empty_context_is_z_iso _)))).

Definition democratic_functor_laws
           {C₁ C₂ : full_comp_cat}
           {D₁ : is_democratic C₁}
           {D₂ : is_democratic C₂}
           {F : full_comp_cat_functor C₁ C₂}
           (d : democratic_functor_data D₁ D₂ F)
  : UU
  := ∏ (Γ : C₁),
     (is_democratic_iso D₂ (F Γ) : _ --> _)
     =
     democratic_functor_laws_mor d Γ.

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
  use invproofirrelevance.
  intros φ₁ φ₂.
  use subtypePath.
  {

    intro.
    use impred ; intro.
    apply homset_property.
  }
  use funextsec ; intro Γ.
  use subtypePath.
  {
    intro.
    apply isaprop_is_z_iso_disp.
  }
  use (invmaponpathsweq
         (disp_functor_ff_weq _ (full_comp_cat_comprehension_fully_faithful C₂) _ _ _)).
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  pose (!(pr2 φ₁ Γ) @ pr2 φ₂ Γ) as p.
  unfold democratic_functor_laws_mor in p.
  use (cancel_z_iso
         _ _
         (comp_cat_extend_over_iso
            (is_democratic_ty D₂ (F Γ))
            (TerminalArrow [] (F []))
            (comp_cat_functor_empty_context_is_z_iso F))).
  use (cancel_z_iso'
         (comp_cat_functor_extension F [] (is_democratic_ty D₁ Γ))).
  use (cancel_z_iso'
         (functor_on_z_iso F (is_democratic_iso D₁ Γ))).
  exact p.
Qed.

Section AllAreDemocratic.
  Context {C₁ C₂ : full_comp_cat}
          (D₁ : is_democratic C₁)
          (D₂ : is_democratic C₂)
          (F : full_comp_cat_functor C₁ C₂).

  Section TheIso.
    Context (Γ : C₁).

    Definition all_functor_democratic_iso
      : z_iso
          (F [] & comp_cat_type_functor F [] (is_democratic_ty D₁ Γ))
          (F [] & (is_democratic_ty D₂ (F Γ) [[TerminalArrow [] (F [])]]))
      := z_iso_comp
           (z_iso_comp
              (z_iso_inv
                 (comp_cat_functor_extension F [] (is_democratic_ty D₁ Γ)))
              (z_iso_comp
                 (functor_on_z_iso
                    F
                    (z_iso_inv (is_democratic_iso D₁ Γ)))
                 (is_democratic_iso D₂ (F Γ))))
           (z_iso_inv
              (comp_cat_extend_over_iso
                 _
                 _
                 (comp_cat_functor_empty_context_is_z_iso F))).

    Proposition all_functor_democratic_data_eq
      : all_functor_democratic_iso · π _ = π _ · identity _.
    Proof.
      use comp_cat_functor_empty_context_arrow_eq.
    Qed.

    Definition all_functor_democratic_data
      : z_iso_disp
          (identity_z_iso (F []))
          (comp_cat_type_functor F [] (is_democratic_ty D₁ Γ))
          (is_democratic_ty D₂ (F Γ) [[TerminalArrow [] (F [])]]).
    Proof.
      use (disp_functor_ff_reflect_disp_iso
             _
             (full_comp_cat_comprehension_fully_faithful C₂)).
      use z_iso_disp_codomain.
      - exact all_functor_democratic_iso.
      - exact all_functor_democratic_data_eq.
    Defined.
  End TheIso.

  Proposition all_functor_democratic_laws
    : democratic_functor_laws all_functor_democratic_data.
  Proof.
    intro Γ.
    refine (!_).
    unfold democratic_functor_laws_mor, all_functor_democratic_data.
    cbn -[comp_cat_functor_extension comp_cat_comp_z_iso comp_cat_extend_over_iso].
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply (maponpaths
               pr1
               (FF_disp_functor_ff_inv (full_comp_cat_comprehension_fully_faithful C₂) _)).
    }
    cbn -[comp_cat_extend_over_iso].
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 4 apply maponpaths_2.
      exact (z_iso_inv_after_z_iso
               (comp_cat_functor_extension F [] (is_democratic_ty D₁ Γ))).
    }
    rewrite id_left.
    rewrite !assoc.
    rewrite <- functor_comp.
    rewrite z_iso_inv_after_z_iso.
    rewrite functor_id.
    rewrite id_left.
    rewrite !assoc'.
    refine (_ @ id_right _).
    apply maponpaths.
    apply z_iso_after_z_iso_inv.
  Qed.
End AllAreDemocratic.

Proposition all_functors_democratic
            {C₁ C₂ : full_comp_cat}
            (D₁ : is_democratic C₁)
            (D₂ : is_democratic C₂)
            (F : full_comp_cat_functor C₁ C₂)
  : is_democratic_functor D₁ D₂ F.
Proof.
  simple refine (_ ,, _).
  - exact (all_functor_democratic_data D₁ D₂ F).
  - exact (all_functor_democratic_laws D₁ D₂ F).
Defined.

Proposition iscontr_is_democratic_functor
            {C₁ C₂ : full_comp_cat}
            (D₁ : is_democratic C₁)
            (D₂ : is_democratic C₂)
            (F : full_comp_cat_functor C₁ C₂)
  : iscontr (is_democratic_functor D₁ D₂ F).
Proof.
  use iscontraprop1.
  - exact (isaprop_is_democratic_functor D₁ D₂ F).
  - exact (all_functors_democratic D₁ D₂ F).
Defined.

(** * 3. The displayed bicategory of democratic full comprehension categories *)
Definition disp_bicat_of_democracy
  : disp_bicat bicat_full_comp_cat
  := disp_fullsubbicat _ (λ (C : full_comp_cat), is_democratic C).

(** * 4. The univalence of this displayed bicategory *)
Definition univalent_2_1_disp_bicat_of_democracy
  : disp_univalent_2_1 disp_bicat_of_democracy.
Proof.
  apply disp_fullsubbicat_univalent_2_1.
Qed.

Definition univalent_2_0_disp_bicat_of_democracy
  : disp_univalent_2_0 disp_bicat_of_democracy.
Proof.
  use disp_univalent_2_0_fullsubbicat.
  - exact is_univalent_2_bicat_full_comp_cat.
  - intro C.
    apply isaprop_is_democratic.
Qed.

Definition univalent_2_disp_bicat_of_democracy
  : disp_univalent_2 disp_bicat_of_democracy.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_democracy.
  - exact univalent_2_1_disp_bicat_of_democracy.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_democracy
  : disp_2cells_isaprop disp_bicat_of_democracy.
Proof.
  apply disp_2cells_isaprop_fullsubbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_democracy
  : disp_locally_groupoid disp_bicat_of_democracy.
Proof.
  apply disp_locally_groupoid_fullsubbicat.
Qed.
