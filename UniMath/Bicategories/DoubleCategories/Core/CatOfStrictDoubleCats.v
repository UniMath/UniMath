(*********************************************************************************

 The univalent category of strict double categories

 In this file, we define the univalent category of strict double categories.
 The approach is as follows:
 1. We start with the univalent category of strict categories.
 2. On top of it, we define a displayed category such that the objects over a
    strict category `C` are strict 2-sided displayed categories over `C` and `C`.
 3. The resulting total category is [cat_of_strict_twosided_disp_cat], which was
    defined in the file `DisplayedCats.Examples.StrictTwoSidedDispCat.v`.
 4. On top of [cat_of_strict_twosided_disp_cat], we define two more displayed
    categories. One represents horizontal identities, which we define in
    [disp_cat_of_strict_twosided_disp_cat_hor_id], and the other adds horizontal
    compositions ([disp_cat_of_strict_twosided_disp_cat_hor_comp]).
 5. Finally, we take a full subcategory ([disp_cat_of_strict_double_cat]).
 Note that the first two steps are performed in the files `CategoryOfSetCategories.v`
 and `StrictTwoSidedDispCat.v`.

 To prove that the resulting category is univalent, we prove that each layer in
 this construction is univalent.

 Contents
 1. The displayed category of horizontal identities
 2. The displayed category of horizontal compositions
 3. The displayed category of horizontal identities and compositions
 4. The category of strict double categories

 *********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.StrictTwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.

Local Open Scope cat.

(** * 1. The displayed category of horizontal identities *)
Definition disp_cat_ob_mor_of_strict_twosided_disp_cat_hor_id
  : disp_cat_ob_mor cat_of_strict_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact (λ CD, hor_id (pr12 CD)).
  - exact (λ CD₁ CD₂ I₁ I₂ F, preserves_hor_id I₁ I₂ (pr2 F)).
Defined.

Definition disp_cat_id_comp_of_strict_twosided_disp_cat_hor_id
  : disp_cat_id_comp
      cat_of_strict_twosided_disp_cat
      disp_cat_ob_mor_of_strict_twosided_disp_cat_hor_id.
Proof.
  simple refine (_ ,, _).
  - intros CD.
    apply identity_preserves_hor_id.
  - intros CD₁ CD₂ CD₃ F G I₁ I₂ I₃ FI GI.
    exact (composition_preserves_hor_id FI GI).
Qed.

Definition disp_cat_data_of_strict_twosided_disp_cat_hor_id
  : disp_cat_data cat_of_strict_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_of_strict_twosided_disp_cat_hor_id.
  - exact disp_cat_id_comp_of_strict_twosided_disp_cat_hor_id.
Defined.

Proposition disp_cat_of_strict_twosided_disp_cat_hor_id_axioms
  : disp_cat_axioms
      cat_of_strict_twosided_disp_cat
      disp_cat_data_of_strict_twosided_disp_cat_hor_id.
Proof.
  repeat split ; intros.
  - apply isaprop_preserves_hor_id.
  - apply isaprop_preserves_hor_id.
  - apply isaprop_preserves_hor_id.
  - apply isasetaprop.
    apply isaprop_preserves_hor_id.
Qed.

Definition disp_cat_of_strict_twosided_disp_cat_hor_id
  : disp_cat cat_of_strict_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_of_strict_twosided_disp_cat_hor_id.
  - exact disp_cat_of_strict_twosided_disp_cat_hor_id_axioms.
Defined.

Proposition transportf_hor_id_data
            {C : category}
            {D : twosided_disp_cat C C}
            {x y : C}
            {f : x --> y}
            {g : x --> y}
            {ψ₁ ψ₂ : ∏ (x : C), D x x}
            (p : ψ₁ = ψ₂)
            (fg : ψ₁ x -->[ f ][ g ] ψ₁ y)
  : transportf
      (λ (φ : ∏ (x : C), D x x), φ x -->[ f ][ g ] φ y)
      p
      fg
    =
    transportf_disp_mor2
      (id_right _ @ id_left _)
      (id_right _ @ id_left _)
      (idtoiso_twosided_disp (idpath _) (idpath _) (!(toforallpaths _ _ _ p x))
       ;;2 fg
       ;;2 idtoiso_twosided_disp (idpath _) (idpath _) (toforallpaths _ _ _ p y)).
Proof.
  induction p ; cbn.
  rewrite (id_two_disp_right (D := D)).
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite (id_two_disp_left (D := D)).
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  refine (!_).
  apply transportf_disp_mor2_idpath.
Qed.

Proposition is_univalent_disp_cat_of_strict_twosided_disp_cat_hor_id
  : is_univalent_disp disp_cat_of_strict_twosided_disp_cat_hor_id.
Proof.
  use is_univalent_disp_from_fibers.
  intros CD I₁ I₂.
  use isweqimplimpl.
  - intro F.
    use subtypePath.
    {
      intro.
      apply isaprop_hor_id_laws.
    }
    use total2_paths_f.
    + use funextsec.
      exact (pr11 F).
    + use funextsec ; intro x.
      use funextsec ; intro y.
      use funextsec ; intro f.
      rewrite !transportf_sec_constant.
      rewrite transportf_hor_id_data.
      rewrite !toforallpaths_funextsec.
      rewrite assoc_two_disp_alt.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        do 2 apply maponpaths.
        exact (is_natural_preserves_hor_id (pr1 F) f).
      }
      rewrite two_disp_post_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite assoc_two_disp.
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply idtoiso_twosided_disp_concat.
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite pathsinv0l.
      cbn.
      rewrite (id_two_disp_left (D := pr12 CD)).
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - apply isaset_hor_id.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_z_iso_disp.
    + intros.
      apply isaprop_preserves_hor_id.
Qed.

(** * 2. The displayed categoryes of horizontal compositions *)
Definition disp_cat_ob_mor_of_strict_twosided_disp_cat_hor_comp
  : disp_cat_ob_mor cat_of_strict_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact (λ CD, hor_comp (pr12 CD)).
  - exact (λ CD₁ CD₂ Cm₁ Cm₂ F, preserves_hor_comp Cm₁ Cm₂ (pr2 F)).
Defined.

Definition disp_cat_id_comp_of_strict_twosided_disp_cat_hor_comp
  : disp_cat_id_comp
      cat_of_strict_twosided_disp_cat
      disp_cat_ob_mor_of_strict_twosided_disp_cat_hor_comp.
Proof.
  simple refine (_ ,, _).
  - intros CD Cm.
    exact (identity_preserves_hor_comp Cm).
  - intros CD₁ CD₂ CD₃ F G Cm₁ Cm₂ Cm₃ Fc Gc.
    exact (composition_preserves_hor_comp Fc Gc).
Qed.

Definition disp_cat_data_of_strict_twosided_disp_cat_hor_comp
  : disp_cat_data cat_of_strict_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_of_strict_twosided_disp_cat_hor_comp.
  - exact disp_cat_id_comp_of_strict_twosided_disp_cat_hor_comp.
Defined.

Proposition disp_cat_of_strict_twosided_disp_cat_hor_comp_axioms
  : disp_cat_axioms
      cat_of_strict_twosided_disp_cat
      disp_cat_data_of_strict_twosided_disp_cat_hor_comp.
Proof.
  repeat split ; intros.
  - apply isaprop_preserves_hor_comp.
  - apply isaprop_preserves_hor_comp.
  - apply isaprop_preserves_hor_comp.
  - apply isasetaprop.
    apply isaprop_preserves_hor_comp.
Qed.

Definition disp_cat_of_strict_twosided_disp_cat_hor_comp
  : disp_cat cat_of_strict_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_of_strict_twosided_disp_cat_hor_comp.
  - exact disp_cat_of_strict_twosided_disp_cat_hor_comp_axioms.
Defined.

Definition transportf_hor_comp_data_path
           {C : category}
           {D : twosided_disp_cat C C}
           {ψ₁ ψ₂ : ∏ (x y z : C), D x y → D y z → D x z}
           (p : ψ₁ = ψ₂)
           {x y z : C}
           (h : D x y)
           (k : D y z)
  : ψ₁ x y z h k
    =
    ψ₂ x y z h k
  := toforallpaths
       _ _ _
       (toforallpaths
          _ _ _
          (toforallpaths
             _ _ _
             (toforallpaths
                _ _ _
                (toforallpaths _ _ _ p x)
                y)
             z)
          h)
       k.

Proposition transportf_hor_comp_data
            {C : category}
            {D : twosided_disp_cat C C}
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {vx : x₁ --> x₂}
            {vy : y₁ --> y₂}
            {vz : z₁ --> z₂}
            {h₁ : D x₁ y₁}
            {k₁ : D y₁ z₁}
            {h₂ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            (s₁ : h₁ -->[ vx ][ vy] h₂)
            (s₂ : k₁ -->[ vy ][ vz] k₂)
            {ψ₁ ψ₂ : ∏ (x y z : C), D x y → D y z → D x z}
            (p : ψ₁ = ψ₂)
            (fg : ψ₁ x₁ y₁ z₁ h₁ k₁
                  -->[ vx ][ vz ]
                  ψ₁ x₂ y₂ z₂ h₂ k₂)
  : transportf
      (λ (φ : ∏ (x y z : C), D x y → D y z → D x z),
       φ x₁ y₁ z₁ h₁ k₁ -->[ vx ][ vz ] φ x₂ y₂ z₂ h₂ k₂)
      p
      fg
    =
    transportf_disp_mor2
      (id_right _ @ id_left _)
      (id_right _ @ id_left _)
      (idtoiso_twosided_disp
         (idpath _) (idpath _)
         (!(transportf_hor_comp_data_path p h₁ k₁))
       ;;2 fg
       ;;2 idtoiso_twosided_disp
             (idpath _) (idpath _)
             (transportf_hor_comp_data_path p h₂ k₂)).
Proof.
  induction p ; cbn.
  rewrite (id_two_disp_right (D := D)).
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite (id_two_disp_left (D := D)).
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  refine (!_).
  apply transportf_disp_mor2_idpath.
Qed.

Proposition is_univalent_disp_cat_of_strict_twosided_disp_cat_hor_comp
  : is_univalent_disp disp_cat_of_strict_twosided_disp_cat_hor_comp.
Proof.
  use is_univalent_disp_from_fibers.
  intros CD Cm₁ Cm₂.
  use isweqimplimpl.
  - intro F.
    use subtypePath.
    {
      intro.
      apply isaprop_hor_comp_laws.
    }
    use total2_paths_f.
    + use funextsec ; intro x.
      use funextsec ; intro y.
      use funextsec ; intro z.
      use funextsec ; intro f.
      use funextsec ; intro g.
      exact (pr11 F x y z f g).
    + use funextsec ; intro x₁.
      use funextsec ; intro x₂.
      use funextsec ; intro y₁.
      use funextsec ; intro y₂.
      use funextsec ; intro z₁.
      use funextsec ; intro z₂.
      use funextsec ; intro vx.
      use funextsec ; intro vy.
      use funextsec ; intro vz.
      use funextsec ; intro h₁.
      use funextsec ; intro k₁.
      use funextsec ; intro h₂.
      use funextsec ; intro k₂.
      use funextsec ; intro s₁.
      use funextsec ; intro s₂.
      rewrite !transportf_sec_constant.
      rewrite (transportf_hor_comp_data s₁ s₂).
      unfold transportf_hor_comp_data_path.
      rewrite !toforallpaths_funextsec.
      rewrite assoc_two_disp_alt.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        do 2 apply maponpaths.
        apply (is_natural_preserves_hor_comp (pr1 F)).
      }
      rewrite two_disp_post_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite assoc_two_disp.
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply idtoiso_twosided_disp_concat.
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite pathsinv0l.
      cbn.
      rewrite (id_two_disp_left (D := pr12 CD)).
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - apply isaset_hor_comp.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_z_iso_disp.
    + intros.
      apply isaprop_preserves_hor_comp.
Qed.

(** * 3. The displayed category of horizontal identities and compositions *)
Definition disp_cat_of_strict_twosided_disp_cat_hor_id_comp
  : disp_cat cat_of_strict_twosided_disp_cat
  := dirprod_disp_cat
       disp_cat_of_strict_twosided_disp_cat_hor_id
       disp_cat_of_strict_twosided_disp_cat_hor_comp.

Proposition is_univalent_disp_cat_of_strict_twosided_disp_cat_hor_id_comp
  : is_univalent_disp disp_cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  use dirprod_disp_cat_is_univalent.
  - exact is_univalent_disp_cat_of_strict_twosided_disp_cat_hor_id.
  - exact is_univalent_disp_cat_of_strict_twosided_disp_cat_hor_comp.
Qed.

Definition cat_of_strict_twosided_disp_cat_hor_id_comp
  : category
  := total_category disp_cat_of_strict_twosided_disp_cat_hor_id_comp.

Proposition is_univalent_cat_of_strict_twosided_disp_cat_hor_id_comp
  : is_univalent cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  use is_univalent_total_category.
  - exact is_univalent_cat_of_strict_twosided_disp_cat.
  - exact is_univalent_disp_cat_of_strict_twosided_disp_cat_hor_id_comp.
Qed.

(** * 4. The category of strict double categories *)
Definition disp_cat_of_strict_double_cat
  : disp_cat cat_of_strict_twosided_disp_cat_hor_id_comp
  := disp_full_sub
       cat_of_strict_twosided_disp_cat_hor_id_comp
       (λ C, strict_double_cat_laws (pr12 C) (pr22 C)).

Proposition is_univalent_disp_cat_of_strict_double_cat
  : is_univalent_disp disp_cat_of_strict_double_cat.
Proof.
  use disp_full_sub_univalent.
  intro CD.
  apply isaprop_strict_double_cat_laws.
Qed.

Definition univalent_cat_of_strict_double_cat
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (total_category disp_cat_of_strict_double_cat).
  - use is_univalent_total_category.
    + exact is_univalent_cat_of_strict_twosided_disp_cat_hor_id_comp.
    + exact is_univalent_disp_cat_of_strict_double_cat.
Defined.
