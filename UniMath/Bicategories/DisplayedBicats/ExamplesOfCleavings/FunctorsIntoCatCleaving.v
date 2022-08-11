(******************************************************************************************

 The fibrations of functors into categories

 In this file, we prove that the displayed bicategory of functors into categories has a
 local opcleaving, a local isocleaving, and a global cleaving.

 Contents:
 1. Local opcleaving
 2. Local isocleaving
 3. Global cleaving

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.StrictCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FunctorsIntoCat.

Local Open Scope cat.

(**
 1. Local opcleaving
 *)
Definition functors_into_cat_is_opcartesian_2cell
           {C₁ C₂ : bicat_of_strict_cats}
           {F₁ F₂ : C₁ --> C₂}
           {α : F₁ ==> F₂}
           {G₁ : disp_bicat_of_functors_into_cat C₁}
           {G₂ : disp_bicat_of_functors_into_cat C₂}
           {β₁ : G₁ -->[ F₁ ] G₂}
           {β₂ : G₁ -->[ F₂ ] G₂}
           (p : β₁ ==>[ α ] β₂)
  : is_opcartesian_2cell disp_bicat_of_functors_into_cat p.
Proof.
  intros H GH γ ββ.
  use iscontraprop1.
  - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
    + use impred ; intro.
      apply homset_property.
    + apply disp_bicat_of_functors_into_cat.
  - simple refine (_ ,, _).
    + intro x ; cbn.
      refine (_ @ ββ x).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (functor_comp G₂).
      }
      refine (assoc (pr1 β₁ x) (# (pr1 G₂) (pr1 α x)) _ @ _).
      apply maponpaths_2.
      exact (p x).
    + apply functors_into_cat_disp_2cells_isaprop.
Qed.

Definition functors_into_cat_local_opcleaving
  : local_opcleaving disp_bicat_of_functors_into_cat.
Proof.
  intros C₁ C₂ G₁ G₂ F₁ F₂ α β.
  simple refine (_ ,, _ ,, functors_into_cat_is_opcartesian_2cell _).
  - exact (nat_trans_comp _ _ _ α (post_whisker β _)).
  - abstract
      (intro x ; cbn ;
       apply idpath).
Defined.

(**
 2. Local isocleaving
 *)
Definition functors_into_cat_local_iso_cleaving
  : local_iso_cleaving disp_bicat_of_functors_into_cat.
Proof.
  intros C₁ C₂ G₁ G₂ F₁ F₂ α β.
  simple refine (_ ,, _ ,, _).
  - exact (nat_trans_comp _ _ _ α (post_whisker (β^-1) _)).
  - abstract
      (intro x ;
       refine (assoc' (pr1 α x) _ _ @ _ @ id_right _) ;
       apply maponpaths ;
       refine (!(functor_comp F₂ _ _) @ _ @ functor_id F₂ _) ;
       apply maponpaths ;
       exact (nat_trans_eq_pointwise (vcomp_linv β) x)).
  - apply functors_into_cat_disp_locally_groupoid.
Defined.

(**
 3. Global cleaving
 *)
Definition functors_into_cat_nat_iso_is_cartesian_1cell
           {C₁ C₂ : bicat_of_strict_cats}
           {F : C₁ --> C₂}
           {G₁ : disp_bicat_of_functors_into_cat C₁}
           {G₂ : disp_bicat_of_functors_into_cat C₂}
           (α : G₁ -->[ F ] G₂)
           (Hα : is_nat_z_iso (pr1 α))
  : cartesian_1cell disp_bicat_of_functors_into_cat α.
Proof.
  split.
  - intros C₃ G₃ H HF.
    simple refine (_ ,, _).
    + exact (nat_trans_comp
                _ _ _
                HF
                (pre_whisker _ (nat_z_iso_inv (make_nat_z_iso _ _ α Hα)))).
    + simple refine (_ ,, _).
      * abstract
          (intro x ; cbn ;
           etrans ;
           [ apply maponpaths ;
             apply (functor_id G₂)
           | ] ;
           refine (id_right (pr1 HF x · _ · _) @ _) ;
           refine (_ @ id_right _) ;
           rewrite assoc' ;
           apply maponpaths ;
           apply Hα).
      * apply functors_into_cat_disp_locally_groupoid.
  - intros C₃ G₃ F₁ F₂ β γ δ p ℓ₁ ℓ₂.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply disp_bicat_of_functors_into_cat | ] ;
         apply functors_into_cat_disp_2cells_isaprop).
    + simple refine (_ ,, _).
      * abstract
          (intro x ;
           pose (pr12 ℓ₁ x) as q₁ ;
           pose (pr12 ℓ₂ x @ !(p x) @ maponpaths (λ z, z · _) (!q₁)) as q₂ ;
           rewrite !(functor_id G₂) in q₂ ;
           pose (!(id_right (pr11 ℓ₂ x · pr1 α (pr1 F₂ x))) @ q₂) as q₃ ;
           pose (q₃ @ maponpaths (λ z, z · # (pr1 G₂) _) (id_right _) @ assoc' _ _ _) as q₄ ;
           pose (q₄ @ maponpaths (λ z, _ · z) (!(nat_trans_ax α _ _ (pr1 δ x)))) as q₅ ;
           pose (maponpaths
                   (λ z, z · nat_z_iso_inv (make_nat_z_iso _ _ _ Hα) (pr1 F₂ x))
                   q₅)
             as q₆ ;
           refine (_ @ !q₆ @ _) ;
           [ refine (_ @ assoc (pr11 ℓ₁ x) _ _) ;
             apply maponpaths ;
             refine (_ @ assoc _ _ _) ;
             refine (!(id_right _) @ _) ;
             apply maponpaths ;
             refine (!_) ;
             apply Hα
           | refine (assoc' (pr11 ℓ₂ x) _ _ @ _) ;
             refine (_ @ id_right _) ;
             apply maponpaths ;
             apply Hα ]).
      * apply functors_into_cat_disp_2cells_isaprop.
Defined.

Section CartesianIsNatIso.
  Context {C₁ C₂ : bicat_of_strict_cats}
          {F : C₁ --> C₂}
          {G₁ : disp_bicat_of_functors_into_cat C₁}
          {G₂ : disp_bicat_of_functors_into_cat C₂}
          (α : G₁ -->[ F ] G₂)
          (Hα : cartesian_1cell disp_bicat_of_functors_into_cat α).

  Local Definition functors_into_cat_cartesian_1cell_is_nat_iso_inv
                   (x : pr1 C₁)
    : (F ∙ G₂) x --> pr1 G₁ x
    := let l := pr1 Hα C₁ (F ∙ G₂) (functor_identity _) (nat_trans_id _) in
       pr1 (pr1 l) x.

  Local Lemma functors_into_cat_cartesian_1cell_is_nat_iso_is_inverse
              (x : pr1 C₁)
    : is_inverse_in_precat
        (pr1 α x)
        (functors_into_cat_cartesian_1cell_is_nat_iso_inv x).
  Proof.
    pose (l := pr1 Hα C₁ (F ∙ G₂) (functor_identity _) (nat_trans_id _)).
    split ; unfold functors_into_cat_cartesian_1cell_is_nat_iso_inv.
    - cbn.
      assert (α ==>[ nat_trans_id (functor_identity _) ▹ F] α) as p.
      {
        intro z ; cbn.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply (functor_id F).
          }
          apply (functor_id G₂).
        }
        apply (id_right (pr1 α z)).
      }
      simple refine (_ @ @cartesian_1cell_lift_2cell
                           _ _ _ _ _ _ _ _
                           Hα
                           C₁
                           G₁
                           (functor_identity _) (functor_identity _)
                           α α
                           (nat_trans_id _)
                           p
                           (nat_trans_comp _ _ _ α (pr1 l) ,, _)
                           (nat_trans_id _ ,, _)
                           x).
      + cbn.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply (functor_id G₁).
        }
        apply (id_right (pr1 α x · _)).
      + simple refine (_ ,, _).
        * intro z.
          cbn.
          refine (_ @ id_right (pr1 α z)).
          refine (_ @ maponpaths (λ z, _ · z) (pr12 l z)).
          cbn.
          refine (assoc' (pr1 α z · pr11 l z) (pr1 α z) _ @ _).
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          apply assoc.
        * apply functors_into_cat_disp_locally_groupoid.
      + simple refine (_ ,, _).
        * intro z.
          cbn.
          etrans.
          {
            apply maponpaths.
            apply (functor_id G₂).
          }
          etrans.
          {
            apply (id_right (_ · pr1 α z)).
          }
          apply (id_left (pr1 α z)).
        * apply functors_into_cat_disp_locally_groupoid.
    - refine (_ @ pr12 l x) ; cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (functor_id G₂).
      }
      apply (id_right (pr11 l x · _)).
  Qed.

  Definition functors_into_cat_cartesian_1cell_is_nat_iso
    : is_nat_z_iso (pr1 α).
  Proof.
    intro x.
    use make_is_z_isomorphism.
    - exact (functors_into_cat_cartesian_1cell_is_nat_iso_inv x).
    - exact (functors_into_cat_cartesian_1cell_is_nat_iso_is_inverse x).
  Defined.
End CartesianIsNatIso.

Definition functors_into_cat_global_cleaving
  : global_cleaving disp_bicat_of_functors_into_cat.
Proof.
  intros C₁ C₂ G₁ F.
  refine (F ∙ G₁ ,, nat_trans_id _ ,, _).
  apply functors_into_cat_nat_iso_is_cartesian_1cell.
  intro.
  apply is_z_isomorphism_identity.
Defined.
