(******************************************************************************************

 Coreflections in a 2-category

 In this file, we construct the double category of coreflections in  a 2-category. Given a
 2-category `C`, we define the following double category:
 - Objects: objects in `C`
 - Vertical morphisms: coreflections in `C` (i.e., adjunctions in `C` whose unit is given
   by an identity)
 - Horizontal morphisms: morphisms in `C`
 - Squares with vertical sides `f : x₁ --> x₂` and `g : y₁ --> y₂` and horizontal sides
   `h : x₁ --> y₁` and `k : x₂ --> y₂` are 2-cells `h · g ==> f · k`

 Note that we only define this double category for locally univalent 2-categories. This is
 to guarantee that being a left adjoint is a property, which we use to prove the laws for
 the vertical morphisms. Such 2-categories are given by categories enriched over posets.

 Contents
 1. Coreflections in a 2-category
 2. The displayed category of adjunctions
 3. The displayed category of coreflections
 4. The double category of coreflections
 5. Companions and conjoints

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.SquaresTwoCat.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Strictness.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.Composition.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.
Require Import UniMath.Bicategories.DoubleCategories.Examples.SquareDoubleCatTwo.
Require Import UniMath.Bicategories.DoubleCategories.Examples.DoubleCatOnDispCat.

Local Open Scope cat.
Local Open Scope double_cat.

Import TwoCategories.Notations.

(** * 1. Coreflections in a 2-category *)
Definition is_coreflection
           {C : two_cat}
           {x y : C}
           (f : x --> y)
           (Hf : left_adjoint (B := two_cat_to_bicat C) f)
  : UU
  := ∑ p, left_adjoint_unit Hf = idto2mor p.

Proposition isaprop_is_coreflection
            {C : two_cat}
            {x y : C}
            (f : x --> y)
            (Hf : left_adjoint (B := two_cat_to_bicat C) f)
  : isaprop (is_coreflection f Hf).
Proof.
  use isaproptotal2.
  - intro.
    apply cellset_property.
  - intros.
    apply (homset_property C).
Qed.

Proposition id_is_coreflection
            {C : two_cat}
            (x : C)
  : is_coreflection
      _
      (internal_adjoint_equivalence_identity (C := two_cat_to_bicat C) x).
Proof.
  simple refine (_ ,, _).
  - exact (!(id_left (C := C) _)).
  - cbn.
    apply idpath.
Qed.

Proposition comp_is_coreflection
            {C : two_cat}
            {x y z : C}
            {f : x --> y}
            {Hf : left_adjoint (B := two_cat_to_bicat C) f}
            (Hf' : is_coreflection f Hf)
            {g : y --> z}
            {Hg : left_adjoint (B := two_cat_to_bicat C) g}
            (Hg' : is_coreflection g Hg)
  : is_coreflection
      _
      (comp_left_adjoint _ _ Hf Hg).
Proof.
  simple refine (_ ,, _).
  - cbn.
    refine (_ @ assoc (C := C) _ _ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (assoc (C := C) _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        exact (!(pr1 Hg')).
      }
      apply (id_left (C := C)).
    }
    exact (!(pr1 Hf')).
  - cbn.
    rewrite (pr2 Hf'), (pr2 Hg').
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!(TwoCategories.lwhisker_vcomp (C := C) _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply idto2mor_lwhisker.
      }
      apply maponpaths_2.
      refine (!(TwoCategories.lwhisker_vcomp (C := C) _ _ _) @ _).
      etrans.
      {
        apply maponpaths_2.
        apply idto2mor_lwhisker.
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply idto2mor_rwhisker.
      }
      apply idto2mor_lwhisker.
    }
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply idto2mor_comp.
          }
          apply idto2mor_comp.
        }
        apply idto2mor_comp.
      }
      apply idto2mor_comp.
    }
    apply maponpaths.
    apply (homset_property C).
Qed.

Section AdjunctionsAndCoreflections.
  Context (C : two_cat)
          (HC : locally_univalent_two_cat C).

  (** * 2. The displayed category of adjunctions *)
  Definition disp_cat_of_adj_ob_mor
    : disp_cat_ob_mor (two_cat_square_double_cat C).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, unit).
    - exact (λ (x y : C) _ _ (f : x --> y), left_adjoint (B := two_cat_to_bicat C) f).
  Defined.

  Definition disp_cat_of_adj_id_comp
    : disp_cat_id_comp
        (two_cat_square_double_cat C)
        disp_cat_of_adj_ob_mor.
  Proof.
    split.
    - refine (λ (x : C) _, _) ; cbn.
      exact (internal_adjoint_equivalence_identity (C := two_cat_to_bicat C) x).
    - intros x y z f g xx yy zz Hf Hg.
      exact (comp_left_adjoint _ _ Hf Hg).
  Defined.

  Definition disp_cat_of_adj_data
    : disp_cat_data (two_cat_square_double_cat C).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_adj_ob_mor.
    - exact disp_cat_of_adj_id_comp.
  Defined.

  Proposition disp_cat_of_adj_axioms
    : disp_cat_axioms
        (two_cat_square_double_cat C)
        disp_cat_of_adj_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply isaprop_left_adjoint.
      exact (is_univalent_2_1_two_cat_to_bicat HC).
    - intro ; intros.
      apply isaprop_left_adjoint.
      exact (is_univalent_2_1_two_cat_to_bicat HC).
    - intro ; intros.
      apply isaprop_left_adjoint.
      exact (is_univalent_2_1_two_cat_to_bicat HC).
    - intro ; intros.
      apply isasetaprop.
      apply isaprop_left_adjoint.
      exact (is_univalent_2_1_two_cat_to_bicat HC).
  Qed.

  Definition disp_cat_of_adj
    : disp_cat (two_cat_square_double_cat C).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_adj_data.
    - exact disp_cat_of_adj_axioms.
  Defined.

  Proposition is_univalent_disp_cat_of_adj
    : is_univalent_disp disp_cat_of_adj.
  Proof.
    use is_univalent_disp_from_fibers.
    intros x xx xx'.
    use isweqimplimpl.
    - intro.
      apply isapropunit.
    - apply isasetunit.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply isaprop_left_adjoint.
        exact (is_univalent_2_1_two_cat_to_bicat HC).
  Qed.

  (** * 3. The displayed category of coreflections *)
  Definition disp_cat_of_adj_is_coreflection_ob_mor
    : disp_cat_ob_mor (total_category disp_cat_of_adj).
  Proof.
    simple refine (_ ,, _).
    - exact (λ _, unit).
    - exact (λ x y _ _ f, is_coreflection _ (pr2 f)).
  Defined.

  Definition disp_cat_of_adj_is_coreflection_id_comp
    : disp_cat_id_comp
        (total_category disp_cat_of_adj)
        disp_cat_of_adj_is_coreflection_ob_mor.
  Proof.
    split.
    - intros.
      apply id_is_coreflection.
    - intros x y z f g xx yy zz Hf Hg.
      exact (comp_is_coreflection Hf Hg).
  Qed.

  Definition disp_cat_of_adj_is_coreflection_data
    : disp_cat_data (total_category disp_cat_of_adj).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_adj_is_coreflection_ob_mor.
    - exact disp_cat_of_adj_is_coreflection_id_comp.
  Defined.

  Proposition disp_cat_of_adj_is_coreflection_axioms
    : disp_cat_axioms
        (total_category disp_cat_of_adj)
        disp_cat_of_adj_is_coreflection_data.
  Proof.
    repeat split ; intros.
    - apply isaprop_is_coreflection.
    - apply isaprop_is_coreflection.
    - apply isaprop_is_coreflection.
    - apply isasetaprop.
      apply isaprop_is_coreflection.
  Qed.

  Definition disp_cat_of_adj_is_coreflection
    : disp_cat (total_category disp_cat_of_adj).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_adj_is_coreflection_data.
    - exact disp_cat_of_adj_is_coreflection_axioms.
  Defined.

  Proposition is_univalent_disp_cat_of_adj_is_coreflection
    : is_univalent_disp disp_cat_of_adj_is_coreflection.
  Proof.
    use is_univalent_disp_from_fibers.
    intros x xx xx'.
    use isweqimplimpl.
    - intro.
      apply isapropunit.
    - apply isasetunit.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply isaprop_is_coreflection.
  Qed.

  Definition disp_cat_of_coreflections
    : disp_cat (two_cat_square_double_cat C).
  Proof.
    use sigma_disp_cat.
    - exact disp_cat_of_adj.
    - exact disp_cat_of_adj_is_coreflection.
  Defined.

  Proposition is_univalent_disp_cat_of_coreflections
    : is_univalent_disp disp_cat_of_coreflections.
  Proof.
    use is_univalent_sigma_disp.
    - exact is_univalent_disp_cat_of_adj.
    - exact is_univalent_disp_cat_of_adj_is_coreflection.
  Qed.

  (** * 4. The double category of coreflections *)
  Definition coreflections_double_cat
    : double_cat.
  Proof.
    use double_cat_on_disp_cat.
    - exact (two_cat_square_double_cat C).
    - exact disp_cat_of_coreflections.
  Defined.
End AdjunctionsAndCoreflections.

Definition transportf_square_coreflections_double_cat
           {C : two_cat}
           {HC : locally_univalent_two_cat C}
           {x₁ x₂ y₁ y₂ : coreflections_double_cat C HC}
           {v₁ v₁' : x₁ -->v y₁}
           (p : v₁ = v₁')
           {v₂ v₂' : x₂ -->v y₂}
           (q : v₂ = v₂')
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (s : square v₁ v₂ h₁ h₂)
  : transportf_square p q s
    =
    (_ ◃ idto2mor (maponpaths pr1 (!q)))
    • s
    • (idto2mor (maponpaths pr1 p) ▹ _).
Proof.
  induction p, q.
  cbn.
  (* Note that we must qualify these identifies due the same names being used for bicategories *)
  rewrite TwoCategories.id2_rwhisker.
  rewrite TwoCategories.lwhisker_id2.
  rewrite TwoCategories.id2_left.
  rewrite TwoCategories.id2_right.
  apply idpath.
Qed.

Definition transportb_square_coreflections_double_cat
           {C : two_cat}
           {HC : locally_univalent_two_cat C}
           {x₁ x₂ y₁ y₂ : coreflections_double_cat C HC}
           {v₁ v₁' : x₁ -->v y₁}
           (p : v₁' = v₁)
           {v₂ v₂' : x₂ -->v y₂}
           (q : v₂' = v₂)
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (s : square v₁ v₂ h₁ h₂)
  : transportb_square p q s
    =
    (_ ◃ idto2mor (maponpaths pr1 q))
    • s
    • (idto2mor (maponpaths pr1 (!p)) ▹ _).
Proof.
  induction p, q.
  cbn.
  (* Note that we must qualify these identifies due the same names being used for bicategories *)
  rewrite TwoCategories.id2_rwhisker.
  rewrite TwoCategories.lwhisker_id2.
  rewrite TwoCategories.id2_left.
  rewrite TwoCategories.id2_right.
  apply idpath.
Qed.

Definition coreflections_univalent_double_cat
           (C : univalent_two_cat)
           (HC : locally_univalent_two_cat C)
  : univalent_double_cat.
Proof.
  use univalent_double_cat_on_disp_cat.
  - exact (two_cat_square_univalent_double_cat _ HC).
  - simple refine (_ ,, _).
    + exact (disp_cat_of_coreflections C HC).
    + apply is_univalent_disp_cat_of_coreflections.
Defined.

Definition coreflections_pseudo_double_setcat
           (C : two_setcat)
           (HC : locally_univalent_two_cat C)
  : pseudo_double_setcat.
Proof.
  use pseudo_double_set_cat_on_disp_cat.
  - exact (strict_two_cat_square_double_cat C).
  - exact (disp_cat_of_coreflections C HC).
  - abstract
      (intros x ;
       use isaset_total2 ; intros ; apply isasetunit).
Defined.

(** * 5. Companions and conjoints *)
Definition all_companions_coreflections_double_cat
           (C : two_cat)
           (HC : locally_univalent_two_cat C)
  : all_companions_double_cat (coreflections_double_cat C HC).
Proof.
  use all_companions_double_cat_on_disp_cat.
  apply all_companions_two_cat_square_double_cat.
Defined.

Section Conjoints.
  Context {C : two_cat}
          (HC : locally_univalent_two_cat C)
          {xx yy : coreflections_double_cat C HC}
          (fHf : xx -->v yy).

  Let x : C := pr1 xx.
  Let y : C := pr1 yy.
  Let f : x --> y := pr1 fHf.
  Let Hf : left_adjoint (B := two_cat_to_bicat C) f := pr12 fHf.

  Let r : yy -->h xx := left_adjoint_right_adjoint Hf.
  Let η : _ ==> f · r := left_adjoint_unit Hf.
  Let ε : r · f ==> _ := left_adjoint_counit Hf.

  Let ηη : square fHf (identity_v xx) (identity_h xx) r := two_cat_runitor _ • η.
  Let εε : square (identity_v yy) fHf r (identity_h yy) := ε • two_cat_rinvunitor _.

  Proposition are_conjoints_coreflections_double_cat_left
    : transportf_square
        (id_v_left (identity_v yy · identity_v yy) @ id_v_left (identity_v yy))
        (id_v_left (identity_v xx · identity_v xx) @ id_v_left (identity_v xx))
        (rinvunitor_h r ⋆v (εε ⋆h ηη ⋆v lunitor_h r))
      =
      id_v_square r.
  Proof.
    rewrite transportf_square_coreflections_double_cat.
    rewrite idto2mor_lwhisker.
    rewrite idto2mor_rwhisker.
    (* we need calculational lemmas for the unitors, associators, and compositions *)
    (* we also need to have triangle lemmas for 2-categories *)
  Admitted.

  Proposition are_conjoints_coreflections_double_cat_right
    : transportf_square
        (id_v_right fHf)
        (id_v_left fHf)
        (ηη ⋆v εε)
      =
      id_h_square fHf.
  Proof.
    rewrite transportf_square_coreflections_double_cat.
    rewrite idto2mor_lwhisker.
    rewrite idto2mor_rwhisker.
    cbn.
  Admitted.

  Definition are_conjoints_coreflections_double_cat
    : double_cat_are_conjoints r fHf.
  Proof.
    use make_double_cat_are_conjoints'.
    - exact ηη.
    - exact εε.
    - exact are_conjoints_coreflections_double_cat_left.
    - exact are_conjoints_coreflections_double_cat_right.
  Defined.
End Conjoints.

Definition all_conjoints_coreflections_double_cat
           (C : two_cat)
           (HC : locally_univalent_two_cat C)
  : all_conjoints_double_cat (coreflections_double_cat C HC).
Proof.
  intros x y fHf.
  cbn in x.
  pose (f := pr1 fHf).
  pose (Hf := pr12 fHf : left_adjoint _).
  refine (left_adjoint_right_adjoint Hf ,, _).
  exact (are_conjoints_coreflections_double_cat HC fHf).
Defined.
