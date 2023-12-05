(**********************************************************************************

 The comma category

 Contents
 1. Definition via two-sided displayed categories
 2. Discreteness and univalence
 3. It is a two-sided fibration
 4. The representable profunctors

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedFibration.

Local Open Scope cat.

Section CommaTwoSidedDispCat.
  Context {C₁ C₂ C₃ : category}
          (F : C₁ ⟶ C₃)
          (G : C₂ ⟶ C₃).

  (**
   1. Definition via two-sided displayed categories
   *)
  Definition comma_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, F x --> G y).
    - exact (λ x₁ x₂ y₁ y₂ h₁ h₂ f g, #F f · h₂ = h₁ · #G g).
  Defined.

  Definition comma_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp comma_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - intros x y xy ; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ h₁ h₂ h₃ f₁ f₂ g₁ g₂ hh₁ hh₂ ; cbn in *.
      rewrite !functor_comp.
      rewrite !assoc'.
      rewrite hh₂.
      rewrite !assoc.
      apply maponpaths_2.
      exact hh₁.
  Qed.

  Definition comma_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact comma_twosided_disp_cat_ob_mor.
    - exact comma_twosided_disp_cat_id_comp.
  Defined.

  Definition isaprop_comma_twosided_mor
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : comma_twosided_disp_cat_data x₁ y₁)
             (xy₂ : comma_twosided_disp_cat_data x₂ y₂)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : isaprop (xy₁ -->[ f ][ g ] xy₂).
  Proof.
    apply homset_property.
  Qed.

  Definition comma_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms comma_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply isaprop_comma_twosided_mor.
    - intro ; intros.
      apply isaprop_comma_twosided_mor.
    - intro ; intros.
      apply isaprop_comma_twosided_mor.
    - intro ; intros.
      apply isasetaprop.
      apply isaprop_comma_twosided_mor.
  Qed.

  Definition comma_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact comma_twosided_disp_cat_data.
    - exact comma_twosided_disp_cat_axioms.
  Defined.

  (**
   2. Discreteness and univalence
   *)
  Proposition is_strict_comma_twosided_disp_cat
    : is_strict_twosided_disp_cat comma_twosided_disp_cat.
  Proof.
    intros x y ; cbn.
    apply homset_property.
  Qed.

  Definition comma_twosided_disp_cat_is_iso
    : all_disp_mor_iso comma_twosided_disp_cat.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - rewrite !functor_on_inv_from_z_iso.
      use z_iso_inv_on_right.
      rewrite assoc.
      use z_iso_inv_on_left ; cbn.
      exact fg.
    - apply isaprop_comma_twosided_mor.
    - apply isaprop_comma_twosided_mor.
  Qed.

  Definition is_univalent_comma_twosided_disp_cat
    : is_univalent_twosided_disp_cat comma_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use isweqimplimpl.
    - intros f.
      pose (p := pr1 f) ; cbn in p.
      rewrite !functor_id in p.
      rewrite id_left, id_right in p.
      exact (!p).
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition discrete_comma_twosided_disp_cat
    : discrete_twosided_disp_cat comma_twosided_disp_cat.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - exact comma_twosided_disp_cat_is_iso.
    - exact is_univalent_comma_twosided_disp_cat.
  Qed.

  (**
   3. It is a two-sided fibration
   *)
  Definition comma_twosided_opcleaving
    : twosided_opcleaving comma_twosided_disp_cat.
  Proof.
    intros x₁ x₂ x₃ f g ; cbn in *.
    simple refine (f · #G g ,, _ ,, _) ; cbn.
    - rewrite functor_id.
      rewrite id_left.
      apply idpath.
    - intros x₄ x₅ h k l p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isaset_disp_mor.
        }
        apply isaprop_comma_twosided_mor.
      + cbn in *.
        simple refine (_ ,, _).
        * rewrite id_left, functor_comp, assoc in p.
          exact p.
        * apply isaprop_comma_twosided_mor.
  Qed.

  Definition comma_twosided_cleaving
    : twosided_cleaving comma_twosided_disp_cat.
  Proof.
    intros x₁ x₂ x₃ f g ; cbn in *.
    simple refine (#F g · f ,, _ ,, _) ; cbn.
    - rewrite functor_id.
      rewrite id_right.
      apply idpath.
    - intros x₄ x₅ h k l p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isaset_disp_mor.
        }
        apply isaprop_comma_twosided_mor.
      + cbn in *.
        simple refine (_ ,, _).
        * rewrite id_right, functor_comp, assoc' in p.
          exact p.
        * apply isaprop_comma_twosided_mor.
  Qed.

  Definition comma_twosided_fibration
    : twosided_fibration comma_twosided_disp_cat.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact comma_twosided_opcleaving.
    - exact comma_twosided_cleaving.
    - intro ; intros.
      apply comma_twosided_disp_cat_is_iso.
  Defined.
End CommaTwoSidedDispCat.

(**
 4. The representable profunctors
 *)
Definition left_repr_twosided_disp_cat
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : twosided_disp_cat C₁ C₂
  := comma_twosided_disp_cat F (functor_identity _).

Definition right_repr_twosided_disp_cat
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : twosided_disp_cat C₂ C₁
  := comma_twosided_disp_cat (functor_identity _) F.
