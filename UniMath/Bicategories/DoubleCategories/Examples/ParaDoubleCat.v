(*************************************************************************************************

 The double category of parametrized morphisms

 We define the double category of parametrized morphisms. This definition is based on the paper
 "Effectful semantics in bicategories: strong, commutative, and concurrent pseudomonads" by
 Paquet and Saville. Given a monoidal category `M`, we define the double category `Para(M)` as
 follows:
 - Objects: objects in `M`
 - Vertical morphisms: morphisms in `M`
 - Horizontal morphisms from `a` to `b`: objects `x` together with a morphism `x ⊗ a --> b`
 - Squares are given by morphisms making a certain diagram commute
 We also construct companion pairs in the double category.

 However, this double category fails to be an equipment. While every morphism in `M` has a
 companion, not every morphism has a conjoint. Since every isomorphism has a conjoint, we also
 give another version of this double category where the vertical morphisms are restricted to be
 the isomorphisms in `M`. We also show that this double category has all companions and
 conjoints. Note that these two double categories have the same horizontal bicategory.

 The advantage of using the second version is that if we have an equipment (also known as a
 fibrant double category), then a monoidal structure on the horizontal bicategory can be
 constructed from a monoidal structure on the double category (see "Constructing symmetric
 monoidal bicategories functorially" by Hansen and Shulman).

 Reference
 - "Effectful semantics in bicategories: strong, commutative, and concurrent pseudomonads" by
   Paquet and Saville
 - "Constructing symmetric monoidal bicategories functorially" by Hansen and Shulman

 Contents
 1. Horizontal identities
 2. Horizontal composition
 3. The unitors and associators
 4. The triangle and pentagon equations
 5. The double category of parametrized morphisms
 6. Parametrized morphisms and isomorphisms

 *************************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.ParaTwoSidedDispCat.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.
Require Import UniMath.Bicategories.DoubleCategories.Examples.DoubleCatOnDispCat.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope double_cat.

Section ParaDoubleCat.
  Context (M : monoidal_cat).

  (** * 1. Horizontal identities *)
  Definition para_double_cat_hor_id_data
    : hor_id_data (para_twosided_disp_cat M).
  Proof.
    use make_hor_id_data.
    - exact (id_para_mor M).
    - exact (λ x y f, id_para_sqr M f).
  Defined.

  Proposition para_double_cat_hor_id_laws
    : hor_id_laws para_double_cat_hor_id_data.
  Proof.
    split.
    - intros a.
      use path_para_sqr ; cbn.
      apply idpath.
    - intros a₁ a₂ a₃ f g.
      use path_para_sqr ; cbn.
      rewrite id_right.
      apply idpath.
  Qed.

  Definition para_double_cat_hor_id
    : hor_id (para_twosided_disp_cat M).
  Proof.
    use make_hor_id.
    - exact para_double_cat_hor_id_data.
    - exact para_double_cat_hor_id_laws.
  Defined.

  (** * 2. Horizontal composition *)
  Definition para_double_cat_hor_comp_data
    : hor_comp_data (para_twosided_disp_cat M).
  Proof.
    use make_hor_comp_data.
    - exact (λ a₁ a₂ a₃ s t, comp_para_mor M s t).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, comp_para_sqr M s₁ s₂).
  Defined.

  Proposition para_double_cat_hor_comp_laws
    : hor_comp_laws para_double_cat_hor_comp_data.
  Proof.
    split.
    - intro ; intros.
      use path_para_sqr ; cbn.
      rewrite tensor_id_id.
      apply idpath.
    - intro ; intros.
      use path_para_sqr ; cbn.
      rewrite tensor_comp_mor.
      apply idpath.
  Qed.

  Definition para_double_cat_hor_comp
    : hor_comp (para_twosided_disp_cat M).
  Proof.
    use make_hor_comp.
    - exact para_double_cat_hor_comp_data.
    - exact para_double_cat_hor_comp_laws.
  Defined.

  (** * 3. The unitors and associators *)
  Definition para_double_cat_lunitor_data
    : double_lunitor_data
        para_double_cat_hor_id
        para_double_cat_hor_comp.
  Proof.
    intros x y h.
    simple refine (_ ,, _).
    - exact (para_mor_lunitor M h).
    - use is_iso_twosided_para_sqr ; cbn.
      apply is_z_iso_para_mor_lunitor.
  Defined.

  Proposition para_double_cat_lunitor_laws
    : double_lunitor_laws para_double_cat_lunitor_data.
  Proof.
    intro ; intros.
    use path_para_sqr ; cbn.
    rewrite transportb_disp_mor2_para ; cbn.
    rewrite tensor_runitor.
    apply idpath.
  Qed.

  Definition para_double_cat_lunitor
    : double_cat_lunitor
        para_double_cat_hor_id
        para_double_cat_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact para_double_cat_lunitor_data.
    - exact para_double_cat_lunitor_laws.
  Defined.

  Definition para_double_cat_runitor_data
    : double_runitor_data
        para_double_cat_hor_id
        para_double_cat_hor_comp.
  Proof.
    intros x y h.
    simple refine (_ ,, _).
    - exact (para_mor_runitor M h).
    - use is_iso_twosided_para_sqr ; cbn.
      apply is_z_iso_para_mor_runitor.
  Defined.

  Proposition para_double_cat_runitor_laws
    : double_runitor_laws para_double_cat_runitor_data.
  Proof.
    intro ; intros.
    use path_para_sqr ; cbn.
    rewrite transportb_disp_mor2_para ; cbn.
    rewrite tensor_lunitor.
    apply idpath.
  Qed.

  Definition para_double_cat_runitor
    : double_cat_runitor
        para_double_cat_hor_id
        para_double_cat_hor_comp.
  Proof.
    use make_double_runitor.
    - exact para_double_cat_runitor_data.
    - exact para_double_cat_runitor_laws.
  Defined.

  Definition para_double_cat_associator_data
    : double_associator_data para_double_cat_hor_comp.
  Proof.
    intros w x y z h₁ h₂ h₃.
    simple refine (_ ,, _).
    - exact (para_mor_associator M h₁ h₂ h₃).
    - use is_iso_twosided_para_sqr ; cbn.
      apply is_z_iso_para_mor_associator.
  Defined.

  Proposition para_double_cat_associator_laws
    : double_associator_laws para_double_cat_associator_data.
  Proof.
    intros a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ f₁ f₂ g₁ g₂ h₁ h₂ va vb vc vd φ₁ φ₂ φ₃.
    use path_para_sqr.
    rewrite transportb_disp_mor2_para ; cbn in *.
    rewrite tensor_lassociator.
    apply idpath.
  Qed.

  Definition para_double_cat_associator
    : double_cat_associator para_double_cat_hor_comp.
  Proof.
    use make_double_associator.
    - exact para_double_cat_associator_data.
    - exact para_double_cat_associator_laws.
  Defined.

  (** * 4. The triangle and pentagon equations *)
  Proposition para_double_cat_triangle
    : triangle_law
        para_double_cat_lunitor
        para_double_cat_runitor
        para_double_cat_associator.
  Proof.
    intro ; intros.
    use path_para_sqr.
    rewrite transportb_disp_mor2_para ; cbn in *.
    rewrite mon_triangle.
    apply idpath.
  Qed.

  Proposition para_double_cat_pentagon
    : pentagon_law para_double_cat_associator.
  Proof.
    intro ; intros.
    use path_para_sqr.
    rewrite transportb_disp_mor2_para ; cbn in *.
    rewrite mon_lassociator_lassociator.
    apply idpath.
  Qed.

  (** * 5. The double category of parametrized morphisms *)
  Definition para_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact M.
    - exact (para_twosided_disp_cat M).
    - exact para_double_cat_hor_id.
    - exact para_double_cat_hor_comp.
    - exact para_double_cat_lunitor.
    - exact para_double_cat_runitor.
    - exact para_double_cat_associator.
    - exact para_double_cat_triangle.
    - exact para_double_cat_pentagon.
  Defined.

  Definition all_companions_para
    : all_companions_double_cat para_double_cat.
  Proof.
    intros x y f.
    simple refine (_ ,, _).
    - exact (para_companion M f).
    - use make_double_cat_are_companions'.
      + exact (para_companion_unit M f).
      + exact (para_companion_counit M f).
      + abstract
          (use path_para_sqr ;
           refine (transportf_disp_mor2_para _ _ _ _ @ _) ; cbn ;
           rewrite tensor_id_id ;
           rewrite id_right ;
           rewrite mon_lunitor_I_mon_runitor_I ;
           apply mon_rinvunitor_runitor).
      + abstract
          (use path_para_sqr ;
           refine (transportf_disp_mor2_para _ _ _ _ @ _) ; cbn ;
           apply id_right).
  Defined.
End ParaDoubleCat.

Definition para_univalent_double_cat
           (M : monoidal_cat)
           (HM : is_univalent M)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (para_double_cat M).
  - split.
    + exact HM.
    + exact (is_univalent_para_twosided_disp_cat M HM).
Defined.

Definition para_pseudo_double_setcat
           (M : monoidal_cat)
           (HM : is_setcategory M)
  : pseudo_double_setcat.
Proof.
  use make_pseudo_double_setcat.
  - exact (para_double_cat M).
  - exact HM.
  - use is_strict_para_twosided_disp_cat.
    exact HM.
Defined.

(** * 6. Parametrized morphisms and isomorphisms *)
Definition iso_para_univalent_double_cat
           (M : monoidal_cat)
           (HM : is_univalent M)
  : univalent_double_cat
  := univalent_double_cat_on_disp_cat
       (para_univalent_double_cat M HM)
       (core_univalent_disp_cat M).

Definition transportf_square_iso_para
           {M : monoidal_cat}
           {HM : is_univalent M}
           {x₁ x₂ y₁ y₂ : iso_para_univalent_double_cat M HM}
           {v₁ v₁' : x₁ -->v y₁}
           (p : v₁ = v₁')
           {v₂ v₂' : x₂ -->v y₂}
           (q : v₂ = v₂')
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (s : square v₁ v₂ h₁ h₂)
  : mor_of_para_sqr M (transportf_square p q s) = mor_of_para_sqr M s.
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Definition transportb_square_iso_para
           {M : monoidal_cat}
           {HM : is_univalent M}
           {x₁ x₂ y₁ y₂ : iso_para_univalent_double_cat M HM}
           {v₁ v₁' : x₁ -->v y₁}
           (p : v₁' = v₁)
           {v₂ v₂' : x₂ -->v y₂}
           (q : v₂' = v₂)
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (s : square v₁ v₂ h₁ h₂)
  : mor_of_para_sqr M (transportb_square p q s) = mor_of_para_sqr M s.
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Definition all_companions_iso_para_univalent_double_cat
           (M : monoidal_cat)
           (HM : is_univalent M)
  : all_companions_double_cat (iso_para_univalent_double_cat M HM).
Proof.
  intros x y f.
  simple refine (_ ,, _).
  - exact (para_companion M (pr1 f)).
  - use make_double_cat_are_companions'.
    + exact (para_companion_unit M (pr1 f)).
    + exact (para_companion_counit M (pr1 f)).
    + abstract
        (use path_para_sqr ;
         refine (transportf_square_iso_para _ _ _ @ _) ; cbn ;
         rewrite tensor_id_id ;
         rewrite id_right ;
         rewrite mon_lunitor_I_mon_runitor_I ;
         apply mon_rinvunitor_runitor).
    + abstract
        (use path_para_sqr ;
         refine (transportf_square_iso_para _ _ _ @ _) ; cbn ;
         apply id_right).
Defined.

Definition all_conjoints_iso_para_univalent_double_cat
           (M : monoidal_cat)
           (HM : is_univalent M)
  : all_conjoints_double_cat (iso_para_univalent_double_cat M HM).
Proof.
  intros x y f.
  simple refine (_ ,, _).
  - exact (para_conjoint M f).
  - use make_double_cat_are_conjoints'.
    + exact (para_conjoint_unit M f).
    + exact (para_conjoint_counit M f).
    + abstract
        (use path_para_sqr ;
         refine (transportf_square_iso_para _ _ _ @ _) ; cbn ;
         rewrite tensor_id_id ;
         rewrite id_left ;
         rewrite mon_runitor_I_mon_lunitor_I ;
         apply mon_linvunitor_lunitor).
    + abstract
        (use path_para_sqr ;
         refine (transportf_square_iso_para _ _ _ @ _) ; cbn ;
         apply id_right).
Defined.
