(*******************************************************************************************

 The bicategory of DFL comprehension categories

 In this file, we construct the bicategory of, what we call, DFL comprehension categories.
 These are comprehension categories that are:
 - democratic (that's what the D stands for)
 - support finite limit constructions being units, products, equalizers, and sigma types
   (hence the FL).
 We construct this bicategory by putting together the desired displayed bicategories.

 This bicategory is based on the bicategory of democratic CwFs that support extensional
 identity types and sigma types (Definition 3.10 in the paper by Clairambault and Dybjer).
 However, there are several differences.

 - We use full comprehension categories whereas Clairambault and Dybjer use CwFs.

 The reason for this difference is caused by the intended examples. Clairambault and Dybjer
 look at CwFs and those are suitable for strict categories. This is because in a CwF, there
 is a set of types. As such, if we would construct a CwF from a category where the dependent
 types in a context `Γ` are morphisms into `Γ`, then we need to require the category to be
 strict in order to guarantee that we have a set of types. This would restrict the examples
 of models that one has: the category of hSets would not form a CwF. Note that one could
 give other models using, for instance, iterative sets (see the work by Gratzer, Gylterud,
 Mörtberg, and Stenholm).

 Instead, we are interested in univalent categories, and for that reason, we use an
 alternative model of type theory. Comprehension categories do not force any restriction on
 the homotopy level of the type since we do not require the fibration of types to be a
 discrete fibration.

 - We do not explicitly require that the 1-cells preserve democracy

 The reason for that is explained the file on democracy. The type that a functor between
 full comprehension categories preserves democracy, is contractible. Here the fully
 faithfulness of the comprehension functor is used. Note that the comprehension category
 associated to a CwF is full, so this also holds for CwFs.

 - Type formers are phrased differently.

 In the paper by Clairambault and Dybjer, a rather syntactical approach is used to describe
 the type formers in a CwF: they are described using introduction and elimination rules. This
 closely connects it to the syntax of type theory. However, we use a more categorical approach,
 and type formers are described using universal properties. For example, product types are
 described using categorical binary products and unit types are described using terminal
 objects. This approach is more common in the literature on comprehension categories (see,
 for example, the book by Jacobs) and hyperdoctrines. Note that we are more flexible regarding
 sigma types. Usually, one can only take sigma types for projections, but we allow sigma types
 over arbitrary substitutions. This is possible in the models of interest. The reason for that
 all maps are display maps in those.

 - Extensional identity types versus equalizer types.

 Clairambault and Dybjer phrase extensional identity types by describing introduction and
 elimination rules. In the literature on comprehension categories (e.g., the book by Jacobs),
 one would phrase extensional identity types as left adjoint of the diagonal satisfying some
 condition. However, we use equalizer types instead. These are equivalent to extensional
 identity types if one has sigma types (Theorem 10.5.10 in 'Categorical Logic and Type Theory'
 by Jacobs), so this is no essential difference.

 - Minimalism in the number of type formers.

 Clairambault and Dybjer take a rather small set of type formers: they only consider sigma
 types and extensional identity types. However, we do not pursue minimalism, and instead, we
 take a larger set of type formers that includes unit types and product types. The reason
 for that is that we are not required to construct product types from sigma types and unit
 types using democracy, while verifying the existence of these types is not difficult in
 practice.

 References
 - 'The biequivalence of locally cartesian closed categories and Martin-Löf type theories'
   by Clairambault and Dybjer.
 - 'The Category of Iterative Sets in Homotopy Type Theory and Univalent Foundations' by
   Gratzer, Gylterud, Mörtberg, Stenholm
 - 'Categorical Logic and Type Theory' by Jacobs

 Contents
 1. The bicategory of DFL comprehension categories
 2. This bicategory is univalent
 3. Builders and accessors
 4. Invertible 2-cells
 5. The adjoint equivalence coming from democracy

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Export UniMath.Bicategories.ComprehensionCat.TypeFormers.UnitTypes.
Require Export UniMath.Bicategories.ComprehensionCat.TypeFormers.ProductTypes.
Require Export UniMath.Bicategories.ComprehensionCat.TypeFormers.EqualizerTypes.
Require Export UniMath.Bicategories.ComprehensionCat.TypeFormers.Democracy.
Require Export UniMath.Bicategories.ComprehensionCat.TypeFormers.SigmaTypes.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. The bicategory of DFL comprehension categories *)
Definition disp_bicat_of_dfl_full_comp_cat
  : disp_bicat bicat_full_comp_cat
  := disp_dirprod_bicat
       disp_bicat_of_democracy
       (disp_dirprod_bicat
          disp_bicat_of_unit_type_full_comp_cat
          (disp_dirprod_bicat
             disp_bicat_of_prod_type_full_comp_cat
             (disp_dirprod_bicat
                disp_bicat_of_equalizer_type_full_comp_cat
                disp_bicat_of_sigma_type_full_comp_cat))).

Definition bicat_of_dfl_full_comp_cat
  : bicat
  := total_bicat disp_bicat_of_dfl_full_comp_cat.

(** * 2. This bicategory is univalent *)
Definition is_univalent_2_1_disp_bicat_of_dfl_full_comp_cat
  : disp_univalent_2_1 disp_bicat_of_dfl_full_comp_cat.
Proof.
  use is_univalent_2_1_dirprod_bicat.
  {
    exact univalent_2_1_disp_bicat_of_democracy.
  }
  use is_univalent_2_1_dirprod_bicat.
  {
    exact univalent_2_1_disp_bicat_of_unit_type_full_comp_cat.
  }
  use is_univalent_2_1_dirprod_bicat.
  {
    exact univalent_2_1_disp_bicat_of_prod_type_full_comp_cat.
  }
  use is_univalent_2_1_dirprod_bicat.
  {
    exact univalent_2_1_disp_bicat_of_equalizer_type_full_comp_cat.
  }
  exact univalent_2_1_disp_bicat_of_sigma_type_full_comp_cat.
Qed.

Definition is_univalent_2_0_disp_bicat_of_dfl_full_comp_cat
  : disp_univalent_2_0 disp_bicat_of_dfl_full_comp_cat.
Proof.
  use (is_univalent_2_0_dirprod_bicat _ _ is_univalent_2_1_bicat_full_comp_cat).
  {
    exact univalent_2_disp_bicat_of_democracy.
  }
  use (is_univalent_2_dirprod_bicat _ _ is_univalent_2_1_bicat_full_comp_cat).
  {
    exact univalent_2_disp_bicat_of_unit_type_full_comp_cat.
  }
  use (is_univalent_2_dirprod_bicat _ _ is_univalent_2_1_bicat_full_comp_cat).
  {
    exact univalent_2_disp_bicat_of_prod_type_full_comp_cat.
  }
  use (is_univalent_2_dirprod_bicat _ _ is_univalent_2_1_bicat_full_comp_cat).
  {
    exact univalent_2_disp_bicat_of_equalizer_type_full_comp_cat.
  }
  exact univalent_2_disp_bicat_of_sigma_type_full_comp_cat.
Qed.

Definition is_univalent_2_disp_bicat_of_dfl_full_comp_cat
  : disp_univalent_2 disp_bicat_of_dfl_full_comp_cat.
Proof.
  split.
  - exact is_univalent_2_0_disp_bicat_of_dfl_full_comp_cat.
  - exact is_univalent_2_1_disp_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_1_bicat_of_dfl_full_comp_cat
  : is_univalent_2_1 bicat_of_dfl_full_comp_cat.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_full_comp_cat.
  - exact is_univalent_2_1_disp_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_0_bicat_of_dfl_full_comp_cat
  : is_univalent_2_0 bicat_of_dfl_full_comp_cat.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_full_comp_cat.
  - exact is_univalent_2_0_disp_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_bicat_cat_with_terminal_disp_cat
  : is_univalent_2 bicat_of_dfl_full_comp_cat.
Proof.
  split.
  - exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  - exact is_univalent_2_1_bicat_of_dfl_full_comp_cat.
Qed.

(** * 3. Builders and accessors *)
Definition dfl_full_comp_cat
  : UU
  := bicat_of_dfl_full_comp_cat.

Definition make_dfl_full_comp_cat
           (C : full_comp_cat)
           (DC : is_democratic C)
           (T : fiberwise_terminal (cleaving_of_types C))
           (P : fiberwise_binproducts (cleaving_of_types C))
           (E : fiberwise_equalizers (cleaving_of_types C))
           (S : strong_dependent_sums C)
  : dfl_full_comp_cat
  := C ,, (DC ,, (T ,, tt) ,, (P ,, tt) ,, (E ,, tt) ,, S).

Coercion dfl_full_comp_cat_to_full_comp_cat
         (C : dfl_full_comp_cat)
  : full_comp_cat
  := pr1 C.

Definition is_democratic_dfl_full_comp_cat
           (C : dfl_full_comp_cat)
  : is_democratic C
  := pr12 C.

Definition fiberwise_terminal_dfl_full_comp_cat
           (C : dfl_full_comp_cat)
  : fiberwise_terminal (cleaving_of_types C)
  := pr1 (pr122 C).

Definition fiberwise_binproducts_dfl_full_comp_cat
           (C : dfl_full_comp_cat)
  : fiberwise_binproducts (cleaving_of_types C)
  := pr1 (pr1 (pr222 C)).

Definition fiberwise_equalizers_dfl_full_comp_cat
           (C : dfl_full_comp_cat)
  : fiberwise_equalizers (cleaving_of_types C)
  := pr1 (pr12 (pr222 C)).

Definition strong_dependent_sum_dfl_full_comp_cat
           (C : dfl_full_comp_cat)
  : strong_dependent_sums C
  := pr22 (pr222 C).

Definition dfl_full_comp_cat_functor
           (C₁ C₂ : dfl_full_comp_cat)
  : UU
  := C₁ --> C₂.

Definition make_dfl_full_comp_cat_functor
           {C₁ C₂ : dfl_full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (FT : ∏ (Γ : C₁),
                 preserves_terminal
                   (fiber_functor (comp_cat_type_functor F) Γ))
           (FP : ∏ (Γ : C₁),
                 preserves_binproduct
                   (fiber_functor (comp_cat_type_functor F) Γ))
           (FE : ∏ (Γ : C₁),
                 preserves_equalizer
                   (fiber_functor (comp_cat_type_functor F) Γ))
  : dfl_full_comp_cat_functor C₁ C₂
  := F ,, tt ,, (tt ,, FT) ,, (tt ,, FP) ,, (tt ,, FE) ,, tt.

Coercion dfl_full_comp_cat_functor_to_full_comp_cat_functor
         {C₁ C₂ : dfl_full_comp_cat}
         (F : dfl_full_comp_cat_functor C₁ C₂)
  : full_comp_cat_functor C₁ C₂
  := pr1 F.

Definition preserves_terminal_dfl_full_comp_cat_functor
           {C₁ C₂ : dfl_full_comp_cat}
           (F : dfl_full_comp_cat_functor C₁ C₂)
           (Γ : C₁)
  : preserves_terminal (fiber_functor (comp_cat_type_functor F) Γ)
  := pr2 (pr122 F) Γ.

Definition preserves_binproducts_dfl_full_comp_cat_functor
           {C₁ C₂ : dfl_full_comp_cat}
           (F : dfl_full_comp_cat_functor C₁ C₂)
           (Γ : C₁)
  : preserves_binproduct (fiber_functor (comp_cat_type_functor F) Γ)
  := pr2 (pr1 (pr222 F)) Γ.

Definition preserves_equalizers_dfl_full_comp_cat_functor
           {C₁ C₂ : dfl_full_comp_cat}
           (F : dfl_full_comp_cat_functor C₁ C₂)
           (Γ : C₁)
  : preserves_equalizer (fiber_functor (comp_cat_type_functor F) Γ)
  := pr2 (pr12 (pr222 F)) Γ.

Definition dfl_full_comp_cat_nat_trans
           {C₁ C₂ : dfl_full_comp_cat}
           (F G : dfl_full_comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Definition make_dfl_full_comp_cat_nat_trans
           {C₁ C₂ : dfl_full_comp_cat}
           {F G : dfl_full_comp_cat_functor C₁ C₂}
           (τ : full_comp_cat_nat_trans F G)
  : dfl_full_comp_cat_nat_trans F G
  := τ ,, tt ,, (tt ,, tt) ,, (tt ,, tt) ,, (tt ,, tt) ,, tt.

Coercion dfl_full_comp_cat_nat_trans_to_full_comp_cat_nat_trans
         {C₁ C₂ : dfl_full_comp_cat}
         {F G : dfl_full_comp_cat_functor C₁ C₂}
         (τ : dfl_full_comp_cat_nat_trans F G)
  : full_comp_cat_nat_trans F G
  := pr1 τ.

Proposition dfl_full_comp_cat_nat_trans_eq
            {C₁ C₂ : dfl_full_comp_cat}
            {F G : dfl_full_comp_cat_functor C₁ C₂}
            (τ₁ τ₂ : dfl_full_comp_cat_nat_trans F G)
            (p : ∏ (x : C₁), τ₁ x = τ₂ x)
            (p' := nat_trans_eq (homset_property _) _ _ _ _ p)
            (pp : ∏ (x : C₁)
                    (xx : disp_cat_of_types C₁ x),
                  transportf
                    _
                    (nat_trans_eq_pointwise p' x)
                    (comp_cat_type_nat_trans τ₁ x xx)
                  =
                  comp_cat_type_nat_trans τ₂ x xx)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    repeat (use isapropdirprod) ; apply isapropunit.
  }
  exact (full_comp_nat_trans_eq p pp).
Qed.

(** * 4. Invertible 2-cells *)
Section Invertible.
  Context {C₁ C₂ : dfl_full_comp_cat}
          {F G : dfl_full_comp_cat_functor C₁ C₂}
          (τ : dfl_full_comp_cat_nat_trans F G)
          (Hτ : ∏ (x : C₁), is_z_isomorphism (τ x)).

  Let τiso : nat_z_iso F G := _ ,, Hτ.

  Context (Hτ' : is_disp_nat_z_iso τiso (comp_cat_type_nat_trans τ)).

  Let ττiso
    : disp_nat_z_iso (comp_cat_type_functor F) (comp_cat_type_functor G) τiso
    := _ ,, Hτ'.

  Definition is_invertible_dfl_full_comp_cat_nat_trans_inv_cleaving
    : nat_trans_with_terminal_cleaving G F.
  Proof.
    use make_nat_trans_with_terminal_cleaving.
    use make_nat_trans_with_terminal_disp_cat.
    - exact (nat_z_iso_inv τiso).
    - exact (disp_nat_z_iso_inv ττiso).
  Defined.

  Proposition is_invertible_dfl_full_comp_cat_nat_trans_inv_eq
    : comprehension_nat_trans_eq
        is_invertible_dfl_full_comp_cat_nat_trans_inv_cleaving
        (comp_cat_functor_comprehension G)
        (comp_cat_functor_comprehension F).
  Proof.
    intros x xx.
    cbn.
    refine (!_).
    use (z_iso_inv_on_right _ _ _ (_ ,, Hτ _)).
    cbn.
    rewrite !assoc.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!(comp_cat_nat_trans_comprehension τ xx)).
    }
    rewrite !assoc'.
    refine (_ @ id_right _).
    apply maponpaths.
    rewrite <- comprehension_functor_mor_comp.
    etrans.
    {
      apply maponpaths.
      exact (disp_nat_z_iso_iso_inv ττiso x xx).
    }
    rewrite comprehension_functor_mor_transportb.
    rewrite comprehension_functor_mor_id.
    apply idpath.
  Qed.

  Definition is_invertible_dfl_full_comp_cat_nat_trans_inv
    : dfl_full_comp_cat_nat_trans G F.
  Proof.
    use make_dfl_full_comp_cat_nat_trans.
    use make_full_comp_cat_nat_trans.
    use make_comp_cat_nat_trans.
    - exact is_invertible_dfl_full_comp_cat_nat_trans_inv_cleaving.
    - exact is_invertible_dfl_full_comp_cat_nat_trans_inv_eq.
  Defined.

  Proposition is_invertible_dfl_full_comp_cat_nat_trans_left
    : τ • is_invertible_dfl_full_comp_cat_nat_trans_inv = id₂ F.
  Proof.
    use dfl_full_comp_cat_nat_trans_eq.
    - intro x.
      apply (z_iso_inv_after_z_iso (_ ,, Hτ x)).
    - intros x xx.
      etrans.
      {
        apply maponpaths.
        exact (disp_nat_z_iso_iso_inv ττiso x xx).
      }
      unfold transportb.
      rewrite transport_f_f.
      use transportf_set.
      apply homset_property.
  Qed.

  Proposition is_invertible_dfl_full_comp_cat_nat_trans_right
    : is_invertible_dfl_full_comp_cat_nat_trans_inv • τ = id₂ G.
  Proof.
    use dfl_full_comp_cat_nat_trans_eq.
    - intro x.
      apply (z_iso_after_z_iso_inv (_ ,, Hτ x)).
    - intros x xx.
      etrans.
      {
        apply maponpaths.
        exact (disp_nat_z_iso_inv_iso ττiso x xx).
      }
      unfold transportb.
      rewrite transport_f_f.
      use transportf_set.
      apply homset_property.
  Qed.

  Definition is_invertible_dfl_full_comp_cat_nat_trans
    : is_invertible_2cell τ.
  Proof.
    use make_is_invertible_2cell.
    - exact is_invertible_dfl_full_comp_cat_nat_trans_inv.
    - exact is_invertible_dfl_full_comp_cat_nat_trans_left.
    - exact is_invertible_dfl_full_comp_cat_nat_trans_right.
  Defined.
End Invertible.

(** * 5. The adjoint equivalence coming from democracy *)
Definition dfl_full_comp_cat_adjequiv_empty
           (C : dfl_full_comp_cat)
  : adj_equivalence_of_cats
      (fiber_functor (comp_cat_comprehension C) []).
Proof.
  use rad_equivalence_of_cats.
  - use is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - use full_comp_cat_comprehension_fiber_fully_faithful.
  - abstract
      (intro y ;
       use hinhpr ;
       exact (is_democratic_weq_split_essentially_surjective
                C
                (is_democratic_dfl_full_comp_cat C)
                y)).
Defined.

Definition dfl_full_comp_cat_adjequiv_terminal
           (C : dfl_full_comp_cat)
           (T : Terminal C)
  : adj_equivalence_of_cats
      (fiber_functor (comp_cat_comprehension C) T).
Proof.
  enough ([] = T) as p.
  {
    induction p.
    exact (dfl_full_comp_cat_adjequiv_empty C).
  }
  use subtypePath.
  {
    intro.
    apply isaprop_isTerminal.
  }
  use (isotoid _ (univalent_category_is_univalent C)).
  apply z_iso_Terminals.
Qed.

Definition dfl_full_comp_cat_adjequiv_base
           (C : dfl_full_comp_cat)
  : adj_equivalence_of_cats
      (fiber_functor (comp_cat_comprehension C) []
       ∙ cod_fib_terminal_to_base _).
Proof.
  use comp_adj_equivalence_of_cats.
  - exact (dfl_full_comp_cat_adjequiv_empty C).
  - exact (cod_fib_terminal _).
Defined.
