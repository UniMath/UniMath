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

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.DependentSums.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.UnitTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.ProductTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.EqualizerTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.Democracy.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SigmaTypes.

Local Open Scope cat.

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
