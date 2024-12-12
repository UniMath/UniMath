(*********************************************************************************************

 The setgroupoid model of type theory

 The groupoid model by Hofmann and Streicher is fundamental in the study of type theory. It
 gives us a space-based interpretation of type theory (groupoids represent spaces of dimension 1),
 and as a consequence, it shows the independence of UIP from Martin-Löf type theory.

 In UF, there are several ways to incarnate the notion of a groupoid, and as a consequence, we
 can represent the groupoid model in multiple ways:
 - with univalent groupoids (groupoids up to adjoint equivalence)
 - with setgroupoids (groupoids up to isomorphism)
 One could also imagine an approach using iterative sets, which would give us a set of
 groupoids (groupoids up to strict equality) following the work by Gratzer, Gylterud, Mörtberg,
 and Stenholm.

 Each of these approaches comes with their own characteristics. For instance, univalent groupoids
 form a univalent bicategory rather than a univalent category, and, as a consequence, the
 model of univalent groupoids is described by a comprehension bicategory. The resulting syntax
 is thus 2-dimensional in nature (see 'Bicategorical type theory: semantics and syntax' or
 'Two-dimensional models of type theory').

 Since setgroupoids form a univalent category rather than a univalent bicategory, we can form
 a univalent comprehension category of setgroupoids. Objects are identified up to isomorphisms
 in this comprehension category, and because of that, all substitution laws from type theory
 hold. Note that this is in contrast to the set-theoretic case, where one needs to replace the
 fibration by a split fibration (see 'The internal languages of univalent categories').

 In this file, we define the univalent comprehension category of setgroupoids. This
 comprehension category is defined as follows:
 - Contexts: setgroupoids
 - Substitution: functors
 - Types in context [Γ]: isofibrations into [Γ], which we represent using displayed categories
 - Context extension: the context extension is given by the total category

 It is important to note that this comprehension category is not full. Morphisms between
 types are given by functors that preserve the chosen Cartesian lifts, which is not generally
 satisfied by all functors. The same holds for other univalent comprehension categories that
 give higher dimensional models of type theory, such as cubical sets or simplicial sets. That
 is because types in such models are equipped with structure that expresses that they are
 fibrant in some suitable sense, and to guarantee that the resulting displayed category is
 univalent, morphisms must be required to preserve that structure on the nose. Since not all
 morphisms satisfy this requirement, the resulting comprehension category will not be full.

 References
 - 'Bicategorical type theory: semantics and syntax' by Ahrens, North, Van der Weide
 - 'Two-dimensional models of type theory' by Garner
 - 'The Category of Iterative Sets in Homotopy Type Theory and Univalent Foundations' by
   Gratzer, Gylterud, Mörtberg, and Stenholm
 - 'The groupoid interpretation of type theory' by Hofmann and Streicher
 - 'The internal languages of univalent categories' by Van der Weide

 Content
 1. The univalent comprehension category of setgroupoids

 *********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetGroupoids.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Examples.CategoryOfSetGroupoidsLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.SetGroupoidsIsoFib.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.SetGroupoidComprehension.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.

(** * 1. The univalent comprehension category of setgroupoids *)
Definition setgroupoid_cat_with_terminal_disp_cat
  : cat_with_terminal_disp_cat.
Proof.
  use make_cat_with_terminal_disp_cat.
  - exact univalent_cat_of_setgroupoid.
  - exact terminal_obj_setgroupoid.
  - exact univalent_disp_cat_isofib.
Defined.

Definition setgroupoid_cat_with_terminal_cleaving
  : cat_with_terminal_cleaving.
Proof.
  use make_cat_with_terminal_cleaving.
  - exact setgroupoid_cat_with_terminal_disp_cat.
  - exact cleaving_disp_cat_isofib.
Defined.

Definition setgroupoid_comprehension_functor
  : comprehension_functor setgroupoid_cat_with_terminal_cleaving.
Proof.
  use make_comprehension_functor.
  - exact disp_cat_isofib_comprehension.
  - exact disp_cat_isofib_comprehension_cartesian.
Defined.

Definition setgroupoid_comp_cat
  : comp_cat.
Proof.
  use make_comp_cat.
  - exact setgroupoid_cat_with_terminal_cleaving.
  - exact setgroupoid_comprehension_functor.
Defined.
