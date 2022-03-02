Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence. (* only coercions *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.Foundations.All.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

(* In "cartesian_factorisation_commutes" we see that factorising through and then composing with a cartesian morphism yields (propositionally) the same morphism.
This lemma shows the reverse, and is proved and then used in "cartesian_factorisation_unique". *)
Definition cartesian_factorisation_of_composite
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c'' : C} {g : c'' --> c'} {d'' : D c''} (gg : d'' -->[g] d')
  : gg = cartesian_factorisation H g (gg ;; ff).
Proof.
  exact (maponpaths pr1 (pr2 (H _ _ _ _) (_,, idpath _))).
Defined.


(* The following is just another proof of cartesian_factorisation_unique, written to use the above lemma directly. *)
Definition cartesian_factorization_unique
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} {g : c'' --> c'} {d'' : D c''} (gg gg' : d'' -->[g] d')
  : (gg ;; ff = gg' ;; ff) -> gg = gg'.
Proof.
  intro Hggff.
  eapply pathscomp0.
  - apply (cartesian_factorisation_of_composite H).
  - eapply pathscomp0.
    + apply maponpaths. exact Hggff.
    + apply pathsinv0. apply cartesian_factorisation_of_composite.
Qed.
