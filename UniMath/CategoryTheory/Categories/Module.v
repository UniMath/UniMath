(**

  Properties of the Category of R-Modules

  The category of R-modules is univalent.
  It also has a zero object: the zero abelian group, considered as a module. Every morphism to and
  from this object is exactly the zero map.

  Contents
  1. Univalence [is_univalent_module_category]
  2. The zero object [module_category_Zero]

  Originally written by Anthony Bordg, Langston Barrett (@siddharthist)

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Modules.
Require Import UniMath.Algebra.Modules.Examples.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.CategoryTheory.Categories.AbelianGroup.
Require Import UniMath.CategoryTheory.Categories.ModuleCore.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Limits.Zero.

Local Open Scope cat.

(** * 1. Univalence *)

Section ModuleCategory.

  Context {R : ring}.

  Lemma is_univalent_module_disp_cat
    : is_univalent_disp (module_disp_cat R).
  Proof.
    apply is_univalent_disp_iff_fibers_are_univalent.
    intros M f g.
    use isweq_iso.
    - intro h.
      apply rigfun_paths.
      apply funextfun.
      intro r.
      refine (!id_right _ @ z_iso_mor h r @ id_left _).
    - abstract (
        intro x;
        apply isaset_ringfun
      ).
    - abstract (
        intro y;
        apply z_iso_eq;
        apply impred_isaprop;
        intro;
        apply homset_property
      ).
  Defined.

  Lemma is_univalent_module_category
    : is_univalent (module_category R).
  Proof.
    apply is_univalent_total_category.
    - apply is_univalent_abelian_group_category.
    - apply is_univalent_module_disp_cat.
  Defined.

  (** * 2. The zero object *)

  (** The set of maps 0 -> M is contractible, it only contains the zero morphism. *)
  Lemma iscontrfromzero_module (M : module_category R) : iscontr (module_category R⟦zero_module R, M⟧).
  Proof.
    refine (unelmodulefun _ _,, _).
    intros f; apply modulefun_paths.
    apply funextfun; intro x.
    unfold unelmodulefun; cbn.
    refine (_ @ monoidfununel (modulefun_to_monoidfun f)).
    apply maponpaths.
    now induction x.
  Defined.

  (** The set of maps M -> 0 is contractible, it only contains the zero morphism. *)
  Lemma iscontrtozero_module (M : module_category R) : iscontr (module_category R⟦M, zero_module R⟧).
  Proof.
    refine (unelmodulefun _ _,, _).
    intros f; apply modulefun_paths.
    apply funextfun.
    exact (fun x => isProofIrrelevantUnit _ _).
  Defined.

  Lemma isZero_zero_module : isZero (zero_module R).
  Proof.
    exact (make_isZero (zero_module _) iscontrfromzero_module iscontrtozero_module).
  Defined.

  Definition module_category_Zero : Zero (module_category R) :=
    make_Zero (zero_module _) isZero_zero_module.

End ModuleCategory.
