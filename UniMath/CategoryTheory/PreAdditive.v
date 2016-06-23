(** Definition of preadditive categories. *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.

Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.

Section def_preadditive.

  (** In preadditive category precomposition and postcomposition for any
    morphism yields a morphism of abelian groups. Classically one says that
    composition is bilinear with respect to the abelian groups? *)
  Definition isPreAdditive (PA : PrecategoryWithAbgrops) :=
    (forall (x y z : PA) (f : x --> y),
        ismonoidfun (PrecategoryWithAbgrops_premor PA x y z f))
      × (forall (x y z : PA) (f : y --> z),
            ismonoidfun (PrecategoryWithAbgrops_postmor PA x y z f)).

  Definition mk_isPreAdditive (PA : PrecategoryWithAbgrops)
             (H1 : forall (x y z : PA) (f : x --> y),
                 ismonoidfun (PrecategoryWithAbgrops_premor PA x y z f))
             (H2 : forall (x y z : PA) (f : y --> z),
                   ismonoidfun (PrecategoryWithAbgrops_postmor PA x y z f)) :
    isPreAdditive PA.
  Proof.
    exact (H1,,H2).
  Defined.

  (** Definition of preadditive categories *)
  Definition PreAdditive : UU :=
    Σ PA : PrecategoryWithAbgrops, isPreAdditive PA.
  Definition PreAdditive_PrecategoryWithAbgrops (A : PreAdditive) :
    PrecategoryWithAbgrops := pr1 A.
  Coercion PreAdditive_PrecategoryWithAbgrops :
    PreAdditive >-> PrecategoryWithAbgrops.
  Definition mk_PreAdditive (PA : PrecategoryWithAbgrops)
             (H : isPreAdditive PA) : PreAdditive.
  Proof.
    exact (tpair _ PA H).
  Defined.

  Variable A : PreAdditive.

  (** The following gives the bilinearity condition of a PreAdditive
    category. *)
  Definition PreAdditive_premor (x y z : A) (f : x --> y) :
    ismonoidfun (PrecategoryWithAbgrops_premor A x y z f)
    := dirprod_pr1 (pr2 A) x y z f.
  Definition PreAdditive_postmor (x y z : A) (f : y --> z) :
    ismonoidfun (PrecategoryWithAbgrops_postmor A x y z f)
    := dirprod_pr2 (pr2 A) x y z f.

  (** The following give that premor and postmor are linear. That is
    mor(op x y) = op (mor x) (mor y). *)
  Definition PreAdditive_premor_linear (x y z : A) (f : x --> y) :
    isbinopfun (PrecategoryWithAbgrops_premor A x y z f)
    := dirprod_pr1 (PreAdditive_premor x y z f).
  Definition PreAdditive_postmor_linear (x y z : A) (f : y --> z) :
    isbinopfun (PrecategoryWithAbgrops_postmor A x y z f)
    := dirprod_pr1 (PreAdditive_postmor x y z f).

  (** The following says that composing with zero object yields a zero
    object. *)
  Definition PreAdditive_premor_0 (x y z : A) (f : x --> y) :
    PrecategoryWithAbgrops_premor A x y z f 1%multmonoid = 1%multmonoid
    := dirprod_pr2 (PreAdditive_premor x y z f).
  Definition PreAdditive_postmor_0 (x y z : A) (f : y --> z) :
    PrecategoryWithAbgrops_postmor A x y z f 1%multmonoid = 1%multmonoid
    := dirprod_pr2 (PreAdditive_postmor x y z f).

End def_preadditive.
