(** ** Definition of preadditive categories. *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.BinaryOperations.
Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.

Require Import UniMath.CategoryTheory.limits.zero.


Section def_preadditive.

  (** In preadditive category precomposition and postcomposition for any
      morphism yields a morphism of abelian groups. Classically one says that
      composition is bilinear with respect to the abelian groups? *)
  Definition isPreAdditive (PA : PrecategoryWithAbgrops) : UU :=
    (Π (x y z : PA) (f : x --> y), ismonoidfun (to_premor z f))
      × (Π (x y z : PA) (f : y --> z), ismonoidfun (to_postmor x f)).

  Definition mk_isPreAdditive (PA : PrecategoryWithAbgrops)
             (H1 : Π (x y z : PA) (f : x --> y), ismonoidfun (to_premor z f))
             (H2 : Π (x y z : PA) (f : y --> z), ismonoidfun (to_postmor x f)) :
    isPreAdditive PA.
  Proof.
    exact (H1,,H2).
  Defined.

  Definition to_premor_monoid {PWA : PrecategoryWithAbgrops} (iPA : isPreAdditive PWA) :
    Π (x y z : PWA) (f : x --> y), ismonoidfun (to_premor z f) := dirprod_pr1 iPA.

  Definition to_postmor_monoid {PWA : PrecategoryWithAbgrops} (iPA : isPreAdditive PWA) :
    Π (x y z : PWA) (f : y --> z), ismonoidfun (to_postmor x f) := dirprod_pr2 iPA.

  (** Definition of preadditive categories *)
  Definition PreAdditive : UU := Σ PA : PrecategoryWithAbgrops, isPreAdditive PA.

  Definition PreAdditive_PrecategoryWithAbgrops (A : PreAdditive) : PrecategoryWithAbgrops := pr1 A.
  Coercion PreAdditive_PrecategoryWithAbgrops : PreAdditive >-> PrecategoryWithAbgrops.

  Definition mk_PreAdditive (PA : PrecategoryWithAbgrops) (H : isPreAdditive PA) : PreAdditive.
  Proof.
    exact (tpair _ PA H).
  Defined.

  Definition PreAdditive_isPreAdditive (A : PreAdditive) : isPreAdditive A := pr2 A.
  Coercion PreAdditive_isPreAdditive : PreAdditive >-> isPreAdditive.

  Variable A : PreAdditive.

  (** The following give that premor and postmor are linear. That is
      mor(op x y) = op (mor x) (mor y). *)
  Definition to_premor_linear {x y : A} (z : A) (f : x --> y) :
    isbinopfun (to_premor z f) := dirprod_pr1 (to_premor_monoid A x y z f).

  Definition to_postmor_linear (x : A) {y z : A} (f : y --> z) :
    isbinopfun (to_postmor x f) := dirprod_pr1 (to_postmor_monoid A x y z f).

  (** Following versions are useful when one wants to rewrite equations *)
  Lemma to_premor_linear' {x y z : A} (f : x --> y) (g h : y --> z) :
    f ;; (to_binop y z g h) = to_binop x z (f ;; g) (f ;; h).
  Proof.
    apply to_premor_linear.
  Qed.

  Lemma to_postmor_linear' {x y z : A} (g h : x --> y) (f : y --> z) :
    (to_binop x y g h) ;; f = to_binop x z (g ;; f) (h ;; f).
  Proof.
    apply to_postmor_linear.
  Qed.

  (** The following says that composing with zero object yields a zero
      object. *)
  Definition to_premor_unel {x y : A} (z : A) (f : x --> y) :
    to_premor z f 1%multmonoid = 1%multmonoid := dirprod_pr2 (to_premor_monoid A x y z f).

  Definition to_postmor_unel (x : A) {y z : A} (f : y --> z) :
    to_postmor x f 1%multmonoid = 1%multmonoid := dirprod_pr2 (to_postmor_monoid A x y z f).

  (** Following versions are useful when one wants to rewrite equations *)
  Lemma to_premor_unel' {x y : A} (z : A) (f : x --> y) : f ;; (to_unel y z) = to_unel x z.
  Proof.
    apply to_premor_unel.
  Qed.

  Lemma to_postmor_unel' (x : A) {y z : A} (f : y --> z) : (to_unel x y) ;; f = to_unel x z.
  Proof.
    apply to_postmor_unel.
  Qed.

End def_preadditive.
Arguments to_premor_linear [A] [x] [y] _ _ _ _.
Arguments to_postmor_linear [A] _ [y] [z] _ _ _.
Arguments to_premor_linear' [A] [x] [y] [z] _ _ _.
Arguments to_postmor_linear' [A] [x] [y] [z] _ _ _.


(** In the following section we prove that if a preadditive category has a zero
    object, then in a homset the unit element is given by the zero arrow *)
Section preadditive_with_zero.

  Variable A : PreAdditive.

  (** Proof that the zero arrow and the unit element coincide *)
  Lemma PreAdditive_unel_zero (Z : Zero A) (x y : A) : to_unel x y = ZeroArrow Z x y.
  Proof.
    unfold ZeroArrow.
    rewrite <- (id_left A _ _ (ZeroArrowFrom y)).
    assert (identity Z = to_unel Z Z) by apply ZeroEndo_is_identity.
    rewrite -> X. clear X.

    set (Y := to_postmor_unel A Z (@ZeroArrowFrom A Z y)).
    unfold to_postmor in Y. unfold to_unel.
    rewrite Y. clear Y.

    set (Y' := to_premor_unel A y (@ZeroArrowTo A Z x)).
    unfold to_premor in Y'.
    rewrite Y'. clear Y'.

    apply idpath.
  Qed.

End preadditive_with_zero.

(** Some equations on inverses in PreAdditiev categories *)
Section preadditive_inv_comp.

  Variable A : PreAdditive.

  Lemma PreAdditive_invlcomp {x y z : A} (f : A⟦x, y⟧) (g : A⟦y, z⟧) :
    (to_inv x z (f ;; g)) = (to_inv x y f) ;; g.
  Proof.
    use (grrcan (to_abgrop x z) (f ;; g)).
    unfold to_inv at 1. rewrite grlinvax.
    use (pathscomp0 _ (to_postmor_linear' (to_inv x y f) f g)).
    rewrite linvax. rewrite to_postmor_unel'.
    unfold to_unel.
    apply idpath.
  Qed.

  Lemma PreAdditive_invrcomp {x y z : A} (f : A⟦x, y⟧) (g : A⟦y, z⟧) :
    (to_inv _ _ (f ;; g)) = f ;; (to_inv _ _ g).
  Proof.
    use (grrcan (to_abgrop x z) (f ;; g)).
    unfold to_inv at 1. rewrite grlinvax.
    use (pathscomp0 _ (to_premor_linear' f (to_inv y z g) g)).
    rewrite linvax. rewrite to_premor_unel'.
    unfold to_unel.
    apply idpath.
  Qed.

End preadditive_inv_comp.
