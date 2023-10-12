(**************************************************************************************************

  The Free Monoid Theory

  One can construct an algebraic theory T by taking T(n) to be the free monoid on n generators. Then
  the type of algebras for this algebraic theory is equivalent to the type of monoids.

  Contents
  1. The definition of the algebraic theory [free_monoid_theory]
  2. The equivalence between algebras and monoids [monoid_weq_free_monoid_theory_algebra]

  **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Export UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.Algebras.

Local Open Scope algebraic_theories.
Local Open Scope vec_scope.

(** * 1. The definition of the algebraic theory *)

Definition free_monoid_theory'_data : algebraic_theory'_data.
Proof.
  use make_algebraic_theory'_data.
  - intro n.
    use tpair.
    * exact (free_monoid (stnset n)).
    * apply isasetmonoid.
  - intros n i.
    exact (free_monoid_unit (i : stnset n)).
  - intros m n f g.
    exact (free_monoid_extend (λ i : stnset m, g i) f).
Defined.

Lemma free_monoid_is_theory' : is_algebraic_theory' free_monoid_theory'_data.
Proof.
  use make_is_algebraic_theory'.
  - now do 4 intro.
  - intros n f.
    apply (free_monoid_extend_comp (idmonoidiso (free_monoid (stnset n)))).
  - intros l m n f_l f_m f_n.
    exact (maponpaths (λ x, pr1monoidfun _ _ x f_l)
      (free_monoid_extend_funcomp2 (X := stnset l) f_m f_n)).
Qed.

Definition free_monoid_theory
  : algebraic_theory
  := make_algebraic_theory' _ free_monoid_is_theory'.

(** * 2. The equivalence between algebras and monoids *)

Definition free_monoid_theory_algebra_to_setwithbinop
  (A : algebra free_monoid_theory)
  : setwithbinop.
Proof.
  use make_setwithbinop.
  - exact A.
  - intros a b.
    eapply action.
    + exact (op
      (free_monoid_unit (make_stn 2 0 (idpath _) : stnset _))
      (free_monoid_unit (make_stn 2 1 (idpath _) : stnset _))).
    + exact (weqvecfun _ [(a ; b)]).
Defined.

Local Lemma move_action_through_weqvecfun
  {A : algebra free_monoid_theory}
  {n : nat}
  {f g : (free_monoid_theory n : hSet)}
  (h : stn n → A)
  : weqvecfun _ [( action f h ; action g h )] = λ i, action (weqvecfun _  [(f ; g)] i) h.
Proof.
  now apply (invmaponpathsweq (invweq (weqvecfun _))).
Qed.

Lemma free_monoid_theory_algebra_to_setwithbinop_op_is_assoc
  (A : algebra free_monoid_theory)
  : isassoc (op (X := free_monoid_theory_algebra_to_setwithbinop A)).
Proof.
  intros a b c.
  pose (f := weqvecfun _ [(a ; b ; c)]).
  pose (Hf := λ i Hi,
    !(algebra_projects_component _ _ (make_stn 3 i Hi) f)).
  do 4 rewrite (idpath _ : op (X := (free_monoid_theory_algebra_to_setwithbinop A)) _ _
    = action _ _).
  rewrite (Hf 0 (idpath true) : a = _),
    (Hf 1 (idpath true) : b = _),
    (Hf 2 (idpath true) : c = _).
  now do 4 (rewrite move_action_through_weqvecfun, <- algebra_is_assoc).
Qed.

Definition free_monoid_theory_algebra_to_unit (A : algebra free_monoid_theory)
  : A
  := action (T := free_monoid_theory) (unel _) (weqvecfun _ [()]).

Lemma free_monoid_theory_algebra_to_isunit (A : algebra free_monoid_theory)
  : isunit
    (op (X := free_monoid_theory_algebra_to_setwithbinop A))
    (free_monoid_theory_algebra_to_unit A).
Proof.
  split;
    intro x;
    now rewrite (idpath _ : op (X := free_monoid_theory_algebra_to_setwithbinop A) _ _
        = action (T := free_monoid_theory) _ _),
      <- (algebra_projects_component _ _ (make_stn 1 0 (idpath _)) (λ _, x)),
      <- (lift_constant_action 1 _ (λ _, x) : _ = free_monoid_theory_algebra_to_unit A),
      move_action_through_weqvecfun,
      <- algebra_is_assoc.
Qed.

Definition free_monoid_theory_algebra_to_setwithbinop_op_is_unital
  (A : algebra free_monoid_theory)
  : isunital (op (X := free_monoid_theory_algebra_to_setwithbinop A))
  := _ ,, free_monoid_theory_algebra_to_isunit A.

Definition free_monoid_theory_algebra_to_setwithbinop_op_is_monoidop
  (A : algebra free_monoid_theory)
  : ismonoidop (op (X := free_monoid_theory_algebra_to_setwithbinop A))
  := free_monoid_theory_algebra_to_setwithbinop_op_is_assoc A ,,
    free_monoid_theory_algebra_to_setwithbinop_op_is_unital A.

Definition free_monoid_theory_algebra_to_monoid (A : algebra free_monoid_theory)
  : monoid
  := free_monoid_theory_algebra_to_setwithbinop A ,,
    free_monoid_theory_algebra_to_setwithbinop_op_is_monoidop A.

Definition monoid_to_free_monoid_theory_algebra_data (M : monoid)
  : algebra_data free_monoid_theory.
Proof.
  use make_algebra_data.
  - exact M.
  - intros n f m.
    exact (free_monoid_extend (X := stnset n) m f).
Defined.

Lemma monoid_to_is_free_monoid_theory_algebra (M : monoid)
  : is_algebra (monoid_to_free_monoid_theory_algebra_data M).
Proof.
  use make_is_algebra'.
  - intros m n f g a.
    now rewrite (idpath _ : action f (λ _, action _ a)
      = free_monoid_extend (X := stnset m) (λ _, free_monoid_extend (X := stnset n) _ _) _),
      <- free_monoid_extend_funcomp2.
  - now do 3 intro.
Qed.

Definition monoid_to_free_monoid_theory_algebra (M : monoid)
  : algebra free_monoid_theory
  := make_algebra _ (monoid_to_is_free_monoid_theory_algebra M).

Lemma monoid_to_free_monoid_theory_algebra_and_back (M : monoid)
  : free_monoid_theory_algebra_to_monoid (monoid_to_free_monoid_theory_algebra M) = M.
Proof.
  apply subtypePath.
  {
    intro.
    apply isapropismonoidop.
  }
  apply idpath.
Qed.

Lemma free_monoid_theory_algebra_to_monoid_and_back
  (A : algebra free_monoid_theory)
  : monoid_to_free_monoid_theory_algebra (free_monoid_theory_algebra_to_monoid A) = A.
Proof.
  use algebra_eq.
  - apply idpath.
  - intros n f.
    rewrite idpath_transportf.
    apply funextfun.
    intro a.
    pose (A' := monoid_to_free_monoid_theory_algebra (free_monoid_theory_algebra_to_monoid A)).
    apply (list_ind (λ x, action (A := A') x a = action (A := A) x a)).
    + exact (!(lift_constant_action (A := A) _ (unel _) _)).
    + intros i xs Haction.
      rewrite (idpath _ : cons i xs = (op
        (free_monoid_unit (make_stn 2 0 (idpath true) : stnset _))
        (free_monoid_unit (make_stn 2 1 (idpath true) : stnset _))
      : (free_monoid_theory 2 : hSet)) • (weqvecfun _ [((free_monoid_unit i) ; xs)])).
      do 2 rewrite algebra_is_assoc.
      now rewrite <- (move_action_through_weqvecfun (A := A) a),
        <- Haction,
        (algebra_projects_component A _ _ _ :
          action (free_monoid_unit i : (free_monoid_theory n : hSet)) _ = _).
Qed.

Definition monoid_weq_free_monoid_theory_algebra
  : monoid ≃ (algebra free_monoid_theory)
  := weq_iso
    monoid_to_free_monoid_theory_algebra
    free_monoid_theory_algebra_to_monoid
    monoid_to_free_monoid_theory_algebra_and_back
    free_monoid_theory_algebra_to_monoid_and_back.
