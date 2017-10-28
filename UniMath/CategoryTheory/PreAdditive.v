(** * Definition of preadditive categories. *)
(** ** Contents
- Definition of preadditive categories [PreAdditive]
- Zero and unit element coincide
- Composition and inverses
- KernelIn, CokernelOut, and binary operations
- Quotient of PreAdditive
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.


(** * Definition of a PreAdditive precategory
   A preadditive precategory is a precategory such that the sets of morphisms are abelian groups and
   pre- and postcomposing with a morphisms is a monoidfun of the abelian groups. *)
Section def_preadditive.

  (** In preadditive category precomposition and postcomposition for any
      morphism yields a morphism of abelian groups. Classically one says that
      composition is bilinear with respect to the abelian groups? *)
  Definition isPreAdditive (PA : categoryWithAbgrops) : UU :=
    (∏ (x y z : PA) (f : x --> y), ismonoidfun (to_premor z f))
      × (∏ (x y z : PA) (f : y --> z), ismonoidfun (to_postmor x f)).

  Definition mk_isPreAdditive (PA : categoryWithAbgrops)
             (H1 : ∏ (x y z : PA) (f : x --> y), ismonoidfun (to_premor z f))
             (H2 : ∏ (x y z : PA) (f : y --> z), ismonoidfun (to_postmor x f)) :
    isPreAdditive PA.
  Proof.
    exact (H1,,H2).
  Defined.

  Definition mk_isPreAdditive' (PA : categoryWithAbgrops)
             (H1 : ∏ (x y z : PA) (f : x --> y) (g h : y --> z),
                   f · (to_binop _ _ g h) = to_binop _ _ (f · g) (f · h))
             (H1' : ∏ (x y z : PA) (f : x --> y), to_premor z f (to_unel y z) = to_unel x z)
             (H2 : ∏ (x y z : PA) (f : y --> z) (g h : x --> y),
                   (to_binop _ _ g h) · f = to_binop _ _ (g · f) (h · f))
             (H2' : ∏ (x y z : PA) (f : y --> z), to_premor z (to_unel x y) f = to_unel x z):
    isPreAdditive PA.
  Proof.
    use mk_isPreAdditive.
    - intros x y z f.
      use tpair.
      + intros g h. exact (H1 x y z f g h).
      + exact (H1' x y z f).
    - intros x y z f.
      use tpair.
      + intros g h. exact (H2 x y z f g h).
      + exact (H2' x y z f).
  Qed.

  Definition to_premor_monoid {PWA : categoryWithAbgrops} (iPA : isPreAdditive PWA) :
    ∏ (x y z : PWA) (f : x --> y), ismonoidfun (to_premor z f) := dirprod_pr1 iPA.

  Definition to_postmor_monoid {PWA : categoryWithAbgrops} (iPA : isPreAdditive PWA) :
    ∏ (x y z : PWA) (f : y --> z), ismonoidfun (to_postmor x f) := dirprod_pr2 iPA.

  Definition to_premor_monoidfun {PWA : categoryWithAbgrops} (iPA : isPreAdditive PWA)
             (x y z : PWA) (f : x --> y) : monoidfun (to_abgrop y z) (to_abgrop x z) :=
    monoidfunconstr (to_premor_monoid iPA x y z f).

  Definition to_postmor_monoidfun {PWA : categoryWithAbgrops} (iPA : isPreAdditive PWA)
             (x y z : PWA) (f : y --> z) : monoidfun (to_abgrop x y) (to_abgrop x z) :=
    monoidfunconstr (to_postmor_monoid iPA x y z f).

  (** Definition of preadditive categories *)
  Definition PreAdditive : UU := ∑ PA : categoryWithAbgrops, isPreAdditive PA.

  Definition PreAdditive_categoryWithAbgrops (A : PreAdditive) : categoryWithAbgrops := pr1 A.
  Coercion PreAdditive_categoryWithAbgrops : PreAdditive >-> categoryWithAbgrops.

  Definition mk_PreAdditive (PA : categoryWithAbgrops) (H : isPreAdditive PA) : PreAdditive.
  Proof.
    exact (tpair _ PA H).
  Defined.

  Definition PreAdditive_isPreAdditive (A : PreAdditive) : isPreAdditive A := pr2 A.
  Coercion PreAdditive_isPreAdditive : PreAdditive >-> isPreAdditive.

  Variable A : PreAdditive.

  (** The following give that premor and postmor are linear. *)
  Definition to_premor_linear {x y : A} (z : A) (f : x --> y) :
    isbinopfun (to_premor z f) := dirprod_pr1 (to_premor_monoid A x y z f).

  Definition to_postmor_linear (x : A) {y z : A} (f : y --> z) :
    isbinopfun (to_postmor x f) := dirprod_pr1 (to_postmor_monoid A x y z f).

  (** Following versions are useful when one wants to rewrite equations *)
  Lemma to_premor_linear' {x y z : A} (f : x --> y) (g h : y --> z) :
    f · (to_binop y z g h) = to_binop x z (f · g) (f · h).
  Proof.
    apply to_premor_linear.
  Qed.

  Lemma to_postmor_linear' {x y z : A} (g h : x --> y) (f : y --> z) :
    (to_binop x y g h) · f = to_binop x z (g · f) (h · f).
  Proof.
    apply to_postmor_linear.
  Qed.

  (** The following says that composing with zero object yields a zero object. *)
  Definition to_premor_unel {x y : A} (z : A) (f : x --> y) :
    to_premor z f 1%multmonoid = 1%multmonoid := dirprod_pr2 (to_premor_monoid A x y z f).

  Definition to_postmor_unel (x : A) {y z : A} (f : y --> z) :
    to_postmor x f 1%multmonoid = 1%multmonoid := dirprod_pr2 (to_postmor_monoid A x y z f).

  (** Following versions are useful when one wants to rewrite equations *)
  Lemma to_premor_unel' {x y : A} (z : A) (f : x --> y) : f · (to_unel y z) = to_unel x z.
  Proof.
    apply to_premor_unel.
  Qed.

  Lemma to_postmor_unel' (x : A) {y z : A} (f : y --> z) : (to_unel x y) · f = to_unel x z.
  Proof.
    apply to_postmor_unel.
  Qed.

End def_preadditive.
Arguments to_premor_linear [A] [x] [y] _ _ _ _.
Arguments to_postmor_linear [A] _ [y] [z] _ _ _.
Arguments to_premor_linear' [A] [x] [y] [z] _ _ _.
Arguments to_postmor_linear' [A] [x] [y] [z] _ _ _.


(** * Zero and unit
   In the following section we prove that if a preadditive category has a zero
   object, then in a homset the unit element is given by the zero arrow *)
Section preadditive_with_zero.

  Variable A : PreAdditive.

  (** Proof that the zero arrow and the unit element coincide *)
  Lemma PreAdditive_unel_zero (Z : Zero A) (x y : A) : to_unel x y = ZeroArrow Z x y.
  Proof.
    unfold ZeroArrow.
    rewrite <- (id_left (ZeroArrowFrom y)).
    assert (X : identity Z = to_unel Z Z) by apply ZeroEndo_is_identity.
    rewrite -> X. clear X.

    set (Y := to_postmor_unel A Z (@ZeroArrowFrom A Z y)).
    unfold to_postmor in Y. unfold to_unel.
    rewrite Y. clear Y.

    set (Y' := to_premor_unel A y (@ZeroArrowTo A Z x)).
    unfold to_premor in Y'.
    rewrite Y'. clear Y'.

    apply idpath.
  Qed.

  Lemma to_lunax'' {Z : Zero A} (x y : A) (f : x --> y) : to_binop x y (ZeroArrow Z x y) f = f.
  Proof.
    rewrite <- to_lunax'. use to_lrw. apply pathsinv0. apply PreAdditive_unel_zero.
  Qed.

  Lemma to_runax'' {Z : Zero A} (x y : A) (f : x --> y) : to_binop x y f (ZeroArrow Z x y) = f.
  Proof.
    rewrite <- to_runax'. use to_rrw. apply pathsinv0. apply PreAdditive_unel_zero.
  Qed.

  Lemma to_linvax' {Z : Zero A} {x y : A} (f : A⟦x, y⟧) :
    to_binop x y (to_inv f) f = ZeroArrow Z x y.
  Proof.
    rewrite linvax. apply PreAdditive_unel_zero.
  Qed.

  Lemma to_rinvax' {Z : Zero A} {x y : A} (f : A⟦x, y⟧) :
    to_binop x y f (to_inv f) = ZeroArrow Z x y.
  Proof.
    rewrite rinvax. apply PreAdditive_unel_zero.
  Qed.

  Lemma to_inv_zero {Z : Zero A} {x y : A} : to_inv (ZeroArrow Z x y) = ZeroArrow Z x y.
  Proof.
    rewrite <- PreAdditive_unel_zero.
    apply to_inv_unel.
  Qed.

End preadditive_with_zero.


(** * Inverses and composition
   Some equations on inverses in PreAdditive categories *)
Section preadditive_inv_comp.

  Variable A : PreAdditive.

  Lemma PreAdditive_invlcomp {x y z : A} (f : A⟦x, y⟧) (g : A⟦y, z⟧) :
    (to_inv (f · g)) = (to_inv f) · g.
  Proof.
    use (grrcan (to_abgrop x z) (f · g)).
    unfold to_inv at 1. rewrite grlinvax.
    use (pathscomp0 _ (to_postmor_linear' (to_inv f) f g)).
    rewrite linvax. rewrite to_postmor_unel'.
    unfold to_unel.
    apply idpath.
  Qed.

  Lemma PreAdditive_invrcomp {x y z : A} (f : A⟦x, y⟧) (g : A⟦y, z⟧) :
    (to_inv (f · g)) = f · (to_inv g).
  Proof.
    use (grrcan (to_abgrop x z) (f · g)).
    unfold to_inv at 1. rewrite grlinvax.
    use (pathscomp0 _ (to_premor_linear' f (to_inv g) g)).
    rewrite linvax. rewrite to_premor_unel'.
    unfold to_unel.
    apply idpath.
  Qed.

  Lemma PreAdditive_cancel_inv {x y : A} (f g : A⟦x, y⟧) (H : (to_inv f)  = (to_inv g)) : f = g.
  Proof.
    apply (grinvmaponpathsinv (to_abgrop x y) H).
  Qed.

End preadditive_inv_comp.


(** * KernelIn, CokernelOut, and Binary Operations *)
(** ** Introduction
   In this section we show that binop commutes with KernelIn and CokernelOut in a PreAdditive
   category. [KernelInOp] proves commutativity for KernelIn and [CokernelOutOp] proves commutativity
   for CokernelOut.
*)
Section def_additive_kernel_cokernel.

  Variable A : PreAdditive.
  Variable Z : Zero A.

  Local Lemma KernelInOp_Eq {x y z : A} (f1 f2 : A⟦x, y⟧) (g : A⟦y, z⟧)
        (H1 : f1 · g = ZeroArrow Z _ _) (H2 : f2 · g = ZeroArrow Z _ _) :
    (to_binop _ _ f1 f2 · g = ZeroArrow Z _ _).
  Proof.
    rewrite to_postmor_linear'. rewrite H1. rewrite H2.
    rewrite <- PreAdditive_unel_zero.
    rewrite to_lunax'. apply idpath.
  Qed.

  Lemma KernelInOp {x y z : A} (f1 f2 : A⟦x, y⟧) (g : A⟦y, z⟧) (K : Kernel Z g)
        (H1 : f1 · g = ZeroArrow Z _ _) (H2 : f2 · g = ZeroArrow Z _ _) :
    KernelIn Z K _ (to_binop _ _ f1 f2) (KernelInOp_Eq f1 f2 g H1 H2) =
    to_binop _ _ (KernelIn Z K _ f1 H1) (KernelIn Z K _ f2 H2).
  Proof.
    use KernelInsEq.
    rewrite KernelCommutes.
    rewrite to_postmor_linear'.
    rewrite KernelCommutes.
    rewrite KernelCommutes.
    apply idpath.
  Qed.

  Local Lemma CokernelOutOp_Eq {x y z : A} (f1 f2 : A⟦y, z⟧) (g : A⟦x, y⟧)
        (H1 : g · f1 = ZeroArrow Z _ _) (H2 : g · f2 = ZeroArrow Z _ _) :
    g · (to_binop _ _ f1 f2) = ZeroArrow Z _ _.
  Proof.
    rewrite to_premor_linear'. rewrite H1. rewrite H2.
    rewrite <- PreAdditive_unel_zero.
    rewrite to_lunax'. apply idpath.
  Qed.

  Lemma CokernelOutOp {x y z : A} (f1 f2 : A⟦y, z⟧) (g : A⟦x, y⟧) (CK : Cokernel Z g)
        (H1 : g · f1 = ZeroArrow Z _ _) (H2 : g · f2 = ZeroArrow Z _ _) :
    CokernelOut Z CK _ (to_binop _ _ f1 f2) (CokernelOutOp_Eq f1 f2 g H1 H2) =
    to_binop _ _ (CokernelOut Z CK _ f1 H1) (CokernelOut Z CK _ f2 H2).
  Proof.
    use CokernelOutsEq.
    rewrite CokernelCommutes.
    rewrite to_premor_linear'.
    rewrite CokernelCommutes.
    rewrite CokernelCommutes.
    apply idpath.
  Qed.

End def_additive_kernel_cokernel.


Section monics_and_epis_in_preadditive.

  Variable PA : PreAdditive.

  Lemma to_inv_isMonic {x y : PA} (f : x --> y) (isM : isMonic f) : isMonic (to_inv f).
  Proof.
    use mk_isMonic.
    intros x0 g h X.
    rewrite <- PreAdditive_invrcomp in X. rewrite <- PreAdditive_invrcomp in X.
    apply cancel_inv in X. use isM. exact X.
  Qed.

  Lemma to_inv_isEpi {x y : PA} (f : x --> y) (isE : isEpi f) : isEpi (to_inv f).
  Proof.
    use mk_isEpi.
    intros x0 g h X.
    rewrite <- PreAdditive_invlcomp in X. rewrite <- PreAdditive_invlcomp in X.
    apply cancel_inv in X. use isE. exact X.
  Qed.

End monics_and_epis_in_preadditive.


(** * Quotient of homsets
   Suppose you have a subgroup for each set of morphisms such that pre- and postcompositions map
   morphisms in a subgroup to another subgroup. Then one can form a new Preadditive category by
   taking the same objects and morphisms as elements of the quotient groups. We call this
   [PreAdditiveQuot]. An example of this construction is when one wants to form the naive homotopy
   category from a category of complexes. *)
Section preadditive_quotient.

  Variable PA : PreAdditive.

  Local Opaque ishinh.

  (** For every set morphisms we have a subgroup. *)
  Definition PreAdditiveSubabgrs : UU := ∏ (x y : ob PA), @subabgr (to_abgrop x y).

  Hypothesis PAS : PreAdditiveSubabgrs.

  (** Pre- and postcomposing with an element in the subgroups gives an element of a subgroup.
      This is important since we want pre- and postcomposition with unit element to be
      the unit element in the new precategory. *)
  Definition PreAdditiveComps : UU :=
    ∏ (x y : ob PA),
    (∏ (z : ob PA) (f : x --> y)
       (inf : pr1submonoid (@to_abgrop PA x y) (PAS x y) f) (g : y --> z),
     pr1submonoid (@to_abgrop PA x z) (PAS x z) (f · g))
      × (∏ (z : ob PA) (f : x --> y) (g : y --> z)
           (ing : pr1submonoid (@to_abgrop PA y z) (PAS y z) g),
         pr1submonoid (@to_abgrop PA x z) (PAS x z) (f · g)).

  Hypothesis PAC : PreAdditiveComps.

  (** ** Here are some random results copied from category_abgr.v.
     Theses should be deleted, removed, renamed, generalized, or ...*)

  (** The hProp which tells if two elements of A belong to the same equivalence class in A/B *)
  Definition subgrhrel_hprop {A : gr} (B : @subgr A) (a1 a2 : A) : hProp :=
    hexists (λ b : B, pr1 b = (a1 * grinv A a2)%multmonoid).

  (** Construct a relation using the above hProp *)
  Definition subgrhrel {A : gr} (B : @subgr A) : @hrel A :=
    (λ a1 : A, λ a2 : A, (subgrhrel_hprop B a1 a2)).

  (** Some equalities *)
  Local Lemma ropeq (X : setwithbinop) (x y z : X) : x = y -> @op X x z = @op X y z.
  Proof.
    intros e. induction e. apply idpath.
  Qed.

  (** Let B be a subgroup of A. Then the canonical map A -> A/B is a monoidfun. *)
  Local Lemma abgrquotpr_ismonoidfun {A : abgr} (H : @binopeqrel A) :
    @ismonoidfun A (abgrquot H) (λ a : A, setquotpr H a).
  Proof.
    split.
    - split.
    - apply idpath.
  Qed.

  Local Lemma funeqpaths {X Y : UU} {f g : X -> Y} (e : f = g) : ∏ (x : X), f x = g x.
  Proof.
    induction e. intros x. apply idpath.
  Qed.

  Local Definition abgrquotpr_monoidfun {A : abgr} (H : @binopeqrel A) : monoidfun A (abgrquot H) :=
    monoidfunconstr (abgrquotpr_ismonoidfun H).

  Local Lemma monoidfun_inv {A B : abgr} (f : monoidfun A B) (a : A) :
    f (grinv A a) = grinv B (f a).
  Proof.
    apply (grlcan B (f a)). rewrite (grrinvax B).
    use (pathscomp0 (pathsinv0 (((pr1 (pr2 f)) a (grinv A a))))).
    rewrite (grrinvax A). apply (pr2 (pr2 f)).
  Qed.

  (** The relation we defined is an equivalence relation *)
  Lemma iseqrel_subgrhrel (A : gr) (B : @subgr A) : iseqrel (subgrhrel B).
  Proof.
    unfold subgrhrel. unfold subgrhrel_hprop.
    use iseqrelconstr.
    (* istrans *)
    - intros x1 x2 x3 y1 y2. cbn in *. unfold ishinh_UU in *.
      use (squash_to_prop y1 (propproperty _)). intros Y1. clear y1.
      use (squash_to_prop y2 (propproperty _)). intros Y2. clear y2.
      use hinhpr.
      induction Y1 as [t p]. induction Y2 as [t0 p0].
      use tpair.
      + use tpair.
        * exact (op (pr1 t) (pr1 t0)).
        * exact (pr2subsetswithbinop B t t0).
      + cbn. rewrite p. rewrite p0. rewrite <- (assocax A).
        apply ropeq. rewrite assocax. rewrite grlinvax. rewrite runax.
        apply idpath.
    (* isrefl *)
    - intros x.
      use hinhpr.
      use tpair.
      + exact (unel B).
      + cbn. apply pathsinv0. apply (grrinvax A).
    (* issymm *)
    - intros x y. cbn. unfold ishinh_UU. intros H.
      use (squash_to_prop H (propproperty _)). intros H'. clear H.
      use hinhpr.
      induction H' as [t p].
      use tpair.
      + exact (grinv B t).
      + cbn. rewrite p. clear p. rewrite grinvop. rewrite grinvinv. apply idpath.
  Qed.

  (** The relation we defined respects binary operations. Note that we use commax, thus the proof
      does not work for nonabelian groups. *)
  Lemma isbinopeqrel_subgr_eqrel {A : abgr} (B : @subabgr A) :
    isbinophrel (eqrelpair (subgrhrel B) (iseqrel_subgrhrel A B)).
  Proof.
    use isbinophrelif.
    - apply (pr2 (pr2 A)).
    - intros a b c X. cbn in *. unfold ishinh_UU in *.
      use (squash_to_prop X (propproperty _)). intros X''.
      use hinhpr.
      use tpair.
      + exact (pr1 X'').
      + cbn.
        set (tmp := pr2 X''). cbn in tmp. rewrite tmp. clear tmp. clear X''.
        rewrite grinvop. rewrite (commax A c). rewrite (assocax A). rewrite (commax A c).
        rewrite (assocax A). rewrite grlinvax. rewrite runax. apply idpath.
  Qed.

  (** Thus the relation is a binopeqrel *)
  Lemma binopeqrel_subgr_eqrel {A : abgr} (B : @subabgr A) : @binopeqrel A.
  Proof.
    use binopeqrelpair.
    - exact (eqrelpair _ (iseqrel_subgrhrel A B)).
    - exact (isbinopeqrel_subgr_eqrel B).
  Defined.

  (** These are the homsets in our new category. *)
  Definition subabgr_quot {A : abgr} (B : @subabgr A) : abgr :=
    abgrquot (binopeqrel_subgr_eqrel B).

  Definition Quotcategory_homsets (c d : ob PA) : abgr := subabgr_quot (PAS c d).

  Definition Quotcategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) (ob PA) (λ A B : ob PA, Quotcategory_homsets A B).

  Lemma Quotcategory_surj {c d : Quotcategory_ob_mor} (f : Quotcategory_ob_mor⟦c, d⟧) :
    ∥ hfiber (setquotpr (binopeqrel_subgr_eqrel (PAS c d))) f ∥.
  Proof.
    use issurjsetquotpr.
  Qed.

  (** ** Composition of morphisms *)

  (** *** Some lemmas *)

  (** If images of f1 and f2 are equal, then f * inv f2 is mapped to unit. *)
  Local Lemma abgrquotpr_rels_to_unel {A : abgr} {f1 f2 : A} {H : @binopeqrel A} {f : abgrquot H}
             (e1 : setquotpr H f1 = f) (e2 : setquotpr H f2 = f) :
    setquotpr H (f1 * grinv A f2)%multmonoid = setquotpr H 1%multmonoid.
  Proof.
    rewrite <- e2 in e1. clear e2.
    apply (maponpaths (λ f : _, (f * (@grinv (abgrquot H) (setquotpr H f2)))%multmonoid)) in e1.
    rewrite grrinvax in e1. apply e1.
  Qed.

  (** Equality on relation to refl *)
  Local Lemma abgrquotpr_rel_to_refl {A : abgr} {H : @binopeqrel A} {f g : A} (e : H g g = H f g) :
    H f g.
  Proof.
    induction e.
    apply eqrelrefl.
  Qed.

  Lemma abgrquotpr_rel_paths {A : abgr} {H : @binopeqrel A} {f g : A}
        (e : setquotpr H f = setquotpr H g) : H f g.
  Proof.
    exact (abgrquotpr_rel_to_refl (! (funeqpaths (base_paths _ _ e)) g)).
  Qed.

  Lemma abgrquotpr_rel_image {A : abgr} {H : @binopeqrel A} {f g : A}
        (e : H f g) : setquotpr H f = setquotpr H g.
  Proof.
    apply iscompsetquotpr.
    exact e.
  Qed.

  (** *** Morphisms to elements of groups *)
  Local Lemma mor_to_elem {a b : PA} (f : PA⟦a, b⟧) (H : pr1 (PAS a b) f) : carrier (pr1 (PAS a b)).
  Proof.
    use tpair.
    - exact f.
    - exact H.
  Defined.

  Local Lemma to_inv_elem {a b : PA} (f : PA⟦a, b⟧) (H : pr1 (PAS a b) f) : carrier (pr1 (PAS a b)).
  Proof.
    use tpair.
    - exact (@grinv (to_abgrop a b) f).
    - apply (pr2 (pr2 (PAS a b))). exact H.
  Defined.

  Local Lemma to_op_elem {A B : PA} (f g : PA⟦A, B⟧) (H1 : pr1 (PAS A B) f) (H2 : pr1 (PAS A B) g) :
    pr1 (PAS A B) (to_binop A B f g).
  Proof.
    set (tmp := pr1 (pr1 (pr2 (PAS A B)))). cbn in tmp. unfold issubsetwithbinop in tmp.
    set (a := mor_to_elem f H1). set (a' := mor_to_elem g H2).
    apply (tmp a a').
  Qed.

  (** *** Composition of morphisms in the quotient precategory *)

  (** **** Structure for composition *)

  Definition QuotcategoryComp {A B C : ob PA} (f : Quotcategory_ob_mor⟦A, B⟧)
             (g : Quotcategory_ob_mor⟦B, C⟧) : UU :=
    ∑ h : Quotcategory_ob_mor⟦A, C⟧,
          (∏ (f' : PA⟦A, B⟧) (e1 : setquotpr _ f' = f)
             (g' : PA⟦B, C⟧) (e2 : setquotpr _ g' = g), setquotpr _ (f' · g') = h).

  Definition mk_QuotcategoryComp {A B C : ob PA} {f : Quotcategory_ob_mor⟦A, B⟧}
             {g : Quotcategory_ob_mor⟦B, C⟧} (h : Quotcategory_ob_mor⟦A, C⟧)
             (H : ∏ (f' : PA⟦A, B⟧) (e1 : setquotpr _ f' = f)
                    (g' : PA⟦B, C⟧) (e2 : setquotpr _ g' = g), setquotpr _ (f' · g') = h) :
    QuotcategoryComp f g := tpair _ h H.

  Definition QuotcategoryCompMor {A B C : ob PA} {f : Quotcategory_ob_mor⟦A, B⟧}
             {g : Quotcategory_ob_mor⟦B, C⟧} (QPC : QuotcategoryComp f g) :
    Quotcategory_ob_mor⟦A, C⟧ := pr1 QPC.

  Definition QuotcategoryCompEq {A B C : ob PA} {f : Quotcategory_ob_mor⟦A, B⟧}
             {g : Quotcategory_ob_mor⟦B, C⟧} (QPC : QuotcategoryComp f g) :
    ∏ (f' : PA⟦A, B⟧) (e1 : setquotpr _ f' = f) (g' : PA⟦B, C⟧) (e2 : setquotpr _ g' = g),
    setquotpr _ (f' · g') = QuotcategoryCompMor QPC := pr2 QPC.


  (** **** Composition for quotient category *)

  Local Lemma Quotcategory_comp_iscontr_PAS_eq {A : abgr} {a b c : A}
        (e : a = (b * (grinv A c))%multmonoid) : b = (a * c)%multmonoid.
  Proof.
    rewrite e. rewrite assocax. rewrite grlinvax. rewrite runax. apply idpath.
  Qed.

  Lemma Quotcategory_comp_iscontr_PAS {A B C : PA} {t : pr1 (PAS A B)} {t' : pr1 (PAS B C)}
        {f1 f'1 : PA⟦A, B⟧} {g1 g'1 : PA⟦B, C⟧}
        (p : pr1 t = to_binop A B f'1 (grinv (to_abgrop A B) f1))
        (p' : pr1 t' = to_binop B C g'1 (grinv (to_abgrop B C) g1)) :
    pr1 (PAS A C) (to_binop A C (f1 · g1) (grinv (to_abgrop A C) (f'1 · g'1))).
  Proof.
    set (e1 := Quotcategory_comp_iscontr_PAS_eq p).
    set (e2 := Quotcategory_comp_iscontr_PAS_eq p').
    rewrite e1. rewrite e2. clear e1 e2 p p'. cbn.
    rewrite to_premor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    set (ac := assocax (to_abgrop A C)). unfold isassoc in ac. cbn in ac.
    set (comm := commax (to_abgrop A C)). unfold iscomm in comm. cbn in comm.
    rewrite (comm _ (f1 · g1)). rewrite <- (ac _ (f1 · g1) _).
    rewrite (comm _ (f1 · g1)). rewrite ac. rewrite ac.
    set (i := grinvop (to_abgrop A C)). cbn in i. rewrite i. repeat rewrite <- ac.
    rewrite comm. rewrite <- ac.
    set (il := linvax _ (f1 · g1)). unfold to_inv in il. rewrite il. clear il.
    set (lu := to_lunax A C). unfold islunit in lu. cbn in lu. unfold to_unel. rewrite lu.
    set (tmp := pr2 (pr2 (PAS A C))). cbn in tmp. apply tmp. clear tmp.
    use to_op_elem.
    - use to_op_elem.
      + apply (dirprod_pr1 (PAC A B) C (pr1 t) (pr2 t) (pr1 t')).
      + apply (dirprod_pr2 (PAC A B) C f1 (pr1 t') (pr2 t')).
    - apply (dirprod_pr1 (PAC A B) C (pr1 t) (pr2 t) g1).
  Qed.

  Local Lemma Quotcategory_comp_iscontr_eq {A B C : ob PA} (f : Quotcategory_ob_mor⟦A, B⟧)
        (g : Quotcategory_ob_mor⟦B, C⟧)  (f'1 : PA ⟦ A, B ⟧) (f''1 : setquotpr _ f'1 = f)
        (g'1 : PA ⟦ B, C ⟧) (g''1 : setquotpr _ g'1 = g) :
    ∏ (f' : PA⟦A, B⟧) (e1 : setquotpr _ f' = f) (g' : PA⟦B, C⟧) (e2 : setquotpr _ g' = g),
    setquotpr _ (f' · g') = setquotpr (binopeqrel_subgr_eqrel (PAS A C)) (f'1 · g'1).
  Proof.
    intros f1 Hf g1 Hg. cbn.
    apply (iscompsetquotpr (eqrelpair _ (iseqrel_subgrhrel (to_abgrop A C) (PAS A C)))).
    set (HH := @abgrquotpr_rels_to_unel
                 (to_abgrop A B) f'1 f1 (binopeqrel_subgr_eqrel (PAS A B)) f f''1 Hf).
    set (HH' := @abgrquotpr_rels_to_unel
                  (to_abgrop B C) g'1 g1 (binopeqrel_subgr_eqrel (PAS B C)) g g''1 Hg).
    apply abgrquotpr_rel_paths in HH. apply abgrquotpr_rel_paths in HH'.
    use (squash_to_prop HH). apply propproperty. intros HHH. clear HH.
    use (squash_to_prop HH'). apply propproperty. intros HHH'. clear HH'.
    cbn in HHH. cbn in HHH'. induction HHH as [t p]. induction HHH' as [t' p'].
    rewrite grinvunel in p. rewrite grinvunel in p'.
    set (tmp := to_runax A B). unfold isrunit in tmp. cbn in tmp. rewrite tmp in p. clear tmp.
    set (tmp := to_runax B C). unfold isrunit in tmp. cbn in tmp. rewrite tmp in p'. clear tmp.
    use hinhpr.
    use tpair.
    + use tpair.
      * exact (to_binop A C (f1 · g1) (grinv (to_abgrop A C) (f'1 · g'1))).
      * apply (Quotcategory_comp_iscontr_PAS p p').
    + apply idpath.
  Qed.

  Local Lemma QuotPrecatetgory_comp_iscontr_univ {A B C : ob PA} (f : Quotcategory_ob_mor⟦A, B⟧)
             (g : Quotcategory_ob_mor⟦B, C⟧)
             (f' : hfiber (setquotpr (binopeqrel_subgr_eqrel (PAS A B))) f)
             (g' : hfiber (setquotpr (binopeqrel_subgr_eqrel (PAS B C))) g) :
    ∏ t : QuotcategoryComp f g,
          t = mk_QuotcategoryComp
                (setquotpr (binopeqrel_subgr_eqrel (PAS A C))
                           (hfiberpr1 _ _ f' · hfiberpr1 _ _ g'))
                (Quotcategory_comp_iscontr_eq
                   f g (hfiberpr1 (setquotpr (binopeqrel_subgr_eqrel (PAS A B))) f f')
                   (hfiberpr2 (setquotpr (binopeqrel_subgr_eqrel (PAS A B))) f f')
                   (hfiberpr1 (setquotpr (binopeqrel_subgr_eqrel (PAS B C))) g g')
                   (hfiberpr2 (setquotpr (binopeqrel_subgr_eqrel (PAS B C))) g g')).
  Proof.
    intros t.
    use total2_paths_f.
    - exact (! (pr2 t (hfiberpr1 _ _ f') (hfiberpr2 _ _ f') (hfiberpr1 _ _ g') (hfiberpr2 _ _ g'))).
    - apply proofirrelevance.
      apply impred. intros t'.
      apply impred. intros H.
      apply impred. intros t0.
      apply impred. intros H0.
      apply isasetsetquot.
  Qed.

  Lemma Quotcategory_comp_iscontr {A B C : ob PA} (f : Quotcategory_ob_mor⟦A, B⟧)
             (g : Quotcategory_ob_mor⟦B, C⟧) : iscontr (QuotcategoryComp f g).
  Proof.
    use (squash_to_prop (Quotcategory_surj f) (isapropiscontr _)). intros f'.
    use (squash_to_prop (Quotcategory_surj g) (isapropiscontr _)). intros g'.
    use iscontrpair.
    - use mk_QuotcategoryComp.
      + exact (setquotpr
                 (binopeqrel_subgr_eqrel (PAS A C)) ((hfiberpr1 _ _ f') · (hfiberpr1 _ _ g'))).
      + exact (Quotcategory_comp_iscontr_eq
                 f g (hfiberpr1 _ _ f') (hfiberpr2 _ _ f') (hfiberpr1 _ _ g') (hfiberpr2 _ _ g')).
    - exact (QuotPrecatetgory_comp_iscontr_univ f g f' g').
  Defined.

  Definition Quotcategory_comp {A B C : ob PA} (f : Quotcategory_ob_mor⟦A, B⟧)
             (g : Quotcategory_ob_mor⟦B, C⟧) : Quotcategory_ob_mor⟦A, C⟧.
  Proof.
    exact (QuotcategoryCompMor (iscontrpr1 (Quotcategory_comp_iscontr f g))).
  Defined.

  Definition to_quot_mor {x y : ob PA} (f : PA⟦x, y⟧) : Quotcategory_ob_mor⟦x, y⟧.
  Proof.
    use setquotpr. exact f.
  Defined.


  (** ** Some equations on linearity, compositions, and binops *)

  Lemma Quotcategory_comp_linear {x y z : ob PA} (f : PA⟦x, y⟧) (g : PA⟦y, z⟧) :
    Quotcategory_comp (to_quot_mor f) (to_quot_mor g) = to_quot_mor (f · g).
  Proof.
    unfold to_quot_mor. unfold Quotcategory_comp.
    apply pathsinv0.
    use (pr2 (pr1 (Quotcategory_comp_iscontr
                           (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) f)
                           (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) g)))).
    - apply idpath.
    - apply idpath.
  Qed.

  (** Pre- and postcomposition respect binop. *)
  Local Lemma Quotcategory_premor {x y z : PA} (f : PA⟦x, y⟧) (g h : PA⟦y, z⟧) :
    Quotcategory_comp (to_quot_mor f) ((to_quot_mor g * to_quot_mor h)%multmonoid) =
    ((Quotcategory_comp (to_quot_mor f) (to_quot_mor g)) *
     (Quotcategory_comp (to_quot_mor f) (to_quot_mor h)))%multmonoid.
  Proof.
    Local Opaque binopeqrel_subgr_eqrel isabgrquot setquotfun2 Quotcategory_comp.
    apply pathsinv0. cbn.
    eapply pathscomp0.
    - rewrite Quotcategory_comp_linear. rewrite Quotcategory_comp_linear.
      use setquotfun2comm.
    - apply pathsinv0.
      unfold to_quot_mor.
      set (tmp := setquotfun2comm (binopeqrel_subgr_eqrel (PAS y z))
                                  (binopeqrel_subgr_eqrel (PAS y z))
                                  (to_binop y z)
                                  (iscompbinoptransrel
                                     (binopeqrel_subgr_eqrel (PAS y z))
                                     (eqreltrans (binopeqrel_subgr_eqrel (PAS y z)))
                                     (pr2 (binopeqrel_subgr_eqrel (PAS y z))))).
      rewrite tmp. clear tmp.
      rewrite <- to_premor_linear'.
      apply pathsinv0.
      Local Transparent Quotcategory_comp. unfold Quotcategory_comp.
      apply (pr2 (pr1 (Quotcategory_comp_iscontr
                         (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) f)
                         (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) (to_binop y z g h))))).
      + apply idpath.
      + apply idpath.
  Qed.

  Local Lemma Quotcategory_postmor {x y z : PA} (f : PA⟦y, z⟧) (g h : PA⟦x, y⟧) :
    Quotcategory_comp (to_quot_mor g * to_quot_mor h)%multmonoid (to_quot_mor f) =
    ((Quotcategory_comp (to_quot_mor g) (to_quot_mor f)) *
     (Quotcategory_comp (to_quot_mor h) (to_quot_mor f)))%multmonoid.
  Proof.
    Local Opaque Quotcategory_comp.
    apply pathsinv0. cbn.
    eapply pathscomp0.
    - rewrite Quotcategory_comp_linear. rewrite Quotcategory_comp_linear.
      use setquotfun2comm.
    - unfold to_quot_mor. rewrite setquotfun2comm.
      Local Transparent Quotcategory_comp.
      unfold Quotcategory_comp.
      rewrite <- to_postmor_linear'.
      apply (pr2 (pr1 (Quotcategory_comp_iscontr
                         (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) (to_binop x y g h))
                         (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) f)))).
      + apply idpath.
      + apply idpath.
  Qed.

  (** Composing with the unit element gives the unit element. *)
  Local Lemma quot_comp_unel_left {x y z : PA} (f : PA⟦x, y⟧) :
    Quotcategory_comp (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) f)
                         (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) (@to_unel PA y z)) =
    (setquotpr (binopeqrel_subgr_eqrel (PAS x z)) (@to_unel PA x z)).
  Proof.
    rewrite <- (to_premor_unel' _ _ f). apply pathsinv0.
    unfold Quotcategory_comp.
    apply (pr2 (pr1 (Quotcategory_comp_iscontr
                       (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) f)
                       (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) (to_unel y z))))).
    - apply idpath.
    - apply idpath.
  Qed.

  Local Lemma quot_comp_unel_right {x y z : PA} (f : PA⟦y, z⟧) :
    Quotcategory_comp (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) (to_unel x y))
                         (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) f) =
    (setquotpr (binopeqrel_subgr_eqrel (PAS x z)) (to_unel x z)).
  Proof.
    rewrite <- (to_postmor_unel' _ _ f). apply pathsinv0.
    unfold Quotcategory_comp.
    apply (pr2 (pr1 (Quotcategory_comp_iscontr
                       (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) (to_unel x y))
                       (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) f)))).
    - apply idpath.
    - apply idpath.
  Qed.


  (** ** Construction of the Quotcategory *)

  Definition Quotcategory_data : precategory_data :=
    precategory_data_pair
      Quotcategory_ob_mor
      (λ (A : ob PA), setquotpr (binopeqrel_subgr_eqrel (PAS A A)) (identity A))
      (fun (A B C : ob PA) (f : Quotcategory_ob_mor⟦A, B⟧)
         (g : Quotcategory_ob_mor⟦B, C⟧) => Quotcategory_comp f g).

  (** The following two lemmas are used to show associaticity of composition in
      Quotcategory. *)
  Local Lemma Quot_assoc1 {a b c d : Quotcategory_data} (f : Quotcategory_data ⟦a, b⟧)
        (g : Quotcategory_data ⟦b, c⟧) (h : Quotcategory_data ⟦c, d⟧)
        (f1 : PA⟦a, b⟧) (f2 : setquotpr (binopeqrel_subgr_eqrel (PAS a b)) f1 = f)
        (g1 : PA⟦b, c⟧) (g2 : setquotpr (binopeqrel_subgr_eqrel (PAS b c)) g1 = g)
        (h1 : PA⟦c, d⟧) (h2 : setquotpr (binopeqrel_subgr_eqrel (PAS c d)) h1 = h) :
    Quotcategory_comp f (Quotcategory_comp g h) =
    setquotpr (binopeqrel_subgr_eqrel (PAS a d)) (f1 · (g1 · h1)).
  Proof.
    apply pathsinv0.
    set (ic2 := Quotcategory_comp_iscontr g h).
    set (ic3 := Quotcategory_comp_iscontr f (pr1 (pr1 ic2))).
    set (tmp := pr2 (pr1 ic3)). cbn beta in tmp. unfold Quotcategory_comp.
    fold ic2. fold ic3. use tmp.
    - exact f2.
    - use (pr2 (pr1 ic2)).
      + exact g2.
      + exact h2.
  Qed.

  Local Lemma Quot_assoc2 {a b c d : Quotcategory_data} (f : Quotcategory_data ⟦a, b⟧)
        (g : Quotcategory_data ⟦b, c⟧) (h : Quotcategory_data ⟦c, d⟧)
        (f1 : PA⟦a, b⟧) (f2 : setquotpr (binopeqrel_subgr_eqrel (PAS a b)) f1 = f)
        (g1 : PA⟦b, c⟧) (g2 : setquotpr (binopeqrel_subgr_eqrel (PAS b c)) g1 = g)
        (h1 : PA⟦c, d⟧) (h2 : setquotpr (binopeqrel_subgr_eqrel (PAS c d)) h1 = h) :
    setquotpr (binopeqrel_subgr_eqrel (PAS a d)) ((f1 · g1) · h1) =
    Quotcategory_comp (Quotcategory_comp f g) h.
  Proof.
    set (ic1 := Quotcategory_comp_iscontr f g).
    set (ic4 := Quotcategory_comp_iscontr (pr1 (pr1 ic1)) h).
    set (tmp := pr2 (pr1 ic4)). cbn beta in tmp. unfold Quotcategory_comp.
    fold ic1. fold ic4. use tmp.
    - use (pr2 (pr1 ic1)).
      + exact f2.
      + exact g2.
    - exact h2.
  Qed.

  (** Quotcategory is a precategory *)
  Lemma is_precategory_Quotcategory_data : is_precategory Quotcategory_data.
  Proof.
    split.
    - split.
      (* id left *)
      + intros a b f. apply pathsinv0. cbn. unfold Quotcategory_comp.
        set (f'' := @issurjsetquotpr (to_abgrop a b) (binopeqrel_subgr_eqrel (PAS a b)) f).
        use (squash_to_prop f''). apply isasetsetquot. intros f'. clear f''.
        induction f' as [f1 f2]. rewrite <- f2. cbn in f1, a, b.
        eapply pathscomp0.
        * apply maponpaths. exact (! (id_left f1)).
        * apply (pr2 (pr1 (Quotcategory_comp_iscontr
                             (setquotpr (binopeqrel_subgr_eqrel (PAS a a)) (@identity PA a))
                             (setquotpr (binopeqrel_subgr_eqrel (PAS a b)) f1)))).
          -- apply idpath.
          -- apply idpath.
      (* id right *)
      + intros a b f. apply pathsinv0. cbn. unfold Quotcategory_comp.
        set (f'' := @issurjsetquotpr (to_abgrop a b) (binopeqrel_subgr_eqrel (PAS a b)) f).
        use (squash_to_prop f''). apply isasetsetquot. intros f'. clear f''.
        induction f' as [f1 f2]. rewrite <- f2. cbn in f1, a, b.
        eapply pathscomp0.
        * apply maponpaths. exact (! (id_right f1)).
        * apply (pr2 (pr1 (Quotcategory_comp_iscontr
                             (setquotpr (binopeqrel_subgr_eqrel (PAS a b)) f1)
                             (setquotpr (binopeqrel_subgr_eqrel (PAS b b)) (@identity PA b))))).
          -- apply idpath.
          -- apply idpath.
    (* assoc *)
    - intros a b c d f g h. cbn.
      set (f'' := @issurjsetquotpr (to_abgrop a b) (binopeqrel_subgr_eqrel (PAS a b)) f).
      use (squash_to_prop f''). apply isasetsetquot. intros f'. clear f''.
      set (g'' := @issurjsetquotpr (to_abgrop b c) (binopeqrel_subgr_eqrel (PAS b c)) g).
      use (squash_to_prop g''). apply isasetsetquot. intros g'. clear g''.
      set (h'' := @issurjsetquotpr (to_abgrop c d) (binopeqrel_subgr_eqrel (PAS c d)) h).
      use (squash_to_prop h''). apply isasetsetquot. intros h'. clear h''.
      induction f' as [f1 f2]. induction g' as [g1 g2]. induction h' as [h1 h2].
      cbn in f1, g1, h1.
      rewrite (Quot_assoc1 f g h f1 f2 g1 g2 h1 h2).
      rewrite <- (Quot_assoc2 f g h f1 f2 g1 g2 h1 h2).
      rewrite assoc. apply idpath.
  Qed.

  Definition Quotcategory : precategory :=
    tpair _ _ is_precategory_Quotcategory_data.

  Lemma has_homsets_Quotcategory : has_homsets Quotcategory.
  Proof.
    intros a b. apply isasetsetquot.
  Qed.


  (** ** Quotient precategory of PreAdditive is PreAdditive *)

  Definition Quotcategory_binops : precategoryWithBinOps.
  Proof.
    use mk_precategoryWithBinOps.
    - exact Quotcategory.
    - intros x y. exact (@op (subabgr_quot (PAS x y))).
  Defined.

  Unset Kernel Term Sharing.
  Definition Quotcategory_abgrops : categoryWithAbgrops.
  Proof.
    use mk_categoryWithAbgrops.
    - exact Quotcategory_binops.
    - exact has_homsets_Quotcategory.
    - intros x y. exact (pr2 (subabgr_quot (PAS x y))).
  Defined.
  Set Kernel Term Sharing.

  Local Lemma quot_unel {x y : PA} :
    setquotpr (binopeqrel_subgr_eqrel (PAS x y)) (@to_unel PA x y) =
    unel (@to_abgrop Quotcategory_abgrops x y).
  Proof.
    apply idpath.
  Qed.

  Local Opaque to_abgrop.
  Local Lemma PreAdditive_pre_linear (x y z : ob Quotcategory_abgrops)
    (f : Quotcategory_abgrops⟦x, y⟧) (g h : Quotcategory_abgrops ⟦y, z⟧):
    f · to_binop y z g h = to_binop x z (f · g) (f · h).
  Proof.
    use (squash_to_prop (Quotcategory_surj f)). apply to_has_homsets. intros f'.
    use (squash_to_prop (Quotcategory_surj g)). apply to_has_homsets. intros g'.
    use (squash_to_prop (Quotcategory_surj h)). apply to_has_homsets. intros h'.
    rewrite <- (hfiberpr2 _ _ f'). rewrite <- (hfiberpr2 _ _ g'). rewrite <- (hfiberpr2 _ _ h').
    exact (Quotcategory_premor (hfiberpr1 _ _ f') (hfiberpr1 _ _ g') (hfiberpr1 _ _ h')).
  Qed.

  Local Lemma PreAdditive_pre_unel (x y z : ob Quotcategory_abgrops)
        (f : Quotcategory_abgrops⟦x, y⟧) : f · (@to_unel Quotcategory_abgrops y z) =
                                              @to_unel Quotcategory_abgrops x z.
  Proof.
    use (squash_to_prop (Quotcategory_surj f)). apply (@to_has_homsets Quotcategory_abgrops).
    intros f'. rewrite <- (hfiberpr2 _ _ f').
    exact (@quot_comp_unel_left x y z (hfiberpr1 _ _ f')).
  Qed.

  Local Lemma PreAdditive_post_linear (x y z : ob Quotcategory_abgrops)
    (f : Quotcategory_abgrops⟦y, z⟧) (g h : Quotcategory_abgrops ⟦x, y⟧):
    to_binop x y g h · f = to_binop x z (g · f) (h · f).
  Proof.
    use (squash_to_prop (Quotcategory_surj f)). apply to_has_homsets. intros f'.
    use (squash_to_prop (Quotcategory_surj g)). apply to_has_homsets. intros g'.
    use (squash_to_prop (Quotcategory_surj h)). apply to_has_homsets. intros h'.
    rewrite <- (hfiberpr2 _ _ f'). rewrite <- (hfiberpr2 _ _ g'). rewrite <- (hfiberpr2 _ _ h').
    exact (Quotcategory_postmor (hfiberpr1 _ _ f') (hfiberpr1 _ _ g') (hfiberpr1 _ _ h')).
  Qed.

  Local Lemma PreAdditive_post_unel (x y z : ob Quotcategory_abgrops)
        (f : Quotcategory_abgrops⟦y, z⟧) : (@to_unel Quotcategory_abgrops x y) · f =
                                              @to_unel Quotcategory_abgrops x z.
  Proof.
    use (squash_to_prop (Quotcategory_surj f)). apply (@to_has_homsets Quotcategory_abgrops).
    intros f'. rewrite <- (hfiberpr2 _ _ f').
    exact (@quot_comp_unel_right x y z (hfiberpr1 _ _ f')).
  Qed.

  Lemma Quotcategory_isPreAdditive : isPreAdditive Quotcategory_abgrops.
  Proof.
    use mk_isPreAdditive'.
    - intros x y z f g h. exact (PreAdditive_pre_linear x y z f g h).
    - intros x y z f. exact (PreAdditive_pre_unel x y z f).
    - intros x y z f g h. exact (PreAdditive_post_linear x y z f g h).
    - intros x y z f. exact (PreAdditive_post_unel x y z f).
  Qed.

  Definition Quotcategory_PreAdditive : PreAdditive.
  Proof.
    use mk_PreAdditive.
    - exact Quotcategory_abgrops.
    - exact Quotcategory_isPreAdditive.
  Defined.

  Lemma setquotpr_linear {x y : PA} (f g : PA⟦x, y⟧) :
    to_quot_mor (@to_binop PA _ _ f g) =
    @to_binop Quotcategory_PreAdditive _ _ (to_quot_mor f) (to_quot_mor g).
  Proof.
    exact (pr1 (abgrquotpr_ismonoidfun (binopeqrel_subgr_eqrel (PAS x y))) f g).
  Qed.

  Lemma comp_eq {x y z : PA} (f : Quotcategory_PreAdditive⟦x, y⟧)
        (g : Quotcategory_PreAdditive⟦y, z⟧) : Quotcategory_comp f g = f · g.
  Proof.
    apply idpath.
  Qed.


  (** ** The canonical functor to Quotcategory *)
  (** This functor is identity on objects and sends morphisms to the equivalence class they
      represent. *)

  Definition QuotcategoryFunctor_data : functor_data PA Quotcategory_PreAdditive.
  Proof.
    use tpair.
    - intros X. exact X.
    - intros X Y f. exact (setquotpr (binopeqrel_subgr_eqrel (PAS X Y)) f).
  Defined.

  Local Lemma QuotcategoryFunctor_isfunctor : is_functor QuotcategoryFunctor_data.
  Proof.
    split.
    - intros X. apply idpath.
    - intros x Y Z f g. exact (! (Quotcategory_comp_linear f g)).
  Qed.

  Definition QuotcategoryFunctor : functor PA Quotcategory_PreAdditive.
  Proof.
    use tpair.
    - exact QuotcategoryFunctor_data.
    - exact QuotcategoryFunctor_isfunctor.
  Defined.


  (** ** If PA has a zero object, then so does Quotcategory of PA *)

  Variable Z : Zero PA.

  Lemma Quotcategory_isZero : isZero Quotcategory Z.
  Proof.
    use mk_isZero.
    - intros a.
      use tpair.
      + exact (to_quot_mor (@ZeroArrowFrom PA Z a)).
      + cbn beta. intros t.
        set (t'1 := @issurjsetquotpr (to_abgrop Z a) (binopeqrel_subgr_eqrel (PAS Z a)) t).
        use (squash_to_prop t'1). apply has_homsets_Quotcategory. intros t1. clear t'1.
        induction t1 as [t1 t2]. rewrite <- t2. unfold to_quot_mor. apply maponpaths.
        apply ArrowsFromZero.
    - intros a.
      use tpair.
      + exact (to_quot_mor (@ZeroArrowTo PA Z a)).
      + cbn beta. intros t.
        set (t'1 := @issurjsetquotpr (to_abgrop a Z) (binopeqrel_subgr_eqrel (PAS a Z)) t).
        use (squash_to_prop t'1). apply has_homsets_Quotcategory. intros t1. clear t'1.
        induction t1 as [t1 t2]. rewrite <- t2. unfold to_quot_mor. apply maponpaths.
        apply ArrowsToZero.
  Qed.

  Definition Quotcategory_Zero : @Zero Quotcategory.
  Proof.
    use mk_Zero.
    - exact Z.
    - exact Quotcategory_isZero.
  Defined.

End preadditive_quotient.
