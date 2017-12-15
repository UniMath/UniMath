(** ****************************************************************

Benedikt Ahrens
started March 2015

Extended by: Anders Mörtberg. October 2015

*******************************************************************)

(** ***************************************************************

Contents :

- Category of algebras of an endofunctor

- This category is saturated if base precategory is

- Lambek's lemma: if (A,a) is an inital F-algebra then a is an iso

- The natural numbers are intial for X ↦ 1 + X

******************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.initial.

(* The following are used for examples *)
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Local Open Scope cat.

(** ** Category of algebras of an endofunctor *)

Section Algebra_Definition.

Context {C : precategory} (F : functor C C).

Definition algebra_ob : UU := ∑ X : C, F X --> X.

(* this coercion causes confusion, and it is not inserted when parsing most of the time
   thus removing coercion globally
*)
Definition alg_carrier (X : algebra_ob) : C := pr1 X.
Local Coercion alg_carrier : algebra_ob >-> ob.

Definition alg_map (X : algebra_ob) : F X --> X := pr2 X.

(** A morphism of an F-algebras (F X, g : F X --> X) and (F Y, h : F Y --> Y)
    is a morphism f : X --> Y such that the following diagram commutes:

    <<
         F f
    F x ----> F y
    |         |
    | g       | h
    V         V
    x ------> y
         f
    >>
 *)
Definition is_algebra_mor (X Y : algebra_ob) (f : alg_carrier X --> alg_carrier Y) : UU
  := alg_map X · f = #F f · alg_map Y.

Definition algebra_mor (X Y : algebra_ob) : UU :=
  ∑ f : X --> Y, is_algebra_mor X Y f.

Coercion mor_from_algebra_mor (X Y : algebra_ob) (f : algebra_mor X Y) : X --> Y := pr1 f.

Definition isaset_algebra_mor (hs : has_homsets C) (X Y : algebra_ob) : isaset (algebra_mor X Y).
Proof.
  apply (isofhleveltotal2 2).
  - apply hs.
  - intro f.
    apply isasetaprop.
    apply hs.
Qed.

Definition algebra_mor_eq (hs : has_homsets C) {X Y : algebra_ob} {f g : algebra_mor X Y}
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro a. apply hs.
Defined.

Lemma algebra_mor_commutes (X Y : algebra_ob) (f : algebra_mor X Y)
  : alg_map X · f = #F f · alg_map Y.
Proof.
  exact (pr2 f).
Qed.

Definition algebra_mor_id (X : algebra_ob) : algebra_mor X X.
Proof.
  exists (identity _ ).
  abstract (unfold is_algebra_mor;
            rewrite id_right ;
            rewrite functor_id;
            rewrite id_left;
            apply idpath).
Defined.

Definition algebra_mor_comp (X Y Z : algebra_ob) (f : algebra_mor X Y) (g : algebra_mor Y Z)
  : algebra_mor X Z.
Proof.
  exists (f · g).
  abstract (unfold is_algebra_mor;
            rewrite assoc;
            rewrite algebra_mor_commutes;
            rewrite <- assoc;
            rewrite algebra_mor_commutes;
            rewrite functor_comp, assoc;
            apply idpath).
Defined.

Definition precategory_alg_ob_mor : precategory_ob_mor.
Proof.
  exists algebra_ob.
  exact algebra_mor.
Defined.

Definition precategory_alg_data : precategory_data.
Proof.
  exists precategory_alg_ob_mor.
  exists algebra_mor_id.
  exact algebra_mor_comp.
Defined.

Lemma is_precategory_precategory_alg_data (hs : has_homsets C)
  : is_precategory precategory_alg_data.
Proof.
  repeat split; intros; simpl.
  - apply algebra_mor_eq.
    + apply hs.
    + apply id_left.
  - apply algebra_mor_eq.
    + apply hs.
    + apply id_right.
  - apply algebra_mor_eq.
    + apply hs.
    + apply assoc.
Qed.

Definition precategory_FunctorAlg (hs : has_homsets C)
  : precategory := tpair _ _ (is_precategory_precategory_alg_data hs).

Local Notation FunctorAlg := precategory_FunctorAlg.

Lemma has_homsets_FunctorAlg (hs : has_homsets C)
  : has_homsets (FunctorAlg hs).
Proof.
  intros f g.
  apply isaset_algebra_mor.
  assumption.
Qed.

(** ** This category is saturated if the base category is  *)

Section FunctorAlg_saturated.

Hypothesis H : is_univalent C.

Definition algebra_eq_type (X Y : FunctorAlg (pr2 H)) : UU
  := ∑ p : iso (pr1 X) (pr1 Y), pr2 X · p = #F p · pr2 Y.

Definition algebra_ob_eq (X Y : FunctorAlg (pr2 H)) :
  (X = Y) ≃ algebra_eq_type X Y.
Proof.
  eapply weqcomp.
  - apply total2_paths_equiv.
  - set (H1 := weqpair _ (pr1 H (pr1 X) (pr1 Y))).
    apply (weqbandf H1).
    simpl.
    intro p.
    destruct X as [X α].
    destruct Y as [Y β]; simpl in *.
    destruct p.
    apply weqimplimpl.
    + intro x; simpl.
      rewrite functor_id.
      rewrite id_left, id_right.
      apply x.
    + simpl; rewrite functor_id, id_left, id_right.
      induction 1. apply idpath.
    + apply (pr2 H).
    + apply (pr2 H).
Defined.

Definition is_iso_from_is_algebra_iso (X Y : FunctorAlg (pr2 H)) (f : X --> Y)
  : is_iso f → is_iso (pr1 f).
Proof.
  intro p.
  apply is_iso_from_is_z_iso.
  set (H' := iso_inv_after_iso (isopair f p)).
  set (H'':= iso_after_iso_inv (isopair f p)).
  exists (pr1 (inv_from_iso (isopair f p))).
  split; simpl.
  - apply (maponpaths pr1 H').
  - apply (maponpaths pr1 H'').
Defined.

Definition inv_algebra_mor_from_is_iso {X Y : FunctorAlg (pr2 H)} (f : X --> Y)
  : is_iso (pr1 f) → (Y --> X).
Proof.
  intro T.
  set (fiso:=isopair (pr1 f) T).
  set (finv:=inv_from_iso fiso).
  exists finv.
  unfold finv.
  apply pathsinv0.
  apply iso_inv_on_left.
  simpl.
  rewrite functor_on_inv_from_iso.
  rewrite <- assoc.
  apply pathsinv0.
  apply iso_inv_on_right.
  simpl.
  apply (pr2 f).
Defined.

Definition is_algebra_iso_from_is_iso {X Y : FunctorAlg (pr2 H)} (f : X --> Y)
  : is_iso (pr1 f) → is_iso f.
Proof.
  intro T.
  apply is_iso_from_is_z_iso.
  exists (inv_algebra_mor_from_is_iso f T).
  split; simpl.
  - apply algebra_mor_eq.
    + apply (pr2 H).
    + simpl.
      apply (iso_inv_after_iso (isopair (pr1 f) T)).
  - apply algebra_mor_eq.
    + apply (pr2 H).
    + apply (iso_after_iso_inv (isopair (pr1 f) T)).
Defined.

Definition algebra_iso_first_iso {X Y : FunctorAlg (pr2 H)}
  : iso X Y ≃ ∑ f : X --> Y, is_iso (pr1 f).
Proof.
  apply (weqbandf (idweq _ )).
  intro f.
  apply weqimplimpl; simpl.
  - apply is_iso_from_is_algebra_iso.
  - apply is_algebra_iso_from_is_iso.
  - apply isaprop_is_iso.
  - apply isaprop_is_iso.
Defined.

Definition swap (A B : UU) : A × B → B × A.
Proof.
  intro ab.
  exists (pr2 ab).
  exact (pr1 ab).
Defined.

Definition swapweq (A B : UU) : (A × B) ≃ (B × A).
Proof.
  exists (swap A B).
  apply (gradth _ (swap B A)).
  - intro ab. destruct ab. apply idpath.
  - intro ba. destruct ba. apply idpath.
Defined.

Definition algebra_iso_rearrange {X Y : FunctorAlg (pr2 H)}
  : (∑ f : X --> Y, is_iso (pr1 f)) ≃ algebra_eq_type X Y.
Proof.
  eapply weqcomp.
  - apply weqtotal2asstor.
  - simpl. unfold algebra_eq_type.
    apply invweq.
    eapply weqcomp.
    + apply weqtotal2asstor.
    + apply (weqbandf (idweq _ )).
      intro f; simpl.
      apply swapweq.
Defined.

Definition algebra_idtoiso (X Y : FunctorAlg (pr2 H)) :
  (X = Y) ≃ iso X Y.
Proof.
  eapply weqcomp.
  - apply algebra_ob_eq.
  - eapply weqcomp.
    + apply (invweq (algebra_iso_rearrange)).
    + apply (invweq algebra_iso_first_iso).
Defined.

Lemma isweq_idtoiso_FunctorAlg (X Y : FunctorAlg (pr2 H))
  : isweq (@idtoiso _ X Y).
Proof.
  apply (isweqhomot (algebra_idtoiso X Y)).
  - intro p. induction p.
    simpl. apply eq_iso. apply algebra_mor_eq.
    + apply (pr2 H).
    + apply idpath.
  - apply (pr2 _ ).
Defined.

Lemma is_univalent_FunctorAlg : is_univalent (FunctorAlg (pr2 H)).
Proof.
  split.
  - apply isweq_idtoiso_FunctorAlg.
  - intros a b.
    apply isaset_algebra_mor.
    apply (pr2 H).
Defined.

End FunctorAlg_saturated.

End Algebra_Definition.

Notation FunctorAlg := precategory_FunctorAlg.

(** ** Lambek's lemma: If (A,a) is an initial F-algebra then a is an iso *)

Section Lambeks_lemma.

Variables (C : precategory) (hsC : has_homsets C) (F : functor C C).
Variables (Aa : algebra_ob F) (AaIsInitial : isInitial (FunctorAlg F hsC) Aa).

Local Definition AaInitial : Initial (FunctorAlg F hsC) :=
  mk_Initial _ AaIsInitial.

Local Notation A := (alg_carrier _ Aa).
Local Notation a := (alg_map _ Aa).

(* (FA,Fa) is an F-algebra *)
Local Definition FAa : algebra_ob F := tpair (λ X, C ⟦F X,X⟧) (F A) (# F a).
Local Definition Fa' := InitialArrow AaInitial FAa.
Local Definition a' : C⟦A,F A⟧ := mor_from_algebra_mor _ _ _ Fa'.
Local Definition Ha' := algebra_mor_commutes _ _ _ Fa'.

Lemma initialAlg_is_iso_subproof : is_inverse_in_precat a a'.
Proof.
assert (Ha'a : a' · a = identity A).
  assert (algMor_a'a : is_algebra_mor _ _ _ (a' · a)).
    unfold is_algebra_mor, a'; rewrite functor_comp.
    eapply pathscomp0; [|eapply cancel_postcomposition; apply Ha'].
    now apply assoc.
  apply pathsinv0; set (X := tpair _ _ algMor_a'a).
  now apply (maponpaths pr1 (!@InitialEndo_is_identity _ AaInitial X)).
split; simpl; trivial.
eapply pathscomp0; [apply Ha'|]; simpl.
rewrite <- functor_comp.
eapply pathscomp0; [eapply maponpaths; apply Ha'a|].
now apply functor_id.
Qed.

Lemma initialAlg_is_iso : is_iso a.
Proof.
exact (is_iso_qinv _ a' initialAlg_is_iso_subproof).
Defined.

End Lambeks_lemma.


(** ** The natural numbers are intial for X ↦ 1 + X *)

(** This can be used as a definition of a natural numbers object (NNO) in
    any category with binary coproducts and a terminal object. We prove
    the universal property of NNOs below. *)

Section Nats.
  Context (C : precategory).
  Context (bc :  BinCoproducts C).
  Context (hsC :  has_homsets C).
  Context (T : Terminal C).

  Local Notation "1" := T.
  Local Notation "f + g" := (BinCoproductOfArrows _ _ _ f g).
  Local Notation "[ f , g ]" := (BinCoproductArrow _ _ f g).

  Let F : functor C C := BinCoproduct_of_functors _ _ bc
                                                  (constant_functor _ _ 1)
                                                  (functor_identity _).

  (** F on objects: X ↦ 1 + X *)
  Definition F_compute1 : ∏ c : C, F c = BinCoproductObject _ (bc 1 c) :=
    fun c => (idpath _).

  (** F on arrows: f ↦ [identity 1, f] *)
  Definition F_compute2 {x y : C} : ∏ f : x --> y, # F f = (identity 1) + f :=
    fun c => (idpath _).

  Definition nat_ob : UU := Initial (FunctorAlg F hsC).

  Definition nat_ob_carrier (N : nat_ob) : ob C :=
    alg_carrier _ (InitialObject N).
  Local Coercion nat_ob_carrier : nat_ob >-> ob.

  (** We have an arrow alg_map : (F N = 1 + N) --> N,
      so by the η-rule (UMP) for the coproduct, we can assume that it
      arises from a pair of maps [nat_ob_z,nat_ob_s] by composing with
      coproduct injections.

      <<
                  in1         in2
               1 ----> 1 + N <---- N
               |         |         |
      nat_ob_z |         | alg_map | nat_ob_s
               |         V         |
               +-------> N <-------+
      >>
   *)
  Definition nat_ob_z (N : nat_ob) : (1 --> N) :=
    BinCoproductIn1 C (bc 1 (alg_carrier F (pr1 N))) · (alg_map _ (pr1 N)).

  Definition nat_ob_s (N : nat_ob) : (N --> N) :=
    BinCoproductIn2 C (bc 1 (alg_carrier F (pr1 N))) · (alg_map _ (pr1 N)).

  Local Notation "0" := (nat_ob_z _).

  (** Use the universal property of the coproduct to make any object with a
      point and an endomorphism into an F-algebra *)
  Definition mk_F_alg {X : ob C} (f : 1 --> X) (g : X --> X) : ob (FunctorAlg F hsC).
  Proof.
    refine (X,, _).
    exact (BinCoproductArrow _ _ f g).
  Defined.

  (** Using mk_F_alg, X will be an F-algebra, and by initiality of N, there will
      be a unique morphism of F-algebras N --> X, which can be projected to a
      morphism in C. *)
  Definition nat_ob_rec (N : nat_ob) {X : ob C} :
    ∏ (f : 1 --> X) (g : X --> X), (N --> X) :=
    fun f g => mor_from_algebra_mor _ _ _ (InitialArrow N (mk_F_alg f g)).

  (** When calling the recursor on 0, you get the base case.
      Specifically,

        nat_ob_z · nat_ob_rec = f
   *)
  Lemma nat_ob_rec_z (N : nat_ob) {X : ob C} :
    ∏ (f : 1 --> X) (g : X --> X), nat_ob_z N · nat_ob_rec N f g = f.
  Proof.
    intros f g.

    pose (inlN := BinCoproductIn1 _ (bc 1 N)).
    pose (succ := nat_ob_s N).

    (** By initiality of N, there is a unique morphism making the following
        diagram commute:

        <<
               inlN         identity 1 + nat_ob_rec
            1 -----> 1 + N -------------------------> 1 + X
                       |                                |
             alg_map N |                                | alg_map X
                       V                                V
                       N   -------------------------->  X
                                   nat_ob_rec
        >>

        This proof uses somewhat idiosyncratic "forward reasoning", transforming
        the term "diagram" rather than the goal.
     *)
    pose
      (diagram :=
         maponpaths
           (fun x => inlN · x)
           (algebra_mor_commutes F (pr1 N) _ (InitialArrow N (mk_F_alg f g)))).
    rewrite (F_compute2 _) in diagram.

    (** Using the η-rules for coproducts, we can assume that alg_map X = [f,g]
        for f : 1 --> X, g : X --> X. *)
    rewrite (BinCoproductArrowEta C 1 X (bc _ _) _ _) in diagram.

    (** Using the β-rules for coproducts, we can simplify some of the terms *)
    (** (identity 1 + _) · [f, g] --β--> [identity 1 · f, _ · g] *)
    rewrite (precompWithBinCoproductArrow C (bc 1 N) (bc 1 X)
                                          (identity 1) _ _ _) in diagram.

    (** inl · [identity 1 · f, _ · g] --β--> identity 1 · f *)
    rewrite (BinCoproductIn1Commutes C 1 N (bc 1 _) _ _ _) in diagram.

    (** We can dispense with the identity *)
    rewrite (id_left _) in diagram.

    rewrite assoc in diagram.
    rewrite (BinCoproductArrowEta C 1 N (bc _ _) _ _) in diagram.

    refine (_ @ (BinCoproductIn1Commutes C _ _ (bc 1 _) _ f g)).
    rewrite (!BinCoproductIn1Commutes C _ _ (bc 1 _) _ 0 succ).
    unfold nat_ob_rec in *.
    exact diagram.
  Defined.

  Opaque nat_ob_rec_z.

  (** The succesor case:

        nat_ob_s · nat_ob_rec = nat_ob_rec · g

      The proof is very similar.
   *)
  Lemma nat_ob_rec_s (N : nat_ob) {X : ob C} :
    ∏ (f : 1 --> X) (g : X --> X),
    nat_ob_s N · nat_ob_rec N f g = nat_ob_rec N f g · g.
  Proof.
    intros f g.

    pose (inrN := BinCoproductIn2 _ (bc 1 N)).
    pose (succ := nat_ob_s N).

    (** By initiality of N, there is a unique morphism making the same diagram
        commute as above, but with "inrN" in place of "inlN". *)
    pose
      (diagram :=
         maponpaths
           (fun x => inrN · x)
           (algebra_mor_commutes F (pr1 N) _ (InitialArrow N (mk_F_alg f g)))).
    rewrite (F_compute2 _) in diagram.

    rewrite (BinCoproductArrowEta C 1 X (bc _ _) _ _) in diagram.

    (** Using the β-rules for coproducts, we can simplify some of the terms *)
    (** (identity 1 + _) · [f, g] --β--> [identity 1 · f, _ · g] *)
    rewrite (precompWithBinCoproductArrow C (bc 1 N) (bc 1 X)
                                          (identity 1) _ _ _) in diagram.

    (** inl · [identity 1 · f, _ · g] --β--> identity 1 · f *)
    rewrite (BinCoproductIn2Commutes C 1 N (bc 1 _) _ _ _) in diagram.

    rewrite assoc in diagram.
    rewrite (BinCoproductArrowEta C 1 N (bc _ _) _ _) in diagram.

    refine
      (_ @ maponpaths (fun x => nat_ob_rec N f g · x)
         (BinCoproductIn2Commutes C _ _ (bc 1 _) _ f g)).
    rewrite (!BinCoproductIn2Commutes C _ _ (bc 1 _) _ 0 (nat_ob_s N)).
    unfold nat_ob_rec in *.
    exact diagram.
  Defined.

  Opaque nat_ob_rec_s.

End Nats.
