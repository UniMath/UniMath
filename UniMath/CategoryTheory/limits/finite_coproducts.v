(** A direct definition of finite coproducts by using arbitrary coproducts *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.limits.arbitrary_coproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.

(** Definition of finite coproduct. *)
Section finite_coproduct_def.

  Variable C : precategory.

  Definition FinCoproducts :=
    forall (n : nat) (a : stn n -> C), ArbitraryCoproductCocone (stn n) C a.
  Definition hasFinCoproducts := ishinh FinCoproducts.

End finite_coproduct_def.

(** In the following section we prove that initial object and coproducts imply
  finite coproducts. *)
Section finite_coproduct_criteria.
  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (* Couldn't find the following elsewhere. *)
  Definition unit_to_ob (c : C) : unit -> C := fun tt : unit => c.

  (** This results is used in the induction step of the proof of the criteria.
    It says that for any object of C we can construct an arbitrary coproduct of
    1 object from it. *)
  Lemma identity_to_arbitrary_coproduct (c : C) :
    ArbitraryCoproductCocone unit C (unit_to_ob c).
  Proof.
    refine (mk_ArbitraryCoproductCocone _ _ _ c (fun tt : unit => identity _) _).
    refine (mk_isArbitraryCoproductCocone _ _ hs _ _ _ _).
    intros c0 g.

    use (subtypeEquality'' (g tt)); simpl.
    intros i. apply remove_id_left. apply idpath.
    apply maponpaths, isconnectedunit.

    (* Equality of equalities of morphisms *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness *)
    intros y X. rewrite <- (X tt). apply pathsinv0.
    apply remove_id_left; apply idpath.
  Defined.

  (** In this Theorem we prove that finite coproducts can be constructed from
    initial and coproducts. The result is proved by induction on the number of
    objects in the finite coproduct. *)
  Theorem fin_coproduct_from_initial_and_coproducts :
    Initial C -> Coproducts C -> FinCoproducts C.
  Proof.
    intros I Coprods. unfold FinCoproducts. intros n. induction n.

    (* Case n = 0 follows from the fact that empty coproduct can be
       constructed from initial. *)
    rewrite (UnivalenceAxiom.weqtopaths (weqstn0toempty)).
    set (e := iscontrfunfromempty C).
    intros a; assert (H : a = fromempty).
    apply (@pathscomp0  _ _ (pr1 e) _).
    apply ((pr2 e) a). apply pathsinv0. apply ((pr2 e) fromempty).
    rewrite H.
    apply (empty_coproduct_from_initial _ hs I).

    (* The general case uses the result that from two arbitrary coproducts,
       such that the coproduct of these exists, we can construct a new
       arbitrary coproduct. *)
    rewrite <- (UnivalenceAxiom.weqtopaths (weqdnicoprod _ (lastelement n))).
    intros a.

    (* Some useful terms *)
    set (A1Cocone := IHn (a ∘ (@ii1 (stn n) unit))).
    set (A2Cocone := identity_to_arbitrary_coproduct (a(ii2 tt))).
    set (CoprodCocone := Coprods (ArbitraryCoproductObject (stn n) C A1Cocone)
                       (ArbitraryCoproductObject unit C A2Cocone)).
    set (ACocone := arbitrary_coproduct_from_arbitrary_coproducts
                    _ hs (stn n) unit _ _ A1Cocone A2Cocone CoprodCocone).

    (* We show that the goal follows from ACocone by showing that the associated
       families of objects are homotopic, hence equal by Univalence. *)
    assert (H : homot a (sumofmaps (a ∘ ii1 (B:=unit))
                                   (unit_to_ob (a (ii2 tt))))).
    intros i. induction i. apply idpath.
    unfold sumofmaps, unit_to_ob, coprod_rect.
    apply maponpaths, maponpaths. apply isconnectedunit.
    unfold homot in H. apply UnivalenceAxiom.funextfun in H.
    rewrite <- H in ACocone.
    exact ACocone.
  Defined.

End finite_coproduct_criteria.