(** A direct definition of finite products by using arbitrary products *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.limits.arbitrary_products.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.

(** Definition of finite coproduct. *)
Section finite_product_def.

  Variable C : precategory.

  Definition FinProducts :=
    forall (n : nat) (a : stn n -> C), ArbitraryProductCone (stn n) C a.
  Definition hasFinProducts := ishinh FinProducts.

End finite_product_def.

(** In the following section we prove that initial object and products imply
  finite products. *)
Section finite_product_criteria.
  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (* Couldn't find the following elsewhere. *)
  Definition unit_to_ob (c : C) : unit -> C := fun tt : unit => c.

  (** This result is used in the induction step of the proof of the criteria. It
    says that for any object of C we can construct an arbitrary product of
    1 object from it. *)
  Lemma identity_to_arbitrary_product (c : C) :
    ArbitraryProductCone unit C (unit_to_ob c).
  Proof.
    refine (mk_ArbitraryProductCone _ _ _ c (fun tt : unit => identity _) _).
    refine (mk_isArbitraryProductCone _ _ hs _ _ _ _).
    intros c0 g.

    use (subtypeEquality'' (g tt)); simpl.
    intros i. apply remove_id_right. apply idpath.
    apply maponpaths, isconnectedunit.

    (* Equality on equalities of morphisms *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness *)
    intros y X. rewrite <- (X tt). apply pathsinv0.
    apply remove_id_right; apply idpath.
  Defined.

  (** In this Theorem we prove that finite products can be constructed from
    initial and products. The result is proved by induction on the number of
    objects in the finite product. *)
  Theorem fin_product_from_terminal_and_products :
    Terminal C -> Products C -> FinProducts C.
  Proof.
    intros I Prods. unfold FinProducts. intros n. induction n.

    (* Case n = 0 follows from the fact that empty product can be
       constructed from terminal. *)
    rewrite (UnivalenceAxiom.weqtopaths (weqstn0toempty)).
    set (e := iscontrfunfromempty C).
    intros a; assert (H : a = fromempty).
    apply (@pathscomp0  _ _ (pr1 e) _).
    apply ((pr2 e) a). apply pathsinv0. apply ((pr2 e) fromempty).
    rewrite H.
    apply (empty_product_from_terminal _ hs I).

    (* The general case uses the result that from two arbitrary products,
       such that the product of these exists, we can construct a new
       arbitrary product. *)
    rewrite <- (UnivalenceAxiom.weqtopaths (weqdnicoprod _ (lastelement n))).
    intros a.

    (* Some useful terms *)
    set (A1Cone := IHn (a ∘ (@ii1 (stn n) unit))).
    set (A2Cone := identity_to_arbitrary_product (a(ii2 tt))).
    set (ProdCone := Prods (ArbitraryProductObject (stn n) C A1Cone)
                       (ArbitraryProductObject unit C A2Cone)).
    set (ACone := arbitrary_product_from_arbitrary_products
                    _ hs (stn n) unit _ _ A1Cone A2Cone ProdCone).

    (* We show that the goal follows from ACone by showing that the associated
       families of objects are homotopic, hence equal by Univalence. *)
    assert (H : homot a (sumofmaps (a ∘ ii1 (B:=unit))
                                   (unit_to_ob (a (ii2 tt))))).
    intros i. induction i. apply idpath.
    unfold sumofmaps, unit_to_ob, coprod_rect.
    apply maponpaths, maponpaths. apply isconnectedunit.
    unfold homot in H. apply UnivalenceAxiom.funextfun in H.
    rewrite <- H in ACone.
    exact ACone.
  Defined.

End finite_product_criteria.