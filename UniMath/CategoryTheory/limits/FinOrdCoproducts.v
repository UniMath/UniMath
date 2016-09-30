(** A direct definition of finite ordered coproducts by using coproducts *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.


(** Definition of finite ordered coproducts. *)
Section def_FinOrdCoproducts.

  Variable C : precategory.

  Definition FinOrdCoproducts : UU :=
    Π (n : nat) (a : stn n -> C), CoproductCocone (stn n) C a.
  Definition hasFinOrdCoproducts := ishinh FinOrdCoproducts.

End def_FinOrdCoproducts.


(** Construction of FinOrdCoproducts from Initial and BinCoproducts. *)
Section FinOrdCoproduct_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Case n = 0 of the theorem. *)
  Lemma InitialToCoproduct (I : Initial C):
    Π (a : stn 0 -> C), CoproductCocone (stn 0) C a.
  Proof.
    intros a.
    use (mk_CoproductCocone _ _ _ I
                            (fun i : stn 0 => fromempty (weqstn0toempty i))).
    use (mk_isCoproductCocone _ _ hs).
    intros c g. use unique_exists.

    apply (InitialArrow I c).
    intros i. apply (fromempty (weqstn0toempty i)).
    intros y. apply impred_isaprop. intros t. apply hs.
    intros y X. apply InitialArrowUnique.
  Defined.

  (** Case n = 1 of the theorem. *)
  Lemma ObjectToCoproduct:
    Π (a : stn 1 -> C), CoproductCocone (stn 1) C a.
  Proof.
    intros a.
    set (stn1ob := invweq(weqstn1tounit) tt).
    use (mk_CoproductCocone _ _ _ (a stn1ob)).
    intros i. exact (idtoiso (! (maponpaths a (isconnectedstn1 stn1ob i)))).

    (* isCoproductcocone *)
    use (mk_isCoproductCocone _ _ hs).
    intros c g.
    use (unique_exists (g stn1ob)).

    (* Commutativity. *)
    intros i. rewrite <- (isconnectedstn1 stn1ob i). apply id_left.

    (* Equality of equalities of morphisms. *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness. *)
    intros y X. rewrite <- (X stn1ob). apply pathsinv0. apply id_left.
  Defined.

  (** Finite ordered coproducts from initial and binary coproducts. *)
  Theorem FinOrdCoproducts_from_Initial_and_BinCoproducts :
    Initial C -> BinCoproducts C -> FinOrdCoproducts C.
  Proof.
    intros I BinCoprods. unfold FinOrdCoproducts. intros n. induction n as [|n IHn].

    (* Case n = 0 *)
    apply (InitialToCoproduct I).

    (* General case. *)
    intros a.
    set (a1 := fun (i : stn n) => a (dni_lastelement i)).
    set (Cone1 := IHn a1).
    set (a2 := (fun _ : stn 1 => a (lastelement n))).
    set (Cone2 := ObjectToCoproduct a2). (* Case n = 1 *)
    set (Cone1In := CoproductIn _ _ Cone1).
    set (Cone2In := CoproductIn _ _ Cone2).
    set (BinCone := BinCoprods (CoproductObject (stn n) C Cone1)
                               (CoproductObject (stn 1) C Cone2)).
    set (in1 := BinCoproductIn1 _ BinCone).
    set (in2 := BinCoproductIn2 _ BinCone).
    set (m1 := fun i1 : stn n => (Cone1In i1) ;; in1).
    set (m2 := fun i2 : stn 1 => (Cone2In i2) ;; in2).

    use (mk_CoproductCocone (stn (S n)) C a (BinCoproductObject _ BinCone) _).

    (* Construction of the arrows from a i to BinCone *)
    intros i. induction (natlehchoice4 (pr1 i) _ (pr2 i)) as [a0|b].
    exact (idtoiso (maponpaths a (dni_lastelement_eq n i a0))
                   ;; m1 (stnpair n (pr1 i) a0)).
    exact (idtoiso (maponpaths a (lastelement_eq n i b))
                   ;;  m2 (invweq(weqstn1tounit) tt)).

    (* Construction of isCoproductCocone. *)
    use (mk_isCoproductCocone _ _ hs).

    intros c g.
    set (g1 := fun i : stn n => g(dni_lastelement i)).
    set (ar1 := CoproductArrow _ _ Cone1 g1).
    set (com1 := BinCoproductIn1Commutes  _ _ _ BinCone c ar1
                                          (g(lastelement n))).
    set (com2 := BinCoproductIn2Commutes _ _ _ BinCone c ar1
                                         (g(lastelement n))).
    set (com3 := CoproductInCommutes _ _ _ Cone1 _ g1).
    set (com4 := CoproductInCommutes _ _ _ Cone2 _
                                     (fun _ : stn 1 => g(lastelement n))).

    use (unique_exists).

    (* Construction of the unique arrow from BinCone to c. *)
    use (BinCoproductArrow _ BinCone).
    use (CoproductArrow _ _ Cone1). intros i. exact (g (dni_lastelement i)).
    use (CoproductArrow _ _ Cone2). intros i. exact (g (lastelement n)).

    (* First commutativity. *)
    intros i. unfold coprod_rect. induction (natlehchoice4 (pr1 i) n (pr2 i)) as [a0|b].
    rewrite (dni_lastelement_eq n i a0). repeat rewrite <- assoc.
    apply remove_id_left. apply idpath.

    unfold m1. unfold in1. rewrite <- assoc. fold g1. fold ar1.
    use (pathscomp0 (maponpaths (fun f : _ => Cone1In (stnpair n (pr1 i) a0) ;; f)
                                com1)).
    fold ar1 in com3. rewrite com3. unfold g1. apply idpath.


    (* Second commutativity. *)
    rewrite (lastelement_eq n i b). repeat rewrite <- assoc.
    apply remove_id_left. apply idpath.

    unfold m2. unfold in2. rewrite <- assoc. fold g1. fold ar1.
    use (pathscomp0 (maponpaths (fun f : _ => Cone2In (lastelement 0) ;; f) com2)).
    rewrite com4. apply idpath.


    (* Equality on equalities of morphisms. *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness *)
    unfold coprod_rect. intros k X.
    apply BinCoproductArrowUnique.


    (* From stn n *)
    apply CoproductArrowUnique.
    intros i. rewrite <- (X (dni_lastelement i)). rewrite assoc.
    apply cancel_postcomposition.
    induction (natlehchoice4 (pr1 (dni_lastelement i)) n
                             (pr2 (dni_lastelement i))) as [a0|b].
    unfold m1. rewrite assoc. unfold in1.
    apply cancel_postcomposition.
    unfold Cone1In. apply pathsinv0.

    set (e := dni_lastelement_is_inj (dni_lastelement_eq n (dni_lastelement i)
                                                         a0)).
    use (pathscomp0 _ (CoproductIn_idtoiso (stn n) C (a ∘ dni_lastelement) Cone1
                                           e)).
    apply cancel_postcomposition.
    apply maponpaths. apply maponpaths. (* Why we need maponpaths twice? *)
    rewrite <- (maponpathscomp _ a).
    apply maponpaths. apply isasetstn.

    (* This is false because of b *)
    apply fromempty. induction i as [i i'].
    cbn in b. induction (!b).
    apply (isirreflnatlth _ i').


    (* From stn 1 *)
    apply CoproductArrowUnique.
    intros i. rewrite <- (X (lastelement n)). rewrite assoc.
    apply cancel_postcomposition.
    induction (natlehchoice4 (pr1 (lastelement n)) n (pr2 (lastelement n))) as [a0|b].

    (* This case is false because of a0 *)
    apply fromempty. cbn in a0. apply (isirreflnatlth _ a0).

    apply pathsinv0. unfold m2. rewrite assoc. unfold in2.
    apply cancel_postcomposition. unfold Cone2In.

    (* This case makes sense *)
    set (e := isconnectedstn1 i (invweq(weqstn1tounit) tt)).
    use (pathscomp0 _ (CoproductIn_idtoiso (stn 1) C
                                           (fun _ : _ => a(lastelement n))
                                           Cone2 e)).
    apply cancel_postcomposition.
    apply maponpaths. apply maponpaths. (* Why we need maponpaths twice? *)
    fold (@funcomp (stn 1) _ _ (fun _ : stn 1 => lastelement n) a).
    rewrite <- (maponpathscomp (fun _ : stn 1 => lastelement n) a).
    apply maponpaths. apply isasetstn.
  Defined.
End FinOrdCoproduct_criteria.
