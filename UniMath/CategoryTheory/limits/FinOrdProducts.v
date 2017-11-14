(** A direct definition of finite ordered products by using products *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.ProductCategory.

Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.


(** Definition of finite ordered products. *)
Section def_FinOrdProducts.

  Variable C : precategory.

  Definition FinOrdProducts : UU :=
    ∏ (n : nat) (a : stn n -> C), ProductCone (stn n) C a.
  Definition hasFinOrdProducts := ishinh FinOrdProducts.

End def_FinOrdProducts.


(** Construction of FinOrdProducts from Terminal and BinProducts. *)
Section FinOrdProduct_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Case n = 0 of the theorem. *)
  Lemma TerminalToProduct (T : Terminal C):
    ∏ (a : stn 0 -> C), ProductCone (stn 0) C a.
  Proof.
    intros a.
    use (mk_ProductCone _ _ _ T
                        (λ i : stn 0, fromempty (weqstn0toempty i))).
    use (mk_isProductCone _ _ hs).
    intros c g. use unique_exists.

    apply (TerminalArrow c).
    intros i. apply (fromempty (weqstn0toempty i)).
    intros y. apply impred_isaprop. intros t. apply hs.
    intros y X. apply ArrowsToTerminal.
  Defined.

  (** Case n = 1 of the theorem. *)
  Lemma identity_to_product:
    ∏ (a : stn 1 -> C), ProductCone (stn 1) C a.
  Proof.
    intros a.
    set (stn1ob := invweq(weqstn1tounit) tt).

    use (mk_ProductCone _ _ _ (a stn1ob)).
    intros i. exact (idtoiso ((maponpaths a (isconnectedstn1 stn1ob i)))).

    use (mk_isProductCone _ _ hs).
    intros c g.
    use (unique_exists).
    exact (g stn1ob).

    (* Commutativity. *)
    intros i. rewrite <- (isconnectedstn1 stn1ob i). apply id_right.

    (* Equality of equalities of morphisms. *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness. *)
    intros y X. rewrite <- (X stn1ob). apply pathsinv0. apply id_right.
  Defined.

  (** Finite ordered products from terminal and binary products *)
  Theorem FinOrdProducts_from_Terminal_and_BinProducts :
    Terminal C -> BinProducts C -> FinOrdProducts C.
  Proof.
    intros T BinProds. unfold FinOrdProducts. intros n. induction n as [|n IHn].

    (* Case n = 0 *)
    apply (TerminalToProduct T).

    (* General case. *)
    intros a.
    set (a1 := λ (i : stn n), a (dni_lastelement i)).
    set (Cone1 := IHn a1).
    set (a2 := (λ _ : stn 1, a lastelement)).
    set (Cone2 := identity_to_product a2). (* Case n = 1 *)
    set (Cone1Pr := ProductPr _ _ Cone1).
    set (Cone2Pr := ProductPr _ _ Cone2).
    set (BinCone := BinProds (ProductObject (stn n) C Cone1)
                             (ProductObject (stn 1) C Cone2)).
    set (p1 := BinProductPr1 _ BinCone).
    set (p2 := BinProductPr2 _ BinCone).
    set (m1 := λ i1 : stn n, p1 · (Cone1Pr i1)).
    set (m2 := λ i2 : stn 1, p2 · (Cone2Pr i2)).
    set (BinConeOb := BinProductObject _ BinCone).
    fold BinConeOb in p1, p2, m1, m2.

    use (mk_ProductCone (stn (S n)) C a BinConeOb _).

    (* Construction of the arrows from a i to BinConeOb *)
    intros i. induction (natlehchoice4 (pr1 i) _ (pr2 i)) as [a0|b].
    exact (m1 (stnpair n (pr1 i) a0) ·
              idtoiso (! maponpaths a (dni_lastelement_eq n i a0))).
    exact (m2 (invweq(weqstn1tounit) tt) ·
              idtoiso (! maponpaths a (lastelement_eq n i b))).

    (* Construction of isProductCone. *)
    use (mk_isProductCone _ _ hs).
    intros c g.

    set (g1 := λ i : stn n, g(dni_lastelement i)).
    set (ar1 := ProductArrow _ _ Cone1 g1). fold ar1.
    set (com1 := BinProductPr1Commutes  _ _ _ BinCone c ar1 (g lastelement)).
    set (com2 := BinProductPr2Commutes _ _ _ BinCone c ar1 (g lastelement)).
    set (com3 := ProductPrCommutes _ _ _ Cone1 _ g1).
    set (com4 := ProductPrCommutes _ _ _ Cone2 _
                                   (λ _ : stn 1, g lastelement)).

    use (unique_exists).

    (* Construction of the unique arrow from ConeOb to c. *)
    use (BinProductArrow _ BinCone).
    use (ProductArrow _ _ Cone1). intros i. exact (g (dni_lastelement i)).
    use (ProductArrow _ _ Cone2). intros i. exact (g lastelement).

    (* First commutativity. *)
    intros i. unfold coprod_rect. induction (natlehchoice4 (pr1 i) n (pr2 i)) as [a0|b].
    rewrite (dni_lastelement_eq n i a0). repeat rewrite assoc.
    apply remove_id_right. apply idpath.

    unfold m1. unfold p1. rewrite assoc. fold g1. fold ar1.
    use (pathscomp0 (maponpaths (λ f : _, f · Cone1Pr (stnpair n (pr1 i) a0))
                                com1)).
    fold ar1 in com3. rewrite com3. unfold g1. apply idpath.


    (* Second commutativity. *)
    rewrite (lastelement_eq n i b). repeat rewrite assoc.
    apply remove_id_right. apply idpath.

    unfold m2. unfold p2. rewrite assoc. fold g1. fold ar1.
    use (pathscomp0 (maponpaths (λ f : _, f · Cone2Pr lastelement) com2)).
    rewrite com4. apply idpath.


    (* Equality on equalities of morphisms. *)
    intros y. apply impred_isaprop. intros t. apply hs.

    (* Uniqueness *)
    unfold coprod_rect. intros k X.
    apply BinProductArrowUnique.


    (* From stn n *)
    apply ProductArrowUnique.
    intros i. rewrite <- (X (dni_lastelement i)). rewrite <- assoc.
    apply cancel_precomposition.
    induction (natlehchoice4 (pr1 (dni_lastelement i)) n
                             (pr2 (dni_lastelement i))) as [a0|b].
    unfold m1. rewrite <- assoc. unfold p1.
    apply cancel_precomposition.
    unfold Cone1Pr. apply pathsinv0.

    set (e := dni_lastelement_is_inj (dni_lastelement_eq n (dni_lastelement i)
                                                         a0)).
    use (pathscomp0 _ (ProductPr_idtoiso (stn n) C (a ∘ dni_lastelement)%functions Cone1
                                         (!e))).
    rewrite maponpathsinv0.
    apply cancel_precomposition.
    apply maponpaths. apply maponpaths. (* Why we need maponpaths twice? *)
    apply maponpaths.
    rewrite <- (maponpathscomp _ a).
    apply maponpaths. apply isasetstn.

    (* This is false because of b *)
    apply fromempty. induction i as [i i'].
    cbn in b. induction (!b).
    apply (isirreflnatlth _ i').


    (* From stn 1 *)
    apply ProductArrowUnique.
    intros i. rewrite <- (X lastelement).  rewrite <- assoc.
    apply cancel_precomposition.
    induction (natlehchoice4 (pr1 lastelement) n (pr2 lastelement)) as [a0|b].

    (* This case is false because of a0 *)
    apply fromempty. cbn in a0. apply (isirreflnatlth _ a0).

    (* This case makes sense *)
    apply pathsinv0. unfold m2. rewrite <- assoc. unfold p2.
    apply cancel_precomposition. unfold Cone2Pr.

    set (e := isconnectedstn1 i (invweq(weqstn1tounit) tt)).
    use (pathscomp0 _ (ProductPr_idtoiso (stn 1) C (λ _ : _, a lastelement)
                                         Cone2 (!e))).
    rewrite maponpathsinv0.
    apply cancel_precomposition.
    apply maponpaths. apply maponpaths. (* Why we need maponpaths twice? *)
    apply maponpaths.
    fold (@funcomp (stn 1) _ _ (λ _ : stn 1, lastelement) a).
    rewrite <- (maponpathscomp (λ _ : stn 1, lastelement) a).
    apply maponpaths. apply isasetstn.
  Defined.
End FinOrdProduct_criteria.
