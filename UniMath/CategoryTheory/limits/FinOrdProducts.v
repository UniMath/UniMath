(** A direct definition of finite ordered products by using products *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.

(** Definition of finite ordered products. *)
Section def_FinOrdProducts.

  Variable C : precategory.

  Definition FinOrdProducts : UU :=
    ∏ (n : nat) (a : stn n -> C), Product (stn n) C a.
  Definition hasFinOrdProducts : UU :=
    ∏ (n : nat) (a : stn n -> C), ∥ Product (stn n) C a ∥.

End def_FinOrdProducts.


(** Construction of FinOrdProducts from Terminal and BinProducts. *)
Section FinOrdProduct_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Case n = 0 of the theorem. *)
  Lemma TerminalToProduct (T : Terminal C):
    ∏ (a : stn 0 -> C), Product (stn 0) C a.
  Proof.
    intros a.
    use (mk_Product _ _ _ T
                        (λ i : stn 0, fromempty (weqstn0toempty i))).
    use (mk_isProduct _ _ hs).
    intros c g. use unique_exists.

    apply (TerminalArrow _ c).
    intros i. apply (fromempty (weqstn0toempty i)).
    intros y. apply impred_isaprop. intros t. apply hs.
    intros y X. apply TerminalArrowEq.
  Defined.

  (** Case n = 1 of the theorem. *)
  Lemma identity_to_product:
    ∏ (a : stn 1 -> C), Product (stn 1) C a.
  Proof.
    intros a.
    set (stn1ob := invweq(weqstn1tounit) tt).

    use (mk_Product _ _ _ (a stn1ob)).
    intros i. exact (idtoiso ((maponpaths a (isconnectedstn1 stn1ob i)))).

    use (mk_isProduct _ _ hs).
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
    set (cone1 := IHn a1).
    set (a2 := (λ _ : stn 1, a lastelement)).
    set (cone2 := identity_to_product a2). (* Case n = 1 *)
    set (cone1Pr := ProductPr _ _ cone1).
    set (cone2Pr := ProductPr _ _ cone2).
    set (Bin := BinProds (ProductObject (stn n) C cone1)
                             (ProductObject (stn 1) C cone2)).
    set (p1 := BinProductPr1 _ Bin).
    set (p2 := BinProductPr2 _ Bin).
    set (m1 := λ i1 : stn n, p1 · (cone1Pr i1)).
    set (m2 := λ i2 : stn 1, p2 · (cone2Pr i2)).
    set (BinOb := BinProductObject _ Bin).
    fold BinOb in p1, p2, m1, m2.

    use (mk_Product (stn (S n)) C a BinOb _).

    (* Construction of the arrows from a i to BinOb *)
    intros i. induction (natlehchoice4 (pr1 i) _ (pr2 i)) as [a0|b].
    exact (m1 (stnpair n (pr1 i) a0) ·
              idtoiso (! maponpaths a (dni_lastelement_eq n i a0))).
    exact (m2 (invweq(weqstn1tounit) tt) ·
              idtoiso (! maponpaths a (lastelement_eq n i b))).

    (* Construction of isProduct. *)
    use (mk_isProduct _ _ hs).
    intros c g.

    set (g1 := λ i : stn n, g(dni_lastelement i)).
    set (ar1 := ProductArrow _ _ cone1 g1). fold ar1.
    set (com1 := BinProductPr1Commutes  _ _ _ Bin c ar1 (g lastelement)).
    set (com2 := BinProductPr2Commutes _ _ _ Bin c ar1 (g lastelement)).
    set (com3 := ProductPrCommutes _ _ _ cone1 _ g1).
    set (com4 := ProductPrCommutes _ _ _ cone2 _
                                   (λ _ : stn 1, g lastelement)).

    use (unique_exists).

    (* Construction of the unique arrow from Ob to c. *)
    use (BinProductArrow _ Bin).
    use (ProductArrow _ _ cone1). intros i. exact (g (dni_lastelement i)).
    use (ProductArrow _ _ cone2). intros i. exact (g lastelement).

    (* First commutativity. *)
    intros i. unfold coprod_rect. induction (natlehchoice4 (pr1 i) n (pr2 i)) as [a0|b].
    rewrite (dni_lastelement_eq n i a0). repeat rewrite assoc.
    apply remove_id_right. apply idpath.

    unfold m1. unfold p1. rewrite assoc. fold g1. fold ar1.
    use (pathscomp0 (maponpaths (λ f : _, f · cone1Pr (stnpair n (pr1 i) a0))
                                com1)).
    fold ar1 in com3. rewrite com3. unfold g1. apply idpath.


    (* Second commutativity. *)
    rewrite (lastelement_eq n i b). repeat rewrite assoc.
    apply remove_id_right. apply idpath.

    unfold m2. unfold p2. rewrite assoc. fold g1. fold ar1.
    use (pathscomp0 (maponpaths (λ f : _, f · cone2Pr lastelement) com2)).
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
    unfold cone1Pr. apply pathsinv0.

    set (e := dni_lastelement_is_inj (dni_lastelement_eq n (dni_lastelement i)
                                                         a0)).
    use (pathscomp0 _ (ProductPr_idtoiso (stn n) C (a ∘ dni_lastelement)%functions cone1
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
    apply cancel_precomposition. unfold cone2Pr.

    set (e := isconnectedstn1 i (invweq(weqstn1tounit) tt)).
    use (pathscomp0 _ (ProductPr_idtoiso (stn 1) C (λ _ : _, a lastelement)
                                         cone2 (!e))).
    rewrite maponpathsinv0.
    apply cancel_precomposition.
    apply maponpaths. apply maponpaths. (* Why we need maponpaths twice? *)
    apply maponpaths.
    fold (@funcomp (stn 1) _ _ (λ _ : stn 1, lastelement) a).
    rewrite <- (maponpathscomp (λ _ : stn 1, lastelement) a).
    apply maponpaths. apply isasetstn.
  Defined.

End FinOrdProduct_criteria.
