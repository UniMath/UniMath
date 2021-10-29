(** * Direct definition of binary direct sum using preadditive categories. *)
(** ** Contents
- Definition of binary direct sums (also known as biproducts)
- Criteria for binary direct sums
- Quotient has binary direct sums
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Monoids.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Local Open Scope cat.

(** BinDirectSum is at the same time product and coproduct of the underlying objects together
    with the following equalities

    i1 · p1 = identity  and   i2 · p2 = identity
    i1 · p2 = unit      and   i2 · p1 = unit
            p1 · i1 + p2 · i2 = identity
*)

Lemma rewrite_op {A:PreAdditive} (x y:A) :
  @to_binop (categoryWithAbgrops_precategoryWithBinOps (PreAdditive_categoryWithAbgrops A)) x y
  =
  @op (pr1monoid (grtomonoid (abgrtogr (@to_abgr (PreAdditive_categoryWithAbgrops A) x y)))).
Proof.
  reflexivity.
Defined.

Section def_bindirectsums.

  Variable A : PreAdditive.
  Context (hs := @to_has_homsets A : has_homsets A).

  Open Scope abgrcat.

  (** Definition of binary direct sum. *)
  Definition isBinDirectSum (a b co : A) (i1 : a --> co) (i2 : b --> co)
             (p1 : co --> a) (p2 : co --> b) : hProp :=
    i1 · p1 = 1  ∧  i2 · p2 = 1  ∧
    i1 · p2 = 0  ∧  i2 · p1 = 0  ∧
    p1 · i1 + p2 · i2 = 1.

  Definition to_isBinCoproduct {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b} :
    isBinDirectSum a b co i1 i2 p1 p2 -> isBinCoproduct A a b co i1 i2.
  Proof.
    intros [e11 [e22 [e12 [e21 e]]]].
    intros T f g.
    use unique_exists.
    - exact ((p1 · f) + (p2 · g)).
    - cbn beta. split.
      + (* This is clumsy: should rewrite PreAdditive.v ! *)
        assert (q := to_premor_linear' i1 (p1 · f) (p2 · g)).
        rewrite 2 rewrite_op in q. rewrite q. clear q.
        rewrite 2 assoc. rewrite e11. rewrite id_left.
        rewrite e12. rewrite to_postmor_unel'. rewrite runax.
        reflexivity.
      + assert (q := to_premor_linear' i2 (p1 · f) (p2 · g)).
        rewrite 2 rewrite_op in q. rewrite q. clear q.
        rewrite 2 assoc. rewrite e22. rewrite id_left.
        rewrite e21. rewrite to_postmor_unel'. rewrite lunax.
        reflexivity.
    - intros h. cbn beta. apply isapropdirprod;apply hs.
    - intros h. cbn beta. intros [p q]. rewrite <- p, <- q.
      rewrite 2 assoc.
      assert (Q := to_postmor_linear' (p1 · i1) (p2 · i2) h).
      rewrite 2 rewrite_op in Q. rewrite <- Q.
      rewrite e. rewrite id_left. reflexivity.
  Defined.

  Definition to_isBinProduct {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b} :
    isBinDirectSum a b co i1 i2 p1 p2 -> isBinProduct A a b co p1 p2.
  Proof.
    intros [e11 [e22 [e12 [e21 e]]]].
    intros T f g.
    use unique_exists.
    - exact ((f · i1) + (g · i2)).
    - cbn beta. split.
      + assert (q := to_postmor_linear' (f · i1) (g · i2) p1).
        rewrite 2 rewrite_op in q. rewrite q. clear q.
        rewrite <- 2 assoc. rewrite e11. rewrite id_right.
        rewrite e21. rewrite to_premor_unel'. rewrite runax.
        reflexivity.
      + assert (q := to_postmor_linear' (f · i1) (g · i2) p2).
        rewrite 2 rewrite_op in q. rewrite q. clear q.
        rewrite <- 2 assoc. rewrite e22. rewrite id_right.
        rewrite e12. rewrite to_premor_unel'. rewrite lunax.
        reflexivity.
    - intros h. cbn beta. apply isapropdirprod;apply hs.
    - intros h. cbn beta. intros [p q]. rewrite <- p, <- q.
      rewrite <- 2 assoc.
      assert (Q := to_premor_linear' h (p1 · i1) (p2 · i2)).
      rewrite 2 rewrite_op in Q. rewrite <- Q.
      rewrite e. rewrite id_right. reflexivity.
  Defined.

  Definition to_IdIn1 {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSum a b co i1 i2 p1 p2) :
    i1 · p1 = identity a := pr1 B.

  Definition to_IdIn2 {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSum a b co i1 i2 p1 p2) :
    i2 · p2 = identity b := pr12 B.

  Definition to_Unel1 {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSum a b co i1 i2 p1 p2) :
    i1 · p2 = (to_unel a b) := pr122 B.

  Definition to_Unel2 {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSum a b co i1 i2 p1 p2) :
    i2 · p1 = (to_unel b a) := pr122 (pr2 B).

  Definition to_BinOpId {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSum a b co i1 i2 p1 p2) :
    (to_binop co co) (p1 · i1) (p2 · i2) = identity co := pr222 (pr2 B).

  (** The following definition constructs isBinDirectSum from data. *)
  Definition make_isBinDirectSum (a b co : A)
             (i1 : a --> co) (i2 : b --> co) (p1 : co --> a) (p2 : co --> b)
             (H1 : i1 · p1 = identity a) (H2 : i2 · p2 = identity b)
             (H3 : i1 · p2 = (to_unel a b)) (H4 : i2 · p1 = (to_unel b a))
             (H5 : (to_binop co co) (p1 · i1) (p2 · i2) = identity co)
    : isBinDirectSum a b co i1 i2 p1 p2 := H1,,H2,,H3,,H4,,H5.

  (** Definition of BinDirectSums. *)
  Definition BinDirectSum (a b : A) : UU :=
    ∑ coab : (∑ co : A, a --> co × b --> co × co --> a × co --> b),
             isBinDirectSum a b (pr1 coab) (pr1 (pr2 coab)) (pr1 (pr2 (pr2 coab)))
                                (pr1 (pr2 (pr2 (pr2 coab)))) (pr2 (pr2 (pr2 (pr2 coab)))).

  (** Construction of BinDirectSum. *)
  Definition make_BinDirectSum (a b co : A) (i1 : a --> co) (i2 : b --> co)
             (p1 : co --> a) (p2 : co --> b) (H :  isBinDirectSum a b co i1 i2 p1 p2) :
    BinDirectSum a b := tpair _ (tpair _ co (i1,,(i2,,(p1,,p2)))) H.

  (** BinDirectSum in categories. *)
  Definition BinDirectSums : UU := ∏ (a b : A), BinDirectSum a b.

  Definition make_BinDirectSums (H : ∏ (a b : A), BinDirectSum a b) : BinDirectSums := H.

  Definition hasBinDirectSums : hProp.
  Proof.
    exists (∏ (a b : A), ∥ BinDirectSum a b ∥).
    apply impred; intro p.
    apply impred; intro q.
    apply isapropishinh.
  Defined.

  (** The direct sum object. *)
  Definition BinDirectSumOb {a b : A} (B : BinDirectSum a b) : A := pr1 (pr1 B).
  Coercion BinDirectSumOb : BinDirectSum >-> ob.

  (** Accessor functions *)
  Definition to_In1 {a b : A} (B : BinDirectSum a b) : A⟦a, B⟧ := dirprod_pr1 (pr2 (pr1 B)).

  Definition to_In2 {a b : A} (B : BinDirectSum a b) : A⟦b, B⟧ :=
    dirprod_pr1 (dirprod_pr2 (pr2 (pr1 B))).

  Definition to_Pr1 {a b : A} (B : BinDirectSum a b) : A⟦B, a⟧ :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (pr2 (pr1 B)))).

  Definition to_Pr2 {a b : A} (B : BinDirectSum a b) : A⟦B, b⟧ :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (pr2 (pr1 B)))).

  (** Another coercion *)
  Definition BinDirectSum_isBinDirectSum {a b : A} (B : BinDirectSum a b) :
    isBinDirectSum a b B (to_In1 B) (to_In2 B) (to_Pr1 B) (to_Pr2 B) := pr2 B.
  Coercion BinDirectSum_isBinDirectSum : BinDirectSum >-> hProptoType.

  (** Construction of BinCoproduct and BinProduct from BinDirectSum. *)
  Definition BinDirectSum_BinCoproduct {a b : A} (B : BinDirectSum a b) :
    BinCoproduct a b.
  Proof.
    use (make_BinCoproduct A a b B (to_In1 B) (to_In2 B)).
    exact (to_isBinCoproduct B).
  Defined.

  Definition BinDirectSum_BinProduct {a b : A} (B : BinDirectSum a b) : BinProduct A a b.
  Proof.
    use (make_BinProduct A a b B (to_Pr1 B) (to_Pr2 B)).
    exact (to_isBinProduct B).
  Defined.

  (** An arrow to BinDirectSum and arrow from BinDirectSum. *)
  Definition ToBinDirectSum {a b : A} (B : BinDirectSum a b) {c : A} (f : c --> a)
             (g : c --> b) : A⟦c, B⟧ := BinProductArrow A (BinDirectSum_BinProduct B) f g.

  Definition FromBinDirectSum {a b : A} (B : BinDirectSum a b) {c : A} (f : a --> c)
             (g : b --> c) : A⟦B, c⟧ := BinCoproductArrow (BinDirectSum_BinCoproduct B) f g.

  (** Commutativity of BinDirectSum. *)
  Definition BinDirectSumIn1Commutes {a b : A} (B : BinDirectSum a b) :
    ∏ (c : A) (f : a --> c) (g : b --> c), (to_In1 B) · (FromBinDirectSum B f g) = f.
  Proof.
    intros c f g.
    apply (BinCoproductIn1Commutes A a b (BinDirectSum_BinCoproduct B) c f g).
  Qed.

  Definition BinDirectSumIn2Commutes {a b : A} (B : BinDirectSum a b) :
    ∏ (c : A) (f : a --> c) (g : b --> c), (to_In2 B) · (FromBinDirectSum B f g) = g.
  Proof.
    intros c f g.
    apply (BinCoproductIn2Commutes A a b (BinDirectSum_BinCoproduct B) c f g).
  Qed.

  Definition BinDirectSumPr1Commutes {a b : A} (B : BinDirectSum a b) :
    ∏ (c : A) (f : c --> a) (g : c --> b), (ToBinDirectSum B f g) · (to_Pr1 B) = f.
  Proof.
    intros c f g.
    apply (BinProductPr1Commutes A a b (BinDirectSum_BinProduct B) c f g).
  Qed.

  Definition BinDirectSumPr2Commutes {a b : A} (B : BinDirectSum a b) :
    ∏ (c : A) (f : c --> a) (g : c --> b), (ToBinDirectSum B f g) · (to_Pr2 B) = g.
  Proof.
    intros c f g.
    apply (BinProductPr2Commutes A a b (BinDirectSum_BinProduct B) c f g).
  Qed.

  (** Uniqueness of arrow to and from BinDirectSum using the BinProduct and BinCoproduct
      structures. *)
  Definition ToBinDirectSumUnique {a b : A} (B : BinDirectSum a b) {c : A} (f : c --> a)
             (g : c --> b) (k : c --> B) :
    k · to_Pr1 B = f -> k · to_Pr2 B = g -> k = ToBinDirectSum B f g :=
    BinProductArrowUnique _ _ _ (BinDirectSum_BinProduct B) c f g k.

  Definition FromBinDirectSumUnique {a b : A} (B : BinDirectSum a b) {c : A} (f : a --> c)
             (g : b --> c) (k : B --> c) :
    to_In1 B · k = f -> to_In2 B · k = g -> k = FromBinDirectSum B f g :=
    BinCoproductArrowUnique _ _ _ (BinDirectSum_BinCoproduct B) c f g k.

  (** Uniqueness of arrows to and from BinDirectSum *)
  Lemma ToBinDirectSumsEq {c d : A} (DS : BinDirectSum c d) {x : A} (k1 k2 : x --> DS) :
    k1 · to_Pr1 DS = k2 · to_Pr1 DS ->
    k1 · to_Pr2 DS = k2 · to_Pr2 DS -> k1 = k2.
  Proof.
    intros H1 H2.
    rewrite (ToBinDirectSumUnique DS (k1 · to_Pr1 DS) (k1 · to_Pr2 DS) k1).
    apply pathsinv0.
    apply ToBinDirectSumUnique.
    - apply pathsinv0. apply H1.
    - apply pathsinv0. apply H2.
    - apply idpath.
    - apply idpath.
  Qed.

  Lemma FromBinDirectSumsEq {c d : A} (DS : BinDirectSum c d) {x : A} (k1 k2 : DS --> x) :
    to_In1 DS · k1 = to_In1 DS · k2 -> to_In2 DS · k1 = to_In2 DS · k2 -> k1 = k2.
  Proof.
    intros H1 H2.
    rewrite (FromBinDirectSumUnique DS (to_In1 DS · k1) (to_In2 DS · k1) k1).
    apply pathsinv0.
    apply FromBinDirectSumUnique.
    - apply pathsinv0. apply H1.
    - apply pathsinv0. apply H2.
    - apply idpath.
    - apply idpath.
  Qed.

  (** The following definitions give a formula for the unique morphisms to and from the
      BinDirectSum. These formulas are important when one uses bindirectsums. The formulas are

      to bindirectsum unique arrow     =   f · in1 + g · in2
      from bindirectsum unique arrow   =   pr1 · f + pr2 · g
   *)
  Definition ToBinDirectSumFormula {a b : A} (B : BinDirectSum a b) {c : A} (f : c --> a)
             (g : c --> b) : A⟦c, B⟧ := (to_binop c B) (f · to_In1 B) (g · to_In2 B).

  Definition FromBinDirectSumFormula {a b : A} (B : BinDirectSum a b) {c : A} (f : a --> c)
             (g : b --> c) : A⟦B, c⟧ := (to_binop B c) (to_Pr1 B · f) (to_Pr2 B · g).

  (** Let us prove that these formulas indeed are the unique morphisms we claimed them to be. *)
  Lemma ToBinDirectSumFormulaUnique {a b : A} (B : BinDirectSum a b) {c : A} (f : c --> a)
        (g : c --> b) : ToBinDirectSumFormula B f g = ToBinDirectSum B f g.
  Proof.
    apply ToBinDirectSumUnique.
    - unfold ToBinDirectSumFormula.
      unfold to_binop.
      use (pathscomp0 (to_postmor_linear c (to_Pr1 B) (f · to_In1 B) (g · to_In2 B))).
      unfold to_postmor. repeat rewrite <- assoc.
      rewrite (to_IdIn1 B).
      rewrite id_right.
      rewrite (to_Unel2 B).
      set (XX := to_premor_unel A a g).
      unfold to_premor in XX.
      unfold to_unel.
      rewrite XX.
      apply (to_runax c a).
    - unfold ToBinDirectSumFormula.
      unfold to_binop. cbn.
      use (pathscomp0 (to_postmor_linear c (to_Pr2 B) (f · to_In1 B) (g · to_In2 B))).
      unfold to_postmor. repeat rewrite <- assoc.
      rewrite (to_IdIn2 B). rewrite (to_Unel1 B). rewrite id_right.
      set (XX := to_premor_unel A b f).
      unfold PrecategoriesWithAbgrops.to_premor in XX.
      unfold PrecategoriesWithAbgrops.to_unel.
      rewrite XX. clear XX.
      apply (to_lunax c b).
  Qed.

  Lemma FromBinDirectSumFormulaUnique {a b : A} (B : BinDirectSum a b) {c : A} (f : a --> c)
        (g : b --> c) : FromBinDirectSumFormula B f g = FromBinDirectSum B f g.
  Proof.
    unfold FromBinDirectSumFormula.
    apply FromBinDirectSumUnique.
    - use (pathscomp0 (to_premor_linear c (to_In1 B) (to_Pr1 B · f) (to_Pr2 B · g))).
      unfold to_premor. repeat rewrite assoc.
      rewrite (to_IdIn1 B). rewrite (to_Unel1 B). rewrite id_left.
      set (XX := to_postmor_unel A a g).
      unfold to_postmor in XX.
      unfold to_unel.
      rewrite XX.
      apply (to_runax a c).
    - use (pathscomp0 (to_premor_linear c (to_In2 B) (to_Pr1 B · f) (to_Pr2 B · g))).
      unfold to_premor. repeat rewrite assoc.
      rewrite (to_IdIn2 B). rewrite (to_Unel2 B). rewrite id_left.
      set (XX := to_postmor_unel A b f).
      unfold to_postmor in XX.
      unfold to_unel.
      rewrite XX.
      apply (to_lunax b c).
  Qed.

  (** The following definitions give 2 ways to construct a morphisms a ⊕ c --> b ⊕ d from two
      morphisms f : a --> b and g : c --> d , by using the binary direct sums as a product and as a
      coproduct. *)
  Definition BinDirectSumIndAr {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSum a c) (B2 : BinDirectSum b d) :
    A⟦B1, B2⟧ := ToBinDirectSum B2 ((to_Pr1 B1) · f) ((to_Pr2 B1) · g).

  Definition BinDirectSumIndAr' {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSum a c) (B2 : BinDirectSum b d) :
    A⟦B1, B2⟧ := FromBinDirectSum B1 (f · (to_In1 B2)) (g · (to_In2 B2)).

  (** Both of the above morphisms are given by the following formula. *)
  Definition BinDirectSumIndArFormula {a b c d: A}  (f : a --> b) (g : c --> d)
             (B1 : BinDirectSum a c) (B2 : BinDirectSum b d) :
    A⟦B1, B2⟧ := (to_binop B1 B2) (to_Pr1 B1 · f · to_In1 B2) (to_Pr2 B1 · g · to_In2 B2).

  Lemma BinDirectSumIndArEq1 {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSum a c) (B2 : BinDirectSum b d) :
    BinDirectSumIndAr f g B1 B2 = BinDirectSumIndArFormula f g B1 B2.
  Proof.
    unfold BinDirectSumIndAr.
    rewrite <- ToBinDirectSumFormulaUnique.
    unfold ToBinDirectSumFormula.
    unfold BinDirectSumIndArFormula.
    apply idpath.
  Qed.

  Lemma BinDirectSumIndArEq2 {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSum a c) (B2 : BinDirectSum b d) :
    BinDirectSumIndAr' f g B1 B2 = BinDirectSumIndArFormula f g B1 B2.
  Proof.
    unfold BinDirectSumIndAr'.
    rewrite <- FromBinDirectSumFormulaUnique.
    unfold FromBinDirectSumFormula.
    unfold BinDirectSumIndArFormula.
    rewrite assoc. rewrite assoc.
    apply idpath.
  Qed.

  (** Thus we have equality. *)
  Definition BinDirectSumIndArEq {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSum a c) (B2 : BinDirectSum b d) :
    BinDirectSumIndAr f g B1 B2 = BinDirectSumIndAr' f g B1 B2.
  Proof.
    rewrite -> BinDirectSumIndArEq1.
    rewrite -> BinDirectSumIndArEq2.
    apply idpath.
  Qed.

  (** ** Composition of IndAr *)
  Lemma BinDirectSumIndArComp {a b c d e f : A} (f1 : a --> b) (f2 : b --> c)
        (g1 : d --> e) (g2 : e --> f) (B1 : BinDirectSum a d) (B2 : BinDirectSum b e)
        (B3 : BinDirectSum c f) :
    BinDirectSumIndAr f1 g1 B1 B2 · BinDirectSumIndAr f2 g2 B2 B3 =
    BinDirectSumIndAr (f1 · f2) (g1 · g2) B1 B3.
  Proof.
    rewrite BinDirectSumIndArEq1. rewrite (BinDirectSumIndArEq1 f2). rewrite (BinDirectSumIndArEq1 (f1 · f2)).
    unfold BinDirectSumIndArFormula.
    rewrite to_postmor_linear'.
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ (to_In1 B2)). rewrite <- (assoc _ (to_In1 B2)).
    rewrite (to_IdIn1 B2). rewrite id_right.
    rewrite (to_Unel1 B2). rewrite to_premor_unel'.
    rewrite to_postmor_unel'. rewrite to_postmor_unel'. rewrite to_runax'.
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ (to_In2 B2)). rewrite <- (assoc _ (to_In2 B2)).
    rewrite (to_IdIn2 B2). rewrite id_right.
    rewrite (to_Unel2 B2). rewrite to_premor_unel'.
    rewrite to_postmor_unel'. rewrite to_postmor_unel'.
    rewrite to_lunax'.
    apply idpath.
  Qed.

End def_bindirectsums.
Arguments BinDirectSumIndAr {_ _ _ _ _}.
Arguments BinDirectSumOb {_ _ _}.
Arguments BinDirectSum {_}.
Arguments to_Pr1 {_ _ _} _.
Arguments to_Pr2 {_ _ _} _.
Arguments to_In1 {_ _ _} _.
Arguments to_In2 {_ _ _} _.
Arguments to_BinOpId {_ _ _ _ _ _ _ _}.
Arguments to_IdIn1 {_ _ _ _ _ _ _ _}.
Arguments to_IdIn2 {_ _ _ _ _ _ _ _}.
Arguments to_Unel1 {_ _ _ _ _ _ _ _}.
Arguments to_Unel2 {_ _ _ _ _ _ _ _}.
Arguments ToBinDirectSum {_ _ _} _ {_}.
Arguments isBinDirectSum {_ _ _ _}.

(** In1 and In2 are monics, and Pr1 and Pr2 are epis. *)
Section bindirectsums_monics_and_epis.

  Variable A : PreAdditive.

  Lemma to_In1_isMonic {a b : A} (B : BinDirectSum a b) : isMonic (to_In1 B).
  Proof.
    intros z f g H.
    apply (maponpaths (λ h : _, h · (to_Pr1 B))) in H.
    repeat rewrite <- assoc in H.
    set (X:= to_IdIn1 (A:=A) B).
    assert (X1 : to_In1 B · to_Pr1 B = 1%abgrcat).
    { apply X. }
    apply (@pathscomp0 _ _ ( f · (to_In1 B · to_Pr1 B)) _).
    apply pathsinv0.
    etrans. apply maponpaths. apply X1.
    apply id_right.
    etrans. apply H.
    etrans. apply maponpaths. apply X1.
    apply id_right.
  Qed.

  Lemma to_In2_isMonic {a b : A} (B : BinDirectSum a b) : isMonic (to_In2 B).
  Proof.
    intros z f g H.
    apply (maponpaths (λ h : _, h · (to_Pr2 B))) in H.
    repeat rewrite <- assoc in H.
    set (X:= to_IdIn2 (A:=A) B).
    assert (X1 : to_In2 B · to_Pr2 B = 1%abgrcat).
    { apply X. }
    apply (@pathscomp0 _ _ ( f · (to_In2 B · to_Pr2 B)) _).
    apply pathsinv0.
    etrans. apply maponpaths. apply X1.
    apply id_right.
    etrans. apply H.
    etrans. apply maponpaths. apply X1.
    apply id_right.
  Qed.

  Lemma to_Pr1_isEpi {a b : A} (B : BinDirectSum a b) : isEpi (to_Pr1 B).
  Proof.
    intros z f g H.
    apply (maponpaths (λ h : _, (to_In1 B) · h)) in H.
    repeat rewrite assoc in H. rewrite (to_IdIn1 B) in H.
    repeat rewrite id_left in H. apply H.
  Qed.

  Lemma to_Pr2_isEpi {a b : A} (B : BinDirectSum a b) : isEpi (to_Pr2 B).
  Proof.
    intros z f g H.
    apply (maponpaths (λ h : _, (to_In2 B) · h)) in H.
    repeat rewrite assoc in H. rewrite (to_IdIn2 B) in H.
    repeat rewrite id_left in H. apply H.
  Qed.

End bindirectsums_monics_and_epis.


(** If a PreAdditive category has BinProducts, then it has all direct sums. *)
Section bindirectsums_criteria.

  Variable A : PreAdditive.
  Hypothesis hs : has_homsets A.
  Variable Z : Zero A.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq1 {X Y : A} (P : BinProduct A X Y) :
    BinProductArrow A P (identity X) (ZeroArrow Z X Y) · BinProductPr1 A P = identity _ .
  Proof.
    apply BinProductPr1Commutes.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq2 {X Y : A} (P : BinProduct A X Y) :
    BinProductArrow A P (identity X) (ZeroArrow Z X Y) · BinProductPr2 A P = to_unel X Y.
  Proof.
    rewrite (PreAdditive_unel_zero A Z).
    apply BinProductPr2Commutes.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq3 {X Y : A} (P : BinProduct A X Y) :
    BinProductArrow A P (ZeroArrow Z Y X) (identity _ ) · BinProductPr1 A P = to_unel Y X.
  Proof.
    rewrite (PreAdditive_unel_zero A Z).
    apply BinProductPr1Commutes.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq4 {X Y : A} (P : BinProduct A X Y) :
    BinProductArrow A P (ZeroArrow Z Y X) (identity _ ) · BinProductPr2 A P = identity _ .
  Proof.
    apply BinProductPr2Commutes.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq5 {X Y : A} (P : BinProduct A X Y) :
    to_binop
      (BinProductObject A P) (BinProductObject A P)
      (BinProductPr1 A P · BinProductArrow A P(identity X) (ZeroArrow Z X Y))
      (BinProductPr2 A P · BinProductArrow A P (ZeroArrow Z Y X) (identity Y)) = identity _ .
  Proof.
    apply BinProductArrowsEq.
    - rewrite to_postmor_linear'.
      rewrite <- assoc. rewrite <- assoc.
      rewrite BinProductPr1Commutes. rewrite BinProductPr1Commutes.
      rewrite id_right. rewrite ZeroArrow_comp_right.
      rewrite <- PreAdditive_unel_zero.
      rewrite id_left.
      apply to_runax.
    - rewrite to_postmor_linear'.
      rewrite <- assoc. rewrite <- assoc.
      rewrite BinProductPr2Commutes. rewrite BinProductPr2Commutes.
      rewrite id_right. rewrite ZeroArrow_comp_right.
      rewrite <- PreAdditive_unel_zero.
      rewrite id_left.
      apply to_lunax.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_isCoproduct {X Y : A}
             (P : BinProduct A X Y) :
    isBinCoproduct A X Y (BinProductObject A P)
                         (BinProductArrow A P (identity X) (ZeroArrow Z X Y))
                         (BinProductArrow A P (ZeroArrow Z Y X) (identity Y)).
  Proof.
    use (make_isBinCoproduct _ hs).
    intros c f g.
    use unique_exists.
    - exact (to_binop (BinProductObject A P) c (BinProductPr1 A P · f) (BinProductPr2 A P · g)).
    - split.
      + rewrite to_premor_linear'.
        rewrite assoc. rewrite assoc.
        rewrite BinProductPr1Commutes.
        rewrite BinProductPr2Commutes.
        rewrite ZeroArrow_comp_left.
        rewrite id_left.
        rewrite <- PreAdditive_unel_zero.
        apply to_runax.
      + rewrite to_premor_linear'.
        rewrite assoc. rewrite assoc.
        rewrite BinProductPr1Commutes.
        rewrite BinProductPr2Commutes.
        rewrite ZeroArrow_comp_left.
        rewrite id_left.
        rewrite <- PreAdditive_unel_zero.
        apply to_lunax.
    - intros y. apply isapropdirprod. apply hs. apply hs.
    - intros y H. induction H as [t p]. rewrite <- t. rewrite <- p.
      rewrite assoc. rewrite assoc.
      rewrite <- to_postmor_linear'.
      rewrite (BinDirectSums_from_binproduct_bincoproducts_eq5 P).
      rewrite id_left. apply idpath.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_isProduct {X Y : A}
             (P : BinProduct A X Y) :
    isBinProduct A X Y (BinProductObject A P) (BinProductPr1 A P) (BinProductPr2 A P).
  Proof.
    use (make_isBinProduct _ ).
    intros c f g.
    use unique_exists.
    - exact (BinProductArrow A P f g).
    - split.
      + apply BinProductPr1Commutes.
      + apply BinProductPr2Commutes.
    - intros y. apply isapropdirprod.
      + apply hs.
      + apply hs.
    - intros y H. induction H as [t p]. rewrite <- t. rewrite <- p.
      rewrite <- precompWithBinProductArrow.
      apply BinProductArrowsEq.
      + rewrite <- assoc. rewrite BinProductPr1Commutes. apply idpath.
      + rewrite <- assoc. rewrite BinProductPr2Commutes. apply idpath.
  Qed.

  Definition BinDirectSum_from_BinProduct {X Y : A} (P : BinProduct A X Y) :
    BinDirectSum X Y :=
    make_BinDirectSum
      A X Y
      (BinProductObject A P)
      (BinProductArrow A P (identity X) (ZeroArrow Z X Y))
      (BinProductArrow A P (ZeroArrow Z Y X) (identity Y))
      (BinProductPr1 A P)
      (BinProductPr2 A P)
      (make_isBinDirectSum
         _ _ _ _ _ _ _ _
         (BinDirectSums_from_binproduct_bincoproducts_eq1 P)
         (BinDirectSums_from_binproduct_bincoproducts_eq4 P)
         (BinDirectSums_from_binproduct_bincoproducts_eq2 P)
         (BinDirectSums_from_binproduct_bincoproducts_eq3 P)
         (BinDirectSums_from_binproduct_bincoproducts_eq5 P)).

  Definition BinDirectSums_from_BinProducts (BinProds : BinProducts A) : BinDirectSums A.
  Proof.
    intros X Y.
    exact (BinDirectSum_from_BinProduct (BinProds X Y)).
  Defined.

End bindirectsums_criteria.


(** * BinDirectSums in quotient of PreAdditive category
   In this section we show that, if a PreAdditive A has BinDirectSums, then the quotient of the
   preadditive category has BinDirectSums. This is used to show that quotient of an CategoryWithAdditiveStructure is
   CategoryWithAdditiveStructure. *)
Section bindirectsums_in_quot.

  Variable A : PreAdditive.
  Hypothesis Z : Zero A.
  Hypothesis BD : BinDirectSums A.
  Hypothesis PAS : PreAdditiveSubabgrs A.
  Hypothesis PAC : PreAdditiveComps A PAS.

  Lemma Quotcategory_isBinCoproduct (x y : A) :
    isBinCoproduct (Quotcategory_PreAdditive A PAS PAC) x y (BD x y)
                         (to_quot_mor A PAS (to_In1 (BD x y)))
                         (to_quot_mor A PAS (to_In2 (BD x y))).
  Proof.
    use make_isBinCoproduct.
    - apply has_homsets_Quotcategory.
    - intros c f g.
      set (f'' := @issurjsetquotpr (@to_abgr A x c) (binopeqrel_subgr_eqrel (PAS x c)) f).
      use (squash_to_prop f''). apply isapropiscontr. intros f'. clear f''.
      set (g'' := @issurjsetquotpr (@to_abgr A y c) (binopeqrel_subgr_eqrel (PAS y c)) g).
      use (squash_to_prop g''). apply isapropiscontr. intros g'. clear g''.
      induction f' as [f1 f2]. induction g' as [g1 g2]. cbn in f1, g1.
      use unique_exists.
      + exact (to_quot_mor A PAS (FromBinDirectSum A (BD x y) f1 g1)).
      + cbn beta. split.
        * use (pathscomp0 (Quotcategory_comp_linear A PAS PAC _ _)).
          rewrite BinDirectSumIn1Commutes. exact f2.
        * use (pathscomp0 (Quotcategory_comp_linear A PAS PAC _ _)).
          rewrite BinDirectSumIn2Commutes. exact g2.
      + intros y0. apply isapropdirprod; apply has_homsets_Quotcategory.
      + intros y0 T. cbn beta in T. induction T as [T1 T2].
        * set (y'' := @issurjsetquotpr (@to_abgr A (BD x y) c)
                                       (binopeqrel_subgr_eqrel (PAS (BD x y) c)) y0).
          use (squash_to_prop y''). apply has_homsets_Quotcategory. intros y'. clear y''.
          induction y' as [y1 y2]. rewrite <- y2. rewrite <- y2 in T1. rewrite <- y2 in T2.
          cbn in y1.
          rewrite <- (@id_left (Quotcategory_PreAdditive A PAS PAC) _ _
                              (setquotpr (binopeqrel_subgr_eqrel (PAS (BD x y) c)) y1)).
          rewrite <- (@id_left A _ _ (FromBinDirectSum A (BD x y) f1 g1)).
          rewrite <- (to_BinOpId (BD x y)). rewrite to_postmor_linear'.
          repeat rewrite <- assoc.
          rewrite BinDirectSumIn1Commutes.
          rewrite BinDirectSumIn2Commutes.
          rewrite <- f2 in T1. rewrite <- g2 in T2. unfold to_quot_mor.
          set (tmp := @setquotpr_linear A PAS PAC (BD x y) c). unfold to_quot_mor in tmp.
          rewrite tmp. clear tmp.
          set (tmp := @Quotcategory_comp_linear A PAS PAC (BD x y) x c).
          unfold to_quot_mor in tmp. rewrite <- tmp. clear tmp.
          rewrite <- T1.
          set (tmp := @Quotcategory_comp_linear A PAS PAC (BD x y) y c).
          unfold to_quot_mor in tmp. rewrite <- tmp. clear tmp.
          rewrite <- T2. unfold to_quot_mor. rewrite comp_eq. rewrite comp_eq.
          rewrite assoc. rewrite assoc.
          rewrite <- to_postmor_linear'.
          repeat rewrite <- comp_eq.
          set (tmp := @Quotcategory_comp_linear A PAS PAC (BD x y) x (BD x y)).
          unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
          set (tmp := @Quotcategory_comp_linear A PAS PAC (BD x y) y (BD x y)).
          unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
          set (tmp := @setquotpr_linear A PAS PAC (BD x y) (BD x y)). unfold to_quot_mor in tmp.
          rewrite <- tmp. clear tmp.
          rewrite comp_eq.
          rewrite (to_BinOpId (BD x y)).
          rewrite comp_eq. apply cancel_postcomposition.
          apply idpath.
  Qed.

  Lemma Quotcategory_isBinProduct (x y : A) :
    isBinProduct (Quotcategory_PreAdditive A PAS PAC) x y (BD x y)
                     (to_quot_mor A PAS (to_Pr1 (BD x y)))
                     (to_quot_mor A PAS (to_Pr2 (BD x y))).
  Proof.
    use make_isBinProduct.
    - intros c f g.
      set (f'' := @issurjsetquotpr (@to_abgr A c x) (binopeqrel_subgr_eqrel (PAS c x)) f).
      use (squash_to_prop f''). apply isapropiscontr. intros f'. clear f''.
      set (g'' := @issurjsetquotpr (@to_abgr A c y) (binopeqrel_subgr_eqrel (PAS c y)) g).
      use (squash_to_prop g''). apply isapropiscontr. intros g'. clear g''.
      induction f' as [f1 f2]. induction g' as [g1 g2]. cbn in f1, g1.
      use unique_exists.
      + exact (to_quot_mor A PAS (ToBinDirectSum (BD x y) f1 g1)).
      + cbn beta. split.
        * use (pathscomp0 (Quotcategory_comp_linear A PAS PAC _ _)).
          rewrite BinDirectSumPr1Commutes. exact f2.
        * use (pathscomp0 (Quotcategory_comp_linear A PAS PAC _ _)).
          rewrite BinDirectSumPr2Commutes. exact g2.
      + intros y0. apply isapropdirprod; apply has_homsets_Quotcategory.
      + intros y0 T. cbn beta in T. induction T as [T1 T2].
        * set (y'' := @issurjsetquotpr (@to_abgr A c (BD x y))
                                       (binopeqrel_subgr_eqrel (PAS c (BD x y))) y0).
          use (squash_to_prop y''). apply has_homsets_Quotcategory. intros y'. clear y''.
          induction y' as [y1 y2]. rewrite <- y2. rewrite <- y2 in T1. rewrite <- y2 in T2.
          cbn in y1.
          rewrite <- (@id_right (Quotcategory_PreAdditive A PAS PAC) _ _
                               (setquotpr (binopeqrel_subgr_eqrel (PAS c (BD x y))) y1)).
          rewrite <- (@id_right A _ _ (ToBinDirectSum (BD x y) f1 g1)).
          rewrite <- (to_BinOpId (BD x y)). rewrite to_premor_linear'.
          repeat rewrite assoc.
          rewrite BinDirectSumPr1Commutes.
          rewrite BinDirectSumPr2Commutes.
          rewrite <- f2 in T1. rewrite <- g2 in T2. unfold to_quot_mor.
          set (tmp := @setquotpr_linear A PAS PAC c (BD x y)). unfold to_quot_mor in tmp.
          rewrite tmp. clear tmp.
          set (tmp := @Quotcategory_comp_linear A PAS PAC c x (BD x y)).
          unfold to_quot_mor in tmp. rewrite <- tmp. clear tmp.
          rewrite <- T1.
          set (tmp := @Quotcategory_comp_linear A PAS PAC c y (BD x y)).
          unfold to_quot_mor in tmp. rewrite <- tmp. clear tmp.
          rewrite <- T2. unfold to_quot_mor. rewrite comp_eq. rewrite comp_eq.
          rewrite <- assoc. rewrite <- assoc.
          rewrite <- to_premor_linear'.
          repeat rewrite <- comp_eq.
          set (tmp := @Quotcategory_comp_linear A PAS PAC (BD x y) x (BD x y)).
          unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
          set (tmp := @Quotcategory_comp_linear A PAS PAC (BD x y) y (BD x y)).
          unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
          set (tmp := @setquotpr_linear A PAS PAC (BD x y) (BD x y)). unfold to_quot_mor in tmp.
          rewrite <- tmp. clear tmp.
          rewrite comp_eq.
          rewrite (to_BinOpId (BD x y)).
          rewrite comp_eq. apply cancel_precomposition.
          apply idpath.
  Qed.

  Opaque Quotcategory_PreAdditive. (* This speeds up the following proof significantly. *)
  Lemma Quotcategory_isBinDirectSum (x y : A) :
    isBinDirectSum
      (A := Quotcategory_PreAdditive A PAS PAC)
      (to_quot_mor A PAS (to_In1 (BD x y))) (to_quot_mor A PAS (to_In2 (BD x y)))
      (to_quot_mor A PAS (to_Pr1 (BD x y))) (to_quot_mor A PAS (to_Pr2 (BD x y))).
  Proof.
    use make_isBinDirectSum.
    - unfold to_quot_mor.
      rewrite <- comp_eq.
      set (tmp := @Quotcategory_comp_linear A PAS PAC x (BD x y) x).
      unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
      rewrite (to_IdIn1 (BD x y)).
      apply idpath.
    - unfold to_quot_mor.
      rewrite <- comp_eq.
      set (tmp := @Quotcategory_comp_linear A PAS PAC y (BD x y) y).
      unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
      rewrite (to_IdIn2 (BD x y)).
      apply idpath.
    - unfold to_quot_mor.
      rewrite <- comp_eq.
      set (tmp := @Quotcategory_comp_linear A PAS PAC x (BD x y) y).
      unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
      rewrite (to_Unel1 (BD x y)).
      apply idpath.
    - unfold to_quot_mor.
      rewrite <- comp_eq.
      set (tmp := @Quotcategory_comp_linear A PAS PAC y (BD x y) x).
      unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
      rewrite (to_Unel2 (BD x y)).
      apply idpath.
    - unfold to_quot_mor.
      repeat rewrite <- comp_eq.
      set (tmp := @Quotcategory_comp_linear A PAS PAC (BD x y) x (BD x y)).
      unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
      set (tmp := @Quotcategory_comp_linear A PAS PAC (BD x y) y (BD x y)).
      unfold to_quot_mor in tmp. rewrite tmp. clear tmp.
      set (tmp := @setquotpr_linear A PAS PAC (BD x y) (BD x y)). unfold to_quot_mor in tmp.
      rewrite <- tmp. clear tmp.
      rewrite (to_BinOpId (BD x y)).
      apply idpath.
  Qed.
  Transparent Quotcategory_PreAdditive. (* Transparent again *)

  Definition Quotcategory_BinDirectSums : BinDirectSums (Quotcategory_PreAdditive A PAS PAC).
  Proof.
    intros x y.
    use make_BinDirectSum.
    - exact (BD x y).
    - exact (to_quot_mor A PAS (to_In1 (BD x y))).
    - exact (to_quot_mor A PAS (to_In2 (BD x y))).
    - exact (to_quot_mor A PAS (to_Pr1 (BD x y))).
    - exact (to_quot_mor A PAS (to_Pr2 (BD x y))).
    - exact (Quotcategory_isBinDirectSum x y).
  Defined.

End bindirectsums_in_quot.

Notation "'π₁'" := (to_Pr1 _) : abgrcat.
Notation "'π₂'" := (to_Pr2 _) : abgrcat.
Notation "'ι₁'" := (to_In1 _) : abgrcat.
Notation "'ι₂'" := (to_In2 _) : abgrcat.
Local Open Scope abgrcat.

Definition reverseBinDirectSum {M:PreAdditive} {A B:M} : BinDirectSum A B -> BinDirectSum B A.
Proof.
  intros AB.
  refine (make_BinDirectSum M B A (BinDirectSumOb AB) ι₂ ι₁ π₂ π₁ _).
  unfold isBinDirectSum.
  exists (to_IdIn2 (pr2 AB)).
  exists (to_IdIn1 (pr2 AB)).
  exists (to_Unel2 (pr2 AB)).
  exists (to_Unel1 (pr2 AB)).
  cbn. rewrite rewrite_op.
  (* goal is now π₂ · ι₂ + π₁ · ι₁ = 1 *)
  exact (commax (to_abgr _ _) _ _ @ to_BinOpId (pr2 AB)).
Defined.

Definition oppositeBinDirectSum {M:PreAdditive} {x y:M} :
  BinDirectSum x y -> BinDirectSum (A:=oppositePreAdditive M) x y.
Proof.
  intros Q.
  use make_BinDirectSum.
  + exact (BinDirectSumOb Q).
  + exact (to_Pr1 Q).
  + exact (to_Pr2 Q).
  + exact (to_In1 Q).
  + exact (to_In2 Q).
  + exact (make_isBinDirectSum (oppositePreAdditive M) _ _ _ _ _ _ _
       (to_IdIn1 Q) (to_IdIn2 Q) (to_Unel2 Q) (to_Unel1 Q)
       (to_BinOpId Q)).
Defined.

Definition isTrivialDirectSum {M : PreAdditive} (Z:Zero M) (A:M) : @isBinDirectSum M A Z A 1 0 1 0.
Proof.
  repeat split; cbn.
  - apply id_right.
  - apply ArrowsToZero.
  - apply ArrowsToZero.
  - apply ArrowsFromZero.
  - rewrite id_right. rewrite to_premor_unel'. rewrite rewrite_op. rewrite runax. reflexivity.
Qed.
Definition TrivialDirectSum {M : PreAdditive} (Z:Zero M) (A:M) : BinDirectSum A Z.
Proof.
  exact (make_BinDirectSum _ _ _ _ _ _ _ _ (isTrivialDirectSum _ _)).
Defined.
Definition isTrivialDirectSum' {M : PreAdditive} (Z:Zero M) (A:M) : @isBinDirectSum M Z A A 0 1 0 1.
Proof.
  repeat split; cbn.
  - apply ArrowsToZero.
  - apply id_right.
  - apply ArrowsFromZero.
  - apply ArrowsToZero.
  - rewrite id_right. rewrite to_premor_unel'. rewrite rewrite_op. rewrite lunax. reflexivity.
Qed.
Definition TrivialDirectSum' {M : PreAdditive} (Z:Zero M) (A:M) : BinDirectSum Z A.
Proof.
  exact (make_BinDirectSum _ _ _ _ _ _ _ _ (isTrivialDirectSum' _ _)).
Defined.
Definition replaceSum {M:PreAdditive} {A B C:M} (S:BinDirectSum A B) :
  z_iso C S -> BinDirectSum A B (* with C judgmentally equal to the sum object *).
Proof.
  intros r.
  exists (C,, ι₁ · z_iso_inv r,, ι₂ · z_iso_inv r,, r · π₁,, r · π₂).
  repeat split; cbn.
  + rewrite assoc'. rewrite (assoc _ r). rewrite z_iso_after_z_iso_inv, id_left. exact (to_IdIn1 S).
  + rewrite assoc'. rewrite (assoc _ r). rewrite z_iso_after_z_iso_inv, id_left. exact (to_IdIn2 S).
  + rewrite assoc'. rewrite (assoc _ r). rewrite z_iso_after_z_iso_inv, id_left. exact (to_Unel1 S).
  + rewrite assoc'. rewrite (assoc _ r). rewrite z_iso_after_z_iso_inv, id_left. exact (to_Unel2 S).
  + rewrite rewrite_op. rewrite 2 (assoc' r). rewrite 4 (assoc _ _ (z_iso_inv_mor r)).
    rewrite <- leftDistribute. rewrite <- rightDistribute. rewrite wrap_inverse'.
    * reflexivity.
    * exact (to_BinOpId S).
Defined.
Lemma DirectSumIn1Pr2 {M:PreAdditive} {a b:M} (S:BinDirectSum a b) : to_In1 S · to_Pr2 S = 0.
Proof.
  exact (to_Unel1 S).
Defined.
Lemma DirectSumIn2Pr1 {M:PreAdditive} {a b:M} (S:BinDirectSum a b) : to_In2 S · to_Pr1 S = 0.
Proof.
  exact (to_Unel2 S).
Defined.
