(** Direct definition of binary direct sum using preadditive categories. *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.zero.

Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.


(** BinDirectSum is at the same time product and coproduct of the underlying
  objects together with the following equalities

    i1 ;; p1 = identity  and   i2 ;; p2 = identity
    i1 ;; p2 = unit      and   i2 ;; p1 = unit
            p1 ;; i1 + p2 ;; i2 = identity
*)
Section def_bindirectsums.

  Variable A : PreAdditive.

  (** Definition of isBinDirectSumCone *)
  Definition isBinDirectSumCone (a b co : A) (i1 : a --> co) (i2 : b --> co)
             (p1 : co --> a) (p2 : co --> b) :=
    (isBinCoproductCocone A a b co i1 i2)
      × (isBinProductCone A a b co p1 p2)
      × (i1 ;; p1 = identity a) × (i2 ;; p2 = identity b)
      × (i1 ;; p2 = (PrecategoryWithAbgrops_unel A a b))
      × (i2 ;; p1 = (PrecategoryWithAbgrops_unel A b a))
      × ((PrecategoryWithBinOps_binop A co co) (p1 ;; i1) (p2 ;; i2) =
         identity co).
  Definition isBinDirectSumCone_coproduct {a b co : A}
             {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    isBinCoproductCocone A a b co i1 i2 := dirprod_pr1 B.
  Definition isBinDirectSumCone_product {a b co : A}
             {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    isBinProductCone A a b co p1 p2 := dirprod_pr1 (dirprod_pr2 B).
  Definition isBinDirectSumCone_idin1 {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    i1 ;; p1 = identity a := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 B)).
  Definition isBinDirectSumCone_idin2 {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) : i2 ;; p2 = identity b
    := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 B))).
  Definition isBinDirectSumCone_unit1 {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2)
    := pr1 (pr2 (pr2 (pr2 (pr2 B)))).
  Definition isBinDirectSumCone_unit2 {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2)
    := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 B))))).
  Definition isBinDirectSumCone_id {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2)
    := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 B))))).


  (** The following definition constructs isBinDirectSumCone from data. *)
  Definition mk_isBinDirectSumCone (a b co : A)
             (i1 : a --> co) (i2 : b --> co) (p1 : co --> a) (p2 : co --> b)
             (isBC : isBinCoproductCocone A a b co i1 i2)
             (isBP : isBinProductCone A a b co p1 p2)
             (H1 : i1 ;; p1 = identity a) (H2 : i2 ;; p2 = identity b)
             (H3 : i1 ;; p2 = (PrecategoryWithAbgrops_unel A a b))
             (H4 : i2 ;; p1 = (PrecategoryWithAbgrops_unel A b a))
             (H5 : (PrecategoryWithBinOps_binop A co co)
                     (p1 ;; i1) (p2 ;; i2) = identity co)
    : isBinDirectSumCone a b co i1 i2 p1 p2
    := isBC,,(isBP,,(H1,,(H2,,(H3,,(H4,,H5))))).

  (** Definition of BinDirectSums. *)
  Definition BinDirectSumCone (a b : A) : UU :=
    Σ coab : (Σ co : A, a --> co × b --> co × co --> a × co --> b),
             isBinDirectSumCone
               a b (pr1 coab) (pr1 (pr2 coab))
               (pr1 (pr2 (pr2 coab)))
               (pr1 (pr2 (pr2 (pr2 coab))))
               (pr2 (pr2 (pr2 (pr2 coab)))).

  (** Construction of BinDirectSumCone. *)
  Definition mk_BinDirectSumCone (a b co : A)
             (i1 : a --> co) (i2 : b --> co) (p1 : co --> a) (p2 : co --> b)
             (H :  isBinDirectSumCone a b co i1 i2 p1 p2) :
    BinDirectSumCone a b := tpair _ (tpair _ co (i1,,(i2,,(p1,,p2)))) H.

  (** BinDirectSum in categories. *)
  Definition BinDirectSums := Π (a b : A), BinDirectSumCone a b.
  Definition has_BinDirectSums := ishinh BinDirectSums.

  (** The direct sum object. *)
  Definition BinDirectSumConeOb {a b : A} (B : BinDirectSumCone a b) :
    A := pr1 (pr1 B).
  Coercion BinDirectSumConeOb : BinDirectSumCone >-> ob.

  (** Inclusions and projections to and from the direct sum. *)
  Definition BinDirectSumIn1 {a b : A} (B : BinDirectSumCone a b) :
    A⟦a, B⟧ := pr1 (pr2 (pr1 B)).
  Definition BinDirectSumIn2 {a b : A} (B : BinDirectSumCone a b) :
    A⟦b, B⟧ := pr1 (pr2 (pr2 (pr1 B))).
  Definition BinDirectSumPr1 {a b : A} (B : BinDirectSumCone a b) :
    A⟦B, a⟧ := pr1 (pr2 (pr2 (pr2 (pr1 B)))).
  Definition BinDirectSumPr2 {a b : A} (B : BinDirectSumCone a b) :
    A⟦B, b⟧ := pr2 (pr2 (pr2 (pr2 (pr1 B)))).

  (** Returns the isBinDirectSum property. *)
  Definition BinDirectSum_isBinDirectSum {a b : A} (B : BinDirectSumCone a b) :
    isBinDirectSumCone a b B (BinDirectSumIn1 B) (BinDirectSumIn2 B)
                       (BinDirectSumPr1 B) (BinDirectSumPr2 B)
    := pr2 B.

  (** Equalities between identity and compositions of inclusions and
    projections. *)
  Definition BinDirectSumIdIn1 {a b : A} (B : BinDirectSumCone a b) :
    (BinDirectSumIn1 B) ;; (BinDirectSumPr1 B) = identity a
    := isBinDirectSumCone_idin1 (BinDirectSum_isBinDirectSum B).
  Definition BinDirectSumIdIn2 {a b : A} (B : BinDirectSumCone a b) :
    (BinDirectSumIn2 B) ;; (BinDirectSumPr2 B) = identity b
    := isBinDirectSumCone_idin2 (BinDirectSum_isBinDirectSum B).

  (** Equalities to unit elements from composition of different inclusion
    and projections. *)
  Definition BinDirectSumUnit1 {a b : A} (B : BinDirectSumCone a b) :
    (BinDirectSumIn1 B) ;; (BinDirectSumPr2 B)
    = PrecategoryWithAbgrops_unel A a b
    := isBinDirectSumCone_unit1 (BinDirectSum_isBinDirectSum B).
  Definition BinDirectSumUnit2 {a b : A} (B : BinDirectSumCone a b) :
    (BinDirectSumIn2 B) ;; (BinDirectSumPr1 B)
    = PrecategoryWithAbgrops_unel A b a
    := isBinDirectSumCone_unit2 (BinDirectSum_isBinDirectSum B).

  (** Sum of projections followed by inclusions is identity. *)
  Definition BinDirectSumId {a b : A} (B : BinDirectSumCone a b)
    := isBinDirectSumCone_id (BinDirectSum_isBinDirectSum B).

  (** Construction of BinCoproduct and BinProduct from BinDirectSum. *)
  Definition BinDirectSum_isBinCoproduct {a b : A} (B : BinDirectSumCone a b) :
    isBinCoproductCocone A a b B (BinDirectSumIn1 B) (BinDirectSumIn2 B)
    := pr1 (BinDirectSum_isBinDirectSum B).
  Definition BinDirectSum_BinCoproduct {a b : A} (B : BinDirectSumCone a b) :
    BinCoproductCocone A a b.
  Proof.
    apply (mk_BinCoproductCocone A a b B (BinDirectSumIn1 B)
                                 (BinDirectSumIn2 B)).
    apply (BinDirectSum_isBinCoproduct B).
  Defined.

  Definition BinDirectSum_isBinProduct {a b : A} (B : BinDirectSumCone a b) :
    isBinProductCone A a b B (BinDirectSumPr1 B) (BinDirectSumPr2 B)
    := pr1 (pr2 (BinDirectSum_isBinDirectSum B)).
  Definition BinDirectSum_BinProduct {a b : A} (B : BinDirectSumCone a b) :
    BinProductCone A a b.
  Proof.
    apply (mk_BinProductCone A a b B (BinDirectSumPr1 B) (BinDirectSumPr2 B)).
    apply (BinDirectSum_isBinProduct B).
  Defined.

  (** An arrow to BinDirectSum and arrow from BinDirectSum. *)
  Definition ToBinDirectSum {a b : A} (B : BinDirectSumCone a b) {c : A}
             (f : c --> a) (g : c --> b) :
    A⟦c, B⟧ := BinProductArrow A (BinDirectSum_BinProduct B) f g.
  Definition FromBinDirectSum {a b : A} (B : BinDirectSumCone a b) {c : A}
             (f : a --> c) (g : b --> c) :
    A⟦B, c⟧ := BinCoproductArrow A (BinDirectSum_BinCoproduct B) f g.

  (** Commutativity of BinDirectSum. *)
  Definition BinDirectSumIn1Commutes {a b : A} (B : BinDirectSumCone a b) :
    Π (c : A) (f : a --> c) (g : b --> c),
      (BinDirectSumIn1 B) ;; (FromBinDirectSum B f g) = f.
  Proof.
    intros c f g.
    apply (BinCoproductIn1Commutes A a b (BinDirectSum_BinCoproduct B) c f g).
  Defined.

  Definition BinDirectSumIn2Commutes {a b : A} (B : BinDirectSumCone a b) :
    Π (c : A) (f : a --> c) (g : b --> c),
      (BinDirectSumIn2 B) ;; (FromBinDirectSum B f g) = g.
  Proof.
    intros c f g.
    apply (BinCoproductIn2Commutes A a b (BinDirectSum_BinCoproduct B) c f g).
  Defined.

  Definition BinDirectSumPr1Commutes {a b : A} (B : BinDirectSumCone a b) :
    Π (c : A) (f : c --> a) (g : c --> b),
      (ToBinDirectSum B f g) ;; (BinDirectSumPr1 B) = f.
  Proof.
    intros c f g.
    apply (BinProductPr1Commutes A a b (BinDirectSum_BinProduct B) c f g).
  Defined.

  Definition BinDirectSumPr2Commutes {a b : A} (B : BinDirectSumCone a b) :
    Π (c : A) (f : c --> a) (g : c --> b),
      (ToBinDirectSum B f g) ;; (BinDirectSumPr2 B) = g.
  Proof.
    intros c f g.
    apply (BinProductPr2Commutes A a b (BinDirectSum_BinProduct B) c f g).
  Defined.

  (** Uniqueness of arrow to and from BinDirectSum using the BinProduct
    and BinCoproduct structures. *)
  Definition ToBinDirectSumUnique {a b : A} (B : BinDirectSumCone a b) {c : A}
    (f : c --> a) (g : c --> b) (k : c --> B) :
    k ;; BinDirectSumPr1 B = f -> k ;; BinDirectSumPr2 B = g ->
    k = ToBinDirectSum B f g
    := BinProductArrowUnique _ _ _ (BinDirectSum_BinProduct B) c f g k.
  Definition FromBinDirectSumUnique {a b : A} (B : BinDirectSumCone a b) {c : A}
    (f : a --> c) (g : b --> c) (k : B --> c) :
    BinDirectSumIn1 B ;; k = f -> BinDirectSumIn2 B ;; k = g ->
    k = FromBinDirectSum B f g
    := BinCoproductArrowUnique _ _ _ (BinDirectSum_BinCoproduct B) c f g k.

  (** The following definitions give a formula for the unique morphisms to and
    from the BinDirectSum. These formulas are important when one uses
    bindirectsums. The formulas are

    to bindirectsum unique arrow     =   f ;; in1 + g ;; in2
    from bindirectsum unique arrow   =   pr1 ;; f + pr2 ;; g
   *)
  Definition ToBinDirectSumFormula {a b : A} (B : BinDirectSumCone a b) {c : A}
             (f : c --> a) (g : c --> b) : A⟦c, B⟧
    := (PrecategoryWithAbgrops_op A c B)
         (f ;; BinDirectSumIn1 B) (g ;; BinDirectSumIn2 B).
  Definition FromBinDirectSumFormula {a b : A} (B : BinDirectSumCone a b)
             {c : A} (f : a --> c) (g : b --> c) : A⟦B, c⟧
    := (PrecategoryWithAbgrops_op A B c)
         (BinDirectSumPr1 B ;; f) (BinDirectSumPr2 B ;; g).

  (** Let us prove that these formulas indeed are the unique morphisms we
    claimed them to be. *)
  Lemma ToBinDirectSumFormulaUnique {a b : A} (B : BinDirectSumCone a b) {c : A}
        (f : c --> a) (g : c --> b) :
    ToBinDirectSumFormula B f g = ToBinDirectSum B f g.
  Proof.
    apply ToBinDirectSumUnique.
    unfold ToBinDirectSumFormula.
    unfold PrecategoryWithAbgrops_op.

    (* First commutativity. *)
    set (X := (PreAdditive_postmor_linear
                 A c B a (BinDirectSumPr1 B) (f ;; BinDirectSumIn1 B)
                 (g ;; BinDirectSumIn2 B))).
    unfold PrecategoryWithAbgrops_postmor in X.
    eapply pathscomp0. apply X.
    rewrite <- assoc. rewrite <- assoc.
    rewrite (BinDirectSumIdIn1 B).
    rewrite id_right.
    rewrite (BinDirectSumUnit2 B).
    set (XX := PreAdditive_premor_0 A c b a g).
    unfold PrecategoryWithAbgrops_premor in XX.
    unfold PrecategoryWithAbgrops_unel.
    rewrite XX.
    apply (PrecategoryWithAbgrops_runax A c a).

    (** The other projection. *)
    unfold ToBinDirectSumFormula.
    unfold PrecategoryWithAbgrops_op.
    simpl.
    set (X := (PreAdditive_postmor_linear
                 A c B b (BinDirectSumPr2 B) (f ;; BinDirectSumIn1 B)
                 (g ;; BinDirectSumIn2 B))).
    unfold PrecategoryWithAbgrops_postmor in X.
    eapply pathscomp0. apply X.
    rewrite <- assoc. rewrite <- assoc.
    rewrite (BinDirectSumIdIn2 B).
    rewrite (BinDirectSumUnit1 B).
    rewrite id_right.
    set (XX := PreAdditive_premor_0 A c a b f).
    unfold PrecategoryWithAbgrops_premor in XX.
    unfold PrecategoryWithAbgrops_unel.
    rewrite XX.
    apply (PrecategoryWithAbgrops_lunax A c b).
  Defined.
  Opaque ToBinDirectSumFormulaUnique.

  Lemma FromBinDirectSumFormulaUnique {a b : A} (B : BinDirectSumCone a b)
        {c : A} (f : a --> c) (g : b --> c) :
    FromBinDirectSumFormula B f g = FromBinDirectSum B f g.
  Proof.
    unfold FromBinDirectSumFormula.
    apply FromBinDirectSumUnique.

    (* First commutativity *)
    set (X := (PreAdditive_premor_linear
                 A a B c (BinDirectSumIn1 B) (BinDirectSumPr1 B ;; f)
                 (BinDirectSumPr2 B ;; g))).
    unfold PrecategoryWithAbgrops_premor in X.
    eapply pathscomp0. apply X.
    rewrite assoc. rewrite assoc.
    rewrite (BinDirectSumIdIn1 B).
    rewrite (BinDirectSumUnit1 B).
    rewrite id_left.
    set (XX := PreAdditive_postmor_0 A a b c g).
    unfold PrecategoryWithAbgrops_postmor in XX.
    unfold PrecategoryWithAbgrops_unel.
    rewrite XX.
    apply (PrecategoryWithAbgrops_runax A a c).

    (* Second commutativity *)
    set (X := (PreAdditive_premor_linear
                 A b B c (BinDirectSumIn2 B) (BinDirectSumPr1 B ;; f)
                 (BinDirectSumPr2 B ;; g))).
    unfold PrecategoryWithAbgrops_premor in X.
    eapply pathscomp0. apply X.
    rewrite assoc. rewrite assoc.
    rewrite (BinDirectSumIdIn2 B).
    rewrite (BinDirectSumUnit2 B).
    rewrite id_left.
    set (XX := PreAdditive_postmor_0 A b a c f).
    unfold PrecategoryWithAbgrops_postmor in XX.
    unfold PrecategoryWithAbgrops_unel.
    rewrite XX.
    apply (PrecategoryWithAbgrops_lunax A b c).
  Defined.
  Opaque FromBinDirectSumFormulaUnique.

  (** The following definitions give 2 ways to construct a morphisms
    a ⊕ c --> b ⊕ d from two morphisms f : a --> b and g : c --> d , by using
    the binary direct sums as a product and as a coproduct. *)
  Definition BinDirectSumIndAr {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) :
    A⟦B1, B2⟧ := ToBinDirectSum B2 ((BinDirectSumPr1 B1) ;; f)
                                ((BinDirectSumPr2 B1) ;; g).

  Definition BinDirectSumIndAr' {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) :
    A⟦B1, B2⟧ := FromBinDirectSum B1 (f ;; (BinDirectSumIn1 B2))
                                  (g ;; (BinDirectSumIn2 B2)).

  (** Both of the above morphisms are given by the following formula. *)
  Definition BinDirectSumIndArFormula {a b c d: A}  (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) : A⟦B1, B2⟧
    := (PrecategoryWithAbgrops_op A B1 B2)
         (BinDirectSumPr1 B1 ;; f ;; BinDirectSumIn1 B2)
         (BinDirectSumPr2 B1 ;; g ;; BinDirectSumIn2 B2).

  Lemma BinDirectSumIndArEq1 {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) :
    BinDirectSumIndAr f g B1 B2 = BinDirectSumIndArFormula f g B1 B2.
  Proof.
    unfold BinDirectSumIndAr.
    rewrite <- ToBinDirectSumFormulaUnique.
    unfold ToBinDirectSumFormula.
    unfold BinDirectSumIndArFormula.
    apply idpath.
  Defined.
  Opaque BinDirectSumIndArEq1.

  Lemma BinDirectSumIndArEq2 {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) :
    BinDirectSumIndAr' f g B1 B2 = BinDirectSumIndArFormula f g B1 B2.
  Proof.
    unfold BinDirectSumIndAr'.
    rewrite <- FromBinDirectSumFormulaUnique.
    unfold FromBinDirectSumFormula.
    unfold BinDirectSumIndArFormula.
    rewrite assoc. rewrite assoc.
    apply idpath.
  Defined.
  Opaque BinDirectSumIndArEq2.

  (** Thus we have equality. *)
  Definition BinDirectSumIndArEq {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) :
    BinDirectSumIndAr f g B1 B2 = BinDirectSumIndAr' f g B1 B2.
  Proof.
    rewrite -> BinDirectSumIndArEq1.
    rewrite -> BinDirectSumIndArEq2.
    apply idpath.
  Defined.
  Opaque BinDirectSumIndArEq.

End def_bindirectsums.
