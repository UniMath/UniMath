(** Direct definition of binary biproducts using preadditive categories. *)
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


(** BinBiProduct is at the same time product and coproduct of the underlying
  objects together with the following equalities

    i1 ;; p1 = identity  and   i2 ;; p2 = identity
    i1 ;; p2 = unit      and   i2 ;; p1 = unit
            p1 ;; i1 + p2 ;; i2 = identity
*)
Section def_binbiproducts.

  Variable A : PreAdditive.

  (** Definition of isBinBiProductCone *)
  Definition isBinBiproductCone (a b co : A) (i1 : a --> co) (i2 : b --> co)
             (p1 : co --> a) (p2 : co --> b) :=
    (isBinCoproductCocone A a b co i1 i2)
      × (isBinProductCone A a b co p1 p2)
      × (i1 ;; p1 = identity a) × (i2 ;; p2 = identity b)
      × (i1 ;; p2 = (PrecategoryWithAbgrops_unel A a b))
      × (i2 ;; p1 = (PrecategoryWithAbgrops_unel A b a))
      × ((PrecategoryWithBinOps_binop A co co) (p1 ;; i1) (p2 ;; i2) =
         identity co).
  Definition isBinBiproductCone_coproduct {a b co : A}
             {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinBiproductCone a b co i1 i2 p1 p2) :
    isBinCoproductCocone A a b co i1 i2 := dirprod_pr1 B.
  Definition isBinBiproductCone_product {a b co : A}
             {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinBiproductCone a b co i1 i2 p1 p2) :
    isBinProductCone A a b co p1 p2 := dirprod_pr1 (dirprod_pr2 B).
  Definition isBinBiproductCone_idin1 {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinBiproductCone a b co i1 i2 p1 p2) :
    i1 ;; p1 = identity a := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 B)).
  Definition isBinBiproductCone_idin2 {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinBiproductCone a b co i1 i2 p1 p2) : i2 ;; p2 = identity b
    := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 B))).
  Definition isBinBiproductCone_unit1 {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinBiproductCone a b co i1 i2 p1 p2)
    := pr1 (pr2 (pr2 (pr2 (pr2 B)))).
  Definition isBinBiproductCone_unit2 {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinBiproductCone a b co i1 i2 p1 p2)
    := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 B))))).
  Definition isBinBiproductCone_id {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b}
             (B : isBinBiproductCone a b co i1 i2 p1 p2)
    := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 B))))).


  (** The following definition constructs isBinBiProductCone from data. *)
  Definition mk_isBinBiProductCone (a b co : A)
             (i1 : a --> co) (i2 : b --> co) (p1 : co --> a) (p2 : co --> b)
             (isBC : isBinCoproductCocone A a b co i1 i2)
             (isBP : isBinProductCone A a b co p1 p2)
             (H1 : i1 ;; p1 = identity a) (H2 : i2 ;; p2 = identity b)
             (H3 : i1 ;; p2 = (PrecategoryWithAbgrops_unel A a b))
             (H4 : i2 ;; p1 = (PrecategoryWithAbgrops_unel A b a))
             (H5 : (PrecategoryWithBinOps_binop A co co)
                     (p1 ;; i1) (p2 ;; i2) = identity co)
    : isBinBiproductCone a b co i1 i2 p1 p2
    := isBC,,(isBP,,(H1,,(H2,,(H3,,(H4,,H5))))).

  (** Definition of BinBiproducts. *)
  Definition BinBiproductCone (a b : A) : UU :=
    Σ coab : (Σ co : A, a --> co × b --> co × co --> a × co --> b),
             isBinBiproductCone
               a b (pr1 coab) (pr1 (pr2 coab))
               (pr1 (pr2 (pr2 coab)))
               (pr1 (pr2 (pr2 (pr2 coab))))
               (pr2 (pr2 (pr2 (pr2 coab)))).

  (** Construction of BinBiProductCone. *)
  Definition mk_BinBiproductCone (a b co : A)
             (i1 : a --> co) (i2 : b --> co) (p1 : co --> a) (p2 : co --> b)
             (H :  isBinBiproductCone a b co i1 i2 p1 p2) :
    BinBiproductCone a b := tpair _ (tpair _ co (i1,,(i2,,(p1,,p2)))) H.

  (** BinBiProduct in categories. *)
  Definition BinBiproducts := forall (a b : A), BinBiproductCone a b.
  Definition has_BinBiproducts := ishinh BinBiproducts.

  (** The biproduct object. *)
  Definition BinBiproductConeOb {a b : A} (B : BinBiproductCone a b) :
    A := pr1 (pr1 B).
  Coercion BinBiproductConeOb : BinBiproductCone >-> ob.

  (** Inclusions and projections to and from the biproduct. *)
  Definition BinBiproductIn1 {a b : A} (B : BinBiproductCone a b) :
    A⟦a, B⟧ := pr1 (pr2 (pr1 B)).
  Definition BinBiproductIn2 {a b : A} (B : BinBiproductCone a b) :
    A⟦b, B⟧ := pr1 (pr2 (pr2 (pr1 B))).
  Definition BinBiproductPr1 {a b : A} (B : BinBiproductCone a b) :
    A⟦B, a⟧ := pr1 (pr2 (pr2 (pr2 (pr1 B)))).
  Definition BinBiproductPr2 {a b : A} (B : BinBiproductCone a b) :
    A⟦B, b⟧ := pr2 (pr2 (pr2 (pr2 (pr1 B)))).

  (** Returns the isBinBiproduct property. *)
  Definition BinBiproduct_isBinBiproduct {a b : A} (B : BinBiproductCone a b) :
    isBinBiproductCone a b B (BinBiproductIn1 B) (BinBiproductIn2 B)
                       (BinBiproductPr1 B) (BinBiproductPr2 B)
    := pr2 B.

  (** Equalities between identity and compositions of inclusions and
    projections. *)
  Definition BinBiproductIdIn1 {a b : A} (B : BinBiproductCone a b) :
    (BinBiproductIn1 B) ;; (BinBiproductPr1 B) = identity a
    := isBinBiproductCone_idin1 (BinBiproduct_isBinBiproduct B).
  Definition BinBiproductIdIn2 {a b : A} (B : BinBiproductCone a b) :
    (BinBiproductIn2 B) ;; (BinBiproductPr2 B) = identity b
    := isBinBiproductCone_idin2 (BinBiproduct_isBinBiproduct B).

  (** Equalities to unit elements from composition of different inclusion
    and projections. *)
  Definition BinBiproductUnit1 {a b : A} (B : BinBiproductCone a b) :
    (BinBiproductIn1 B) ;; (BinBiproductPr2 B)
    = PrecategoryWithAbgrops_unel A a b
    := isBinBiproductCone_unit1 (BinBiproduct_isBinBiproduct B).
  Definition BinBiproductUnit2 {a b : A} (B : BinBiproductCone a b) :
    (BinBiproductIn2 B) ;; (BinBiproductPr1 B)
    = PrecategoryWithAbgrops_unel A b a
    := isBinBiproductCone_unit2 (BinBiproduct_isBinBiproduct B).

  (** Sum of projections followed by inclusions is identity. *)
  Definition BinBiproductId {a b : A} (B : BinBiproductCone a b)
    := isBinBiproductCone_id (BinBiproduct_isBinBiproduct B).

  (** Construction of BinCoproduct and BinProduct from BinBiproduct. *)
  Definition BinBiproduct_isBinCoproduct {a b : A} (B : BinBiproductCone a b) :
    isBinCoproductCocone A a b B (BinBiproductIn1 B) (BinBiproductIn2 B)
    := pr1 (BinBiproduct_isBinBiproduct B).
  Definition BinBiproduct_BinCoproduct {a b : A} (B : BinBiproductCone a b) :
    BinCoproductCocone A a b.
  Proof.
    apply (mk_BinCoproductCocone A a b B (BinBiproductIn1 B)
                                 (BinBiproductIn2 B)).
    apply (BinBiproduct_isBinCoproduct B).
  Defined.

  Definition BinBiproduct_isBinProduct {a b : A} (B : BinBiproductCone a b) :
    isBinProductCone A a b B (BinBiproductPr1 B) (BinBiproductPr2 B)
    := pr1 (pr2 (BinBiproduct_isBinBiproduct B)).
  Definition BinBiproduct_BinProduct {a b : A} (B : BinBiproductCone a b) :
    BinProductCone A a b.
  Proof.
    apply (mk_BinProductCone A a b B (BinBiproductPr1 B) (BinBiproductPr2 B)).
    apply (BinBiproduct_isBinProduct B).
  Defined.

  (** An arrow to BinBiproduct and arrow from BinBiproduct. *)
  Definition ToBinBiproduct {a b : A} (B : BinBiproductCone a b) {c : A}
             (f : c --> a) (g : c --> b) :
    A⟦c, B⟧ := BinProductArrow A (BinBiproduct_BinProduct B) f g.
  Definition FromBinBiproduct {a b : A} (B : BinBiproductCone a b) {c : A}
             (f : a --> c) (g : b --> c) :
    A⟦B, c⟧ := BinCoproductArrow A (BinBiproduct_BinCoproduct B) f g.

  (** Commutativity of BinBiProduct. *)
  Definition BinBiproductIn1Commutes {a b : A} (B : BinBiproductCone a b) :
    forall (c : A) (f : a --> c) (g : b --> c),
      (BinBiproductIn1 B) ;; (FromBinBiproduct B f g) = f.
  Proof.
    intros c f g.
    apply (BinCoproductIn1Commutes A a b (BinBiproduct_BinCoproduct B) c f g).
  Defined.

  Definition BinBiproductIn2Commutes {a b : A} (B : BinBiproductCone a b) :
    forall (c : A) (f : a --> c) (g : b --> c),
      (BinBiproductIn2 B) ;; (FromBinBiproduct B f g) = g.
  Proof.
    intros c f g.
    apply (BinCoproductIn2Commutes A a b (BinBiproduct_BinCoproduct B) c f g).
  Defined.

  Definition BinBiproductPr1Commutes {a b : A} (B : BinBiproductCone a b) :
    forall (c : A) (f : c --> a) (g : c --> b),
      (ToBinBiproduct B f g) ;; (BinBiproductPr1 B) = f.
  Proof.
    intros c f g.
    apply (BinProductPr1Commutes A a b (BinBiproduct_BinProduct B) c f g).
  Defined.

  Definition BinBiproductPr2Commutes {a b : A} (B : BinBiproductCone a b) :
    forall (c : A) (f : c --> a) (g : c --> b),
      (ToBinBiproduct B f g) ;; (BinBiproductPr2 B) = g.
  Proof.
    intros c f g.
    apply (BinProductPr2Commutes A a b (BinBiproduct_BinProduct B) c f g).
  Defined.

  (** Uniqueness of arrow to and from BinBiproduct using the BinProduct
    and BinCoproduct structures. *)
  Definition ToBinBiproductUnique {a b : A} (B : BinBiproductCone a b) {c : A}
    (f : c --> a) (g : c --> b) (k : c --> B) :
    k ;; BinBiproductPr1 B = f -> k ;; BinBiproductPr2 B = g ->
    k = ToBinBiproduct B f g
    := BinProductArrowUnique _ _ _ (BinBiproduct_BinProduct B) c f g k.
  Definition FromBinBiproductUnique {a b : A} (B : BinBiproductCone a b) {c : A}
    (f : a --> c) (g : b --> c) (k : B --> c) :
    BinBiproductIn1 B ;; k = f -> BinBiproductIn2 B ;; k = g ->
    k = FromBinBiproduct B f g
    := BinCoproductArrowUnique _ _ _ (BinBiproduct_BinCoproduct B) c f g k.

  (** The following definitions give a formula for the unique morphisms to and
    from the BinBiProduct. These formulas are important when one uses
    binbiproducts. The formulas are

    to binbiproduct unique arrow     =   f ;; in1 + g ;; in2
    from binbiproduct unique arrow   =   pr1 ;; f + pr2 ;; g
   *)
  Definition ToBinBiproductFormula {a b : A} (B : BinBiproductCone a b) {c : A}
             (f : c --> a) (g : c --> b) : A⟦c, B⟧
    := (PrecategoryWithAbgrops_op A c B)
         (f ;; BinBiproductIn1 B) (g ;; BinBiproductIn2 B).
  Definition FromBinBiproductFormula {a b : A} (B : BinBiproductCone a b)
             {c : A} (f : a --> c) (g : b --> c) : A⟦B, c⟧
    := (PrecategoryWithAbgrops_op A B c)
         (BinBiproductPr1 B ;; f) (BinBiproductPr2 B ;; g).

  (** Let us prove that these formulas indeed are the unique morphisms we
    claimed them to be. *)
  Lemma ToBinBiproductFormulaUnique {a b : A} (B : BinBiproductCone a b) {c : A}
        (f : c --> a) (g : c --> b) :
    ToBinBiproductFormula B f g = ToBinBiproduct B f g.
  Proof.
    apply ToBinBiproductUnique.
    unfold ToBinBiproductFormula.
    unfold PrecategoryWithAbgrops_op.

    (* First commutativity. *)
    set (X := (PreAdditive_postmor_linear
                 A c B a (BinBiproductPr1 B) (f ;; BinBiproductIn1 B)
                 (g ;; BinBiproductIn2 B))).
    unfold PrecategoryWithAbgrops_postmor in X.
    eapply pathscomp0. apply X.
    rewrite <- assoc. rewrite <- assoc.
    rewrite (BinBiproductIdIn1 B).
    rewrite id_right.
    rewrite (BinBiproductUnit2 B).
    set (XX := PreAdditive_premor_0 A c b a g).
    unfold PrecategoryWithAbgrops_premor in XX.
    unfold PrecategoryWithAbgrops_unel.
    rewrite XX.
    apply (PrecategoryWithAbgrops_runax A c a).

    (** The other projection. *)
    unfold ToBinBiproductFormula.
    unfold PrecategoryWithAbgrops_op.
    simpl.
    set (X := (PreAdditive_postmor_linear
                 A c B b (BinBiproductPr2 B) (f ;; BinBiproductIn1 B)
                 (g ;; BinBiproductIn2 B))).
    unfold PrecategoryWithAbgrops_postmor in X.
    eapply pathscomp0. apply X.
    rewrite <- assoc. rewrite <- assoc.
    rewrite (BinBiproductIdIn2 B).
    rewrite (BinBiproductUnit1 B).
    rewrite id_right.
    set (XX := PreAdditive_premor_0 A c a b f).
    unfold PrecategoryWithAbgrops_premor in XX.
    unfold PrecategoryWithAbgrops_unel.
    rewrite XX.
    apply (PrecategoryWithAbgrops_lunax A c b).
  Defined.

  Lemma FromBinBiproductFormulaUnique {a b : A} (B : BinBiproductCone a b)
        {c : A} (f : a --> c) (g : b --> c) :
    FromBinBiproductFormula B f g = FromBinBiproduct B f g.
  Proof.
    unfold FromBinBiproductFormula.
    apply FromBinBiproductUnique.

    (* First commutativity *)
    set (X := (PreAdditive_premor_linear
                 A a B c (BinBiproductIn1 B) (BinBiproductPr1 B ;; f)
                 (BinBiproductPr2 B ;; g))).
    unfold PrecategoryWithAbgrops_premor in X.
    eapply pathscomp0. apply X.
    rewrite assoc. rewrite assoc.
    rewrite (BinBiproductIdIn1 B).
    rewrite (BinBiproductUnit1 B).
    rewrite id_left.
    set (XX := PreAdditive_postmor_0 A a b c g).
    unfold PrecategoryWithAbgrops_postmor in XX.
    unfold PrecategoryWithAbgrops_unel.
    rewrite XX.
    apply (PrecategoryWithAbgrops_runax A a c).

    (* Second commutativity *)
    set (X := (PreAdditive_premor_linear
                 A b B c (BinBiproductIn2 B) (BinBiproductPr1 B ;; f)
                 (BinBiproductPr2 B ;; g))).
    unfold PrecategoryWithAbgrops_premor in X.
    eapply pathscomp0. apply X.
    rewrite assoc. rewrite assoc.
    rewrite (BinBiproductIdIn2 B).
    rewrite (BinBiproductUnit2 B).
    rewrite id_left.
    set (XX := PreAdditive_postmor_0 A b a c f).
    unfold PrecategoryWithAbgrops_postmor in XX.
    unfold PrecategoryWithAbgrops_unel.
    rewrite XX.
    apply (PrecategoryWithAbgrops_lunax A b c).
  Defined.

  (** The following definitions give 2 ways to construct a morphisms
    a ⊕ c --> b ⊕ d from two morphisms f : a --> b and g : c --> d , by using
    the binary biproducts as a product and as a coproduct. *)
  Definition BinBiproductIndAr {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinBiproductCone a c) (B2 : BinBiproductCone b d) :
    A⟦B1, B2⟧ := ToBinBiproduct B2 ((BinBiproductPr1 B1) ;; f)
                                ((BinBiproductPr2 B1) ;; g).

  Definition BinBiproductIndAr' {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinBiproductCone a c) (B2 : BinBiproductCone b d) :
    A⟦B1, B2⟧ := FromBinBiproduct B1 (f ;; (BinBiproductIn1 B2))
                                  (g ;; (BinBiproductIn2 B2)).

  (** Both of the above morphisms are given by the following formula. *)
  Definition BinBiproductIndArFormula {a b c d: A}  (f : a --> b) (g : c --> d)
             (B1 : BinBiproductCone a c) (B2 : BinBiproductCone b d) : A⟦B1, B2⟧
    := (PrecategoryWithAbgrops_op A B1 B2)
         (BinBiproductPr1 B1 ;; f ;; BinBiproductIn1 B2)
         (BinBiproductPr2 B1 ;; g ;; BinBiproductIn2 B2).

  Lemma BinBiproductIndArEq1 {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinBiproductCone a c) (B2 : BinBiproductCone b d) :
    BinBiproductIndAr f g B1 B2 = BinBiproductIndArFormula f g B1 B2.
  Proof.
    unfold BinBiproductIndAr.
    rewrite <- ToBinBiproductFormulaUnique.
    unfold ToBinBiproductFormula.
    unfold BinBiproductIndArFormula.
    apply idpath.
  Defined.

  Lemma BinBiproductIndArEq2 {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinBiproductCone a c) (B2 : BinBiproductCone b d) :
    BinBiproductIndAr' f g B1 B2 = BinBiproductIndArFormula f g B1 B2.
  Proof.
    unfold BinBiproductIndAr'.
    rewrite <- FromBinBiproductFormulaUnique.
    unfold FromBinBiproductFormula.
    unfold BinBiproductIndArFormula.
    rewrite assoc. rewrite assoc.
    apply idpath.
  Defined.

  (** Thus we have equality. *)
  Definition BinBiproductIndArEq {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinBiproductCone a c) (B2 : BinBiproductCone b d) :
    BinBiproductIndAr f g B1 B2 = BinBiproductIndAr' f g B1 B2.
  Proof.
    rewrite -> BinBiproductIndArEq1.
    rewrite -> BinBiproductIndArEq2.
    apply idpath.
  Defined.

End def_binbiproducts.
