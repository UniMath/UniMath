(** ** Direct definition of binary direct sum using preadditive categories. *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.BinaryOperations.
Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.zero.

Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.


(** BinDirectSum is at the same time product and coproduct of the underlying objects together with
    the following equalities

    i1 ;; p1 = identity  and   i2 ;; p2 = identity
    i1 ;; p2 = unit      and   i2 ;; p1 = unit
            p1 ;; i1 + p2 ;; i2 = identity
*)
Section def_bindirectsums.

  Variable A : PreAdditive.
  Hypothesis hs : has_homsets A.

  (** Definition of isBinDirectSumCone *)
  Definition isBinDirectSumCone (a b co : A) (i1 : a --> co) (i2 : b --> co)
             (p1 : co --> a) (p2 : co --> b) : UU :=
    (isBinCoproductCocone A a b co i1 i2)
      × (isBinProductCone A a b co p1 p2)
      × (i1 ;; p1 = identity a) × (i2 ;; p2 = identity b)
      × (i1 ;; p2 = (to_unel a b)) × (i2 ;; p1 = (to_unel b a))
      × ((to_binop co co) (p1 ;; i1) (p2 ;; i2) = identity co).

  Lemma isaprop_isBinDirectSumCone {a b co : A} {i1 : a --> co} {i2 : b --> co}
        {p1 : co --> a} {p2 : co --> b} :
    isaprop (isBinDirectSumCone a b co i1 i2 p1 p2).
  Proof.
    apply isapropdirprod.
    - apply isaprop_isBinCoproductCocone.
    - apply isapropdirprod.
      + apply isaprop_isBinProductCone.
      + apply isapropdirprod.
        * apply hs.
        * apply isapropdirprod.
          -- apply hs.
          -- apply isapropdirprod.
             ++ apply hs.
             ++ apply isapropdirprod.
                ** apply hs.
                ** apply hs.
  Qed.

  Definition to_isBinCoproductCocone {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b} (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    isBinCoproductCocone A a b co i1 i2 := dirprod_pr1 B.

  Definition to_isBinProductCone {a b co : A} {i1 : a --> co} {i2 : b --> co}
             {p1 : co --> a} {p2 : co --> b} (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    isBinProductCone A a b co p1 p2 := dirprod_pr1 (dirprod_pr2 B).

  Definition to_IdIn1 {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    i1 ;; p1 = identity a := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 B)).

  Definition to_IdIn2 {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    i2 ;; p2 = identity b := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 B))).

  Definition to_Unel1 {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    i1 ;; p2 = (to_unel a b) := pr1 (pr2 (pr2 (pr2 (pr2 B)))).

  Definition to_Unel2 {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    i2 ;; p1 = (to_unel b a) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 B))))).

  Definition to_BinOpId {a b co : A} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSumCone a b co i1 i2 p1 p2) :
    (to_binop co co) (p1 ;; i1) (p2 ;; i2) = identity co := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 B))))).


  (** The following definition constructs isBinDirectSumCone from data. *)
  Definition mk_isBinDirectSumCone (a b co : A)
             (i1 : a --> co) (i2 : b --> co) (p1 : co --> a) (p2 : co --> b)
             (isBC : isBinCoproductCocone A a b co i1 i2)
             (isBP : isBinProductCone A a b co p1 p2)
             (H1 : i1 ;; p1 = identity a) (H2 : i2 ;; p2 = identity b)
             (H3 : i1 ;; p2 = (to_unel a b)) (H4 : i2 ;; p1 = (to_unel b a))
             (H5 : (to_binop co co) (p1 ;; i1) (p2 ;; i2) = identity co)
    : isBinDirectSumCone a b co i1 i2 p1 p2 := isBC,,(isBP,,(H1,,(H2,,(H3,,(H4,,H5))))).

  (** Definition of BinDirectSums. *)
  Definition BinDirectSumCone (a b : A) : UU :=
    Σ coab : (Σ co : A, a --> co × b --> co × co --> a × co --> b),
             isBinDirectSumCone a b (pr1 coab) (pr1 (pr2 coab)) (pr1 (pr2 (pr2 coab)))
                                (pr1 (pr2 (pr2 (pr2 coab)))) (pr2 (pr2 (pr2 (pr2 coab)))).

  (** Construction of BinDirectSumCone. *)
  Definition mk_BinDirectSumCone (a b co : A) (i1 : a --> co) (i2 : b --> co)
             (p1 : co --> a) (p2 : co --> b) (H :  isBinDirectSumCone a b co i1 i2 p1 p2) :
    BinDirectSumCone a b := tpair _ (tpair _ co (i1,,(i2,,(p1,,p2)))) H.

  (** BinDirectSum in categories. *)
  Definition BinDirectSums : UU := Π (a b : A), BinDirectSumCone a b.

  Definition has_BinDirectSums : UU := ishinh BinDirectSums.

  (** The direct sum object. *)
  Definition BinDirectSumConeOb {a b : A} (B : BinDirectSumCone a b) : A := pr1 (pr1 B).
  Coercion BinDirectSumConeOb : BinDirectSumCone >-> ob.

  (** Accessor functions *)
  Definition to_In1 {a b : A} (B : BinDirectSumCone a b) : A⟦a, B⟧ := dirprod_pr1 (pr2 (pr1 B)).

  Definition to_In2 {a b : A} (B : BinDirectSumCone a b) : A⟦b, B⟧ :=
    dirprod_pr1 (dirprod_pr2 (pr2 (pr1 B))).

  Definition to_Pr1 {a b : A} (B : BinDirectSumCone a b) : A⟦B, a⟧ :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (pr2 (pr1 B)))).

  Definition to_Pr2 {a b : A} (B : BinDirectSumCone a b) : A⟦B, b⟧ :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (pr2 (pr1 B)))).

  (** Another coercion *)
  Definition BinDirectSum_isBinDirectSumCone {a b : A} (B : BinDirectSumCone a b) :
    isBinDirectSumCone a b B (to_In1 B) (to_In2 B) (to_Pr1 B) (to_Pr2 B) := pr2 B.
  Coercion BinDirectSum_isBinDirectSumCone : BinDirectSumCone >-> isBinDirectSumCone.

  (** Construction of BinCoproduct and BinProduct from BinDirectSum. *)
  Definition BinDirectSum_BinCoproduct {a b : A} (B : BinDirectSumCone a b) :
    BinCoproductCocone A a b.
  Proof.
    use (mk_BinCoproductCocone A a b B (to_In1 B) (to_In2 B)).
    exact (to_isBinCoproductCocone B).
  Defined.

  Definition BinDirectSum_BinProduct {a b : A} (B : BinDirectSumCone a b) : BinProductCone A a b.
  Proof.
    use (mk_BinProductCone A a b B (to_Pr1 B) (to_Pr2 B)).
    exact (to_isBinProductCone B).
  Defined.

  (** An arrow to BinDirectSum and arrow from BinDirectSum. *)
  Definition ToBinDirectSum {a b : A} (B : BinDirectSumCone a b) {c : A} (f : c --> a)
             (g : c --> b) : A⟦c, B⟧ := BinProductArrow A (BinDirectSum_BinProduct B) f g.

  Definition FromBinDirectSum {a b : A} (B : BinDirectSumCone a b) {c : A} (f : a --> c)
             (g : b --> c) : A⟦B, c⟧ := BinCoproductArrow A (BinDirectSum_BinCoproduct B) f g.

  (** Commutativity of BinDirectSum. *)
  Definition BinDirectSumIn1Commutes {a b : A} (B : BinDirectSumCone a b) :
    Π (c : A) (f : a --> c) (g : b --> c), (to_In1 B) ;; (FromBinDirectSum B f g) = f.
  Proof.
    intros c f g.
    apply (BinCoproductIn1Commutes A a b (BinDirectSum_BinCoproduct B) c f g).
  Qed.

  Definition BinDirectSumIn2Commutes {a b : A} (B : BinDirectSumCone a b) :
    Π (c : A) (f : a --> c) (g : b --> c), (to_In2 B) ;; (FromBinDirectSum B f g) = g.
  Proof.
    intros c f g.
    apply (BinCoproductIn2Commutes A a b (BinDirectSum_BinCoproduct B) c f g).
  Qed.

  Definition BinDirectSumPr1Commutes {a b : A} (B : BinDirectSumCone a b) :
    Π (c : A) (f : c --> a) (g : c --> b), (ToBinDirectSum B f g) ;; (to_Pr1 B) = f.
  Proof.
    intros c f g.
    apply (BinProductPr1Commutes A a b (BinDirectSum_BinProduct B) c f g).
  Qed.

  Definition BinDirectSumPr2Commutes {a b : A} (B : BinDirectSumCone a b) :
    Π (c : A) (f : c --> a) (g : c --> b), (ToBinDirectSum B f g) ;; (to_Pr2 B) = g.
  Proof.
    intros c f g.
    apply (BinProductPr2Commutes A a b (BinDirectSum_BinProduct B) c f g).
  Qed.

  (** Uniqueness of arrow to and from BinDirectSum using the BinProduct and BinCoproduct
      structures. *)
  Definition ToBinDirectSumUnique {a b : A} (B : BinDirectSumCone a b) {c : A} (f : c --> a)
             (g : c --> b) (k : c --> B) :
    k ;; to_Pr1 B = f -> k ;; to_Pr2 B = g -> k = ToBinDirectSum B f g :=
    BinProductArrowUnique _ _ _ (BinDirectSum_BinProduct B) c f g k.

  Definition FromBinDirectSumUnique {a b : A} (B : BinDirectSumCone a b) {c : A} (f : a --> c)
             (g : b --> c) (k : B --> c) :
    to_In1 B ;; k = f -> to_In2 B ;; k = g -> k = FromBinDirectSum B f g :=
    BinCoproductArrowUnique _ _ _ (BinDirectSum_BinCoproduct B) c f g k.

  (** Uniqueness of arrows to and from BinDirectSum *)
  Lemma ToBinDirectSumsEq {c d : A} (DS : BinDirectSumCone c d) {x : A} (k1 k2 : x --> DS) :
    k1 ;; to_Pr1 DS = k2 ;; to_Pr1 DS ->
    k1 ;; to_Pr2 DS = k2 ;; to_Pr2 DS -> k1 = k2.
  Proof.
    intros H1 H2.
    rewrite (ToBinDirectSumUnique DS (k1 ;; to_Pr1 DS) (k1 ;; to_Pr2 DS) k1).
    apply pathsinv0.
    apply ToBinDirectSumUnique.
    - apply pathsinv0. apply H1.
    - apply pathsinv0. apply H2.
    - apply idpath.
    - apply idpath.
  Qed.

  Lemma FromBinDirectSumsEq {c d : A} (DS : BinDirectSumCone c d) {x : A} (k1 k2 : DS --> x) :
    to_In1 DS ;; k1 = to_In1 DS ;; k2 -> to_In2 DS ;; k1 = to_In2 DS ;; k2 -> k1 = k2.
  Proof.
    intros H1 H2.
    rewrite (FromBinDirectSumUnique DS (to_In1 DS ;; k1) (to_In2 DS ;; k1) k1).
    apply pathsinv0.
    apply FromBinDirectSumUnique.
    - apply pathsinv0. apply H1.
    - apply pathsinv0. apply H2.
    - apply idpath.
    - apply idpath.
  Qed.

  (** The following definitions give a formula for the unique morphisms to and from the
      BinDirectSum. These formulas are important when one uses bindirectsums. The formulas are

      to bindirectsum unique arrow     =   f ;; in1 + g ;; in2
      from bindirectsum unique arrow   =   pr1 ;; f + pr2 ;; g
   *)
  Definition ToBinDirectSumFormula {a b : A} (B : BinDirectSumCone a b) {c : A} (f : c --> a)
             (g : c --> b) : A⟦c, B⟧ := (to_binop c B) (f ;; to_In1 B) (g ;; to_In2 B).

  Definition FromBinDirectSumFormula {a b : A} (B : BinDirectSumCone a b) {c : A} (f : a --> c)
             (g : b --> c) : A⟦B, c⟧ := (to_binop B c) (to_Pr1 B ;; f) (to_Pr2 B ;; g).

  (** Let us prove that these formulas indeed are the unique morphisms we claimed them to be. *)
  Lemma ToBinDirectSumFormulaUnique {a b : A} (B : BinDirectSumCone a b) {c : A} (f : c --> a)
        (g : c --> b) : ToBinDirectSumFormula B f g = ToBinDirectSum B f g.
  Proof.
    apply ToBinDirectSumUnique.
    - unfold ToBinDirectSumFormula.
      unfold to_binop.
      use (pathscomp0 (to_postmor_linear c (to_Pr1 B) (f ;; to_In1 B) (g ;; to_In2 B))).
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
      use (pathscomp0 (to_postmor_linear c (to_Pr2 B) (f ;; to_In1 B) (g ;; to_In2 B))).
      unfold to_postmor. repeat rewrite <- assoc.
      rewrite (to_IdIn2 B). rewrite (to_Unel1 B). rewrite id_right.
      set (XX := to_premor_unel A b f).
      unfold PrecategoriesWithAbgrops.to_premor in XX.
      unfold PrecategoriesWithAbgrops.to_unel.
      rewrite XX. clear XX.
      apply (to_lunax c b).
  Defined.
  Opaque ToBinDirectSumFormulaUnique.

  Lemma FromBinDirectSumFormulaUnique {a b : A} (B : BinDirectSumCone a b) {c : A} (f : a --> c)
        (g : b --> c) : FromBinDirectSumFormula B f g = FromBinDirectSum B f g.
  Proof.
    unfold FromBinDirectSumFormula.
    apply FromBinDirectSumUnique.
    - use (pathscomp0 (to_premor_linear c (to_In1 B) (to_Pr1 B ;; f) (to_Pr2 B ;; g))).
      unfold to_premor. repeat rewrite assoc.
      rewrite (to_IdIn1 B). rewrite (to_Unel1 B). rewrite id_left.
      set (XX := to_postmor_unel A a g).
      unfold to_postmor in XX.
      unfold to_unel.
      rewrite XX.
      apply (to_runax a c).
    - use (pathscomp0 (to_premor_linear c (to_In2 B) (to_Pr1 B ;; f) (to_Pr2 B ;; g))).
      unfold to_premor. repeat rewrite assoc.
      rewrite (to_IdIn2 B). rewrite (to_Unel2 B). rewrite id_left.
      set (XX := to_postmor_unel A b f).
      unfold to_postmor in XX.
      unfold to_unel.
      rewrite XX.
      apply (to_lunax b c).
  Defined.
  Opaque FromBinDirectSumFormulaUnique.

  (** The following definitions give 2 ways to construct a morphisms a ⊕ c --> b ⊕ d from two
      morphisms f : a --> b and g : c --> d , by using the binary direct sums as a product and as a
      coproduct. *)
  Definition BinDirectSumIndAr {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) :
    A⟦B1, B2⟧ := ToBinDirectSum B2 ((to_Pr1 B1) ;; f) ((to_Pr2 B1) ;; g).

  Definition BinDirectSumIndAr' {a b c d : A} (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) :
    A⟦B1, B2⟧ := FromBinDirectSum B1 (f ;; (to_In1 B2)) (g ;; (to_In2 B2)).

  (** Both of the above morphisms are given by the following formula. *)
  Definition BinDirectSumIndArFormula {a b c d: A}  (f : a --> b) (g : c --> d)
             (B1 : BinDirectSumCone a c) (B2 : BinDirectSumCone b d) :
    A⟦B1, B2⟧ := (to_binop B1 B2) (to_Pr1 B1 ;; f ;; to_In1 B2) (to_Pr2 B1 ;; g ;; to_In2 B2).

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

(** In1 and In2 are monics, and Pr1 and Pr2 are epis. *)
Section bindirectsums_monics_and_epis.

  Variable A : PreAdditive.

  Lemma to_In1_isMonic {a b : A} (B : BinDirectSumCone A a b) : isMonic (to_In1 A B).
  Proof.
    intros z f g H.
    apply (maponpaths (fun h : _ => h ;; (to_Pr1 A B))) in H.
    repeat rewrite <- assoc in H. rewrite (to_IdIn1 A B) in H.
    repeat rewrite id_right in H. apply H.
  Qed.

  Lemma to_In2_isMonic {a b : A} (B : BinDirectSumCone A a b) : isMonic (to_In2 A B).
  Proof.
    intros z f g H.
    apply (maponpaths (fun h : _ => h ;; (to_Pr2 A B))) in H.
    repeat rewrite <- assoc in H. rewrite (to_IdIn2 A B) in H.
    repeat rewrite id_right in H. apply H.
  Qed.

  Lemma to_Pr1_isEpi {a b : A} (B : BinDirectSumCone A a b) : isEpi (to_Pr1 A B).
  Proof.
    intros z f g H.
    apply (maponpaths (fun h : _ => (to_In1 A B) ;; h)) in H.
    repeat rewrite assoc in H. rewrite (to_IdIn1 A B) in H.
    repeat rewrite id_left in H. apply H.
  Qed.

  Lemma to_Pr2_isEpi {a b : A} (B : BinDirectSumCone A a b) : isEpi (to_Pr2 A B).
  Proof.
    intros z f g H.
    apply (maponpaths (fun h : _ => (to_In2 A B) ;; h)) in H.
    repeat rewrite assoc in H. rewrite (to_IdIn2 A B) in H.
    repeat rewrite id_left in H. apply H.
  Qed.

End bindirectsums_monics_and_epis.


(** If a PreAdditive category has BinProducts, then it has all direct sums. *)
Section bindirectsums_criteria.

  Variable A : PreAdditive.
  Hypothesis hs : has_homsets A.
  Variable Z : Zero A.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq1 {X Y : A} (P : BinProductCone A X Y) :
    BinProductArrow A P (identity X) (ZeroArrow Z X Y) ;; BinProductPr1 A P = identity _ .
  Proof.
    apply BinProductPr1Commutes.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq2 {X Y : A} (P : BinProductCone A X Y) :
    BinProductArrow A P (identity X) (ZeroArrow Z X Y) ;; BinProductPr2 A P = to_unel X Y.
  Proof.
    rewrite (PreAdditive_unel_zero A Z).
    apply BinProductPr2Commutes.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq3 {X Y : A} (P : BinProductCone A X Y) :
    BinProductArrow A P (ZeroArrow Z Y X) (identity _ ) ;; BinProductPr1 A P = to_unel Y X.
  Proof.
    rewrite (PreAdditive_unel_zero A Z).
    apply BinProductPr1Commutes.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq4 {X Y : A} (P : BinProductCone A X Y) :
    BinProductArrow A P (ZeroArrow Z Y X) (identity _ ) ;; BinProductPr2 A P = identity _ .
  Proof.
    apply BinProductPr2Commutes.
  Qed.

  Definition BinDirectSums_from_binproduct_bincoproducts_eq5 {X Y : A} (P : BinProductCone A X Y) :
    to_binop
      (BinProductObject A P) (BinProductObject A P)
      (BinProductPr1 A P ;; BinProductArrow A P(identity X) (ZeroArrow Z X Y))
      (BinProductPr2 A P ;; BinProductArrow A P (ZeroArrow Z Y X) (identity Y)) = identity _ .
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
             (P : BinProductCone A X Y) :
    isBinCoproductCocone A X Y (BinProductObject A P)
                         (BinProductArrow A P (identity X) (ZeroArrow Z X Y))
                         (BinProductArrow A P (ZeroArrow Z Y X) (identity Y)).
  Proof.
    use (mk_isBinCoproductCocone _ hs).
    intros c f g.
    use unique_exists.
    - exact (to_binop (BinProductObject A P) c (BinProductPr1 A P ;; f) (BinProductPr2 A P ;; g)).
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
             (P : BinProductCone A X Y) :
    isBinProductCone A X Y (BinProductObject A P) (BinProductPr1 A P) (BinProductPr2 A P).
  Proof.
    use (mk_isBinProductCone _ hs).
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

  Definition BinDirectSum_from_BinProduct {X Y : A} (P : BinProductCone A X Y) :
    BinDirectSumCone A X Y :=
    mk_BinDirectSumCone
      A X Y
      (BinProductObject A P)
      (BinProductArrow A P (identity X) (ZeroArrow Z X Y))
      (BinProductArrow A P (ZeroArrow Z Y X) (identity Y))
      (BinProductPr1 A P)
      (BinProductPr2 A P)
      (mk_isBinDirectSumCone
         _ _ _ _ _ _ _ _
         (BinDirectSums_from_binproduct_bincoproducts_isCoproduct P)
         (BinDirectSums_from_binproduct_bincoproducts_isProduct P)
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
