(** * FiveLemma *)
(** ** Contents
- Definition of structures for five lemma
- Five Lemma structure to opposite category
- Five Lemma
- Five Lemma for short exact sequences, [ShortExact]
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.Opp.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.opp_precat.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Morphisms.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.
Require Import UniMath.CategoryTheory.AbelianPushoutPullback.
Require Import UniMath.CategoryTheory.ShortExactSequences.
Require Import UniMath.CategoryTheory.PseudoElements.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.


(** ** FiveLemma
Five lemma says that if you have the following commutative diagram in an abelian category
                              C_1 --> C_2 --> C_3 --> C_4 --> C_5
                           f_1 |   f_2 |   f_3 |   f_4 |   f_5 |
                              D_1 --> D_2 --> D_3 --> D_4 --> D_5
where the rows are exact and the morphisms f_1, f_2, f_4, and f_5 are isomorphisms, then f_3 is an
isomorphism. Exactness of the first row means that an image of C_1 --> C_2 is a kernel of
C_2 --> C_3, an image of C_2 --> C_3 is a kernel of C_3 --> C_4, and an image of C_3 --> C_4 is a
kernel of C_4 --> C_5.

The idea of the proof is to show that f_3 is monic and epi, and thus is an isomorphism by
[monic_epi_is_iso]. To show that f_3 is monic, we use pseudo elements, [PseudoElem]. By [PEq_isMonic]
it suffices to show that if a is a pseudo element of C_3 is mapped to PZero by f_3, then a is
pseudo equal to PZero. We construct a pseudo element a' of C_1 which is mapped to a by the composite
 C_1 --> C_2 --> C_3. Since the first row is exact, this composite is Zero, and thus the pseudo
image is PZero.

We construct such a pseudo element a' as follows. First, by using exactness at C_3, and the fact
that a is mapped to Pzero by C_3 --> C_4 (because of commutativity of f_3 f_4 square and the fact
that f_4 is a monic), we obtain by [PEq_isExact] a pseudo element b' of C_2 which is mapped to a.
The image of b' under f_2 · D_2 --> D_3 is PZero by commutativity and the assumption that a is
mapped to PZero. By [PEq_isExact] we obtain aa pseudo element b'' of D_1 which is mapped to the
image of b' under f_2. By the fact that f_1 is an epi, we get a pseudo element a' which is mapped
to b''. Now, using commutativity of the square f_1 f_2, and the fact that f_2 is a monic, we get
that the image of a' under C_1 --> C_2 is b'. Hence a' is mapped to a, under C_1 --> C_2 --> C_3,
and the proof is complete.

See [FiveLemma_isMonic] for formalization of the above.

To show that f_3 is an epi we use opposite categories. First we transform the above diagram to
the following diagram in the opposite category
                              D_5 --> D_4 --> D_3 --> D_2 --> D_1
                           f_1 |   f_2 |   f_3 |   f_4 |   f_5 |
                              C_5 --> D_2 --> D_3 --> D_4 --> C_5
Thus, we need to show that f_3 is monic (here f_3 is the opposite morphism of f_3 in the first
diagram), to show that the original f_3 is epi! But this follows from the above proof. See
[FiveLemma_isEpi].

Finally, in [FiveLemma] we put [FiveLemma_isMonic] and [FiveLemma_isEpi] together, and prove the
lemma.



Five lemma is sometimes used for short exact sequences in which case C_1, C_5, D_1, and D_5 are
Zeros. Thus, f_1 and f_5 are automatically isomorphisms, and one only needs to show that f_2 and
f_4 are isomorphisms. This is proved in [ShortExactFiveLemma].
*)


(** ** Introduction
In this section we define the data needed to state the five lemma. The main definitions are
[FiveRow] and [FiveRowMorphism]. The first contains the data of a row in the five lemma, and the
second contains the data for a morphism between two rows.

[FiveRow] consists of Objects of the row, [FiveRowObs], differentials of the row [FiveRowDiffs],
equations that composition of consecutive differentials is zero, [FiveRowDiffsEq], and the fact
that the row is exact, [FiveRowExacts].

[FiveRowMorphism] takes arguments two [FiveRow] and consists of morphisms between the objects in
the rows, [FiveRowMors], and commutativity of the squares, [FiveRowMorsComm].
**)
Section five_lemma_data.

  Context {A : AbelianPreCat}.
  Variable hs : has_homsets A.

  (** ** Rows *)

  (** *** Objects for a row *)

  Definition FiveRowObs : UU := (ob A) × (ob A) × (ob A) × (ob A) × (ob A).

  Definition make_FiveRowObs (C1 C2 C3 C4 C5 : ob A) : FiveRowObs := (C1,,(C2,,(C3,,(C4,,C5)))).

  Definition FOb1 (FRO : FiveRowObs) : ob A := dirprod_pr1 FRO.

  Definition FOb2 (FRO : FiveRowObs) : ob A := dirprod_pr1 (dirprod_pr2 FRO).

  Definition FOb3 (FRO : FiveRowObs) : ob A := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 FRO)).

  Definition FOb4 (FRO : FiveRowObs) : ob A :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 FRO))).

  Definition FOb5 (FRO : FiveRowObs) : ob A :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 FRO))).


  (** *** Differentials for a row *)

  Definition FiveRowDiffs (FRO : FiveRowObs) : UU :=
    (A⟦FOb1 FRO, FOb2 FRO⟧) × (A⟦FOb2 FRO, FOb3 FRO⟧) × (A⟦FOb3 FRO, FOb4 FRO⟧)
                            × (A⟦FOb4 FRO, FOb5 FRO⟧).

  Definition make_FiveRowDiffs (FRO : FiveRowObs) (f1 : A⟦FOb1 FRO, FOb2 FRO⟧)
             (f2 : A⟦FOb2 FRO, FOb3 FRO⟧) (f3 : A⟦FOb3 FRO, FOb4 FRO⟧)
             (f4 : A⟦FOb4 FRO, FOb5 FRO⟧) : FiveRowDiffs FRO := (f1,,(f2,,(f3,,f4))).

  Definition FDiff1 {FRO : FiveRowObs} (FRD : FiveRowDiffs FRO) : A⟦FOb1 FRO, FOb2 FRO⟧ :=
    dirprod_pr1 FRD.

  Definition FDiff2 {FRO : FiveRowObs} (FRD : FiveRowDiffs FRO) : A⟦FOb2 FRO, FOb3 FRO⟧ :=
    dirprod_pr1 (dirprod_pr2 FRD).

  Definition FDiff3 {FRO : FiveRowObs} (FRD : FiveRowDiffs FRO) : A⟦FOb3 FRO, FOb4 FRO⟧ :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 FRD)).

  Definition FDiff4 {FRO : FiveRowObs} (FRD : FiveRowDiffs FRO) : A⟦FOb4 FRO, FOb5 FRO⟧ :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 FRD)).

  (** *** Composition of consecutive differentials is 0 *)

  Definition FiveRowDiffsEq {FRO : FiveRowObs} (FRD : FiveRowDiffs FRO) : UU :=
    (FDiff1 FRD · FDiff2 FRD = ZeroArrow (to_Zero A) _ _)
      × (FDiff2 FRD · FDiff3 FRD = ZeroArrow (to_Zero A) _ _)
      × (FDiff3 FRD · FDiff4 FRD = ZeroArrow (to_Zero A) _ _).

  Definition make_FiveRowDiffsEq {FRO : FiveRowObs} (FRD : FiveRowDiffs FRO)
             (H1 : FDiff1 FRD · FDiff2 FRD = ZeroArrow (to_Zero A) _ _)
             (H2 : FDiff2 FRD · FDiff3 FRD = ZeroArrow (to_Zero A) _ _)
             (H3 : FDiff3 FRD · FDiff4 FRD = ZeroArrow (to_Zero A) _ _) : FiveRowDiffsEq FRD :=
    (H1,,(H2,,H3)).

  Definition FEq1 {FRO : FiveRowObs} {FRD : FiveRowDiffs FRO} (FRDE : FiveRowDiffsEq FRD) :
    FDiff1 FRD · FDiff2 FRD = ZeroArrow (to_Zero A) _ _ := dirprod_pr1 FRDE.

  Definition FEq2 {FRO : FiveRowObs} {FRD : FiveRowDiffs FRO} (FRDE : FiveRowDiffsEq FRD) :
    FDiff2 FRD · FDiff3 FRD = ZeroArrow (to_Zero A) _ _ := dirprod_pr1 (dirprod_pr2 FRDE).

  Definition FEq3 {FRO : FiveRowObs} {FRD : FiveRowDiffs FRO} (FRDE : FiveRowDiffsEq FRD) :
    FDiff3 FRD · FDiff4 FRD = ZeroArrow (to_Zero A) _ _ := dirprod_pr2 (dirprod_pr2 FRDE).

  (** *** Row is exact *)

  Definition FiveRowExacts {FRO : FiveRowObs} {FRD : FiveRowDiffs FRO}
             (FRDE : FiveRowDiffsEq FRD) : UU :=
    (isExact A hs (FDiff1 FRD) (FDiff2 FRD) (FEq1 FRDE))
      × (isExact A hs (FDiff2 FRD) (FDiff3 FRD) (FEq2 FRDE))
      × (isExact A hs (FDiff3 FRD) (FDiff4 FRD) (FEq3 FRDE)).

  Definition make_FiveRowExacts {FRO : FiveRowObs} {FRD : FiveRowDiffs FRO}
             (FRDE : FiveRowDiffsEq FRD) (H1 : isExact A hs (FDiff1 FRD) (FDiff2 FRD) (FEq1 FRDE))
             (H2 : isExact A hs (FDiff2 FRD) (FDiff3 FRD) (FEq2 FRDE))
             (H3 : isExact A hs (FDiff3 FRD) (FDiff4 FRD) (FEq3 FRDE)) : FiveRowExacts FRDE :=
    (H1,,(H2,,H3)).

  Definition FEx1 {FRO : FiveRowObs} {FRD : FiveRowDiffs FRO} {FRDE : FiveRowDiffsEq FRD}
             (FRE : FiveRowExacts FRDE) : isExact A hs (FDiff1 FRD) (FDiff2 FRD) (FEq1 FRDE) :=
    dirprod_pr1 FRE.

  Definition FEx2 {FRO : FiveRowObs} {FRD : FiveRowDiffs FRO} {FRDE : FiveRowDiffsEq FRD}
             (FRE : FiveRowExacts FRDE) : isExact A hs (FDiff2 FRD) (FDiff3 FRD) (FEq2 FRDE) :=
    dirprod_pr1 (dirprod_pr2 FRE).

  Definition FEx3 {FRO : FiveRowObs} {FRD : FiveRowDiffs FRO} {FRDE : FiveRowDiffsEq FRD}
             (FRE : FiveRowExacts FRDE) : isExact A hs (FDiff3 FRD) (FDiff4 FRD) (FEq3 FRDE) :=
    dirprod_pr2 (dirprod_pr2 FRE).

  (** *** Define row for [FiveLemma] *)

  Definition FiveRow : UU :=
    ∑ (FRO : FiveRowObs),
    (∑ (FRD : FiveRowDiffs FRO), (∑ (FRDE : FiveRowDiffsEq FRD), FiveRowExacts FRDE)).

  Definition make_FiveRow (FRO : FiveRowObs) (FRD : FiveRowDiffs FRO) (FRDE : FiveRowDiffsEq FRD)
             (FRE : FiveRowExacts FRDE) : FiveRow := (FRO,,(FRD,,(FRDE,,FRE))).

  Definition FiveRow_Obs (FR : FiveRow) : FiveRowObs := pr1 FR.
  Coercion FiveRow_Obs : FiveRow >-> FiveRowObs.

  Definition FiveRow_Diffs (FR : FiveRow) : FiveRowDiffs FR := pr1 (pr2 FR).
  Coercion FiveRow_Diffs : FiveRow >-> FiveRowDiffs.

  Definition FiveRow_DiffsEq (FR : FiveRow) : FiveRowDiffsEq FR := pr1 (pr2 (pr2 FR)).
  Coercion FiveRow_DiffsEq : FiveRow >-> FiveRowDiffsEq.

  Definition FiveRow_Exacts (FR : FiveRow) : FiveRowExacts FR := pr2 (pr2 (pr2 FR)).
  Coercion FiveRow_Exacts : FiveRow >-> FiveRowExacts.


  (** ** Morphism of [FiveRows] *)

  (** *** Morphisms in the morphism *)

  Definition FiveRowMors (FR1 FR2 : FiveRow) : UU :=
    (A⟦FOb1 FR1, FOb1 FR2⟧) × (A⟦FOb2 FR1, FOb2 FR2⟧) × (A⟦FOb3 FR1, FOb3 FR2⟧)
                            × (A⟦FOb4 FR1, FOb4 FR2⟧) × (A⟦FOb5 FR1, FOb5 FR2⟧).

  Definition make_FiveRowMors (FR1 FR2 : FiveRow) (f1 : A⟦FOb1 FR1, FOb1 FR2⟧)
             (f2 : A⟦FOb2 FR1, FOb2 FR2⟧) (f3 : A⟦FOb3 FR1, FOb3 FR2⟧)
             (f4 : A⟦FOb4 FR1, FOb4 FR2⟧) (f5 : A⟦FOb5 FR1, FOb5 FR2⟧) : FiveRowMors FR1 FR2 :=
    (f1,,(f2,,(f3,,(f4,,f5)))).

  Definition FMor1 {FR1 FR2 : FiveRow} (FRMs : FiveRowMors FR1 FR2) : A⟦FOb1 FR1, FOb1 FR2⟧ :=
    dirprod_pr1 FRMs.

  Definition FMor2 {FR1 FR2 : FiveRow} (FRMs : FiveRowMors FR1 FR2) : A⟦FOb2 FR1, FOb2 FR2⟧ :=
    dirprod_pr1 (dirprod_pr2 FRMs).

  Definition FMor3 {FR1 FR2 : FiveRow} (FRMs : FiveRowMors FR1 FR2) : A⟦FOb3 FR1, FOb3 FR2⟧ :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 FRMs)).

  Definition FMor4 {FR1 FR2 : FiveRow} (FRMs : FiveRowMors FR1 FR2) : A⟦FOb4 FR1, FOb4 FR2⟧ :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 FRMs))).

  Definition FMor5 {FR1 FR2 : FiveRow} (FRMs : FiveRowMors FR1 FR2) : A⟦FOb5 FR1, FOb5 FR2⟧ :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 FRMs))).

  (** *** Commutativity of the squares *)

  Definition FiveRowMorsComm {FR1 FR2 : FiveRow} (FRMs : FiveRowMors FR1 FR2) : UU :=
    (FDiff1 FR1 · FMor2 FRMs = FMor1 FRMs · FDiff1 FR2)
      × (FDiff2 FR1 · FMor3 FRMs = FMor2 FRMs · FDiff2 FR2)
      × (FDiff3 FR1 · FMor4 FRMs = FMor3 FRMs · FDiff3 FR2)
      × (FDiff4 FR1 · FMor5 FRMs = FMor4 FRMs · FDiff4 FR2).

  Definition make_FiveRowMorsComm {FR1 FR2 : FiveRow} (FRMs : FiveRowMors FR1 FR2)
    (H1 : FDiff1 FR1 · FMor2 FRMs = FMor1 FRMs · FDiff1 FR2)
    (H2 : FDiff2 FR1 · FMor3 FRMs = FMor2 FRMs · FDiff2 FR2)
    (H3 : FDiff3 FR1 · FMor4 FRMs = FMor3 FRMs · FDiff3 FR2)
    (H4 : FDiff4 FR1 · FMor5 FRMs = FMor4 FRMs · FDiff4 FR2) : FiveRowMorsComm FRMs :=
    (H1,,(H2,,(H3,,H4))).

  Definition FComm1 {FR1 FR2 : FiveRow} {FRMs : FiveRowMors FR1 FR2} (FRMC : FiveRowMorsComm FRMs) :
    FDiff1 FR1 · FMor2 FRMs = FMor1 FRMs · FDiff1 FR2 := dirprod_pr1 FRMC.

  Definition FComm2 {FR1 FR2 : FiveRow} {FRMs : FiveRowMors FR1 FR2} (FRMC : FiveRowMorsComm FRMs) :
    FDiff2 FR1 · FMor3 FRMs = FMor2 FRMs · FDiff2 FR2 := dirprod_pr1 (dirprod_pr2 FRMC).

  Definition FComm3 {FR1 FR2 : FiveRow} {FRMs : FiveRowMors FR1 FR2} (FRMC : FiveRowMorsComm FRMs) :
    FDiff3 FR1 · FMor4 FRMs = FMor3 FRMs · FDiff3 FR2 :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 FRMC)).

  Definition FComm4 {FR1 FR2 : FiveRow} {FRMs : FiveRowMors FR1 FR2} (FRMC : FiveRowMorsComm FRMs) :
    FDiff4 FR1 · FMor5 FRMs = FMor4 FRMs · FDiff4 FR2 :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 FRMC)).

  (** *** Morphism of rows *)

  Definition FiveRowMorphism (FR1 FR2 : FiveRow) : UU :=
    ∑ (FRMs : FiveRowMors FR1 FR2), FiveRowMorsComm FRMs.

  Definition make_FiveRowMorphism (FR1 FR2 : FiveRow) (FRMs : FiveRowMors FR1 FR2)
             (FRMC : FiveRowMorsComm FRMs) : FiveRowMorphism FR1 FR2 := (FRMs,,FRMC).

  Definition FiveRowMorphism_Mors {FR1 FR2 : FiveRow} (FRM : FiveRowMorphism FR1 FR2) :
    FiveRowMors FR1 FR2 := pr1 FRM.
  Coercion FiveRowMorphism_Mors : FiveRowMorphism >-> FiveRowMors.

  Definition FiveRowMorphism_Comms {FR1 FR2 : FiveRow} (FRM : FiveRowMorphism FR1 FR2) :
    FiveRowMorsComm FRM := pr2 FRM.
  Coercion FiveRowMorphism_Comms : FiveRowMorphism >-> FiveRowMorsComm.

End five_lemma_data.


(** ** Introduction
In this section we translate the definitions in the previous section [five_lemma_data] to opposite
categories, so that [FiveLemma_isEpi] can use these.
*)
Section five_lemma_opp.

  Definition FiveRowObs_opp {A : AbelianPreCat} {hs : has_homsets A} (FRO : FiveRowObs) :
    @FiveRowObs (Abelian_opp A hs) :=
    @make_FiveRowObs (Abelian_opp A hs) (FOb5 FRO) (FOb4 FRO) (FOb3 FRO) (FOb2 FRO) (FOb1 FRO).

  Definition FiveRowDiffs_opp {A : AbelianPreCat} {hs : has_homsets A} {FRO : @FiveRowObs A}
             (FRD : FiveRowDiffs FRO) : @FiveRowDiffs (Abelian_opp A hs) (FiveRowObs_opp FRO) :=
    @make_FiveRowDiffs (Abelian_opp A hs) (FiveRowObs_opp FRO)
                     (FDiff4 FRD) (FDiff3 FRD) (FDiff2 FRD) (FDiff1 FRD).

  Local Opaque ZeroArrow.
  Local Lemma FiveRowDiffsEq_opp1 {A : AbelianPreCat} {hs : has_homsets A} {FRO : @FiveRowObs A}
        {FRD : @FiveRowDiffs A FRO} (FRDE : @FiveRowDiffsEq A FRO FRD) :
    (@FDiff1 (Abelian_opp A hs) _ (FiveRowDiffs_opp FRD))
      · (@FDiff2 (Abelian_opp A hs) _ (FiveRowDiffs_opp FRD)) =
    ZeroArrow (to_Zero (Abelian_opp A hs)) _ _.
  Proof.
    use (pathscomp0 (FEq3 FRDE)). use ZeroArrow_opp.
  Qed.

  Local Lemma FiveRowDiffsEq_opp2 {A : AbelianPreCat} {hs : has_homsets A} {FRO : @FiveRowObs A}
        {FRD : @FiveRowDiffs A FRO} (FRDE : @FiveRowDiffsEq A FRO FRD) :
    (@FDiff2 (Abelian_opp A hs) _ (FiveRowDiffs_opp FRD))
      · (@FDiff3 (Abelian_opp A hs) _ (FiveRowDiffs_opp FRD)) =
    ZeroArrow (to_Zero (Abelian_opp A hs)) _ _.
  Proof.
    use (pathscomp0 (FEq2 FRDE)). use ZeroArrow_opp.
  Qed.

  Local Lemma FiveRowDiffsEq_opp3 {A : AbelianPreCat} {hs : has_homsets A} {FRO : @FiveRowObs A}
        {FRD : @FiveRowDiffs A FRO} (FRDE : @FiveRowDiffsEq A FRO FRD) :
    (@FDiff3 (Abelian_opp A hs) _ (FiveRowDiffs_opp FRD))
      · (@FDiff4 (Abelian_opp A hs) _ (FiveRowDiffs_opp FRD)) =
    ZeroArrow (to_Zero (Abelian_opp A hs)) _ _.
  Proof.
    use (pathscomp0 (FEq1 FRDE)). use ZeroArrow_opp.
  Qed.

  Definition FiveRowDiffsEq_opp {A : AbelianPreCat} {hs : has_homsets A} {FRO : @FiveRowObs A}
             {FRD : @FiveRowDiffs A FRO} (FRDE : @FiveRowDiffsEq A FRO FRD) :
    @FiveRowDiffsEq (Abelian_opp A hs) _ (FiveRowDiffs_opp FRD) :=
    @make_FiveRowDiffsEq _ _ (FiveRowDiffs_opp FRD) (FiveRowDiffsEq_opp1 FRDE)
                       (FiveRowDiffsEq_opp2 FRDE) (FiveRowDiffsEq_opp3 FRDE).

  Definition FiveRowExacts_opp {A : AbelianPreCat} {hs : has_homsets A} {FRO : @FiveRowObs A}
             {FRD : @FiveRowDiffs A FRO} {FRDE : @FiveRowDiffsEq A FRO FRD}
             (FRE : @FiveRowExacts A hs FRO FRD FRDE) :
    @FiveRowExacts (Abelian_opp A hs) (has_homsets_opp hs) _ _ (FiveRowDiffsEq_opp FRDE) :=
    @make_FiveRowExacts (Abelian_opp A hs) (has_homsets_opp hs) _ _ (FiveRowDiffsEq_opp FRDE)
                      (isExact_opp (FEx3 hs FRE)) (isExact_opp (FEx2 hs FRE))
                      (isExact_opp (FEx1 hs FRE)).

  Definition FiveRow_opp {A : AbelianPreCat} {hs : has_homsets A} (FR : @FiveRow A hs) :
    @FiveRow (Abelian_opp A hs) (has_homsets_opp hs) :=
    @make_FiveRow (Abelian_opp A hs) (has_homsets_opp hs) (FiveRowObs_opp FR)
                (FiveRowDiffs_opp FR) (FiveRowDiffsEq_opp FR) (FiveRowExacts_opp FR).

  Definition FiveRowMors_opp {A : AbelianPreCat} {hs : has_homsets A} {FR1 FR2 : @FiveRow A hs}
             (FRM : @FiveRowMors A hs FR1 FR2) :
    @FiveRowMors (Abelian_opp A hs) (has_homsets_opp hs) (FiveRow_opp FR2) (FiveRow_opp FR1) :=
    @make_FiveRowMors (Abelian_opp A hs) (has_homsets_opp hs) (FiveRow_opp FR2) (FiveRow_opp FR1)
                    (FMor5 hs FRM) (FMor4 hs FRM) (FMor3 hs FRM) (FMor2 hs FRM) (FMor1 hs FRM).

  Definition FiveRowMorsComm_opp {A : AbelianPreCat} {hs : has_homsets A} {FR1 FR2 : @FiveRow A hs}
             {FRM : @FiveRowMors A hs FR1 FR2} (FRMC : @FiveRowMorsComm A hs FR1 FR2 FRM) :
    @FiveRowMorsComm (Abelian_opp A hs) (has_homsets_opp hs) _ _ (FiveRowMors_opp FRM) :=
    @make_FiveRowMorsComm (Abelian_opp A hs) (has_homsets_opp hs) _ _ (FiveRowMors_opp FRM)
                        (! FComm4 hs FRMC) (! FComm3 hs FRMC) (! FComm2 hs FRMC) (! FComm1 hs FRMC).

  Definition FiveRowMorphism_opp {A : AbelianPreCat} {hs : has_homsets A} {FR1 FR2 : @FiveRow A hs}
             (FRM : @FiveRowMorphism A hs FR1 FR2) :
    @FiveRowMorphism (Abelian_opp A hs) (has_homsets_opp hs) (FiveRow_opp FR2) (FiveRow_opp FR1) :=
    @make_FiveRowMorphism (Abelian_opp A hs) (has_homsets_opp hs) (FiveRow_opp FR2) (FiveRow_opp FR1)
                        (FiveRowMors_opp FRM) (FiveRowMorsComm_opp FRM).

End five_lemma_opp.


(** ** Introduction
In this section we prove the five lemma following the sketch of a proof on top of this file.
*)
Section five_lemma.

  Lemma FiveLemma_isMonic {A : AbelianPreCat} {hs : has_homsets A} {FR1 FR2 : FiveRow hs}
        (FRM : FiveRowMorphism hs FR1 FR2) (H1 : is_z_isomorphism (FMor1 hs FRM))
        (H2 : is_z_isomorphism (FMor2 hs FRM)) (H4 : is_z_isomorphism (FMor4 hs FRM))
        (H5 : is_z_isomorphism (FMor5 hs FRM)) : isMonic (FMor3 hs FRM).
  Proof.
    use (dirprod_pr2 (PEq_isMonic hs (FMor3 hs FRM))).
    intros d' a X. apply pathsinv0. cbn in X. set (X' := PEq_Zero_Eq' _ _ X). cbn in X'.
    assert (e1 : a · FDiff3 FR1 = ZeroArrow (to_Zero A) _ _).
    {
      set (comm := FComm3 hs FRM). use (is_iso_isMonic A _ H4).
      rewrite <- assoc. rewrite comm. clear comm. rewrite assoc.
      rewrite X'. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
      apply idpath.
    }
    set (b := dirprod_pr1 (PEq_isExact hs _ _ (FEq2 FR1)) (FEx2 hs FR1) a e1).
    set (PE1 := PseudoIm b (FMor2 hs FRM)).
    assert (e2 : PE1 · FDiff2 FR2 = ZeroArrow (to_Zero A) _ _).
    {
      cbn. set (comm := FComm2 hs FRM). rewrite <- assoc. rewrite <- comm. clear comm.
      rewrite assoc. set (tmp := PEqEq (PFiber_Eq b)). cbn in tmp.
      use (EpiisEpi _ (PEqEpi2 (PFiber_Eq b))). rewrite assoc.
      cbn in tmp. cbn. rewrite <- tmp. clear tmp. rewrite <- assoc. rewrite X'.
      rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
      apply idpath.
    }
    set (b' := dirprod_pr1 (PEq_isExact hs _ _ (FEq1 FR2)) (FEx1 hs FR2) PE1 e2).
    set (a' := dirprod_pr1 (PEq_isEpi hs (FMor1 hs FRM)) (is_iso_isEpi A _ H1) b').
    assert (e3 : PEq (PseudoIm a' (FDiff1 FR1)) b).
    {
      assert (e31 : PEq (PseudoIm (PseudoIm a' (FDiff1 FR1)) (FMor2 hs FRM))
                        (PseudoIm b (FMor2 hs FRM))).
      {
        use (PEq_trans hs (PEq_Im_Comm hs a' (FComm1 hs FRM))).
        use (PEq_trans hs (PEq_Im _ _ (FDiff1 FR2) (PFiber_Eq a'))).
        use (PEq_trans hs (PFiber_Eq b')). use PEq_refl.
      }
      exact (dirprod_pr1 (PEq_isMonic' hs (FMor2 hs FRM)) (is_iso_isMonic A _ H2)
                         (PseudoIm a' (FDiff1 FR1)) b e31).
    }
    assert (e4 : PEq (PseudoIm (PseudoIm a' (FDiff1 FR1)) (FDiff2 FR1)) a).
    {
      use (PEq_trans hs _ (PFiber_Eq b)).
      use (PEq_trans hs _ (PEq_Im _ _ (FDiff2 FR1) e3)).
      use PEq_refl.
    }
    use PEq_Zero_Eq'.
    - exact (PseudoOb a').
    - use (PEq_trans hs (PEq_symm e4)).
      use (PEq_trans hs (PEq_Comp a' (FDiff1 FR1) (FDiff2 FR1))).
      use (PEq_trans hs (PEq_Im_Paths a' (FEq1 FR1))).
      use PEq_Eq_Zero. cbn. apply ZeroArrow_comp_right.
  Qed.

  Context {A : AbelianPreCat}.
  Variable hs : has_homsets A.

  Lemma FiveLemma_isEpi {FR1 FR2 : FiveRow hs} (FRM : FiveRowMorphism hs FR1 FR2)
        (H1 : is_z_isomorphism (FMor1 hs FRM)) (H2 : is_z_isomorphism (FMor2 hs FRM))
        (H4 : is_z_isomorphism (FMor4 hs FRM)) (H5 : is_z_isomorphism (FMor5 hs FRM)) :
    isEpi (FMor3 hs FRM).
  Proof.
    use opp_isMonic.
    set (H1' := opp_is_z_isomorphism _ H1).
    set (H2' := opp_is_z_isomorphism _ H2).
    set (H4' := opp_is_z_isomorphism _ H4).
    set (H5' := opp_is_z_isomorphism _ H5).
    set (FRM' := FiveRowMorphism_opp FRM).
    exact (FiveLemma_isMonic FRM' H5' H4' H2' H1').
  Qed.

  Lemma FiveLemma {FR1 FR2 : FiveRow hs} (FRM : FiveRowMorphism hs FR1 FR2)
        (H1 : is_z_isomorphism (FMor1 hs FRM)) (H2 : is_z_isomorphism (FMor2 hs FRM))
        (H4 : is_z_isomorphism (FMor4 hs FRM)) (H5 : is_z_isomorphism (FMor5 hs FRM)) :
    is_z_isomorphism (FMor3 hs FRM).
  Proof.
    use monic_epi_is_iso.
    - use FiveLemma_isMonic.
      + exact H1.
      + exact H2.
      + exact H4.
      + exact H5.
    - use FiveLemma_isEpi.
      + exact H1.
      + exact H2.
      + exact H4.
      + exact H5.
  Qed.

End five_lemma.


(** ** Introduction
Five lemma for short exact sequences. Suppose you have a morphism of short exact sequences
represented by the following diagram
                               0  --> C_1 --> C_2 --> C_3 -->  0
                               |   f_2 |   f_3 |   f_4 |       |
                               0  --> D_1 --> D_2 --> D_3 -->  0
If f_2 and f_4 are isomorphisms, then f_3 is an isomorphism. This is proved in
[ShortExactFiveLemma].
 *)
Section short_exact_five_lemma.

  Context {A : AbelianPreCat}.
  Variable hs : has_homsets A.

  (** ** Construction of the first row *)

  Definition ShortExactObs1 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowObs A.
  Proof.
    use make_FiveRowObs.
    - exact (to_Zero A).
    - exact (Ob1 SSE1).
    - exact (Ob2 SSE1).
    - exact (Ob3 SSE1).
    - exact (to_Zero A).
  Defined.

  Definition ShortExactDiffs1 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowDiffs A (ShortExactObs1 Mor).
  Proof.
    use make_FiveRowDiffs.
    - exact (ZeroArrow (to_Zero A) _ _).
    - exact (Mor1 SSE1).
    - exact (Mor2 SSE1).
    - exact (ZeroArrow (to_Zero A) _ _).
  Defined.

  Lemma ShortExactDiffsEq1 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowDiffsEq A _ (ShortExactDiffs1 Mor).
  Proof.
    use make_FiveRowDiffsEq.
    - cbn. apply ZeroArrow_comp_left.
    - cbn. use (ShortShortExactData_Eq (to_Zero A) SSE1).
    - cbn. apply ZeroArrow_comp_right.
  Qed.

  Lemma ShortExactExacts1 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowExacts A hs _ _ (ShortExactDiffsEq1 Mor).
  Proof.
    use make_FiveRowExacts.
    - cbn. use isExactisMonic. exact (ShortExactSequences.isMonic hs SSE1).
    - unfold isExact. exact (ShortShortExact_isKernel hs SSE1).
    - cbn. use isExactisEpi. exact (ShortExactSequences.isEpi hs SSE1).
  Qed.

  Definition ShortExactRow1 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRow A hs.
  Proof.
    use make_FiveRow.
    - exact (ShortExactObs1 Mor).
    - exact (ShortExactDiffs1 Mor).
    - exact (ShortExactDiffsEq1 Mor).
    - exact (ShortExactExacts1 Mor).
  Defined.

  (** ** Construction of the second row *)

  Definition ShortExactObs2 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowObs A.
  Proof.
    use make_FiveRowObs.
    - exact (to_Zero A).
    - exact (Ob1 SSE2).
    - exact (Ob2 SSE2).
    - exact (Ob3 SSE2).
    - exact (to_Zero A).
  Defined.

  Definition ShortExactDiffs2 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowDiffs A (ShortExactObs2 Mor).
  Proof.
    use make_FiveRowDiffs.
    - exact (ZeroArrow (to_Zero A) _ _).
    - exact (Mor1 SSE2).
    - exact (Mor2 SSE2).
    - exact (ZeroArrow (to_Zero A) _ _).
  Defined.

  Lemma ShortExactDiffsEq2 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowDiffsEq A _ (ShortExactDiffs2 Mor).
  Proof.
    use make_FiveRowDiffsEq.
    - cbn. apply ZeroArrow_comp_left.
    - cbn. use (ShortShortExactData_Eq (to_Zero A) SSE2).
    - cbn. apply ZeroArrow_comp_right.
  Qed.

  Lemma ShortExactExacts2 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowExacts A hs _ _ (ShortExactDiffsEq2 Mor).
  Proof.
    use make_FiveRowExacts.
    - cbn. use isExactisMonic. exact (ShortExactSequences.isMonic hs SSE2).
    - unfold isExact. exact (ShortShortExact_isKernel hs SSE2).
    - cbn. use isExactisEpi. exact (ShortExactSequences.isEpi hs SSE2).
  Qed.

  Definition ShortExactRow2 {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRow A hs.
  Proof.
    use make_FiveRow.
    - exact (ShortExactObs2 Mor).
    - exact (ShortExactDiffs2 Mor).
    - exact (ShortExactDiffsEq2 Mor).
    - exact (ShortExactExacts2 Mor).
  Defined.

  (** ** Construction of the morphism between rows *)

  Definition ShortExactMors {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowMors A hs (ShortExactRow1 Mor) (ShortExactRow2 Mor).
  Proof.
    use make_FiveRowMors.
    - exact (identity _).
    - exact (MPMor1 Mor).
    - exact (MPMor2 Mor).
    - exact (MPMor3 Mor).
    - exact (identity _).
  Defined.

  Lemma ShortExactMorComm {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowMorsComm A hs _ _ (ShortExactMors Mor).
  Proof.
    use make_FiveRowMorsComm.
    - cbn. rewrite ZeroArrow_comp_left. rewrite id_left. apply idpath.
    - cbn. exact (! (MPComm1 Mor)).
    - cbn. exact (! (MPComm2 Mor)).
    - cbn. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition ShortExactMor {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2) :
    @FiveRowMorphism A hs (ShortExactRow1 Mor) (ShortExactRow2 Mor).
  Proof.
    use make_FiveRowMorphism.
    - exact (ShortExactMors Mor).
    - exact (ShortExactMorComm Mor).
  Defined.

  (** ** FiveLemma for short exact sequences *)

  Lemma ShortExactFiveLemma {SSE1 SSE2 : ShortExact A hs} (Mor : MPMor SSE1 SSE2)
        (H2 : is_z_isomorphism (MPMor1 Mor)) (H4 : is_z_isomorphism (MPMor3 Mor)) :
    is_z_isomorphism (MPMor2 Mor).
  Proof.
    set (FR1 := ShortExactRow1 Mor).
    set (FR2 := ShortExactRow2 Mor).
    set (FM := ShortExactMor Mor).
    use (FiveLemma hs FM).
    - exact (is_z_isomorphism_identity _).
    - exact H2.
    - exact H4.
    - exact (is_z_isomorphism_identity _).
  Qed.

End short_exact_five_lemma.