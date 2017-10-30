(** * Pseudo elements *)
(** ** Contents
- Pseudo elements
 - Definition of pseudo elements
 - Basics of pseudo elements
 - Criteria for Zero, isMonic, isEpi, isExact, Minus, and Pullback using pseudo elements
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.Opp.

Require Import UniMath.CategoryTheory.Categories.
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

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.


(** ** Introduction
We define pseudo elements which are used in diagram lemmas in homological algebra. A pseudo element
of an object x of an abelian category A is a morphism from some object y to x. Two pseudo elements
f_1 : y_1 --> x, f_2 : y_2 --> x are pseudo equal if there is an object y_3 and epimorphisms
p : y_3 --> y_1 and q : y_3 --> y_2 such that the following diagram is commutative
                                 y_3 --p--> y_1
                                q |      f_1 |
                                 y_2 -f_2->  x

Pseudo elements are defined in [PseudoElem]. In [PseudoEq_iseqrel] we prove that pseudo equality
is an equivalence relation.

Here are the results we prove about pseudo elements :
- Let f_1 : x_1 --> y and f_2 : x_2 --> y be ZeroArrows. As pseudo elements they are pseudo equal,
  [PEq_Zeros'].
- A morphism f : x --> y is a ZeroArrow if and only if for all pseudo elements g : x' --> x of x
  the composite g · f is pseudo equal to ZeroArrow, [PEq_ZeroArrow].
- A morphism f : x --> y is Monic if and only is for all pseudo elements a : a' -> x of x, the
  composite a' -> x is ZeroArrow, [PEq_isMonic].
- A morphism f : x --> y is Monic if and only is for all pseudo elements a_1  : a_1' --> x and
  a_2 : a_2' --> x, pseudo equality of a_1' · f and a_2' · f implies that a_1' and a_2' are
  pseudo equal, [PEq_isMonic']
- A morphism f : x --> y is Epi if and only if for all pseudo elements b : b' --> y of y there
  exists a pseudo element a : a' --> x of x such that a · f is pseudo equal to b, [PEq_isEpi].
- A pair of morphisms f : x --> y, g : y --> z is exact if and only if the composite is ZeroArrow
  and for all pseudo elements b : b' --> y such that b · g is pseudo equal to PZero, there exists
  a pseudo element a : a' --> x of x such that a · f is pseudo equal to b, [PEq_isExact].
- Let f : x --> y be a morphism, and a_1 : a_1' --> x and a_2 : a_2' --> x two pseudo elements of x
  such that a_1 · f and a_2 · f are pseudo equal. Then there exists a pseudo element
  a_3 : a_3' --> x of x such that a_3 · f is pseudo equal to PZero, and for all morphisms
  g : x --> z such that a_1 · g is pseudo equal to PZero, we have that a_2 · g and a_3 · g are
  pseudo equal, [PEq_Diff].
- Let f : x --> z and g : y --> z be morphisms and let a : a' --> x and b : b' --> y be pseudo
  elements of x and y, respectively. Then there exists a pseudo element d : d' --> Pb, where Pb
  is a pullback of f and g, such that d · pr1 is pseudo equal to f and d · pr2 is pseudo equal to
  g, [PEq_Pullback].
*)
Section def_pseudo_element.

  Context {A : AbelianPreCat}.
  Variable hs : has_homsets A.

  Local Opaque Abelian.Pullbacks.

  (** ** Definition of pseudo elements *)

  Definition PseudoElem (c : A) : UU := ∑ d : A, d --> c.

  Definition mk_PseudoElem {c d : A} (f : d --> c) : PseudoElem c := tpair _ d f.

  Definition PseudoOb {c : A} (P : PseudoElem c) : ob A := pr1 P.

  Definition PseudoMor {c : A} (P : PseudoElem c) : A⟦PseudoOb P, c⟧ := pr2 P.
  Coercion PseudoMor : PseudoElem >-> precategory_morphisms.

  Definition PseudoIm {c d : A} (P : PseudoElem c) (f : c --> d) : PseudoElem d :=
    mk_PseudoElem (P · f).

  (** Pseudo equality *)
  Definition PEq {c : A} (PE1 PE2 : PseudoElem c) : UU :=
    ∑ (Y : ob A) (E1 : Epi A Y (PseudoOb PE2)) (E2 : Epi A Y (PseudoOb PE1)), E1 · PE2 = E2 · PE1.

  Definition mk_PEq {c : A} (PE1 PE2 : PseudoElem c) {Y : ob A} (E1 : Epi A Y (PseudoOb PE2))
             (E2 : Epi A Y (PseudoOb PE1)) (H : E1 · PE2 = E2 · PE1) : PEq PE1 PE2 :=
    (Y,,(E1,,(E2,,H))).

  Definition PEqOb {c : A} {PE1 PE2 : PseudoElem c} (PE : PEq PE1 PE2) : ob A := pr1 PE.

  Definition PEqEpi1 {c : A} {PE1 PE2 : PseudoElem c} (PE : PEq PE1 PE2) :
    Epi A (PEqOb PE) (PseudoOb PE2) := pr1 (pr2 PE).

  Definition PEqEpi2 {c : A} {PE1 PE2 : PseudoElem c} (PE : PEq PE1 PE2) :
    Epi A (PEqOb PE) (PseudoOb PE1) := pr1 (pr2 (pr2 PE)).

  Definition PEqEq {c : A} {PE1 PE2 : PseudoElem c} (PE : PEq PE1 PE2) :
    (PEqEpi1 PE) · PE2 = (PEqEpi2 PE) · PE1 := pr2 (pr2 (pr2 PE)).

  Definition PEq_hrel {c : A} : hrel (PseudoElem c) := λ (PE1 PE2 : PseudoElem c), ∥ PEq PE1 PE2 ∥.

  Definition PEq_precomp_Epi {c d : A} (P : PseudoElem c) (E : Epi A d (PseudoOb P)) :
    PEq P (mk_PseudoElem (E · P)).
  Proof.
    use mk_PEq.
    - exact d.
    - exact (identity_Epi _).
    - exact E.
    - apply id_left.
  Defined.

  Local Lemma PEq_trans_eq {c : ob A} {E1 E2 E3 : PseudoElem c} (P1 : PEq E1 E2) (P2 : PEq E2 E3) :
    let Pb := Abelian.Pullbacks A hs _ _ _ (PEqEpi1 P1) (PEqEpi2 P2) in
    PullbackPr2 Pb · PEqEpi1 P2 · E3 = PullbackPr1 Pb · PEqEpi2 P1 · E1.
  Proof.
    intros Pb.
    rewrite <- assoc. rewrite <- assoc. rewrite (PEqEq P2). rewrite <- (PEqEq P1).
    rewrite assoc. rewrite assoc. apply cancel_postcomposition.
    apply pathsinv0. exact (PullbackSqrCommutes Pb).
  Qed.

  Definition PEq_trans {c : ob A} {E1 E2 E3 : PseudoElem c} (P1 : PEq E1 E2) (P2 : PEq E2 E3) :
    PEq E1 E3.
  Proof.
    set (Pb := Abelian.Pullbacks A hs _ _ _ (PEqEpi1 P1) (PEqEpi2 P2)).
    use mk_PEq.
    * exact Pb.
    * use mk_Epi.
      -- exact (PullbackPr2 Pb · PEqEpi1 P2).
      -- use isEpi_comp.
         ++ use AbelianPullbackEpi2. exact hs.
         ++ apply EpiisEpi.
    * use mk_Epi.
      -- exact (PullbackPr1 Pb · PEqEpi2 P1).
      -- use isEpi_comp.
         ++ use AbelianPullbackEpi1. exact hs.
         ++ apply EpiisEpi.
    * cbn. exact (PEq_trans_eq P1 P2).
  Defined.

  Lemma PEq_istrans (c : ob A) : istrans (@PEq_hrel c).
  Proof.
    intros E1 E2 E3 H1 H2.
    use (squash_to_prop H1 (propproperty _)). intros X1.
    use (squash_to_prop H2 (propproperty _)). intros X2.
    intros P X3. apply X3. clear P X3.
    exact (PEq_trans X1 X2).
  Qed.

  Definition PEq_refl {c : ob A} (E1 : PseudoElem c) : PEq E1 E1.
  Proof.
    use mk_PEq.
    - exact (PseudoOb E1).
    - use identity_Epi.
    - use identity_Epi.
    - apply idpath.
  Defined.

  Lemma PEq_isrefl (c : ob A) : isrefl (@PEq_hrel c).
  Proof.
    intros E1. intros P X. apply X. clear X P.
    exact (PEq_refl E1).
  Qed.

  Definition PEq_symm {c : ob A} {E1 E2 : PseudoElem c} (P1 : PEq E1 E2) : PEq E2 E1.
  Proof.
    use mk_PEq.
    - exact (PEqOb P1).
    - exact (PEqEpi2 P1).
    - exact (PEqEpi1 P1).
    - exact (! (PEqEq P1)).
  Defined.

  Lemma PEq_issymm (c : ob A) : issymm (@PEq_hrel c).
  Proof.
    intros E1 E2 H1.
    use (squash_to_prop H1 (propproperty _)). intros X1.
    intros P X. apply X. clear X P.
    exact (PEq_symm X1).
  Qed.

  Lemma PseudoEq_iseqrel (c : A) : iseqrel (@PEq_hrel c).
  Proof.
    split.
    - split.
      + exact (PEq_istrans c).
      + exact (PEq_isrefl c).
    - exact (PEq_issymm c).
  Qed.

  (** *** Pseudo fiber *)

  Definition PFiber {c d : ob A} (f : c --> d) (b : PseudoElem d) : UU :=
    ∑ (a : PseudoElem c), PEq (PseudoIm a f) b.

  Definition mk_PFiber {c d : ob A} (f : c --> d) (b : PseudoElem d) (a : PseudoElem c)
             (H : PEq (PseudoIm a f) b) : PFiber f b := tpair _ a H.

  Definition PFiber_Elem {c d : ob A} {f : c --> d} {b : PseudoElem d} (P : PFiber f b) :
    PseudoElem c := pr1 P.
  Coercion PFiber_Elem : PFiber >-> PseudoElem.

  Definition PFiber_Eq {c d : ob A} {f : c --> d} {b : PseudoElem d} (P : PFiber f b) :
    PEq (PseudoIm P f) b := pr2 P.

  (** ** Basics of pseudo elements *)

  Lemma PEq_to_hrel {c : A} (P1 P2 : PseudoElem c) (H : PEq P1 P2) : PEq_hrel P1 P2.
  Proof.
    intros P X. apply X. exact H.
  Qed.

  Local Lemma PEq_Im_Eq {c d : A} (P1 P2 : PseudoElem c) (f : c --> d) (H : PEq P1 P2):
    PEqEpi1 H · (P2 · f) = PEqEpi2 H · (P1 · f).
  Proof.
    rewrite assoc. rewrite assoc. apply cancel_postcomposition. exact (PEqEq H).
  Qed.

  Definition PEq_Im {c d : A} (P1 P2 : PseudoElem c) (f : c --> d) (H : PEq P1 P2) :
    PEq (PseudoIm P1 f) (PseudoIm P2 f).
  Proof.
    use mk_PEq.
    - exact (PEqOb H).
    - exact (PEqEpi1 H).
    - exact (PEqEpi2 H).
    - exact (PEq_Im_Eq P1 P2 f H).
  Defined.

  Local Lemma PEq_Comp_Eq {c d1 d2 : A} (P : PseudoElem c) (f : c --> d1) (g : d1 --> d2) :
    identity (PseudoOb P) · (P · (f · g)) = identity (PseudoOb P) · (P · f · g).
  Proof.
    rewrite id_left. rewrite id_left. apply assoc.
  Qed.

  Definition PEq_Comp {c d1 d2 : A} (P : PseudoElem c) (f : c --> d1) (g : d1 --> d2)  :
    PEq (PseudoIm (PseudoIm P f) g) (PseudoIm P (f · g)).
  Proof.
    use mk_PEq.
    - exact (PseudoOb P).
    - use identity_Epi.
    - use identity_Epi.
    - exact (PEq_Comp_Eq P f g).
  Qed.

  Definition PEq_Im_Paths {x y : A} (P : PseudoElem x) {f g : x --> y} (H : f = g) :
    PEq (PseudoIm P f) (PseudoIm P g).
  Proof.
    induction H. apply PEq_refl.
  Qed.

  Definition PEq_Im_Comm {x y z w : A} (P : PseudoElem x) {f : x --> y} {g : y --> w}
             {h : x --> z} {k : z --> w} (H : f · g = h · k) :
    PEq (PseudoIm (PseudoIm P f) g) (PseudoIm (PseudoIm P h) k).
  Proof.
    use (PEq_trans (PEq_Comp P f g)). use (PEq_trans _ (PEq_symm (PEq_Comp P h k))).
    use PEq_Im_Paths. exact H.
  Qed.

  Definition PZero {c : A} (d : A) : PseudoElem c := mk_PseudoElem (ZeroArrow (to_Zero A) d c).

  Lemma PEq_Zero_Eq' {c : A} (d : A) (PE : PseudoElem c) :
    PEq PE (PZero d) -> (PE : A⟦_,_⟧ ) = ZeroArrow (to_Zero A) _ _.
  Proof.
    intros X1.
    set (tmp := PEqEq X1). cbn in tmp. rewrite ZeroArrow_comp_right in tmp.
    use (EpiisEpi _ (PEqEpi2 X1)). rewrite <- tmp. clear tmp. rewrite ZeroArrow_comp_right.
    apply idpath.
  Qed.

  Lemma PEq_Zero_Eq {c : A} (PE : PseudoElem c) :
    PEq_hrel PE (PZero (PseudoOb PE)) -> (PE : A⟦_,_⟧ ) = ZeroArrow (to_Zero A) _ _.
  Proof.
    intros H1. use (squash_to_prop H1). apply hs. intros X1. exact (PEq_Zero_Eq' _ PE X1).
  Qed.

  Definition PEq_Zeros' {c : A} (d1 d2 : A) : @PEq c (PZero d1) (PZero d2).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A hs) d1 d2).
    use mk_PEq.
    - exact DS.
    - use (mk_Epi _ _ (to_Pr2_isEpi _ DS)).
    - use (mk_Epi _ _ (to_Pr1_isEpi _ DS)).
    - cbn. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. apply idpath.
  Defined.

  Lemma PEq_Zeros {c : A} (d1 d2 : A) : @PEq_hrel c (PZero d1) (PZero d2).
  Proof.
    intros P X. apply X. clear P X. exact (PEq_Zeros' _ _).
  Qed.

  Definition PEq_ZeroIm (c d1 d2 d3 : A) (f : d1 --> d2) : PEq (PseudoIm (PZero c) f) (PZero d3).
  Proof.
    use (PEq_trans _ (PEq_Zeros' c d3)).
    use mk_PEq.
    - exact c.
    - exact (identity_Epi _).
    - exact (identity_Epi _).
    - cbn. rewrite ZeroArrow_comp_left. apply idpath.
  Qed.

  Local Lemma PEq_Eq_Zero_Eq {c : A} (PE : PseudoElem c)
        (H : (PE : A⟦_, c⟧) = ZeroArrow (to_Zero A) _ _) :
    identity (PseudoOb PE) · ZeroArrow (to_Zero A) (PseudoOb PE) c = identity (PseudoOb PE) · PE.
  Proof.
    rewrite id_left. rewrite id_left. apply pathsinv0. exact H.
  Qed.

  Lemma PEq_Eq_Zero {c : A} (PE : PseudoElem c) :
    (PE : A⟦_, c⟧) = ZeroArrow (to_Zero A) _ _ -> PEq PE (PZero (PseudoOb PE)).
  Proof.
    intros H.
    use mk_PEq.
    - exact (PseudoOb PE).
    - use identity_Epi.
    - use identity_Epi.
    - exact (PEq_Eq_Zero_Eq PE H).
  Qed.

  (** ** Pseudo element criterias *)

  (** *** Zero criteria *)
  Lemma PEq_ZeroArrow {c d : ob A} (f : c --> d) :
    f = ZeroArrow (to_Zero A) _ _ <-> (∏ (a : PseudoElem c), a · f = ZeroArrow (to_Zero A) _ _).
  Proof.
    split.
    - intros H. intros a. rewrite H. apply ZeroArrow_comp_right.
    - intros H. set (tmp := H (mk_PseudoElem (identity c))). cbn in tmp.
      rewrite <- tmp. rewrite id_left. apply idpath.
  Qed.

  (** *** isMonic criteria *)

  Lemma PEq_isMonic {c d : ob A} (f : c --> d) :
    isMonic f <-> (∏ (d' : ob A) (a : PseudoElem c),
                 PEq (PseudoIm a f) (PZero d') -> ZeroArrow (to_Zero A) _ _ = a).
  Proof.
    split.
    - intros isM. intros d' a X. use isM. rewrite ZeroArrow_comp_left.
      set (tmp := PseudoIm a f). apply pathsinv0. use (PEq_Zero_Eq tmp). unfold tmp. clear tmp.
      use (PEq_istrans _ _ (PZero d')).
      + exact (PEq_to_hrel _ _ X).
      + use PEq_Zeros.
    - intros X. use (to_isMonic (AbelianToAdditive A hs)).
      intros z g H.
      exact (! ( X z (mk_PseudoElem g) (PEq_Eq_Zero (PseudoIm (mk_PseudoElem g) f) H))).
  Qed.

  Lemma PEq_isMonic' {c d : ob A} (f : c --> d) :
    isMonic f <-> (∏ (a a' : PseudoElem c), PEq (PseudoIm a f) (PseudoIm a' f) -> PEq a a').
  Proof.
    split.
    - intros isM. intros a a' X.
      use mk_PEq.
      + exact (PEqOb X).
      + exact (PEqEpi1 X).
      + exact (PEqEpi2 X).
      + apply isM. set (tmp := PEqEq X). cbn in tmp. rewrite assoc in tmp. rewrite assoc in tmp.
        apply tmp.
    - intros X. use (dirprod_pr2 (PEq_isMonic f)). intros d' a X0.
      apply pathsinv0. use PEq_Zero_Eq'.
      + exact (PseudoOb a).
      + use (X a (PZero (PseudoOb a))).
        use (PEq_trans X0). use PEq_symm. use PEq_ZeroIm.
  Qed.

  (** *** isEpi criteria *)

  Lemma PEq_isEpi {c d : ob A} (f : c --> d) : isEpi f <-> (∏ (b : PseudoElem d), PFiber f b).
  Proof.
    split.
    - intros isE b.
      set (E := mk_Epi _ _ isE).
      set (Pb := Abelian.Pullbacks A hs _ _ _ E b).
      set (isEpi1 := AbelianPullbackEpi2 hs E b Pb).
      set (E2 := mk_Epi A _ isEpi1).
      use (mk_PFiber _ _ (mk_PseudoElem (PullbackPr1 Pb))).
      use mk_PEq.
      + exact Pb.
      + exact E2.
      + use identity_Epi.
      + cbn. rewrite id_left. exact (! PullbackSqrCommutes Pb).
    - intros H.
      set (fib := H (mk_PseudoElem (identity _))).
      set (P1 := PFiber_Elem fib).
      set (e := PEqEq (PFiber_Eq fib)).
      use isEpi_precomp.
      + exact (PEqOb (PFiber_Eq fib)).
      + exact (PEqEpi2 (PFiber_Eq fib) · P1).
      + cbn in e. rewrite id_right in e. rewrite assoc in e. use (isEpi_path A _ _ e).
        apply EpiisEpi.
  Qed.

  (** *** isExact criteria *)

  Lemma PEq_isExact {x y z : ob A} (f : x --> y) (g : y --> z)
        (H : f · g = ZeroArrow (to_Zero A) _ _) :
    isExact A hs f g H <->
    ∏ (b : PseudoElem y) (H : b · g = ZeroArrow (to_Zero A) _ _), PFiber f b.
  Proof.
    split.
    - intros isK b H'. unfold isExact in isK.
      set (K := mk_Kernel _ _ _ _ isK).
      set (KI := KernelIn _ K (PseudoOb b) b H').
      set (Pb := Abelian.Pullbacks A hs _ _ _ (factorization1_epi A hs f) KI).
      use mk_PFiber.
      + exact (mk_PseudoElem (PullbackPr1 Pb)).
      + use mk_PEq.
        * exact Pb.
        * exact (mk_Epi _ _ (AbelianPullbackEpi2 hs (factorization1_epi A hs f) KI Pb)).
        * use identity_Epi.
        * cbn. rewrite id_left. apply pathsinv0.
          set (tmp := PullbackSqrCommutes Pb).
          set (tmp' := factorization1 hs f).
          apply (maponpaths (λ gg : _, gg · (factorization1_monic A f))) in tmp.
          rewrite <- assoc in tmp. rewrite <- tmp' in tmp. clear tmp'.
          use (pathscomp0 tmp). clear tmp. rewrite <- assoc. apply cancel_precomposition.
          use (KernelCommutes (to_Zero A) K).
    - intros X.
      set (fac := factorization1 hs f).
      use mk_isKernel.
      + exact hs.
      + intros w h H'.
        set (P := X (mk_PseudoElem h) H').
        set (PE := PFiber_Eq P).
        set (Pb := Abelian.Pullbacks A hs _ _ _ h (factorization1_monic A f)).
        set (isM := MonicPullbackisMonic' _ _ _ Pb).
        assert (i : is_z_isomorphism (PullbackPr1 Pb)).
        {
          use monic_epi_is_iso.
          - exact isM.
          - assert (ee : PEqEpi1 PE · h =
                         PEqEpi2 PE · P · factorization1_epi A hs f · factorization1_monic A f).
            {
              cbn. set (ee := PEqEq PE). cbn in ee. rewrite ee.
              rewrite assoc. rewrite <- (assoc _ _ (KernelArrow (Abelian.Image f))).
              apply cancel_precomposition. exact fac.
            }
            set (tmp := PullbackArrow
                          Pb _ (PEqEpi1 PE)
                          ((PEqEpi2 PE) · (PFiber_Elem P) · (factorization1_epi A hs f)) ee).
            set (t := PullbackArrow_PullbackPr1
                        Pb _ (PEqEpi1 PE)
                        ((PEqEpi2 PE) · (PFiber_Elem P) · (factorization1_epi A hs f)) ee).
            use (isEpi_precomp _ tmp). unfold tmp. use (isEpi_path _ _ _ (! t)).
            apply EpiisEpi.
        }
        set (q := PullbackSqrCommutes Pb).
        assert (e1 : h = (inv_from_iso (isopair _ (is_iso_qinv _ _ i)))
                           · PullbackPr2 Pb · factorization1_monic A f).
        {
          rewrite <- assoc. rewrite <- q. rewrite assoc.
          set (tmp := iso_after_iso_inv (isopair _ (is_iso_qinv _ _ i))).
          cbn in tmp. cbn. rewrite tmp.
          rewrite id_left. apply idpath.
        }
        use unique_exists.
        * exact (inv_from_iso (isopair (PullbackPr1 Pb) (is_iso_qinv _ _ i)) · PullbackPr2 Pb).
        * cbn. cbn in e1. rewrite <- e1. apply idpath.
        * intros y0. apply hs.
        * intros y0 XX. cbn in XX.
          use (KernelArrowisMonic (to_Zero A) (Abelian.Image f)). rewrite XX.
          apply e1.
  Qed.

  (** *** Difference criteria *)

  (** **** Data for Difference *)
  Definition PDiff {x y : ob A} {a a' : PseudoElem x} (f : x --> y)
             (H : PEq (PseudoIm a f) (PseudoIm a' f)) : UU :=
    ∑ (a'' : PseudoElem x) (H' : a'' · f = ZeroArrow (to_Zero A) _ _),
    ∏ (z : ob A) (g : x --> z),
    a · g = ZeroArrow (to_Zero A) _ _ -> PEq (PseudoIm a' g) (PseudoIm a'' g).

  Definition mk_PDiff {x y : ob A} {a a' : PseudoElem x} (f : x --> y)
             (H : PEq (PseudoIm a f) (PseudoIm a' f)) (a'' : PseudoElem x)
             (H' : a'' · f = ZeroArrow (to_Zero A) _ _)
             (H'' : ∏ (z : ob A) (g : x --> z),
                    a · g = ZeroArrow (to_Zero A) _ _ -> PEq (PseudoIm a' g) (PseudoIm a'' g)) :
    PDiff f H := (a'',,(H',,H'')).

  Definition PDiffElem {x y : ob A} {a a' : PseudoElem x} {f : x --> y}
             {H : PEq (PseudoIm a f) (PseudoIm a' f)} (PD : PDiff f H) : PseudoElem x := pr1 PD.
  Coercion PDiffElem : PDiff >-> PseudoElem.

  Definition PDiffIm {x y : ob A} {a a' : PseudoElem x} {f : x --> y}
             {H : PEq (PseudoIm a f) (PseudoIm a' f)} (PD : PDiff f H) :
    PD · f = ZeroArrow (to_Zero A) _ _ := pr1 (pr2 PD).

  Definition PDiffEq {x y : ob A} {a a' : PseudoElem x} {f : x --> y}
             {H : PEq (PseudoIm a f) (PseudoIm a' f)} (PD : PDiff f H) :
    ∏ (z : ob A) (g : x --> z),
    a · g = ZeroArrow (to_Zero A) _ _ -> PEq (PseudoIm a' g) (PseudoIm PD g) := pr2 (pr2 PD).

  (** **** Difference criteria *)
  Local Opaque to_binop to_inv.

  Local Lemma PEq_Diff_Eq1 {x y : ob A} {a a' : PseudoElem x} (f : x --> y)
        (H : PEq (PseudoIm a f) (PseudoIm a' f)) :
    let PA := (AbelianToAdditive A hs) : PreAdditive in
    @to_binop PA _ _ (PEqEpi2 H · a) (PEqEpi1 H · @to_inv PA _ _ a') · f =
    ZeroArrow (to_Zero A) _ _.
  Proof.
    intros PA.
    set (tmp := PEqEq H). cbn in tmp.
    set (tmp' := @to_postmor_linear' PA _ _ _ (PEqEpi2 H · a) (PEqEpi1 H · @to_inv PA _ _ a') f).
    use (pathscomp0 tmp'). clear tmp'. rewrite assoc in tmp. rewrite assoc in tmp.
    cbn in tmp. cbn. rewrite <- tmp. clear tmp.
    set (tmp' := @to_postmor_linear' PA _ _ _ (PEqEpi1 H · a') (PEqEpi1 H · @to_inv PA _ _ a') f).
    use (pathscomp0 (! tmp')). clear tmp'.
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ f). apply cancel_postcomposition.
    set (tmp' := @to_premor_linear' PA _ _ _ (PEqEpi1 H) a' (@to_inv PA _ _ a')).
    use (pathscomp0 (! tmp')). clear tmp'.
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ (PEqEpi1 H)). apply cancel_precomposition.
    use (@to_rinvax' PA).
  Qed.

  Local Lemma PEq_Diff_Eq2 {x y : ob A} {a a' : PseudoElem x} (f : x --> y)
        (H : PEq (PseudoIm a f) (PseudoIm a' f)) {z0 : A} {g : A ⟦ x, z0 ⟧}
        (X : a · g = ZeroArrow (to_Zero A) (PseudoOb a) z0) :
    let PA := (AbelianToAdditive A hs) : PreAdditive in
    identity (PEqOb H) · (@to_binop PA (PEqOb H) x (PEqEpi2 H · a)
                                     (PEqEpi1 H · @to_inv PA _ _ a') · g) =
    @to_inv PA _ _ (PEqEpi1 H) · (a' · g).
  Proof.
    intros PA.
    rewrite id_left. cbn.
    set (tmp := PEqEq H). cbn in tmp.
    set (tmp' := @to_postmor_linear' PA _ _ _ (PEqEpi2 H · a) (PEqEpi1 H · @to_inv PA _ _ a') g).
    use (pathscomp0 tmp'). clear tmp'. rewrite <- assoc. cbn. rewrite X. rewrite ZeroArrow_comp_right.
    rewrite (@to_lunax'' PA). rewrite assoc. apply cancel_postcomposition.
    rewrite <- (@PreAdditive_invlcomp PA). rewrite <- (@PreAdditive_invrcomp PA).
    apply idpath.
  Qed.

  Definition PEq_Diff {x y : ob A} {a a' : PseudoElem x} (f : x --> y)
        (H : PEq (PseudoIm a f) (PseudoIm a' f)) : PDiff f H.
  Proof.
    set (PA := (AbelianToAdditive A hs) : PreAdditive).
    use mk_PDiff.
    - exact (mk_PseudoElem (@to_binop PA _ _ (PEqEpi2 H · a)
                                      (PEqEpi1 H · (@to_inv (AbelianToAdditive A hs) _ _ a')))).
    - exact (PEq_Diff_Eq1 f H).
    - intros z0 g X.
      use (mk_PEq _ _ (identity_Epi _)).
      + cbn. exact (mk_Epi _ _ (to_inv_isEpi PA _ (EpiisEpi PA (PEqEpi1 H)))).
      + cbn. exact (PEq_Diff_Eq2 f H X).
  Defined.

  (** *** Pullback using pseudo elements *)

  Local Lemma PEq_Pullback_Eq {x y z : ob A} (f : x --> z) (g : y --> z) (Pb : Pullback f g)
             (a : PseudoElem x) (b : PseudoElem y) (H : PEq (PseudoIm a f) (PseudoIm b g)) :
    PEqEpi2 H · a · f = PEqEpi1 H · b · g.
  Proof.
    rewrite <- assoc. rewrite <- assoc. apply pathsinv0. exact (PEqEq H).
  Qed.

  Local Lemma PEq_Pullback_Eq1 {x y z : ob A} (f : x --> z) (g : y --> z) (Pb : Pullback f g)
        (a : PseudoElem x) (b : PseudoElem y) (H : PEq (PseudoIm a f) (PseudoIm b g)) :
    PEqEpi2 H · a = (identity (PEqOb H))
                       · ((PullbackArrow Pb (PEqOb H) (PEqEpi2 H · a) (PEqEpi1 H · b)
                                          (PEq_Pullback_Eq f g Pb a b H))
                             · PullbackPr1 Pb).
  Proof.
    rewrite id_left.
    use (! (PullbackArrow_PullbackPr1 Pb _ (PEqEpi2 H · a) (PEqEpi1 H · b)
                                      (PEq_Pullback_Eq f g Pb a b H))).
  Qed.

  Local Lemma PEq_Pullback_Eq2 {x y z : ob A} (f : x --> z) (g : y --> z) (Pb : Pullback f g)
        (a : PseudoElem x) (b : PseudoElem y) (H : PEq (PseudoIm a f) (PseudoIm b g)) :
    PEqEpi1 H · b = (identity (PEqOb H))
                       · ((PullbackArrow Pb (PEqOb H) (PEqEpi2 H · a) (PEqEpi1 H · b)
                                          (PEq_Pullback_Eq f g Pb a b H))
                             · (PullbackPr2 Pb)).
  Proof.
    rewrite id_left.
    use (! (PullbackArrow_PullbackPr2 Pb _ (PEqEpi2 H · a) (PEqEpi1 H · b)
                                      (PEq_Pullback_Eq f g Pb a b H))).
  Qed.

  Definition PEq_Pullback {x y z : ob A} (f : x --> z) (g : y --> z) (Pb : Pullback f g)
             (a : PseudoElem x) (b : PseudoElem y) (H : PEq (PseudoIm a f) (PseudoIm b g)) :
    ∑ (d : PseudoElem Pb), (PEq (PseudoIm d (PullbackPr1 Pb)) a)
                             × (PEq (PseudoIm d (PullbackPr2 Pb))) b.
  Proof.
    set (mor1 := PEqEpi1 H · b). set (mor2 := PEqEpi2 H · a).
    use tpair.
    - exact (mk_PseudoElem (PullbackArrow Pb _ mor2 mor1 (PEq_Pullback_Eq f g Pb a b H))).
    - cbn. split.
      + use mk_PEq.
        * exact (PEqOb H).
        * exact (PEqEpi2 H).
        * exact (identity_Epi _).
        * exact (PEq_Pullback_Eq1 f g Pb a b H).
      + use mk_PEq.
        * exact (PEqOb H).
        * exact (PEqEpi1 H).
        * exact (identity_Epi _).
        * exact (PEq_Pullback_Eq2 f g Pb a b H).
  Defined.

End def_pseudo_element.
