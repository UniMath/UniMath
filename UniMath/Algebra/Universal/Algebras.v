(** * Basic definitions for universal algebras *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HLists.
Require Export UniMath.Algebra.Universal.SortedTypes.
Require Import UniMath.Algebra.Universal.Signatures.

(** ** Algebras for a given signature *)

Local Open Scope sorted.

Section Algebra.

  Definition algebra (σ: signature): UU
    := ∑ A: shSet (sorts σ), ∏ nm: σ, A* (arity nm) → A (sort nm).

  Definition supportset {σ: signature} (A: algebra σ) := pr1 A.

  Coercion supportset: algebra >-> shSet.

  Definition support {σ: signature} (A: algebra σ): sUU (sorts σ) := pr1 A.

  Coercion support: algebra >-> sUU.

  Definition ops {σ: signature} (A: algebra σ) := pr2 A.

  Coercion ops: algebra >-> Funclass.

  Definition make_algebra {σ: signature} (A : shSet (sorts σ)) (ops: ∏ nm: σ, A* (arity nm) → A (sort nm))
    : algebra σ := A ,, ops.

  Definition dom {σ: signature} (A: algebra σ) (nm: σ): UU := A* (arity nm).

  Definition rng {σ: signature} (A: algebra σ) (nm: σ): UU := support A (sort nm).

  Definition make_algebra_simple_single_sorted (σ: signature_simple_single_sorted) (A : hSet)
             (ops: HList (map (λ n: nat, Vector A n → A) σ)): algebra σ.
  Proof.
    exists (λ _, A).
    unfold arity.
    revert σ ops.
    refine (list_ind _ _ _).
    - intros.
      cbn in nm.
      apply fromstn0.
      assumption.
    - simpl.
      intros x xs HPind ops.
      change ( (Vector A x → A) × (HList  (map (λ n0 : nat, Vector A n0 → A) xs))) in ops.
      induction ops as [op ops].
      intro.
      cbn in nm.
      induction nm as [nm nmproof].
      induction nm.
      + unfold star.
        rewrite map_const.
        rewrite hlist_fill.
        rewrite length_fill.
        exact op.
      + change  (nth (x :: xs) (S nm,, nmproof)) with (nth xs (nm ,, nmproof)).
        exact (HPind ops  (nm ,, nmproof)).
  Defined.

  Definition make_algebra_simple (σ: signature_simple) (A: Vector hSet (pr1 σ)) 
                                 (ops: HList (map (λ a, (el A)* (dirprod_pr1 a) → el A (dirprod_pr2 a)) (pr2 σ)))
    : algebra σ.
  Proof.
    exists (el A).
    unfold arity.
    induction σ as [ns ar].
    simpl in A.
    revert ar ops.
    refine (list_ind _ _ _).
    - intros.
      cbn in nm.
      apply fromstn0.
      assumption.
    - simpl.
      intros x xs HPind ops.
      rewrite map_cons in ops.
      rewrite hlist_cons in ops.
      induction ops as [op ops].
      intro.
      cbn in nm.
      induction nm as [nm nmproof].
      induction nm.
      + unfold star.
        exact op.
      + exact (HPind ops  (nm ,, nmproof)).
  Defined.

End Algebra.

(** ** Homomorphisms of algebras *)

Section Homomorphism.

  Context {σ: signature}.

  Definition ishom {A1 A2: algebra σ} (h: A1 s→ A2) : UU
    := ∏ (nm: σ) (x: dom A1 nm), h _ (A1 nm x) = A2 nm (h** _ x).

  Definition hom (A1 A2: algebra σ): UU := ∑ (h: A1 s→ A2), ishom h.

  Local Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity).

  Definition hom2fun {A1 A2: algebra σ} (f: A1 ↦ A2):= pr1 f.

  Coercion hom2fun: hom >-> sfun.

  Definition hom2axiom {A1 A2: algebra σ} (f: A1 ↦ A2):= pr2 f.

  Definition make_hom {A1 A2: algebra σ} {f: sfun A1 A2} (is: ishom f): A1 ↦ A2 := f ,, is.

  Theorem isapropishom {A1 A2: algebra σ} (f: sfun A1 A2): isaprop (ishom f).
  Proof.
    red.
    apply impred_isaprop.
    intros.
    apply impred_isaprop.
    intros.
    apply setproperty.
  Defined.

  Theorem isasethom (A1 A2: algebra σ): isaset (A1 ↦ A2).
  Proof.
    red.
    apply isaset_total2.
    - apply isaset_set_sfun_space.
    - intros.
      apply isasetaprop.
      apply isapropishom.
  Defined.

  Lemma ishomid (A: algebra σ): ishom (idsfun A).
  Proof.
    red.
    intros.
    rewrite staridfun.
    apply idpath.
  Defined.

  Definition homid (A: algebra σ): A ↦ A := make_hom (ishomid A).

  Lemma ishomcomp  {A1 A2 A3: algebra σ} (h1: A1 ↦ A2) (h2: A2 ↦ A3): ishom (h2 ∘ h1).
  Proof.
    red.
    intros.
    induction h1 as [h1 ishomh1].
    induction h2 as [h2 ishomh2].
    cbn.
    rewrite starcomp.
    rewrite ishomh1.
    rewrite ishomh2.
    apply idpath.
  Defined.

  Definition homcomp {a1 a2 a3: algebra σ} (h1: a1 ↦ a2) (h2: a2 ↦ a3) : a1 ↦ a3
    := make_hom (ishomcomp h1 h2).

End Homomorphism.

(** ** Declaring the scope [hom_scope] for homomorphisms *)

Declare Scope hom_scope.

Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity): hom_scope.

Delimit Scope hom_scope with hom.

Bind Scope hom_scope with hom.

Local Open Scope hom.

(** ** The unit algebra with a single element and the proof it is final *)

Section Unitalgebra.

  Definition unitalgebra (σ: signature): algebra σ
    := make_algebra (sunitset (sorts σ)) tosunit.

  Context {σ: signature}.

  Lemma ishomtounit (A: algebra σ): @ishom σ A (unitalgebra σ) tosunit.
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition unithom (A : algebra σ): hom A (unitalgebra σ)
    := make_hom (ishomtounit A).

  Theorem iscontrhomstounit (A: algebra σ): iscontr (hom A (unitalgebra σ)).
  Proof.
    exists (unithom A).
    intro.
    apply subtypePairEquality'.
    - apply proofirrelevancecontr.
      apply iscontr_sfuntosunit.
    - apply isapropishom.
  Defined.

End Unitalgebra.
