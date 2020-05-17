(** * Basic definitions for universal algebras *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Terms.

(** ** Algebras for a given signature *)

Section Algebra.

  Definition dom {sigma: signature} (support: UU) (nm: names sigma): UU
    := Vector support (arity nm).

  Definition cod {sigma: signature} (support: UU) (nm: names sigma): UU
    := support.

  Definition algebra (sigma: signature): UU
    := ∑ (support: hSet), ∏ (nm: names sigma), dom support nm → cod support nm.

  Coercion support {sigma: signature} (a: algebra sigma): hSet := pr1 a.

  Definition op {sigma: signature} (a: algebra sigma) (nm: names sigma)
    : dom a nm → cod a nm := pr2 a nm.

  Definition make_algebra (support : hSet) {sigma: signature}
    (ops: ∏ nm: names sigma, dom support nm → cod support nm)
    : algebra sigma := support ,, ops.

End Algebra.

(** ** Homomorphisms of algebras *)

Section Homomorphism.

  Context {sigma: signature}.

  Definition ishom {a1 a2: algebra sigma} (f: a1 → a2): UU
    := ∏ (nm: names sigma) (x: dom a1 nm), f (op a1 nm x) = (op a2 nm (vector_map f x)).

  Definition hom (a1 a2: algebra sigma): UU := ∑ (f: a1 → a2), ishom f.

  Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity).

  Definition hom2fun {a1 a2: algebra sigma} (f: a1 ↦ a2): support a1 → support a2 := pr1 f.

  Coercion hom2fun: hom >-> Funclass.

  Definition hom2axiom {a1 a2: algebra sigma} (f: a1 ↦ a2): ishom f := pr2 f.

  Definition make_hom {a1 a2: algebra sigma} {f: a1 → a2} (is: ishom f): a1 ↦ a2 := f ,, is.

  Theorem isapropishom {a1 a2: algebra sigma} (f: a1 → a2): isaprop (ishom f).
  Proof.
    red.
    apply impred_isaprop.
    intros.
    apply impred_isaprop.
    intros.
    apply setproperty.
  Defined.

  Theorem isasethom (a1 a2: algebra sigma): isaset (a1 ↦ a2).
  Proof.
    red.
    apply isaset_total2.
    - apply isaset_forall_hSet.
    - intros.
      apply isasetaprop.
      apply isapropishom.
  Defined.

  Lemma ishomidfun (a: algebra sigma): ishom (idfun a).
  Proof.
    red.
    intros.
    rewrite vector_map_id.
    apply idpath.
  Defined.

  Definition homid (a: algebra sigma): a ↦ a := make_hom (ishomidfun a).

  Lemma ishomcomp  {a1 a2 a3: algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3): ishom (h2 ∘ h1).
  Proof.
    red.
    intros.
    induction h1 as [f1 ishomf1].
    induction h2 as [f2 ishomf2].
    cbn.
    rewrite vector_map_comp.
    rewrite ishomf1.
    rewrite ishomf2.
    apply idpath.
  Defined.

  Definition homcomp {a1 a2 a3: algebra sigma} (h1: a1 ↦ a2) (h2: a2 ↦ a3) : a1 ↦ a3
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

  Definition unitalgebra (sigma: signature): algebra sigma
    := make_algebra unitset (λ nm: names sigma, tounit).

  Context {sigma: signature}.

  Lemma ishomtounit (a: algebra sigma)
    : @ishom sigma a (unitalgebra sigma) tounit.
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition unithom (a : algebra sigma): hom a (unitalgebra sigma)
    := make_hom (ishomtounit a).

  Theorem iscontrhomstounit (a: algebra sigma): iscontr (hom a (unitalgebra sigma)).
  Proof.
    exists (unithom a).
    intros.
    apply subtypePairEquality'.
    - apply iscontrfuntounit.
    - apply isapropishom.
  Defined.

End Unitalgebra.

(** ** The term algebra and the proof it is initial *)

Section Termalgebra.

  Definition term_algebra (sigma: signature): algebra sigma
    := make_algebra (termset sigma) build_term.

  Context {sigma: signature}.

  Definition eval (a: algebra sigma): term_algebra sigma → a
    := fromterm (op a).

  Lemma evalstep {a: algebra sigma} (nm: names sigma) (v: Vector (term sigma) (arity nm))
    : eval a (build_term nm v) = op a nm (vector_map (eval a) v).
  Proof.
    unfold eval, fromterm.
    rewrite term_rec_step.
    apply idpath.
  Defined.

  Lemma ishomeval (a: algebra sigma): ishom (eval a).
  Proof.
    red.
    intros.
    simpl.
    apply evalstep.
  Defined.

  Definition evalhom (a: algebra sigma): term_algebra sigma ↦ a
    := make_hom (ishomeval a).

  Definition iscontrhomsfromterm (a: algebra sigma): iscontr (term_algebra sigma ↦ a).
  Proof.
    exists (evalhom a).
    intro.
    rename t into f.
    apply subtypePairEquality'.
    2: apply isapropishom.
    apply funextfun.
    unfold homot.
    apply term_ind.
    unfold term_ind_HP.
    intros.
    change (build_term nm v) with (op (term_algebra sigma) nm v) at 1.
    rewrite (hom2axiom f).
    rewrite evalstep.
    apply maponpaths.
    apply vector_extens.
    intros.
    do 2 rewrite el_vector_map.
    rewrite IH.
    apply idpath.
  Defined.

End Termalgebra.
