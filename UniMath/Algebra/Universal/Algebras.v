(** * Basic definitions for universal algebras *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HLists.
Require Import UniMath.Algebra.Universal.Signatures.

Declare Scope sorted_scope.

Delimit Scope sorted_scope with sorted.

Local Open Scope sorted_scope.

Definition sUU (S: UU): UU := S → UU.

Definition sfun {S: UU} (X Y: sUU S): UU := ∏ s: S, X s → Y s.

Infix "s→" := sfun (at level 99, right associativity): sorted_scope.

Definition idsfun {S: UU} (X: sUU S): X s→ X := λ s: S, idfun (X s).

Definition sunit (S: UU): sUU S := λ σ: S, unit.

Definition tosunit {S: UU} {X: sUU S}: X s→ sunit S := λ σ: S, tounit.

Lemma iscontr_sfuntosunit {S: UU} {X: sUU S}: iscontr (X s→ sunit S).
Proof.
  apply impred_iscontr.
  intros.
  apply iscontrfuntounit.
Defined.

Definition scomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y): sfun X Z
  := λ s: S, (f s) ∘ (g s).

Infix "∘" := scomp: sorted_scope.

Definition shSet (S: UU): UU := S → hSet.

Definition sunitset (S: UU): shSet S := λ _, unitset.

Lemma isaset_set_sfun_space {S: UU} {X Y: shSet S}: isaset (X s→ Y).
Proof.
  apply impred_isaset.
  intros.
  apply isaset_forall_hSet.
Defined.

Definition star {S: UU} (X: sUU S): sUU (list S) := λ l: list S, HList (map X l).

Notation "A *" := (star A) (at level 10): sorted_scope.

Definition starfun {S: UU} {X Y: sUU S} (f: sfun X Y): sfun (star X) (star Y)
  := list_ind (λ arity, star X arity → star Y arity)
              (idfun unit)
              (λ (x: S) (xs: list S) HP, (dirprodf (f x) HP)).

Notation "f **" := (starfun f) (at level 10): sorted_scope.

Lemma staridfun {S: UU} {X: sUU S} (l: list S) (x: (star X) l): (idsfun X)** _ x = idsfun (X*) _ x.
Proof.
  change (idsfun (X*) l x) with x.
  revert l x.
  refine (list_ind _ _ _).
  - apply idpath.
  - intros σ σs HP x.
    change (X* (cons σ σs)) with (dirprod (X σ) (X* σs)) in x.
    induction x as [x1 x2].
    change ((idsfun X)** (cons σ σs)) with (dirprodf (idsfun X σ) ((idsfun X)** σs)).
    cbv [dirprodf make_dirprod].
    rewrite HP.
    apply idpath.
Defined.

Lemma starcomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y) (l: list S) (x: (star X) l)
  : (f ∘ g) ** _ x = f** _ (g** _ x).
Proof.
  revert l x.
  refine (list_ind _ _ _).
  - apply idpath.
  - intros σ σs HP x.
    change (((f ∘ g) **) (cons σ σs)) with (dirprodf ((f ∘ g) σ) (((f ∘ g))** σs)).
    cbv [dirprodf make_dirprod].
    rewrite HP.
    apply idpath.
Defined.

(** ** Algebras for a given signature *)

Section Algebra.

  Definition algebra (Σ: signature): UU
    := ∑ A: shSet (sorts Σ), ∏ σ: Σ, A* (arity σ) → A (sort σ).

  Definition supportset {Σ: signature} (A: algebra Σ) := pr1 A.

  Coercion supportset: algebra >-> shSet.

  Definition support {Σ: signature} (A: algebra Σ): sUU (sorts Σ) := pr1 A.

  Coercion support: algebra >-> sUU.

  Definition ops {Σ: signature} (A: algebra Σ) := pr2 A.

  Coercion ops: algebra >-> Funclass.

  Definition make_algebra {Σ: signature} (A : shSet (sorts Σ)) (ops: ∏ σ: Σ, A* (arity σ) → A (sort σ))
    : algebra Σ := A ,, ops.

  Definition dom {Σ: signature} (A: algebra Σ) (σ: Σ): UU := A* (arity σ).

  Definition rng {Σ: signature} (A: algebra Σ) (σ: Σ): UU := support A (sort σ).

  Definition make_algebra_simple_single_sorted (Σ: signature_simple_single_sorted) (A : hSet)
             (ops: HList (map (λ n: nat, Vector A n → A) Σ)): algebra Σ.
  Proof.
    exists (λ _, A).
    unfold arity.
    revert Σ ops.
    refine (list_ind _ _ _).
    - intros.
      cbn in σ.
      apply fromstn0.
      assumption.
    - simpl.
      intros x xs HPind ops.
      change ( (Vector A x → A) × (HList  (map (λ n0 : nat, Vector A n0 → A) xs))) in ops.
      induction ops as [op ops].
      intro.
      cbn in σ.
      induction σ as [σ σproof].
      induction σ.
      + unfold star.
        rewrite map_list_fill.
        rewrite hlist_uniform.
        rewrite length_list_fill.
        exact op.
      + change  (nth (x :: xs) (S σ,, σproof)) with (nth xs (σ ,, σproof)).
        exact (HPind ops  (σ ,, σproof)).
  Defined.

  Definition make_algebra_simple (Σ: signature_simple) (A: Vector hSet (pr1 Σ)) 
                                 (ops: HList (map (λ a, (el A)* (dirprod_pr1 a) → el A (dirprod_pr2 a)) (pr2 Σ)))
    : algebra Σ.
  Proof.
    exists (el A).
    unfold arity.
    induction Σ as [ns ar].
    simpl in A.
    revert ar ops.
    refine (list_ind _ _ _).
    - intros.
      cbn in σ.
      apply fromstn0.
      assumption.
    - simpl.
      intros x xs HPind ops.
      rewrite map_cons in ops.
      rewrite hlist_cons in ops.
      induction ops as [op ops].
      intro.
      cbn in σ.
      induction σ as [σ σproof].
      induction σ.
      + unfold star.
        exact op.
      + exact (HPind ops  (σ ,, σproof)).
  Defined.

End Algebra.

(** ** Homomorphisms of algebras *)

Section Homomorphism.

  Context {Σ: signature}.

  Definition ishom {A1 A2: algebra Σ} (h: A1 s→ A2) : UU
    := ∏ (σ: Σ) (x: dom A1 σ), h _ (A1 σ x) = A2 σ (h** _ x).

  Definition hom (A1 A2: algebra Σ): UU := ∑ (h: A1 s→ A2), ishom h.

  Local Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity).

  Definition hom2fun {A1 A2: algebra Σ} (f: A1 ↦ A2):= pr1 f.

  Coercion hom2fun: hom >-> sfun.

  Definition hom2axiom {A1 A2: algebra Σ} (f: A1 ↦ A2):= pr2 f.

  Definition make_hom {A1 A2: algebra Σ} {f: sfun A1 A2} (is: ishom f): A1 ↦ A2 := f ,, is.

  Theorem isapropishom {A1 A2: algebra Σ} (f: sfun A1 A2): isaprop (ishom f).
  Proof.
    red.
    apply impred_isaprop.
    intros.
    apply impred_isaprop.
    intros.
    apply setproperty.
  Defined.

  Theorem isasethom (A1 A2: algebra Σ): isaset (A1 ↦ A2).
  Proof.
    red.
    apply isaset_total2.
    - apply isaset_set_sfun_space.
    - intros.
      apply isasetaprop.
      apply isapropishom.
  Defined.

  Lemma ishomid (A: algebra Σ): ishom (idsfun A).
  Proof.
    red.
    intros.
    rewrite staridfun.
    apply idpath.
  Defined.

  Definition homid (A: algebra Σ): A ↦ A := make_hom (ishomid A).

  Lemma ishomcomp  {A1 A2 A3: algebra Σ} (h1: A1 ↦ A2) (h2: A2 ↦ A3): ishom (h2 ∘ h1).
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

  Definition homcomp {a1 a2 a3: algebra Σ} (h1: a1 ↦ a2) (h2: a2 ↦ a3) : a1 ↦ a3
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

  Definition unitalgebra (Σ: signature): algebra Σ
    := make_algebra (sunitset (sorts Σ)) tosunit.

  Context {Σ: signature}.

  Lemma ishomtounit (A: algebra Σ): @ishom Σ A (unitalgebra Σ) tosunit.
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition unithom (A : algebra Σ): hom A (unitalgebra Σ)
    := make_hom (ishomtounit A).

  Theorem iscontrhomstounit (A: algebra Σ): iscontr (hom A (unitalgebra Σ)).
  Proof.
    exists (unithom A).
    intro.
    apply subtypePairEquality'.
    - apply proofirrelevancecontr.
      apply iscontr_sfuntosunit.
    - apply isapropishom.
  Defined.

End Unitalgebra.
