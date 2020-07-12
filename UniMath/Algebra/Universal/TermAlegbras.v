(** * Basic definitions for universal algebras *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Signatures.

Declare Scope sortedhSet_scope.

Delimit Scope sortedhSet_scope with shSet.

Open Scope sortedhSet_scope.

Definition sortedhSet (S: hSet): UU := S → hSet.

Definition sortedunit (S: hSet): sortedhSet S := λ σ: S, unitset.

Definition sortedfun {S: hSet} (X Y: sortedhSet S): UU := ∏ s: S, X s → Y s.

Infix "↦" := sortedfun (at level 80, right associativity): sortedhSet_scope.

Lemma isaset_sortedfun {S: hSet} {X Y: sortedhSet S}: isaset (X ↦ Y).
Proof.
  apply impred_isaset.
  intros.
  apply isaset_forall_hSet.
Defined.

Definition idsortedfun {S: hSet} (X: sortedhSet S): X ↦ X := λ s: S, idfun (X s).

Definition tosortedunit {S: hSet} {X: sortedhSet S}: X ↦ sortedunit S := λ σ: S, tounit.

Lemma iscontr_sortedfuntosortedunit {S: hSet} {X: sortedhSet S}: iscontr (X ↦ sortedunit S).
Proof.
  apply impred_iscontr.
  intros.
  apply iscontrfuntounit.
Defined.

Definition compsortedfun {S: hSet} {X Y Z: sortedhSet S} (f: Y ↦ Z) (g: X ↦ Y): sortedfun X Z
  := λ s: S, (f s) ∘ (g s).

Infix "∘" := compsortedfun: sortedhSet_scope.

Definition star {S: hSet} (X: sortedhSet S): sortedhSet (listset S)
  := list_ind (λ _, hSet) unitset (λ x xs HPind, dirprod_hSet (X x) (HPind)).

Notation "A *" := (star A) (at level 10): sortedhSet_scope.
 
Definition starfun {S: hSet} {X Y: sortedhSet S} (f: sortedfun X Y): sortedfun (star X) (star Y)
  := list_ind (λ arity, star X arity → star Y arity)
              (idfun unit)
              (λ (x: S) (xs: list S) HP, (dirprodf (f x) HP)).

Notation "f **" := (starfun f ) (at level 10): sortedhSet_scope.

Lemma staridfun {S: hSet} {X: sortedhSet S} (l: list S) (x: (star X) l): (idsortedfun X)** _ x = idsortedfun (X*) _ x.
Proof.
  change (idsortedfun (X*) l x) with x.
  revert l x.
  refine (list_ind _ _ _).
  - apply idpath.
  - intros σ σs HP x.
    change (X* (cons σ σs)) with (dirprod_hSet (X σ) (X* σs)) in x.
    induction x as [x1 x2].
    change ((idsortedfun X)** (cons σ σs)) with (dirprodf (idsortedfun X σ) ((idsortedfun X)** σs)).
    cbv [dirprodf make_dirprod].
    rewrite HP.
    apply idpath.
Defined.

Lemma starcomp {S: hSet} {X Y Z: sortedhSet S} (f: Y ↦ Z) (g: X ↦  Y) (l: list S) (x: (star X) l)
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

Context {S: hSet}.

(** ** Algebras for a given signature *)

Section Algebra.

  Definition algebra (Σ: signature S): UU
    := ∑ (A: sortedhSet S), ∏ (σ: Σ), A* (arity σ) → A (sort σ).

  Definition support {Σ: signature S} (A: algebra Σ): sortedhSet S := pr1 A.

  Coercion support: algebra >-> sortedhSet.

  Definition ops {Σ: signature S} (A: algebra Σ) := pr2 A.

  Coercion ops: algebra >-> Funclass.

  Definition make_algebra {Σ: signature S} (A : sortedhSet S) (ops: ∏ σ: Σ, A* (arity σ) → A (sort σ))
    : algebra Σ := A ,, ops.

  Definition dom {Σ: signature S} (A: algebra Σ) (σ: Σ): UU := A* (arity σ).

  Definition rng {Σ: signature S} (A: algebra Σ) (σ: Σ): UU := support A (sort σ).

End Algebra.

(** ** Homomorphisms of algebras *)

Section Homomorphism.

  Context {Σ: signature S}.

  Definition ishom {A1 A2: algebra Σ} (h: sortedfun A1 A2) : UU
    := ∏ (σ: Σ) (x: dom A1 σ), h _ (A1 σ x) = A2 σ (h** _ x).

  Definition hom (A1 A2: algebra Σ): UU := ∑ (h: sortedfun A1 A2), ishom h.

  Notation "a1 ↦ a2" := (hom a1 a2) (at level 80, right associativity).

  Definition hom2fun {A1 A2: algebra Σ} (f: A1 ↦ A2):= pr1 f.

  Coercion hom2fun: hom >-> sortedfun.

  Definition hom2axiom {A1 A2: algebra Σ} (f: A1 ↦ A2):= pr2 f.

  Definition make_hom {A1 A2: algebra Σ} {f: sortedfun A1 A2} (is: ishom f): A1 ↦ A2 := f ,, is.

  Theorem isapropishom {A1 A2: algebra Σ} (f: sortedfun A1 A2): isaprop (ishom f).
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
    - apply isaset_sortedfun.
    - intros.
      apply isasetaprop.
      apply isapropishom.
  Defined.

  Lemma ishomid (A: algebra Σ): ishom (idsortedfun A).
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

  Definition unitalgebra (Σ: signature S): algebra Σ
    := make_algebra (sortedunit S) tosortedunit.

  Context {Σ: signature S}.

  Lemma ishomtounit (A: algebra Σ): @ishom Σ A (unitalgebra Σ) tosortedunit.
  Proof.
    red.
    intros.
    apply iscontrunit.
  Defined.

  Definition unithom (A : algebra Σ): hom A (unitalgebra Σ)
    := make_hom (ishomtounit A).


  Theorem iscontrhomstounit (A: algebra Σ): iscontr (hom A (unitalgebra Σ)).
  Proof.
    change (iscontr) with (isofhlevel 0).
    apply isofhleveltotal2.
    - apply iscontr_sortedfuntosortedunit.
    - intros.
      apply iscontraprop1.
      + apply isapropishom.
      + apply ishomtounit.
  Defined.


  Theorem iscontrhomstounit (A: algebra Σ): iscontr (hom A (unitalgebra Σ)).
  Proof.
    change (iscontr) with (isofhlevel 0).
    apply isofhleveltotal2.
    - apply iscontr_sortedfuntosortedunit.
    - intros.
      apply iscontraprop1.
      + apply isapropishom.
      + apply ishomtounit.
  Defined.

End Unitalgebra.

(** ** The term algebra and the proof it is initial *)

Section Termalgebra.

  Definition term_algebra (Σ: signature): algebra Σ
    := make_algebra (termset Σ) build_term.

  Context {Σ: signature}.

  Definition eval (a: algebra Σ): term_algebra Σ → a
    := fromterm (op a).

  Lemma evalstep {a: algebra Σ} (nm: names Σ) (v: Vector (term Σ) (arity nm))
    : eval a (build_term nm v) = op a nm (vector_map (eval a) v).
  Proof.
    unfold eval.
    apply fromtermstep.
  Defined.

  Lemma ishomeval (a: algebra Σ): ishom (eval a).
  Proof.
    red.
    intros.
    simpl.
    apply evalstep.
  Defined.

  Definition evalhom (a: algebra Σ): term_algebra Σ ↦ a
    := make_hom (ishomeval a).

  Definition iscontrhomsfromterm (a: algebra Σ): iscontr (term_algebra Σ ↦ a).
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
    change (build_term nm v) with (op (term_algebra Σ) nm v) at 1.
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
