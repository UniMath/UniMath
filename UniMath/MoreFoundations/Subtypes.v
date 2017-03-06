Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Propositions.

Delimit Scope subtype with subtype.

Local Open Scope subtype.

Local Open Scope logic.

Definition subtype_set X : hSet := hSetpair (hsubtype X) (isasethsubtype X).

Definition subtype_isIn {X:UU} {S:hsubtype X} (s:S) (T:hsubtype X) : hProp := T (pr1 s).

Notation " s ∈ T " := (subtype_isIn s T) (at level 70) : subtype.

Notation " s ∉ T " := (¬ (subtype_isIn s T) : hProp) (at level 70) : subtype.

Definition subtype_containedIn {X:UU} : hrel (subtype_set X) := λ S T, ∀ x:X, S x ⇒ T x.

Notation " S ⊆ T " := (subtype_containedIn S T) (at level 70) : subtype.

Definition subtype_notContainedIn {X:UU} (S T : hsubtype X) : hProp := ∃ x:X, S x ∧ ¬ (T x).

Definition subtype_inc {X:UU} {S T : hsubtype X} : S ⊆ T -> S -> T.
Proof.
  intros le s. exact (pr1 s,, le (pr1 s) (pr2 s)).
Defined.

Notation " S ⊈ T " := (subtype_notContainedIn S T) (at level 70) : subtype.

Definition subtype_smallerThan {X:UU} (S T : hsubtype X) : hProp := (S ⊆ T) ∧ (T ⊈ S).

Notation " S ⊊ T " := (subtype_smallerThan S T) (at level 70) : subtype.

Local Open Scope logic.

Definition subtype_equal {X:UU} (S T : hsubtype X) : hProp := ∀ x, S x ⇔ T x.

Notation " S ≡ T " := (subtype_equal S T) (at level 70) : subtype.

Definition subtype_notEqual {X:UU} (S T : hsubtype X) : hProp := (S ⊈ T) ∨ (T ⊈ S).

Notation " S ≢ T " := (subtype_notEqual S T) (at level 70) : subtype.

Definition subtype_difference {X:UU} (S T : hsubtype X) : hsubtype X := λ x, S x ∧ ¬ (T x).

Notation " S - T " := (subtype_difference S T) : subtype.

Definition subtype_difference_containedIn {X:UU} (S T : hsubtype X) : (S - T) ⊆ S.
Proof.
  intros x u. exact (pr1 u).
Defined.

Lemma subtype_equal_cond {X:UU} (S T : hsubtype X) : ((S ⊆ T) ∧ (T ⊆ S)) ⇔ (S ≡ T).
Proof.
  split.
  - intros c x. induction c as [st ts].
    split.
    + intro s. exact (st x s).
    + intro t. exact (ts x t).
  - intro e. split.
    + intros x s. exact (pr1 (e x) s).
    + intros x t. exact (pr2 (e x) t).
Defined.

Definition subtype_union {X I:UU} (S : I -> hsubtype X) : hsubtype X := λ x, ∃ i, S i x.

Notation "⋃ S" := (subtype_union S) (at level 100, no associativity) : subtype.

Theorem hsubtype_univalence {X:UU} (S T : hsubtype X) : (S = T) ≃ (S ≡ T).
Proof.
  intros. intermediate_weq (∏ x, S x = T x).
  - apply weqtoforallpaths.
  - unfold subtype_equal. apply weqonsecfibers; intro x.
    apply weqlogeq.
Defined.

Theorem hsubtype_rect {X:UU} (S T : hsubtype X) (P : S ≡ T -> UU) :
  (∏ e : S=T, P (hsubtype_univalence S T e)) ≃ ∏ f, P f.
Proof.
  intros. apply weqinvweq, weqonsecbase.
Defined.

Ltac hsubtype_induction f e := generalize f; apply hsubtype_rect; intro e; clear f.

Lemma subtype_containment_isPartialOrder X : isPartialOrder (@subtype_containedIn X).
Proof.
  repeat split.
  - intros S T U i j x. exact (j x ∘ i x).
  - intros S x s. exact s.
  - intros S T i j. apply (invmap (hsubtype_univalence S T)). now apply subtype_equal_cond.
Defined.

Lemma subtype_inc_comp {X:UU} {S T U : hsubtype X} (i:S⊆T) (j:T⊆U) (s:S) :
  subtype_inc j (subtype_inc i s) = subtype_inc (λ x, j x ∘ i x) s.
Proof.
  reflexivity.
Defined.

Lemma subtype_deceq {X} (S:hsubtype X) : isdeceq X -> isdeceq S.
Proof.
  intro i. intros s t. induction (i (pr1 s) (pr1 t)) as [eq|ne].
  - apply ii1, subtypeEquality_prop, eq.
  - apply ii2. intro eq. apply ne. apply maponpaths. exact eq.
Defined.

Definition subtype_decidable {X} (S:hsubtype X) := ∏ x, decidable (S x).

Definition carrier_set {X : hSet} (S : hsubtype X) : hSet :=
  hSetpair (carrier S) (isaset_carrier_subset _ S).
