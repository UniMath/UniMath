Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Propositions.

Delimit Scope subtype with subtype.

Local Open Scope subtype.

Definition subtype_isIn {X:UU} {S:hsubtype X} (s:S) (T:hsubtype X) : hProp := T (pr1 s).

Notation " s ∈ T " := (subtype_isIn s T) (at level 95) : subtype.

Notation " s ∉ T " := (¬ (subtype_isIn s T)) (at level 95) : subtype.

Definition subtype_containedIn {X:UU} (S T : hsubtype X) : hProp.
Proof.
  intros. exists (∏ s:S, s ∈ T). apply impred; intros x. apply propproperty.
Defined.

Notation " S ⊆ T " := (subtype_containedIn S T) (at level 95) : subtype.

Definition subtype_notContainedIn {X:UU} (S T : hsubtype X) : hProp := ∃ s:S, s ∉ T.

Notation " S ⊈ T " := (subtype_notContainedIn S T) (at level 95) : subtype.

Definition subtype_smallerThan {X:UU} (S T : hsubtype X) : hProp := (S ⊆ T) ∧ (T ⊈ S).

Notation " S ⊊ T " := (subtype_smallerThan S T) (at level 95) : subtype.

Local Open Scope logic.

Definition subtype_equal {X:UU} (S T : hsubtype X) : hProp := ∀ x, S x ⇔ T x.

Notation " S ≡ T " := (subtype_equal S T) (at level 95) : subtype.

Definition subtype_notEqual {X:UU} (S T : hsubtype X) : hProp := (S ⊈ T) ∨ (T ⊈ S).

Notation " S ≢ T " := (subtype_notEqual S T) (at level 95) : subtype.

Definition subtype_inc {X:UU} {S T : hsubtype X} : S ⊆ T -> S -> T.
Proof.
  intros le s. exact (pr1 s,, le s).
Defined.

Lemma subtype_equal_cond {X:UU} (S T : hsubtype X) : ((S ⊆ T) ∧ (T ⊆ S)) ⇔ (S ≡ T).
Proof.
  split.
  - intros c x. induction c as [st ts].
    split.
    + intro s. exact (st (x,,s)).
    + intro t. exact (ts (x,,t)).
  - intro e. split.
    + intro s. exact (pr1 (e (pr1 s)) (pr2 s)).
    + intro t. exact (pr2 (e (pr1 t)) (pr2 t)).
Defined.

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

