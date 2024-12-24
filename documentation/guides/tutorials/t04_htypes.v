Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Definition iscontr_weq_unit
  {X : UU}        (* The curly braces make `X` implicit, so coq infers it from the type of H, and the signature will be `iscontr_weq_unit H` *)
  (H : iscontr X)
  : X ≃ unit.
Proof.
  use weq_iso.
  - intro x.
    exact tt.
  - intro t.
    exact (iscontrpr1 H).
  - intro x.      (* The goal is now `iscontrpr1 H = x` *)
    exact (!iscontr_uniqueness H x).
  - intro y.      (* The goal is now `tt = y` *)
    induction y.
    reflexivity.
Defined.

Definition iscontr_weq_unit'
  {X : UU}
  (H : iscontr X)
  : X ≃ unit.
Proof.
  use weq_iso.
  - intro x.
    exact tt.
  - intro t.
    apply H.
  - intro x.
    symmetry.
    apply H.
  - intro y.
    induction y.
    reflexivity.
Defined.

Definition is_infinite
  (m : nat)
  : UU
  := ∏ (n : nat), n < m.

Lemma isaprop_is_infinite
  (m : nat)
  : isaprop (is_infinite m).
Proof.
  apply impred_isaprop.
  intro n.
  unfold natlth.
  unfold natgth.    (* `n < m` is defined as `natgtb m n = true` *)
  apply isasetbool. (* Since bool is a set, any two equality proofs in bool are the same *)
Qed.

Definition is_finite
  (m : nat)
  : UU
  := ∥ ∑ (n : nat), m ≤ n ∥.

Lemma nat_is_finite
  (m : nat)
  : is_finite m.
Proof.
  apply hinhpr.       (* This changes the goal to ∑ n, m ≤ n *)
  exists m.           (* This changes the goal to m ≤ m *)
  apply isreflnatleh.
Qed.

Lemma is_finite_to_is_not_infinite
  (m : nat)
  : is_finite m → ¬ (is_infinite m).
Proof.
  (* `¬ P` is defined as `P → ∅`, so by introducing `Hi`, the goal becomes `∅` *)
  intros Hf Hi.
  (* The revert tactic puts Hf back into the goal, so the goal becomes `is_finite m → ∅`. *)
  revert Hf.
  (* Applying `factor_through_squash` splits the goal into `isaprop empty` and `(∑ n, m ≤ n) → ∅` *)
  apply factor_through_squash.
  - exact isapropempty.
  - intro Hf.
    (* We will use a lemma which says that we cannot have `pr1 Hf < m` and `pr1 Hf ≥ m` at the same time *)
    apply (natlthtonegnatgeh (pr1 Hf) m).
    + apply Hi.
    + apply Hf.
Qed.
