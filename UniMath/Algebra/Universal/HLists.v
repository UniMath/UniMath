(** * Basic definitions for heterogeneous vectors *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Algebra.Universal.MoreLists.

Local Open Scope stn.

Definition HList : ∏ (l: list UU), UU :=
  list_ind (λ _, UU) unit (λ x xs HPind, x × HPind).

Declare Scope hlist_scope.

Delimit Scope hlist_scope with hlist.

Local Open Scope hlist_scope.

Bind Scope hlist_scope with HList.

(** *** Constructors. *)

Definition hnil : HList nil := tt.

Definition hcons {A: UU} (x: A) {l: list UU} (hv: HList l) : HList (cons A l) := x ,, hv.

Notation "[ x ; .. ; y ]" := (hcons x .. (hcons y hnil) ..): hlist_scope.

Notation "[]" := hnil (at level 0, format "[]"): hlist_scope.

Infix "::" := hcons: hlist_scope.

Definition mk_hlist {n: nat} {P: ⟦ n ⟧ → UU} (f: ∏ i: ⟦ n ⟧, P i) : HList (functionToList _ P).
Proof.
  induction n.
  - exact hnil.
  - exact (hcons (f firstelement) (IHn (P ∘ dni_firstelement) (f ∘ dni_firstelement))).
Defined.

Lemma hlist_cons (x: UU) (xs: list UU): HList (x :: xs) = (x × HList xs).
Proof. apply idpath. Defined. 

(** *** Projections. *)

Definition hhd {A: UU} {l: list UU} (hv: HList (cons A l)): A := pr1 hv.

Definition htl {A: UU} {l: list UU} (hv: HList (cons A l)): HList l := pr2 hv.

Definition hnth {l: list UU} (hv: HList l): ∏ i: ⟦ length l ⟧, nth l i.
Proof.
  revert l hv.
  refine (list_ind _ _ _).
  - intros.
    apply (fromempty (negnatlthn0 (pr1 i) (pr2 i))).
  - intros x  xs HPind.
    induction i as [i iproof].
    induction i.
    + exact (hhd hv).
    + exact (HPind (htl hv) (make_stn _ i iproof)).
Defined.

(** *** HList and standard vectors *)

Lemma hlist_uniform {A: UU} {n: nat}: HList (list_fill A n) = Vector A n.
Proof.
  induction n.
  - apply idpath.
  - change ((A × HList (list_fill A n)) = (A × Vector A n)).
    apply maponpaths.
    exact IHn.
Defined.

