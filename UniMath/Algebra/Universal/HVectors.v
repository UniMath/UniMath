(** * Basic definitions for heterogeneous lists *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Local Open Scope stn.

Definition HVec {n: nat} (v: Vector UU n): UU.
Proof.
  revert n v.
  exact (vector_ind (λ _ _, UU) unit (λ x _ _ IHv, x × IHv)).
Defined.

Declare Scope hvec_scope.

Delimit Scope hvec_scope with hvec.

Local Open Scope hvec_scope.

Bind Scope hvec_scope with HVec.

(** ** Constructors *)

Definition hvnil : HVec vnil := tt.

Definition hvcons {A: UU} (x: A) {n: nat} {v: Vector UU n} (hv: HVec v) : HVec (A ::: v) := x ,, hv.

Notation "[ x ; .. ; y ]" := (hvcons x .. (hvcons y hvnil) ..): hvec_scope.

Notation "[]" := hvnil (at level 0, format "[]"): hvec_scope.

Infix ":::" := hvcons: hvec_scope.

Definition make_hvec {n: nat} {P: ⟦ n ⟧ → UU} (f: ∏ i: ⟦ n ⟧, P i) : HVec (mk_vector P).
Proof.
  induction n.
  - exact [].
  - exact ((f firstelement) ::: (IHn (P ∘ dni_firstelement) (f ∘ dni_firstelement))).
Defined.

Lemma hvec_cons (x: UU) {n: nat} (xs: Vector UU n): HVec (x ::: xs) = (x × HVec xs).
Proof. apply idpath. Defined.

Definition vec_to_hvec {A: UU} {n: nat} (v: Vector A n): HVec (vector_map  (λ _, A) v).
Proof.
  revert n v.
  apply vector_ind.
  - exact hvnil.
  - intros x n xs IHv.
    exact (x ,, IHv).
Defined.

(** ** Projections *)

Definition hhd {A: UU} {n: nat} {v: Vector UU n} (hv: HVec (A ::: v)): A := pr1 hv.  

Definition htl {A: UU} {n: nat} {v: Vector UU n} (hv: HVec (A ::: v)): HVec v := pr2 hv.

Definition hel {n: nat} {v: Vector UU n} (hv: HVec v): ∏ i: ⟦ n ⟧, el v i.
Proof.
  revert n v hv.
  refine (vector_ind _ _ _).
  - intros.
    apply (fromempty (negnatlthn0 (pr1 i) (pr2 i))).
  - intros x n xs IHv.
    induction i as [i iproof].
    induction i.
    + exact (hhd hv).
    + exact (IHv (htl hv) (make_stn _ i iproof)).
Defined.

(** ** Map of HVecs *)

Definition hmap {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {Q: A → UU} (f: ∏ (a: A), P a → Q a)
                (hv: HVec (vector_map P v)): HVec (vector_map Q v).
Proof.
  revert n v f hv.
  refine (vector_ind _ _ _ ).
  - intros.
    exact hvnil.
  - intros x n xs IHv.
    change ((∏ a : A, P a → Q a) → P x × HVec (vector_map P xs) → Q x × HVec (vector_map Q xs)).
    intros f hv.
    exact (f x (pr1 hv) ::: IHv f (pr2 hv)).
Defined.

Definition hmap_vector {A B: UU} {n: nat} {v: Vector A n} {P: A → UU} (f: ∏ (a: A), P a → B)
                       (hv: HVec (vector_map P v)): Vector B n.
Proof.
  revert n v f hv.
  refine (vector_ind _ _ _).
  - intros.
    exact vnil.
  - intros x n xs IHv.
    change ((∏ a : A, P a → B) → P x × HVec (vector_map P xs) → B × Vector B n).
    intros f hv.
    exact (vcons (f x (pr1 hv)) (IHv f (pr2 hv))).
Defined.

Definition hmap' {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {Q: ∏ (a: A) (p: P a), UU} (f: ∏ (a: A) (p: P a), Q a p)
                (hv: HVec (vector_map P v)): HVec (hmap_vector (λ a pa, Q a pa) hv).
Proof.
  revert n v f hv.
  refine (vector_ind _ _ _ ).
  - intros.
    exact hvnil.
  - intros x n xs IHv f hv.
    exact (f x (pr1 hv) ::: IHv f (pr2 hv)).
Defined.

Lemma helfam {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (hv: HVec (vector_map P v)) (i: ⟦ n ⟧): P (el v i).
Proof.
  revert n v hv i.
  refine (vector_ind _ _ _).
  - intros.
    apply (fromempty (negnatlthn0 (pr1 i) (pr2 i))).
  - intros x n xs IHv.
    induction i as [i iproof].
    induction i.
    + exact (hhd hv).
    + exact (IHv (htl hv) (make_stn _ i iproof)).
Defined.

Lemma el_hmap_vector {A B: UU} {n: nat} {v: Vector A n} {P: A → UU} (f: ∏ (a: A), P a → B)
                     (hv: HVec (vector_map P v)) (i: ⟦ n ⟧)
  : el (hmap_vector f hv) i = f (el v i) (helfam hv i).
Proof.
  revert n v i hv.
  refine (vector_ind _ _ _).
  - intros.
    contradiction (negstn0 i).
  - intros x n xs IHv i hv.
    induction i as [i ilehn].
    induction i.
    + apply idpath.
    + change (el (hmap_vector f hv) (S i,, ilehn)) with (el (hmap_vector f (htl hv)) (i ,, ilehn)).
      change (el (x ::: xs) (S i,, ilehn)) with (el xs (i,, ilehn)).
      change (helfam hv (S i,, ilehn)) with (helfam (htl hv) (i ,, ilehn)).
      apply (IHv (i ,, ilehn) (htl hv)).
Defined.

(** ** HVec and standard vectors *)

Lemma hvec_fill {A: UU} {n: nat}: HVec (vector_fill A n) = Vector A n.
Proof.
  induction n.
  - apply idpath.
  - change ((A × HVec (vector_fill A n)) = (A × Vector A n)).
    apply maponpaths.
    exact IHn.
Defined.

Lemma isofhlevelhvec {m: nat} {n: nat} (v: Vector UU n) (levels: HVec (vector_map (isofhlevel m) v)): isofhlevel m (HVec v).
Proof.
  revert n v levels.
  refine (vector_ind _ _ _).
  - intro.
    apply isofhlevelcontr.
    apply iscontrunit.
  - intros x n xs IH levels.
    rewrite hvec_cons.
    apply isofhleveldirprod.
    + apply (pr1 levels).
    + apply (IH (pr2 levels)).
Defined.
