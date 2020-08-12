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

Definition functionToHVec {n: nat} {P: ⟦ n ⟧ → UU} (f: ∏ i: ⟦ n ⟧, P i) : HVec (mk_vector P).
Proof.
  induction n.
  - exact [].
  - exact ((f firstelement) ::: (IHn (P ∘ dni_firstelement) (f ∘ dni_firstelement))).
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

Lemma hfill {A: UU} {n: nat}: HVec (vector_fill A n) = Vector A n.
Proof.
  induction n.
  - apply idpath.
  - change ((A × HVec (vector_fill A n)) = (A × Vector A n)).
    apply maponpaths.
    exact IHn.
Defined.

Definition hfoldr {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (hv: HVec (vector_map P v))
                  {B: UU} (comb: ∏ (a: A), P a → B → B) (s: B): B.
Proof.
   revert n v hv.
   refine (vector_ind _ _ _).
   - intro.
     exact s.
   - intros x n xs IH.
     simpl.
     intro.
     exact (comb _ (pr1 hv) (IH (pr2 hv))).
Defined.

Lemma isofhlevelhvec {m: nat} {n: nat} (v: Vector UU n) (levels: HVec (vector_map (isofhlevel m) v)): isofhlevel m (HVec v).
Proof.
  revert n v levels.
  refine (vector_ind _ _ _).
  - intro.
    apply isofhlevelcontr.
    apply iscontrunit.
  - intros x n xs IH levels.
    simpl.
    apply isofhleveldirprod.
    + apply (pr1 levels).
    + apply (IH (pr2 levels)).
Defined.

(** ** Map of HVecs *)

Definition hmap {A: UU} {n: nat} {v: Vector A n} {P: A → UU}
                {Q: A → UU} (f: ∏ (a: A), P a → Q a) (hv: HVec (vector_map P v)): HVec (vector_map Q v).
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

Lemma hmap_idfun {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (hv: HVec (vector_map P v))
  : hmap (λ a: A, idfun (P a)) hv = hv.
Proof.
  revert n v hv.
  refine (vector_ind _ _ _).
  - induction hv.
    apply idpath.
  - intros.
    simpl in hv.
    simpl.
    change hv with (pr1 hv ::: pr2 hv).
    apply maponpaths.
    apply (X (pr2 hv)).
Defined.

Lemma hmap_comp {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {Q: A → UU} {R: A → UU}
                (f: ∏ a: A, P a → Q a) (g: ∏ (a: A), Q a → R a) (hv: HVec (vector_map P v))
  : hmap g (hmap f hv) = hmap (λ a: A, (g a) ∘ (f a)) hv. 
Proof.
  revert n v hv.
  refine (vector_ind _ _ _).
  - induction hv.
    apply idpath.
  - intros.
    simpl in hv.
    simpl.
    apply maponpaths.
    apply (X (pr2 hv)).
Defined.

Definition hmap_vector {A: UU} {n: nat} {v: Vector A n} {P: A → UU} 
                       {B: UU} (f: ∏ (a: A), P a → B) (hv: HVec (vector_map P v)): Vector B n.
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

Lemma hmap_path {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {Q: A → UU} (f: ∏ a: A, P a → Q a) 
                (g: ∏ (a: A), P a → Q a) (hv: HVec (vector_map P v))
                (hpath: HVec (hmap_vector (λ a p, f a p = g a p) hv))
  : hmap f hv = hmap g hv.
Proof.
  revert n v hv hpath.
  refine (vector_ind _ _ _).
  - induction hv.
    reflexivity.
  - intros.
    simpl in hv, hpath.
    simpl.
    use map_on_two_paths.
    + exact (pr1 hpath).
    + exact (X (pr2 hv) (pr2 hpath)).
Defined.

Lemma hmap_vector_flat {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {hv: HVec (vector_map P v)}
                       {Q: A → UU} (hhv: HVec (hmap_vector (λ a p, Q a) hv))
   : HVec (vector_map Q v).
Proof.
  revert n v hv hhv.
  refine (vector_ind _ _ _).
  - reflexivity.
  - intros.
    simpl.
    simpl in hv, hhv.
    split.
    + exact (pr1 hhv).
    + exact (X (pr2 hv) (pr2 hhv)).
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

Lemma hmap_vector_flat_hmap'
   {A: UU} {n: nat} {v: Vector A n} 
   {P: A → UU} (hv: HVec (vector_map P v))
   {Q: ∏ (a: A), UU} (f: ∏ (a: A), P a → Q a) 
   : hmap_vector_flat (hmap' (λ a p, f a p) hv) = hmap f hv.
Proof.
  revert n v hv.
  refine (vector_ind _ _ _).
  - reflexivity.
  - intros.
    simpl.
    apply maponpaths.
    exact (X (pr2 hv)).
Defined.

Definition hmap'' {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {hv: HVec (vector_map P v)}
                  {Q: ∏ (a: A) (p: P a), UU} (hhv: HVec (hmap_vector (λ a p, Q a p) hv))
                  {R: ∏ (a: A) (p: P a), UU} (f: ∏ (a: A) (p: P a) (q: Q a p), R a p)
                  : HVec (hmap_vector (λ a p, R a p) hv).
Proof.
  revert n v f hv hhv.
  refine (vector_ind _ _ _ ).
  - intros.
    exact hvnil.
  - intros x n xs IHv f hv hhv.
    exact (f x (pr1 hv) (pr1 hhv) ::: IHv f (pr2 hv) (pr2 hhv)).
Defined.

Lemma hmap12 {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (hv: HVec (vector_map P v))
             {Q: ∏ (a: A) (p: P a), UU} (hhv: HVec (hmap_vector (λ a p, Q a p) hv))
             {R: ∏ (a: A) (p: P a), UU} (f: ∏ (a: A) (p: P a), R a p)
  : hmap' f hv = hmap'' hhv  (λ a p q, f a p).
Proof.
  revert n v hv hhv.
  refine (vector_ind _ _ _).
  - reflexivity.
  - intros x n xs IH hv hhv.
    simpl in hv.
    simpl in hhv.
    simpl.
    apply maponpaths.
    exact (IH (pr2 hv) (pr2 hhv)).
Defined.

Definition hvec_foldr' {A: UU} {n: nat} {v: Vector A n} 
                {P: A → UU} {hv: HVec (vector_map P v)}
                {Q: ∏ (a: A) (p: P a), UU} (hhv: HVec (hmap_vector (λ a p, Q a p) hv))
                {B: UU} (comp: ∏ (a: A) (p: P a), Q a p → B → B) (s: B)
                : B.
Proof.
   revert n v hv hhv.
   refine (vector_ind _ _ _).
   - intros.
     exact s.
   - intros x n xs IH hv hhv.
     simpl in hv, hhv.
     exact (comp _ _ (pr1 hhv) (IH (pr2 hv) (pr2 hhv))).
Defined.
