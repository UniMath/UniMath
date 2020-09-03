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

Definition hhd {A: UU} {n: nat} {v: Vector UU n} (hv: HVec (A ::: v)): A := pr1 hv.  

Definition htl {A: UU} {n: nat} {v: Vector UU n} (hv: HVec (A ::: v)): HVec v := pr2 hv.

Definition hel {n: nat} {v: Vector UU n} (hv: HVec v): ∏ i: ⟦ n ⟧, el v i.
Proof.
  revert n v hv.
  refine (vector_ind _ _ _).
  - intros.
    apply (fromempty (negnatlthn0 (pr1 i) (pr2 i))).
  - intros x n xs IHxs.
    induction i as [i iproof].
    induction i.
    + exact (hhd hv).
    + exact (IHxs (htl hv) (make_stn _ i iproof)).
Defined.

Lemma isofhlevelhvec {m: nat} {n: nat} (v: Vector UU n) (levels: HVec (vector_map (isofhlevel m) v)): isofhlevel m (HVec v).
Proof.
  revert n v levels.
  refine (vector_ind _ _ _).
  - intro.
    apply isofhlevelcontr.
    apply iscontrunit.
  - intros x n xs IHxs levels.
    simpl.
    apply isofhleveldirprod.
    + apply (pr1 levels).
    + apply (IHxs (pr2 levels)).
Defined.

Lemma hvcons_paths {A: UU} (x y: A) {n: nat} (v: Vector UU n) (xs ys: HVec v) (p: x = y) (ps: xs = ys)
  : hvcons x xs = hvcons y ys.
Proof.
  apply (map_on_two_paths (λ x xs, @hvcons A x n v xs)) ; assumption.
Defined.

(** ** HVecs of vector_map *)

Lemma hvec_vector_map_const {A: UU} {n: nat} (v: Vector A n) {B: UU}
  : HVec (vector_map (λ _, B) v) = Vector B n.
Proof.
  revert n v.
  refine (vector_ind _ _ _).
  - apply idpath.
  - simpl.
    intros x n xs IHxs.
    use map_on_two_paths.
    + apply idpath.
    + assumption.
Defined.

Definition hfoldr {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {B: UU} (comb: ∏ (a: A), P a → B → B)
                  (s: B) (hv: HVec (vector_map P v)): B.
Proof.
   revert n v hv.
   refine (vector_ind _ _ _).
   - intro.
     exact s.
   - intros x n xs IHxs.
     simpl.
     intro.
     exact (comb _ (pr1 hv) (IHxs (pr2 hv))).
Defined.

Definition hmap {A: UU} {n: nat} {v: Vector A n} {P: A → UU}
                {Q: A → UU} (f: ∏ (a: A), P a → Q a) (hv: HVec (vector_map P v)): HVec (vector_map Q v).
Proof.
  revert n v f hv.
  refine (vector_ind _ _ _ ).
  - intros.
    exact hvnil.
  - intros x n xs IHxs.
    simpl.
    intros f hv.
    exact (f x (pr1 hv) ::: IHxs f (pr2 hv)).
Defined.

Lemma hmap_idfun {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (hv: HVec (vector_map P v))
  : hmap (λ a: A, idfun (P a)) hv = hv.
Proof.
  revert n v hv.
  refine (vector_ind _ _ _).
  - induction hv.
    apply idpath.
  - simpl.
    intros x n xs IHxs hv.
    change hv with (pr1 hv ::: pr2 hv).
    apply maponpaths.
    apply (IHxs (pr2 hv)).
Defined.

Lemma hmap_comp {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {Q: A → UU} {R: A → UU}
                (f: ∏ a: A, P a → Q a) (g: ∏ (a: A), Q a → R a) (hv: HVec (vector_map P v))
  : hmap g (hmap f hv) = hmap (λ a: A, (g a) ∘ (f a)) hv. 
Proof.
  revert n v hv.
  refine (vector_ind _ _ _).
  - induction hv.
    apply idpath.
  - simpl.
    intros x n xs IHxs hv.
    apply maponpaths.
    apply (IHxs (pr2 hv)).
Defined.

Definition hmap_vector {A: UU} {n: nat} {v: Vector A n} {P: A → UU} 
                       {B: UU} (f: ∏ (a: A), P a → B) (hv: HVec (vector_map P v))
  : Vector B n.
Proof.
  revert n v f hv.
  refine (vector_ind _ _ _).
  - intros.
    exact vnil.
  - simpl.
    intros x n xs IHxs f hv.
    exact (vcons (f x (pr1 hv)) (IHxs f (pr2 hv))).
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
  - simpl.
    intros x n xs IHxs hv hpath.
    use map_on_two_paths.
    + exact (pr1 hpath).
    + exact (IHxs (pr2 hv) (pr2 hpath)).
Defined.

(** ** HVecs of vector_map *)

Definition hmap_lift {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {Q: ∏ (a: A) (p: P a), UU} (f: ∏ (a: A) (p: P a), Q a p)
                     (hv: HVec (vector_map P v)): HVec (hmap_vector Q hv).
Proof.
  revert n v hv.
  refine (vector_ind _ _ _ ).
  - intros.
    exact hvnil.
  - intros x n xs IHv hv.
    exact (f x (pr1 hv) ::: IHv (pr2 hv)).
Defined.

Lemma hvec_lower {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {hv: HVec (vector_map P v)}
                 {Q: A → UU} (hhv: HVec (hmap_vector (λ a _, Q a) hv))
  : HVec (vector_map Q v).
Proof.
  revert n v hv hhv.
  refine (vector_ind _ _ _).
  - reflexivity.
  - simpl.
    intros x n xs IHxs hv hhv.
    split.
    + exact (pr1 hhv).
    + exact (IHxs (pr2 hv) (pr2 hhv)).
Defined.

Lemma hvec_lower_hmap_lift {A: UU} {n: nat} {v: Vector A n}  {P: A → UU} 
                       {Q: ∏ (a: A), UU} (f: ∏ (a: A), P a → Q a) (hv: HVec (vector_map P v))
 : hvec_lower (hmap_lift f hv) = hmap f hv.
Proof.
  revert n v hv.
  refine (vector_ind _ _ _).
  - reflexivity.
  - intros x n xs IHxs hv. 
    simpl.
    apply maponpaths.
    exact (IHxs (pr2 hv)).
Defined.

Definition hhmap {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {hv: HVec (vector_map P v)}
                 {Q: ∏ (a: A) (p: P a), UU} {R: ∏ (a: A) (p: P a), UU} 
                 (f: ∏ (a: A) (p: P a) (q: Q a p), R a p) (hhv: HVec (hmap_vector Q hv))
  : HVec (hmap_vector R hv).
Proof.
  revert n v f hv hhv.
  refine (vector_ind _ _ _ ).
  - intros.
    exact hvnil.
  - intros x n xs IHv f hv hhv.
    exact (f x (pr1 hv) (pr1 hhv) ::: IHv f (pr2 hv) (pr2 hhv)).
Defined.

Lemma hmap_lift_as_hhmap {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (hv: HVec (vector_map P v))
             {Q: ∏ (a: A) (p: P a), UU} (hhv: HVec (hmap_vector Q hv))
             {R: ∏ (a: A) (p: P a), UU} (f: ∏ (a: A) (p: P a), R a p)
  : hmap_lift f hv = hhmap (λ a p _, f a p) hhv.
Proof.
  revert n v hv hhv.
  refine (vector_ind _ _ _).
  - reflexivity.
  - simpl.
    intros x n xs IHxs hv hhv.
    apply maponpaths.
    exact (IHxs (pr2 hv) (pr2 hhv)).
Defined.

Definition hhfoldr {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {hv: HVec (vector_map P v)}
                   {Q: ∏ (a: A) (p: P a), UU} {B: UU}
                   (comp: ∏ (a: A) (p: P a), Q a p → B → B) (s: B) (hhv: HVec (hmap_vector Q hv))
  : B.
Proof.
   revert n v hv hhv.
   refine (vector_ind _ _ _).
   - intros.
     exact s.
   - simpl.
     intros x n xs IHxs hv hhv.
     exact (comp _ _ (pr1 hhv) (IHxs (pr2 hv) (pr2 hhv))).
Defined.
