(** * Heterogeneous vectors. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Export UniMath.Combinatorics.Vectors.

Local Open Scope stn.

(** ** Basic definitions.
If [v] is a vector of types [U1], [U2], ..., [Un], then [HVec v] is the product type [U1 × (U2 × ... × Un)]. We
introduce several basic operations on heterogeneous vectors: often they have the same syntax then the
corresponding operation on plain vectors, and a name which begins with h.

We also introduce a new scope, [hvec_scope], delimited by [hvec], which adds useful notations for
heterogeneous vectors. A vector of elements [x1], [x2], ..., [xn] may be written a [[x1; x2; ...; xn]].
Moreover [[]] denotes the empty vector and [:::] is the cons operator.
*)

Definition HVec {n: nat} (v: Vector UU n): UU.
Proof.
  revert n v.
  exact (vector_ind (λ _ _, UU) unit (λ x _ _ IHv, x × IHv)).
Defined.

Declare Scope hvec_scope.

Delimit Scope hvec_scope with hvec.

Local Open Scope hvec_scope.

Bind Scope hvec_scope with HVec.

Definition hnil : HVec vnil := tt.

Definition hcons {A: UU} (x: A) {n: nat} {v: Vector UU n} (hv: HVec v) : HVec (A ::: v) := x ,, hv.

Notation "[( x ; .. ; y )]" := (hcons x .. (hcons y hnil) ..): hvec_scope.

Notation "[()]" := hnil (at level 0, format "[()]"): hvec_scope.

Infix ":::" := hcons: hvec_scope.

Definition functionToHVec {n: nat} {P: ⟦ n ⟧ → UU} (f: ∏ i: ⟦ n ⟧, P i) : HVec (mk_vector P).
Proof.
  induction n.
  - exact [()].
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

Lemma hcons_paths {A: UU} (x y: A) {n: nat} (v: Vector UU n) (xs ys: HVec v) (p: x = y) (ps: xs = ys)
  : x ::: xs = y ::: ys.
Proof.
  apply (map_on_two_paths (λ x xs, @hcons A x n v xs)) ; assumption.
Defined.

Lemma isofhlevelhvec {m: nat} {n: nat} (v: Vector UU n) (levels: HVec (vector_map (isofhlevel m) v))
  : isofhlevel m (HVec v).
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

Lemma hvec_vector_fill {A: UU} {n: nat}
  : HVec (vector_fill A n)  = Vector A n.
Proof.
  induction n.
  - apply idpath.
  - simpl.
    apply maponpaths.
    assumption.
Defined.

(** ** Level-1 heterogeneous vectors.

A level-1 hvec is a term of type [HVec (vector_map P v)] for some [v: Vector A n] and [P: A → UU].
Some operations may be easily defined for a level-1 hvec but not for a generic heterogeneous. Operations
on level-1 hvec have names beginning with h1.
*)

(** *** Miscellanea of operations on level-1 hvecs. *)

(** [h1const_is_vector] proves that an [HVec (vector_map P v)] is a [Vector] when [P] is a constant map. *)

Definition h1const_is_vector {A: UU} {n: nat} (v: Vector A n) (B: UU)
  : HVec (vector_map (λ _, B) v) = Vector B n.
Proof.
  induction n.
  - apply idpath.
  - simpl.
    apply maponpaths.
    apply IHn.
Defined.

(** [h1lower] transforms a [HVec (vector_map P v)]  into a [Vector] when [P] is a constant map. Although
it would be possibile to define [h1lower] starting from [h1const_is_vector], this would make difficult
to work by induction over [v]. *)

Definition h1lower {A: UU} {n: nat} {v: Vector A n} {B: UU} (h1v: HVec (vector_map (λ _, B) v))
  : Vector B n.
Proof.
  revert n v h1v.
  refine (vector_ind _ _ _).
  - apply idfun.
  - intros x n xs IHxs h1v.
    exact (vcons (hhd h1v) (IHxs (htl h1v))).
Defined.

(** [h1foldr] is the analogous of [foldr] for level-1 hvecs. *)

Definition h1foldr {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {B: UU} (comb: ∏ (a: A), P a → B → B)
                  (s: B) (h1v: HVec (vector_map P v)): B.
Proof.
   revert n v h1v.
   refine (vector_ind _ _ _).
   - intro.
     exact s.
   - intros x n xs IHxs.
     simpl.
     intro.
     exact (comb _ (pr1 h1v) (IHxs (pr2 h1v))).
Defined.

(** *** Map for level-1 hvecs.

The [h1map] function is analogous to [map] for level-1 hvecs: [hmap f hv] applies the
function [f] to all elements of [hv]. The result is of type [HVec (vector_map Q v)] for an appropriate
[Q: A → UU]. When [Q] is the constant map in [hmap], we may instead use [h1map_vector] which
returns a Vector instead of an HVec.
*)
Definition h1map {A: UU} {n: nat} {v: Vector A n} {P: A → UU}
                 {Q: A → UU} (f: ∏ (a: A), P a → Q a) (h1v: HVec (vector_map P v))
  : HVec (vector_map Q v).
Proof.
  revert n v f h1v.
  refine (vector_ind _ _ _ ).
  - intros.
    exact [()].
  - intros x n xs IHxs.
    simpl.
    intros f h1v.
    exact (f x (pr1 h1v) ::: IHxs f (pr2 h1v)).
Defined.

Lemma h1map_idfun {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (h1v: HVec (vector_map P v))
  : h1map (λ a: A, idfun (P a)) h1v = h1v.
Proof.
  revert n v h1v.
  refine (vector_ind _ _ _).
  - induction h1v.
    apply idpath.
  - simpl.
    intros x n xs IHxs h1v.
    change h1v with (pr1 h1v ::: pr2 h1v).
    apply maponpaths.
    apply (IHxs (pr2 h1v)).
Defined.

Lemma h1map_compose {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {Q: A → UU} {R: A → UU}
                    (f: ∏ a: A, P a → Q a) (g: ∏ (a: A), Q a → R a) (h1v: HVec (vector_map P v))
  : h1map g (h1map f h1v) = h1map (λ a: A, (g a) ∘ (f a)) h1v.
Proof.
  revert n v h1v.
  refine (vector_ind _ _ _).
  - induction h1v.
    apply idpath.
  - simpl.
    intros x n xs IHxs h1v.
    apply maponpaths.
    apply (IHxs (pr2 h1v)).
Defined.

(** [h1map_vector] is just the composition of [h1map] and [h1lower], but it deserves a name
since it is used in the definition of level-2 hvecs (see later). *)

Definition h1map_vector {A: UU} {n: nat} {v: Vector A n} {P: A → UU}
                        {B: UU} (f: ∏ (a: A), P a → B) (h1v: HVec (vector_map P v))
  : Vector B n := h1lower (h1map f h1v).

(** ** Level-2 heterogeneous vectors.

A level-2 hvec is a term of type [HVec (h1map_vector Q h1v)] for some [h1v: HVec (vector_map P v)],
[v: Vector A n], [P: A → UU], [Q: ∏ a: A, P a → UU]. Operators on level-2 hvecs have names which
begins with h2.

The need to work explicitly with level-1 and level-2 hvecs, instead of generic heterogeneous vectors,
seems unfortunate. A refactoring of this library could free us from the burden of working with such
articulate data types
*)

(** [h2map] is like [h1map] for level-2 hvecs. *)

Definition h2map {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {h1v: HVec (vector_map P v)}
                 {Q: ∏ (a: A) (p: P a), UU} {R: ∏ (a: A) (p: P a), UU}
                 (f: ∏ (a: A) (p: P a), Q a p → R a p) (h2v: HVec (h1map_vector Q h1v))
  : HVec (h1map_vector R h1v).
Proof.
  revert n v f h1v h2v.
  refine (vector_ind _ _ _ ).
  - intros.
    exact [()].
  - intros x n xs IHv f h1v h2v.
    exact (f x (pr1 h1v) (pr1 h2v) ::: IHv f (pr2 h1v) (pr2 h2v)).
Defined.

(** [h1lift] transforms a level-1 hvec into a level-2 hvec. *)

Definition h1lift {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (h1v: HVec (vector_map P v))
  : HVec (h1map_vector (λ a _, P a) h1v).
Proof.
  revert n v h1v.
  refine (vector_ind _ _ _ ).
  - intros.
    exact [()].
  - intros x n xs IHv h1v.
    exact ((pr1 h1v) ::: IHv (pr2 h1v)).
Defined.

(** [h2lower] transforms a level-2 hvec [h2v: HVec (hmap_vector Q h1v)] into a level-1 hvec when
[Q: ∏ a: A, P a → UU] is constant on the argument of type [P a].
*)
Definition h2lower {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {h1v: HVec (vector_map P v)}
                 {Q: A → UU} (h2v: HVec (h1map_vector (λ a _, Q a) h1v))
  : HVec (vector_map Q v).
Proof.
  revert n v h1v h2v.
  refine (vector_ind _ _ _).
  - reflexivity.
  - simpl.
    intros x n xs IHxs h1v h2v.
    split.
    + exact (pr1 h2v).
    + exact (IHxs (pr2 h1v) (pr2 h2v)).
Defined.

(** [h2lower_h1map_h1lift] and [h1map_h1lift_as_h2map] are two normalization lemmas relating level-1 and
level-2 hvecs. *)

Lemma h2lower_h1map_h1lift {A: UU} {n: nat} {v: Vector A n}  {P: A → UU}
                       {Q: ∏ (a: A), UU} (f: ∏ (a: A), P a → Q a) (h1v: HVec (vector_map P v))
  : h2lower (h2map (λ a p _, f a p) (h1lift h1v)) = h1map f h1v.
Proof.
  revert n v h1v.
  refine (vector_ind _ _ _).
  - reflexivity.
  - intros x n xs IHxs h1v.
    simpl.
    apply maponpaths.
    exact (IHxs (pr2 h1v)).
Defined.

Lemma h1map_h1lift_as_h2map {A: UU} {n: nat} {v: Vector A n} {P: A → UU} (h1v: HVec (vector_map P v))
             {Q: ∏ (a: A) (p: P a), UU} (h2v: HVec (h1map_vector Q h1v))
             {R: ∏ (a: A) (p: P a), UU} (f: ∏ (a: A) (p: P a), R a p)
  : h2map (λ a p _, f a p) (h1lift h1v) = h2map (λ a p _, f a p) h2v.
Proof.
  revert n v h1v h2v.
  refine (vector_ind _ _ _).
  - reflexivity.
  - simpl.
    intros x n xs IHxs h1v h2v.
    apply maponpaths.
    exact (IHxs (pr2 h1v) (pr2 h2v)).
Defined.

(** [h2foldr] is the analogous of [foldr] for level-2 hvecs. *)

Definition h2foldr {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {h1v: HVec (vector_map P v)}
                   {Q: ∏ (a: A) (p: P a), UU} {B: UU}
                   (comp: ∏ (a: A) (p: P a), Q a p → B → B) (s: B) (h2v: HVec (h1map_vector Q h1v))
  : B.
Proof.
   revert n v h1v h2v.
   refine (vector_ind _ _ _).
   - intros.
     exact s.
   - simpl.
     intros x n xs IHxs h1v h2v.
     exact (comp _ _ (pr1 h2v) (IHxs (pr2 h1v) (pr2 h2v))).
Defined.

(** [h1map_path] returns a proof that [hmap f h1v] and [hmap g h1v] are equal, provided that we
have a level-2 hvec [h2path] of proofs that the images of [f] and [g] on corresponding elements
of [h1v] are equal.
*)

Lemma h1map_path {A: UU} {n: nat} {v: Vector A n} {P: A → UU} {Q: A → UU} (f: ∏ a: A, P a → Q a)
                (g: ∏ (a: A), P a → Q a) (h1v: HVec (vector_map P v))
                (h2path: HVec (h1map_vector (λ a p, f a p = g a p) h1v))
  : h1map f h1v = h1map g h1v.
Proof.
  revert n v h1v h2path.
  refine (vector_ind _ _ _).
  - induction h1v.
    reflexivity.
  - simpl.
    intros x n xs IHxs h1v h2path.
    use map_on_two_paths.
    + exact (pr1 h2path).
    + exact (IHxs (pr2 h1v) (pr2 h2path)).
Defined.
