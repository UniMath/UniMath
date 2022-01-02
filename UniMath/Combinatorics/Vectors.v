(** * Vectors as iterated products. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Foundations.NaturalNumbers.

Local Open Scope nat.
Local Open Scope stn.

(** ** Lemmata about standard finite sets. *)

Definition stn_extens {n} (i j : ⟦ n ⟧) (p : stntonat _ i = stntonat _ j)
  : i = j
  := subtypePath' p (propproperty (j < n)).

Definition fromstn0 (i : ⟦ 0 ⟧) {A : UU} : A
  := fromempty (negnatlthn0 (pr1 i) (pr2 i)).

(** ** Vectors. *)

Definition vec (A : UU) (n : nat) : UU.
Proof.
induction n as [|n IHn].
- apply unit.
- apply (A × IHn).
Defined.

(** *** Constructors. *)

Definition vnil {A: UU}: vec A 0 := tt.

Definition vcons {A: UU} {n} (x : A) (v : vec A n) : vec A (S n)
  := x,, v.

(** *** Notations. *)

Declare Scope vec_scope.

Delimit Scope vec_scope with vec.

Bind Scope vec_scope with vec.

Local Open Scope vec_scope.

Notation "[()]" := vnil (at level 0, format "[()]"): vec_scope.

Infix ":::" := vcons (at level 60, right associativity) : vec_scope.

Notation "[( x ; .. ; y )]" := (vcons x .. (vcons y [()]) ..): vec_scope.

Section vecs.

Context {A : UU}.

Definition drop {n} (f : ⟦ S n ⟧ → A) (i : ⟦ n ⟧) : A :=
  f (dni_firstelement i).

Definition make_vec {n} (f : ⟦ n ⟧ → A) : vec A n.
Proof.
  induction n as [|m h].
  - exact [()].
  - exact ((f firstelement) ::: (h (drop f))).
Defined.

(** *** Projections. *)

Definition hd {n} (v : vec A (S n)) : A := pr1 v.

Definition tl {n} (v : vec A (S n)) : vec A n := pr2 v.

Definition el {n} (v : vec A n) : ⟦ n ⟧ → A.
Proof.
  induction n as [|m f].
  - apply (λ i, fromstn0 i).
  - intro i.
    induction i as (j,jlt).
    induction j as [|k _].
    + exact (hd v).
    + exact (f (tl v) (k,, jlt)).
Defined.

(** *** Some identities for computing [el]. *)

Lemma el_make_vec {n} (f : ⟦ n ⟧ → A) : el (make_vec f) ~ f .
Proof.
  intro i.
  induction n as [|m meq].
  - exact (fromstn0 i).
  - induction i as (j,jlt).
    induction j as [|k _].
    + cbn.
      apply maponpaths.
      apply stn_extens.
      apply idpath.
    + etrans.
      { apply meq. }
      unfold drop.
      apply maponpaths.
      apply idpath.
Defined.

Lemma el_make_vec_fun {n} (f : ⟦ n ⟧ → A) : el (make_vec f) = f.
Proof.
  apply funextfun.
  apply el_make_vec.
Defined.

Lemma el_vcons_tl {n} (v : vec A n) (x : A) (i : ⟦ n ⟧) :
  el (x ::: v) (dni_firstelement i) = el v i.
Proof.
  induction n as [|m meq].
  - apply fromstn0. exact i.
  - cbn. apply maponpaths.
    apply proofirrelevance;
    exact (propproperty (pr1 i < S m)).
Defined.

Lemma el_vcons_hd {n} (v : vec A n) (x : A) :
  el (x ::: v) (firstelement) = x.
Proof.
  reflexivity.
Defined.

Lemma drop_el {n} (v : vec A (S n)) (i: ⟦ n ⟧ ) : drop (el v) i = el (tl v) i.
Proof.
  induction v as (x, u).
  change (drop (el (x ::: u)) i = el u i).
  apply el_vcons_tl.
Defined.

Lemma el_tl {n} (v : vec A (S n)) (i : ⟦ n ⟧)
  : el (tl v) i = drop (el v) i.
Proof.
  rewrite drop_el.
  reflexivity.
Defined.

(** *** Extensionality. *)

Definition vec0_eq (u v : vec A 0) : u = v
  := proofirrelevancecontr iscontrunit u v.

Definition vecS_eq {n} {u v : vec A (S n)}
           (p : hd u = hd v) (q : tl u = tl v)
  : u = v
  := dirprod_paths p q.

Lemma vec_extens {n} {u v : vec A n}
  : (∏ i : ⟦ n ⟧, el u i = el v i) → u = v.
Proof.
  intros H.
  induction n as [|m meq].
  - apply vec0_eq.
  - apply vecS_eq.
    + exact (H firstelement).
    + apply meq.
      intros.
      do 2 rewrite el_tl.
      apply H.
Defined.

Lemma make_vec_el {n} (v : vec A n) : make_vec (el v) = v.
Proof.
  apply vec_extens.
  intros i.
  rewrite el_make_vec.
  reflexivity.
Defined.

(** *** Weak equivalence with functions. *)

Definition isweqvecfun {n} : isweq (el:vec A n → ⟦ n ⟧ → A)
  := isweq_iso el make_vec make_vec_el el_make_vec_fun.

Definition wqevecfun n : vec A n ≃ (⟦ n ⟧ -> A)
  := make_weq el isweqvecfun.

Lemma isofhlevelvec {n} (is1 : isofhlevel n A) k
  : isofhlevel n (vec A k).
Proof.
  induction k as [|k IH].
  - apply isofhlevelcontr, iscontrunit.
  - apply isofhleveldirprod.
    + apply is1.
    + apply IH.
Defined.

(** *** Induction. *)

Lemma vec_ind (P : ∏ n, vec A n → UU) :
  P 0 [()]
  → (∏ x n (v : vec A n), P n v → P (S n) (x ::: v))
  → (∏ n (v : vec A n), P n v).
Proof.
  intros Hnil Hcons.
  induction n as [|m H]; intros.
  - apply (transportb (P 0) (vec0_eq v [()]) Hnil).
  - apply Hcons, H.
Defined.

End vecs.

(** *** Map, fold and append. *)

Definition vec_map {A B : UU} (f : A → B) {n} (v : vec A n) : vec B n.
Proof.
  induction n as [|m h].
  - exact vnil.
  - eapply vcons.
    + exact (f (hd v)).
    + exact (h (tl v)).
Defined.

Lemma hd_vec_map {A B : UU} (f : A → B) {n} (v : vec A (S n))
  : hd (vec_map f v) = f (hd v).
Proof.
  reflexivity.
Defined.

Lemma tl_vec_map {A B : UU} (f : A → B) {n} (v : vec A (S n))
  : tl (vec_map f v) = vec_map f (tl v).
Proof.
  reflexivity.
Defined.

Lemma el_vec_map {A B : UU} (f : A → B) {n} (v : vec A n) (i : ⟦ n ⟧)
  : el (vec_map f v) i = f (el v i).
Proof.
  induction n as [|m H].
  - exact (fromstn0 i).
  - induction i as (j, jlt).
    induction j as [|k _].
    + apply hd_vec_map.
    + change (el (tl (vec_map f v)) (make_stn _ k jlt) =
              f (el (tl v) (make_stn _ k jlt))).
      etrans.
      { apply el_tl. }
      etrans.
      { apply H. }
      apply maponpaths.
      apply maponpaths.
      reflexivity.
Defined.

Lemma vec_map_as_make_vec {A B: UU} (f: A → B) {n} (v: vec A n)
  : vec_map f v = make_vec (λ i, f (el v i)).
Proof.
  apply vec_extens.
  intro i.
  rewrite el_vec_map.
  rewrite el_make_vec.
  apply idpath.
Defined.

Definition vec_foldr {A B : UU} (f : A -> B -> B) (b : B) {n}
  : vec A n -> B
  := vec_ind (λ (n : nat) (_ : vec A n), B) b
                (λ (a : A) (m : nat) (_ : vec A m) (acc : B), f a acc)
                n.

Definition vec_foldr1 {A : UU} (f : A -> A -> A) {n} : vec A (S n) → A
  := nat_rect (λ n : nat, vec A (S n) → A)
              hd
              (λ (m : nat) (h : vec A (S m) → A),
               uncurry (λ (x : A) (u : vec A (S m)), f x (h u)))
              n.

Definition vec_append {A : UU} {m} (u : vec A m) {n} (v : vec A n)
  : vec A (m + n)
  := vec_ind (λ (p : nat) (_ : vec A p), vec A (p + n))
                v
                (λ (x : A) (p : nat) (_ : vec A p) (w : vec A (p + n)),
                 x ::: w)
                m u.

(** *** Fusion laws. *)

Lemma vec_map_id {A : UU} {n} (v: vec A n)
  : vec_map (idfun A) v = v.
Proof.
  revert n v.
  refine (vec_ind _ _ _).
  - apply idpath.
  - intros x n xs HPxs.
    simpl.
    apply maponpaths.
    apply HPxs.
Defined.

Lemma vec_map_comp {A B C: UU} (f: A → B) (g: B → C) {n: nat} (v: vec A n) :
  vec_map (funcomp f g) v = (funcomp (vec_map f) (vec_map g)) v.
Proof.
  revert n v.
  refine (vec_ind _ _ _).
  - apply idpath.
  - intros x n xs HPxs.
    apply vecS_eq.
    + reflexivity.
    + apply HPxs.
Defined.

Lemma vec_map_make_vec {A B: UU} {n: nat} (g: ⟦ n ⟧ → A) (f: A → B)
  : vec_map f (make_vec g) = make_vec (f ∘ g).
Proof.
  apply vec_extens.
  intro i.
  rewrite el_vec_map.
  rewrite el_make_vec.
  rewrite el_make_vec.
  apply idpath.
Defined.

Lemma vec_append_lid {A : UU} (u : vec A 0) {n}
  : vec_append u = idfun (vec A n).
Proof.
  induction u.
  reflexivity.
Defined.

(** *** Other operations on vecs. *)

Definition vec_fill {A: UU} (a: A): ∏ n: nat, vec A n
  := nat_rect (λ n: nat, vec A n) [()] (λ (n: nat) (v: vec A n), a ::: v).

Lemma vec_map_const {A: UU} {n: nat} {v: vec A n} {B: UU} (b: B) : vec_map (λ _, b) v = vec_fill b n.
Proof.
  revert n v.
  apply vec_ind.
  - apply idpath.
  - intros x n xs HPind.
    change (b ::: vec_map (λ _: A, b) xs = b ::: vec_fill b n).
    apply maponpaths.
    exact HPind.
Defined.

Definition vec_zip {A B: UU} {n: nat} (v1: vec A n) (v2: vec B n): vec (A × B) n.
Proof.
  induction n.
  - exact [()].
  - induction v1 as [x1 xs1].
    induction v2 as [x2 xs2].
    exact ((x1 ,, x2) ::: IHn xs1 xs2).
Defined.
