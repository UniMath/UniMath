(* ========================================================================= *)
(** * Vectors as iterated products.

    Marco Maggesi, April 2019                                                *)
(* ========================================================================= *)

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Foundations.NaturalNumbers.

Local Open Scope nat.
Local Open Scope stn.

(** ** Lemmata about natural numbers and standard finite sets. *)

Lemma nat_S_lt (m n : nat) : S m < S n → m < n.
Proof.
  induction m; apply idfun.
Defined.

Definition stn_extens {n} (i j : ⟦ n ⟧) (p : stntonat _ i = stntonat _ j)
  : i = j
  := subtypePath' p (propproperty (j < n)).

Definition fromstn0 (i : ⟦ 0 ⟧) {A : UU} : A
  := fromempty (negnatlthn0 (pr1 i) (pr2 i)).

(** ** Vectors *)

Definition Vector (A : UU) (n : nat) : UU.
Proof.
induction n as [|n IHn].
- apply unit.
- apply (A × IHn).
Defined.

Section Vectors.

Context {A : UU}.

(** *** Constructors. *)

Definition vnil : Vector A 0 := tt.

Definition vcons {n} (x : A) (v : Vector A n) : Vector A (S n)
  := x,, v.

Definition drop {n} (f : ⟦ S n ⟧ → A) (i : ⟦ n ⟧) : A :=
  f (dni_firstelement i).

Definition mk_vector {n} (f : ⟦ n ⟧ → A) : Vector A n.
Proof.
  induction n as [|m h].
  - exact vnil.
  - exact (vcons (f firstelement) (h (drop f))).
Defined.

(** *** Projections. *)

Definition hd {n} (v : Vector A (S n)) : A := pr1 v.

Definition tl {n} (v : Vector A (S n)) : Vector A n := pr2 v.

Definition el {n} (v : Vector A n) : ⟦ n ⟧ → A.
Proof.
  induction n as [|m f].
  - apply (λ i, fromstn0 i).
  - intro i.
    induction i as (j,jlt).
    induction j as [|k _].
    + exact (hd v).
    + exact (f (tl v) (make_stn _ k (nat_S_lt _ _ jlt))).
Defined.

(** *** Some identities for computing [el]. *)

Lemma el_mk_vector_i {n} (f : ⟦ n ⟧ → A) (i: ⟦ n ⟧ ): el (mk_vector f) i = f i.
Proof.
  induction n as [|m meq].
  - exact (fromstn0 i).
  - induction i as (j,jlt).
    induction j as [|k _].
    + cbn.
      apply maponpaths.
      apply stn_extens.
      reflexivity.
    + etrans.
      { apply meq. }
      unfold funcomp, drop.
      apply maponpaths.
      apply stn_extens.
      reflexivity.
Defined.

Lemma el_mk_vector {n} (f : ⟦ n ⟧ → A) : el (mk_vector f) = f.
Proof.
  apply funextfun. intro i.
  apply el_mk_vector_i.
Defined.

Lemma el_vcons_tl {n} (v : Vector A n) (x : A) (i : ⟦ n ⟧) :
  el (vcons x v) (dni_firstelement i) = el v i.
Proof.
  induction n as [|m meq].
  - apply fromstn0. exact i.
  - cbn. apply maponpaths.
    abstract
      (apply proofirrelevance;
       exact (propproperty (pr1 i < S m))).
Defined.

Lemma el_vcons_hd {n} (v : Vector A n) (x : A) (ilt : 0 < S n) :
  el (vcons x v) (make_stn _ 0 ilt) = x.
Proof.
  reflexivity.
Defined.

Lemma drop_el {n} (v : Vector A (S n)) : drop (el v) = el (tl v).
Proof.
  apply funextfun. intro i.
  induction v as (x, u).
  change (drop (el (vcons x u)) i = el u i).
  apply el_vcons_tl.
Defined.

Lemma el_tl {n} (v : Vector A (S n)) (i : ⟦ n ⟧)
  : el (tl v) i = drop (el v) i.
Proof.
  rewrite drop_el.
  reflexivity.
Defined.

(** *** Extensionality. *)

Definition vector0_eq (u v : Vector A 0) : u = v
  := proofirrelevancecontr iscontrunit u v.

Definition vectorS_eq {n} {u v : Vector A (S n)}
           (p : hd u = hd v) (q : tl u = tl v)
  : u = v
  := dirprod_paths p q.

Lemma vector_extens {n} {u v : Vector A n}
  : (∏ i : ⟦ n ⟧, el u i = el v i) → u = v.
Proof.
  intros H.
  induction n as [|m meq].
  - apply vector0_eq.
  - apply vectorS_eq.
    + exact (H firstelement).
    + apply meq.
      intros.
      do 2 rewrite el_tl.
      apply H.
Defined.

Lemma mk_el_vector {n} (v : Vector A n) : mk_vector (el v) = v.
Proof.
  apply vector_extens.
  intros i.
  rewrite el_mk_vector.
  reflexivity.
Defined.

(** *** Weak equivalence with functions. *)

Definition isweq_el {n} : isweq (el:Vector A n → ⟦ n ⟧ → A)
  := isweq_iso el mk_vector mk_el_vector el_mk_vector.

Definition vector_weq_fun n : Vector A n ≃ (⟦ n ⟧ -> A)
  := make_weq el isweq_el.

Lemma isofhlevel_Vector {n} (is1 : isofhlevel n A) k
  : isofhlevel n (Vector A k).
Proof.
  eapply isofhlevelweqb.
  - apply vector_weq_fun.
  - apply impredfun, is1.
Defined.

(** *** Induction. *)

Lemma vector_ind (P : ∏ n, Vector A n → UU) :
  P 0 vnil
  → (∏ x n (v : Vector A n), P n v → P (S n) (vcons x v))
  → (∏ n (v : Vector A n), P n v).
Proof.
  intros Hnil Hcons.
  induction n as [|m H]; intros.
  - apply (transportb (P 0) (vector0_eq v vnil) Hnil).
  - apply Hcons, H.
Defined.

End Vectors.

Definition vector_map {A B : UU} (f : A → B) {n} (v : Vector A n) : Vector B n.
Proof.
  induction n as [|m h].
  - exact vnil.
  - eapply vcons.
    + exact (f (hd v)).
    + exact (h (tl v)).
Defined.

Lemma hd_vector_map {A B : UU} (f : A → B) {n} (v : Vector A (S n))
  : hd (vector_map f v) = f (hd v).
Proof.
  reflexivity.
Defined.

Lemma tl_vector_map {A B : UU} (f : A → B) {n} (v : Vector A (S n))
  : tl (vector_map f v) = vector_map f (tl v).
Proof.
  reflexivity.
Defined.

Lemma el_vector_map {A B : UU} (f : A → B) {n} (v : Vector A n) (i : ⟦ n ⟧)
  : el (vector_map f v) i = f (el v i).
Proof.
  induction n as [|m H].
  - exact (fromstn0 i).
  - induction i as (j, jlt).
    induction j as [|k _].
    + apply hd_vector_map.
    + change (el (tl (vector_map f v)) (make_stn _ k (nat_S_lt _ _ jlt)) =
              f (el (tl v) (make_stn _ k (nat_S_lt _ _ jlt)))).
      etrans.
      { apply el_tl. }
      etrans.
      { apply H. }
      apply maponpaths.
      apply maponpaths.
      apply stn_extens.
      reflexivity.
Defined.

(** *** Iteration. *)

Definition vector_foldr {A B : UU} (f : A -> B -> B) (b : B) {n}
  : Vector A n -> B
  := vector_ind (λ (n : nat) (_ : Vector A n), B) b
                (λ (a : A) (m : nat) (_ : Vector A m) (acc : B), f a acc)
                n.

Definition vector_foldr1 {A : UU} (f : A -> A -> A) {n} : Vector A (S n) → A
  := nat_rect (λ n : nat, Vector A (S n) → A)
              hd
              (λ (m : nat) (h : Vector A (S m) → A),
               uncurry (λ (x : A) (u : Vector A (S m)), f x (h u)))
              n.

Definition vector_append {A : UU} {m} (u : Vector A m) {n} (v : Vector A n)
  : Vector A (m + n)
  := vector_ind (λ (p : nat) (_ : Vector A p), Vector A (p + n))
                v
                (λ (x : A) (p : nat) (_ : Vector A p) (w : Vector A (p + n)),
                 vcons x w)
                m u.

(** *** Fusion laws. *)

Lemma vector_map_id {A : UU} {n}
  : vector_map (idfun A) = idfun (Vector A n).
Proof.
  apply funextfun.
  intro v.
  induction n.
  - induction v.
    reflexivity.
  - apply vectorS_eq.
    + reflexivity.
    + change (vector_map (idfun A) (tl v) = tl v).
      apply IHn.
Defined.

Lemma vector_map_comp {A B C: UU} (f: A → B) (g: B → C) {n: nat}:
  (vector_map (funcomp f g): Vector A n -> Vector C n) = funcomp (vector_map f) (vector_map g).
Proof.
  apply funextfun.
  intro v.
  induction n.
  - reflexivity.
  - apply vectorS_eq.
    + reflexivity.
    + apply IHn.
Defined.

Lemma vector_append_lid {A : UU} (u : Vector A 0) {n} (v : Vector A n)
  : vector_append u v = v.
Proof.
  induction u.
  reflexivity.
Defined.
