(* ========================================================================= *)
(** * Vectors as iterated products.

    Marco Maggesi, April 2019                                                *)
(* ========================================================================= *)

Require Import UniMath.Combinatorics.StandardFiniteSets.

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

Definition vnil : Vector A 0 := tt.

Definition vcons {n} (x : A) (v : Vector A n) : Vector A (S n)
  := x,, v.

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

Definition drop {n} (f : ⟦ S n ⟧ → A) (i : ⟦ n ⟧) : A :=
  f (dni_firstelement i).

Definition mk_vector {n} (f : ⟦ n ⟧ → A) : Vector A n.
Proof.
  induction n as [|m h].
  - exact vnil.
  - exact (vcons (f firstelement) (h (drop f))).
Defined.

Definition vector_eq {n} {u v : Vector A (S n)} (p : hd u = hd v) (q : tl u = tl v)
  : u = v
  := dirprod_paths p q.

Goal ∏ n (f : ⟦ S n ⟧ → A),
   mk_vector f = vcons (f firstelement) (mk_vector (drop f)).
Proof.
  reflexivity.
Qed.

Lemma el_mk_vector {n} (f : ⟦ n ⟧ → A) : el (mk_vector f) = f.
Proof.
  apply funextfun. intro i.
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

Lemma el_vcons_tl {n} (v : Vector A n) (x : A) (i : ⟦ n ⟧) :
  el (vcons x v) (dni_firstelement i) = el v i.
Proof.
  induction n as [|m meq].
  - apply fromstn0. exact i.
  - cbn. apply maponpaths.
    abstract (apply proofirrelevance; exact (propproperty (pr1 i < S m))).
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

Lemma mk_el_vector {n} (v : Vector A n) : mk_vector (el v) = v.
Proof.
  induction n as [|m meq].
  - apply proofirrelevancecontr.
    exact iscontrunit.
  - change (vcons (el v firstelement) (mk_vector (drop (el v))) = v).
    apply vector_eq.
    + reflexivity.
    + change (mk_vector (drop (el v)) = tl v).
      rewrite drop_el.
      apply meq.
Defined.

Definition isweq_el {n} : isweq (el:Vector A n → ⟦ n ⟧ → A)
  := isweq_iso el mk_vector mk_el_vector el_mk_vector.

Definition vector_weq_fun n : Vector A n ≃ (⟦ n ⟧ -> A)
  := make_weq el isweq_el.

(** Test the computational behaviour. *)

Section Test.

  Local Open Scope stn.

  Context {a b c d:A}.
  Let v := vcons a (vcons b (vcons c (vcons d vnil))).
  Goal el v (●0) = a. reflexivity. Qed.
  Goal el v (●1) = b. reflexivity. Qed.
  Goal el v (●2) = c. reflexivity. Qed.
  Goal el v (●3) = d. reflexivity. Qed.
  Goal mk_vector (el v) = v. reflexivity. Qed.
  (* Eval compute in (el v). *)

End Test.

Lemma isofhlevel_Vector {n} (is1 : isofhlevel n A) k
  : isofhlevel n (Vector A k).
Proof.
  eapply isofhlevelweqb.
  - apply vector_weq_fun.
  - apply impredfun, is1.
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

Lemma vector_map_id {A : UU} {n}
  : vector_map (idfun A) = idfun (Vector A n).
Proof.
  apply funextfun.
  intro v.
  induction n.
  - induction v.
    reflexivity.
  - apply vector_eq.
    + reflexivity.
    + change (vector_map (idfun A) (tl v) = tl v).
      apply IHn.
Defined.
