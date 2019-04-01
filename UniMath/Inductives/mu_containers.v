
Require Import UniMath.Inductives.auxiliary_lemmas.

Open Scope transport.

Inductive W {I} (A : Fam I) (B : ∏ i, A i -> Fam I) : I -> UU :=
  sup : ∏ {i} (a : A i), (B i a ->__i W A B) -> W A B i.
Arguments sup {_ _ _ _} _ _.
Definition label {I A B} {i : I} (w : W A B i) :=
  match w with sup a f => a end.
Definition arg {I A B} {i : I} (w : W A B i) {j} :
  B i (label w) j -> W A B j :=
  match w with sup a f => f j end.

(* Inductive Addr {I A B} {i : I} (w : W A B i) : ∏ {j}, A j -> Type := *)
(* | root_addr : Addr w (label w) *)
(* | subtree_addr : ∏ {j} (b : B i (label w) j) *)
(*                    {k} {a : A k}, *)
(*                  @Addr I A B j (arg w b) k a -> Addr w a. *)
(* Check Addr_rect. *)


Fixpoint Addr_of_Depth {I A B} (n : nat) {i : I} (w : W A B i) {j} (a : A j) :
  UU :=
  match n with
  | 0 => ∑ p : i = j, p # label w = a
  | S n => ∑ j (b : B i (label w) j),
          Addr_of_Depth n (arg w b) a
  end.

Definition Addr {I A B} {i : I} (w : W A B i) {j} (a : A j):=
  ∑ n, Addr_of_Depth n w a.

Definition root_addr {I A B} {i : I} (w : W A B i) : Addr w (label w) :=
  0,, idpath _,, idpath _.

Definition subtree_addr {I A B}
           {i : I} (w : W A B i)
           {j} (b : B i (label w) j)
           {k} {a : A k} (addr' : Addr (arg w b) a) :
  Addr w a :=
  let '(n,, addr') := addr' in
  S n,, j,, b,, addr'.

Definition Addr_rect I A B
           (P : ∏ (i : I) (w : W A B i) (j : I) (a : A j), Addr w a → UU) :
  (∏ i w, P i w i (label w) (root_addr w)) →
  (∏ i (w : W A B i)
     j (b : B i (label w) j)
     k (a : A k) (addr : Addr (arg w b) a),
          P j (arg w b) k a addr → P i w k a (subtree_addr w b addr)) →
  ∏ i (w : W A B i)
    j (a : A j) (addr : Addr w a),
  P i w j a addr.
Proof.
  intros root_step subtree_step i w j a [n addr].
  revert i w addr; induction n; intros i w addr.
  - cbn in addr. destruct addr as [p q].
    induction p. cbn in q; unfold idfun in q. induction q.
    change (P i w i (label w) (root_addr w)).
    exact (root_step i w).
  - cbn in addr. destruct addr as [k [b addr']].
    change (P i w j a (subtree_addr w b (n,, addr'))).
    apply subtree_step.
    exact (IHn k (arg w b) addr').
Defined.

Goal ∏ I A B P root_case subtree_case i w,
@Addr_rect I A B P root_case subtree_case i w i (label w) (root_addr w) =
root_case i w.
Proof. reflexivity. Qed.

Goal ∏ I A B P root_case subtree_case i w j b k a addr,
@Addr_rect I A B P root_case subtree_case i w k a
           (subtree_addr w b addr) =
subtree_case i w j b k a addr
             (Addr_rect _ _ _ P root_case subtree_case j (arg w b) k a addr).
Proof. reflexivity. Defined.






Variable (I : UU) (A1 : Fam I) (A2 : ∏ i, A1 i -> UU) (B : ∏ i, A1 i -> Fam I).


Definition dec i : (∑ w : W A1 B i, ∏ j (a : A1 j), Addr w a -> A2 j a) ->
                   W (λ j, ∑ a, A2 j a) (B ∘__i (λ _, pr1)) i :=
  λ '(w,, f),
  W_rect I A1 B (λ j w, (∏ k a, Addr w a -> A2 k a) ->
                        W (λ k, ∑ a, A2 k a) (B ∘__i (λ _, pr1)) j)
         (λ j a f IH g, sup (a,, g j a (root_addr (sup a f)))
                            (λ k b, IH k b
                                       (λ l a' addr, g l a' (subtree_addr (sup a f) b addr))))
         i
         w
         f.

Fixpoint dec' i (w : W A1 B i) : (∏ j a, Addr w a -> A2 j a) ->
                                 W (λ j, ∑ a, A2 j a) (B ∘__i (λ _, pr1)) i :=
  match w with
    sup a f =>
    λ g, sup (a,, g _ a (root_addr (sup a f)))
             (λ j b, dec' j (f _ b)
                          (λ l a' addr, g l a'
                                          (subtree_addr (sup a f) b addr)))
  end.

Goal forall i w f, dec' i w f = dec i (w,, f).
Proof. reflexivity. Qed.


Fixpoint undec1 i (w : W (λ j, ∑ a, A2 j a) (λ j, B j ∘ pr1) i) : W A1 B i :=
  match w with sup (a1,, _) f => sup a1 (undec1 ∘__i f) end.

Definition undec2 i (w : W (λ j, ∑ a, A2 j a) (λ j, B j ∘ pr1) i)
           j (a : A1 j) (addr : Addr (undec1 i w) a) :
  A2 j a.
Proof.
  (* set (w' := undec1 i w) in *. set (p := idpath _ : w' = undec1 i w). *)
  revert addr.
  refine ((λ w' (p : w' = undec1 i w), _ : Addr w' a -> A2 j a)
            (undec1 i w)
            (idpath _)).
  intros addr.
  revert i w' j a addr w p. use Addr_rect; hnf.
  - intros i w' w p.
    destruct w as [i [a1 a2] f].
    rewrite p. cbn.
    exact a2.
  - intros i w' j b k a addr' IH w p.
    Check transportf (λ w, B i (label w) j) p b.
    destruct w as [i [a1 a2] f].
    apply (IH (f j (transportf (λ w, B i (label w) j) p b))).
    generalize b.
    apply toforallpaths.
    rewrite p.
    cbn.
    reflexivity.
Defined.

Definition undec {i} : W (λ j, ∑ a, A2 j a) (λ j, B j ∘ pr1) i ->
                   ∑ w : W A1 B i, ∏ j a, Addr w a -> A2 j a :=
  λ w, (undec1 i w,, undec2 i w).


Fixpoint undec1_dec {i} (w : W A1 B i) :
  ∏ g, undec1 i (dec' i w g) = w.
Proof.
  destruct w as [i a f]; intros g.
  change (sup a (λ j b, undec1 j (dec' j (f j b)
                                   (λ k a' addr, g k a' (subtree_addr (sup a f) b addr)))) =
          sup a f).
  apply maponpaths.
  apply funextsec; intros j.
  apply funextfun; intros b.
  apply undec1_dec.
Defined.


Lemma toforallpaths_funextfun {X Y} {f1 f2 : X -> Y} (p : f1 ~ f2) :
  toforallpaths _ f1 f2 (funextfun f1 f2 p) = p.
Proof. exact (homotweqinvweq (weqtoforallpaths _ _ _) p). Defined.

Lemma toforallpaths_funextsec {X Y} {f1 f2 : ∏ x : X, Y x} (p : f1 ~ f2) :
  toforallpaths Y f1 f2 (funextsec Y f1 f2 p) = p.
Proof. exact (homotweqinvweq (weqtoforallpaths _ _ _) p). Defined.

Lemma transport_root_addr {i} (a : A1 i) (f1 f2 : B i a ->__i W A1 B)
      (p : f1 = f2) :
  transportb (λ w, Addr w a) (maponpaths (sup a) p) (root_addr (sup a f2)) =
  root_addr (sup a f1).
Proof. induction p; reflexivity. Defined.

  (* transportb (λ w : W A1 B i, Addr w (label (sup a f))) *)
  (*   (undec1_dec (sup a f) g) (root_addr (sup a f)) = *)
  (* root_addr (undec1 i (dec' i (sup a f) g)) *)

Lemma transport_subtree_addr {i} {a : A1 i} {f1 f2 : B i a ->__i W A1 B}
      (p : ∏ j b, f1 j b = f2 j b) {j} {b : B i a j} {k} {a' : A1 k}
      (addr' : Addr (f2 j b) a') :
  transportb (λ w, Addr w a')
             (maponpaths (sup a) (funextsec _ _ _ (λ j, funextfun _ _ (p j))))
             (subtree_addr (sup a f2) b addr') =
  subtree_addr (sup a f1) b (transportb (λ w, Addr w a') (p j b) addr').
Proof.
  set (p' := funextsec _ _ _ (λ j, funextfun _ _ (p j))).
  transitivity (
      subtree_addr (sup a f1) b
        (transportb (λ w, Addr w a')
                    (toforallpaths _ _ _ (toforallpaths _ _ _ p' j) b) addr')). {
    induction p'. reflexivity.
  }
  subst p'.
  rewrite toforallpaths_funextsec. rewrite toforallpaths_funextfun.
  reflexivity.
Defined.

Lemma undec2_dec i w g :
  transportf (λ w, ∏ j a, Addr w a -> A2 j a)
             (undec1_dec w g)
             (undec2 i (dec' i w g)) =
  g.
Proof.
  apply funextsec; intros j. apply funextsec; intros a.
  apply funextfun; intros addr.
  transitivity (undec2 i (dec' i w g) j a
                       (transportb (λ w, Addr w a) (undec1_dec w g) addr)). {
    rewrite transportf_sec_constant. rewrite transportf_sec_constant.
    rewrite transportf_fun. reflexivity.
  }
  revert i w j a addr g. use Addr_rect; hnf.
  - intros i w g.
    destruct w as [i a f].
    transitivity (undec2 i (dec' i (sup a f) g) i a (root_addr _)). {
      apply maponpaths.
      apply transport_root_addr.
    }
    reflexivity.
  - intros i w j b k a' addr' IH g. induction w as [i a f _].
    Check undec1_dec (f j b).
    transitivity
      (undec2 i (dec' i (sup a f) g) k a'
              (subtree_addr
                 (undec1 i (dec' i (sup a f) g))
                 b
                 (transportb (fun w => Addr w a')
                             (undec1_dec (f j b)
                                         (λ j a addr,
                                          g j a (subtree_addr _ b addr)))
                             addr'))). {
      apply maponpaths. exact (transport_subtree_addr _ _).
    }
    exact (IH (λ j' a'' addr, g j' a'' (subtree_addr (sup a f) b addr))).
Defined.

Lemma undec_dec i w f : undec (dec i (w,, f)) = (w,, f).
Proof.
  use total2_paths_f.
  - apply undec1_dec.
  - apply undec2_dec.
Defined.