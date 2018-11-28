(** This file contain various results that could be upstreamed to Foundations/PartA.v *)
Require Import UniMath.MoreFoundations.Foundations.
Require Import UniMath.MoreFoundations.Tactics.

Lemma maponpaths_for_constant_function {T1 T2 : UU} (x : T2) {t1 t2 : T1}
      (e: t1 = t2): maponpaths (fun _: T1 => x) e = idpath x.
Proof.
  induction e.
  apply idpath.
Qed.

Lemma base_paths_pair_path_in2 {X : UU} (P : X → UU) {x : X} {p q : P x} (e : p = q) :
  base_paths _ _ (pair_path_in2 P e) = idpath x.
Proof.
now induction e.
Qed.

(* taken from TypeTheory/Display_Cats/Auxiliary.v *)
(** Very handy for reasoning with “dependent paths” —

Note: similar to [transportf_pathsinv0_var], [transportf_pathsinv0'],
but not quite a special case of them, or (as far as I can find) any other
library lemma.
 *)



Lemma transportf_transpose {X : UU} {P : X → UU} {x x' : X}
      (e : x = x') (y : P x) (y' : P x') :
      transportb P e y' = y -> y' = transportf P e y.
Proof.
intro H; induction e; exact H.
Defined.

Definition transportf_pathsinv0 {X} (P:X->UU) {x y:X} (p:x = y) (u:P x) (v:P y) :
  transportf _ (!p) v = u -> transportf _ p u = v.
Proof. intro e. induction p, e. reflexivity. Defined.

Definition maponpaths_2 {X Y Z : UU} (f : X -> Y -> Z) {x x'} (e : x = x') y
  : f x y = f x' y
:= maponpaths (λ x, f x y) e.

Lemma transportf_comp_lemma (X : UU) (B : X -> UU) {A A' A'': X} (e : A = A'') (e' : A' = A'')
  (x : B A) (x' : B A')
  : transportf _ (e @ !e') x = x'
  -> transportf _ e x = transportf _ e' x'.
Proof.
  intro H.
  eapply pathscomp0.
  2: { apply maponpaths. exact H. }
  eapply pathscomp0.
  2: { symmetry. apply transport_f_f. }
  apply (maponpaths (λ p, transportf _ p x)).
  apply pathsinv0.
  eapply pathscomp0.
  - apply @pathsinv0, path_assoc.
  - eapply pathscomp0.
    apply maponpaths.
    apply pathsinv0l.
    apply pathscomp0rid.
Defined.

Lemma transportf_comp_lemma_hset (X : UU) (B : X -> UU) (A : X) (e : A = A)
  {x x' : B A} (hs : isaset X)
  : x = x'
  -> transportf _ e x = x'.
Proof.
  intros ex.
  apply @pathscomp0 with (transportf _ (idpath _) x).
  - apply (maponpaths (λ p, transportf _ p x)).
    apply hs.
  - exact ex.
Qed.


Lemma transportf_set {A : UU} (B : A → UU)
      {a : A} (e : a = a) (b : B a)
      (X : isaset A)
  : transportf B e b = b.
Proof.
  apply transportf_comp_lemma_hset.
  - apply X.
  - apply idpath.
Defined.


Lemma transportf_pair {A B} (P : A × B -> UU) {a a' : A} {b b' : B}
      (eA : a = a') (eB : b = b') (p : P (a,,b))
      : transportf P (pathsdirprod eA eB) p =
        transportf (λ bb, P(a',,bb) ) eB (transportf (λ aa, P(aa,,b)) eA p).
Proof.
  induction eA. induction eB. apply idpath.
Defined.

Lemma weqhomot {A B : UU} (f : A -> B) (w : A ≃ B) (H : w ~ f) : isweq f.
Proof.
  apply isweqhomot with w. apply H. apply weqproperty.
Defined.

Lemma invmap_eq {A B : UU} (f : A ≃ B) (b : B) (a : A)
  : b = f a → invmap f b = a.
Proof.
  intro H.
  apply (invmaponpathsweq f).
  etrans. apply homotweqinvweq. apply H.
Defined.

Lemma pr1_transportf {A : UU} {B : A -> UU} {P : ∏ a, B a -> UU}
   {a a' : A} (e : a = a') (xs : ∑ b : B a, P _ b):
   pr1 (transportf (λ x, ∑ b : B x, P _ b) e xs) =
     transportf (λ x, B x) e (pr1 xs).
Proof.
  apply pathsinv0.
  apply (transport_map (λ a, pr1 (P := P a))).
Defined.

Lemma pr2_transportf {A} {B1 B2 : A → UU}
    {a a' : A} (e : a = a') (xs : B1 a × B2 a)
  : pr2 (transportf (λ a, B1 a × B2 a) e xs) = transportf _ e (pr2 xs).
Proof.
  apply pathsinv0.
  apply (transport_map (λ a, pr2 (P := λ _, B2 a))).
Defined.

Lemma coprodcomm_coprodcomm {X Y : UU} (v : X ⨿ Y) : coprodcomm Y X (coprodcomm X Y v) = v.
Proof.
  induction v as [x|y]; reflexivity.
Defined.

Definition sumofmaps_funcomp {X1 X2 Y1 Y2 Z : UU} (f1 : X1 → X2) (f2 : X2 → Z) (g1 : Y1 → Y2)
  (g2 : Y2 → Z) : sumofmaps (f2 ∘ f1) (g2 ∘ g1) ~ sumofmaps f2 g2 ∘ coprodf f1 g1.
Proof.
  intro x. induction x as [x|y]; reflexivity.
Defined.

Definition sumofmaps_homot {X Y Z : UU} {f f' : X → Z} {g g' : Y → Z} (h : f ~ f') (h2 : g ~ g')
  : sumofmaps f g ~ sumofmaps f' g'.
Proof.
  intro x. induction x as [x|y].
  - exact (h x).
  - exact (h2 y).
Defined.

(** coprod computation helper lemmas  *)

Definition coprod_rect_compute_1
           (A B : UU) (P : A ⨿ B -> UU)
           (f : ∏ (a : A), P (ii1 a))
           (g : ∏ (b : B), P (ii2 b)) (a:A) :
  coprod_rect P f g (ii1 a) = f a.
Proof.
  intros.
  apply idpath.
Defined.

Definition coprod_rect_compute_2
           (A B : UU) (P : A ⨿ B -> UU)
           (f : ∏ a : A, P (ii1 a))
           (g : ∏ b : B, P (ii2 b)) (b:B) :
  coprod_rect P f g (ii2 b) = g b.
Proof.
  intros.
  apply idpath.
Defined.

(** Flip the arguments of a function *)
Definition flipsec {A B : UU} {C : A -> B -> UU} (f : ∏ a b, C a b) : ∏ b a, C a b :=
  λ x y, f y x.
Notation flip := flipsec.

(** Flip is a weak equivalence (in fact, it is an involution) *)
Lemma isweq_flipsec {A B : UU} {C : A -> B -> UU} : isweq (@flipsec A B C).
Proof.
  apply (isweq_iso _ flipsec); reflexivity.
Defined.

Definition flipsec_weq {A B : UU} {C : A -> B -> UU} :
  (∏ a b, C a b) ≃ (∏ b a, C a b) := weqpair flipsec isweq_flipsec.

(** The subtypes of a type of hlevel S n are also of hlevel S n.
    This doesn't work for types of hlevel 0: a subtype of a contractible
    type might be empty, not contractible! *)
Lemma isofhlevel_hsubtype {X : UU} {n : nat} (isof : isofhlevel (S n) X) :
  ∏ subt : hsubtype X, isofhlevel (S n) subt.
Proof.
  intros subt.
  apply isofhleveltotal2.
  - assumption.
  - intro.
    apply isofhlevelsnprop.
    apply propproperty.
Defined.

(** Homotopy equivalence on total spaces.

  This result combines weqfp and weqfibtototal conveniently.
  *)
Lemma weqtotal2 {X Y:Type} {P:X->Type} {Q:Y->Type} (f : X ≃ Y) :
  (∏ x, P x ≃ Q (f x)) -> (∑ x:X, P x) ≃ (∑ y:Y, Q y).
Proof.
  intros e. exists (λ xp, (f(pr1 xp),,e (pr1 xp) (pr2 xp))).
  exact (twooutof3c _ _ (isweqfibtototal P (Q ∘ f) e) (pr2 (weqfp f Q))).
Defined.
