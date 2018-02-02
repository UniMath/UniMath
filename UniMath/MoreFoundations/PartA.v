(** This file contain various results that could be upstreamed to Foundations/PartA.v *)
Require Import UniMath.MoreFoundations.Foundations.
Require Import UniMath.MoreFoundations.Tactics.

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
  eapply pathscomp0. Focus 2.
    apply maponpaths. exact H.
  eapply pathscomp0. Focus 2.
    symmetry. apply transport_f_f.
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

Lemma pr1_transportf (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
   (a a' : A) (e : a = a') (xs : ∑ b : B a, P _ b):
   pr1 (transportf (λ x, ∑ b : B x, P _ b) e xs) =
     transportf (λ x, B x) e (pr1 xs).
Proof.
  destruct e; apply idpath.
Defined.

Lemma transportf_const (A B : UU) (a a' : A) (e : a = a') (b : B) :
   transportf (λ _, B) e b = b.
Proof.
  induction e.
  apply idpath.
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
