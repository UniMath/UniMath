(**

  In this file we formalize the approach of Marc Bezem and Ulrik Buchholtz for proving that the type
  of Z-torsors has the induction principle that the circle should have.  In my older approach, (see
  the file Circle.v), I managed to show only the recursion principle for the circle (where the
  family of types is constant), and the computations were complicated and onerous.  Their approach
  follows the same basic idea, goes further, and is simpler.  It is described in the file
  https://github.com/UniMath/SymmetryBook/blob/master/ZTors.tex, commit
  1ba615fa7625516ad79fe3ad9ef68e1fc001d485.

  The main things proved are these:

  Definition circle := B ℤ.
  Definition pt := basepoint circle.
  Theorem loops_circle : ℤ ≃ Ω circle.
  Definition loop := loops_circle 1 : Ω circle.
  Definition CircleInduction (circle : Type) (pt : circle) (loop : pt = pt) :=
    ∏ (X:circle->Type) (x:X pt) (p:PathOver x x loop),
      ∑ (f:∏ t:circle, X t) (r : f pt = x), apd f loop = r ⟤ p ⟥ !r.
  Theorem circle_induction : CircleInduction circle pt loop.

  *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids. Import AddNotation.
Require Import UniMath.SyntheticHomotopyTheory.AffineLine.
Require Import UniMath.NumberSystems.Integers.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.GroupAction.
Require Import UniMath.Algebra.Groups.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Delimit Scope circle with circle.
Local Open Scope hz.
Local Open Scope addoperation.
Local Open Scope abgr.
Local Open Scope action_scope.
Local Open Scope pathsover.
Local Open Scope circle.
Local Notation "0" := (toℤ 0).
Local Notation "1" := (toℤ 1).
Local Definition elem (X:Torsor ℤ) : Type := X.
Local Notation "ℤ¹" := (trivialTorsor ℤ) : circle.

(** Statement of circle induction *)

Definition CircleRecursion (circle : Type) (pt : circle) (loop : pt = pt) :=
  ∏ (X:Type) (x:X) (p:x=x),
    ∑ (f:circle -> X) (r : f pt = x), maponpaths f loop = r @ p @ !r.

Arguments CircleRecursion : clear implicits.

Definition CircleInduction (circle : Type) (pt : circle) (loop : pt = pt) :=
  ∏ (X:circle->Type) (x:X pt) (p:PathOver x x loop),
    ∑ (f:∏ t:circle, X t) (r : f pt = x), apd f loop = r ⟤ p ⟥ !r.

Arguments CircleInduction : clear implicits.

Lemma CircleInduction_isaprop (circle : Type) (pt : circle) (loop : pt = pt) :
  isaprop (CircleInduction circle pt loop).
Proof.
  apply invproofirrelevance.
  intros I J.
  apply funextsec; intros A.
  apply funextsec; intros a.
  apply funextsec; intros p.
Abort.

Definition Circles := ∑ (circle : Type) (pt : circle) (loop : pt = pt), CircleInduction circle pt loop.

Lemma Circles_isaprop : isaprop Circles.
Proof.
  apply invproofirrelevance.
  intros [C [pt [loop I]]] [C' [pt' [loop' I']]].
Abort.

Lemma CircleInduction_to_Recursion (C : Type) (pt : C) (loop : pt = pt) :
     CircleInduction C pt loop -> CircleRecursion C pt loop.
Proof.
  intros ci ? ? ?.
  assert (q := ci (λ c, X) x (PathOver_inConstantFamily loop p)); cbn beta in q.
  induction q as [F [R E]].
  exists F.
  exists R.
  unfold PathOver_inConstantFamily in E.
Abort.

(** now start the formalization, following Marc and Ulrik *)

Definition circle := B ℤ.

Theorem loops_circle : ℤ ≃ Ω circle.
Proof.
  apply loopsBG.
Defined.

Definition loop := loops_circle 1 : Ω circle.

Definition loop' (X : Torsor ℤ) : X = X
  := invmap torsor_univalence (left_mult_Iso X 1).

Definition pt := basepoint circle.

Definition pt_0 : underlyingAction pt := 0.
Definition pt_1 : underlyingAction pt := 1.

Definition loop_loop' : loop = loop' pt.
Proof.
  change (
      invmap torsor_univalence (trivialTorsorAuto ℤ 1) =
      invmap torsor_univalence (left_mult_Iso pt 1)).
  apply maponpaths.
  apply underlyingIso_injectivity, pr1weq_injectivity, funextsec; intros n.
  change (n + 1 = 1 + n)%addmonoid.
  apply commax.
Defined.

Definition s {Z : Torsor ℤ} (x : Z) : pt = Z
(* 0.5.6 *)
  := invmap torsor_univalence (triviality_isomorphism Z x).

Lemma s_compute_0 : s pt_0 = idpath pt.
Proof.
  intermediate_path (invmap torsor_univalence (idActionIso ℤ¹)).
  - change (s pt_0) with (invmap torsor_univalence (triviality_isomorphism ℤ¹ 0)).
    apply maponpaths.
    exact (triviality_isomorphism_compute ℤ). (* too slow *)
  - apply torsor_univalence_id.
Defined.

Definition ε {X : Torsor ℤ} (x : X) : loop @ s x = s (1 + x).
(* 0.5.7 *)
Proof.
  change ((invmap torsor_univalence (trivialTorsorRightMultiplication ℤ one)) @ s x = s (1 + x)).
  refine (invUnivalenceCompose _ _ @ _). unfold s. apply maponpaths.
  apply underlyingIso_injectivity, pr1weq_injectivity, funextsec; intros n.
  change (((n + 1)%addoperation + x) = (n + (1 + x))). apply ac_assoc.
Defined.

Definition ε1 {X : Torsor ℤ} (x : X) : s x @ loop' X = s (1 + x).
Proof.
  unfold loop'.
  refine (invUnivalenceCompose _ _ @ _). unfold s. apply maponpaths.
  apply underlyingIso_injectivity, pr1weq_injectivity, funextsec; intros n.
  change (1 + (n + x) = n + (1 + x)).
  refine (! ac_assoc _ _ _ _ @ _ @ ac_assoc _ _ _ _).
  apply (maponpaths (right_mult x)). apply commax.
Defined.

Definition ε'' (x : underlyingAction pt) : ! s x @ s (1 + x) = loop.
Proof.
  apply path_inv_rotate_ll, pathsinv0. refine (_ @ ε1 x).
  apply maponpaths; clear x. apply loop_loop'.
Defined.

Definition cp_irrelevance_circle
           (A:=circle) (B:circle->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p q:a1=a2) (α β: p=q) :
  cp (b1:=b1) (b2:=b2) α = cp (b1:=b1) (b2:=b2) β.
Proof.
  apply cp_irrelevance. apply torsor_hlevel.
Defined.

Definition cp_irrelevance_circle_value
           (A:=circle) (B:circle->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p q:a1=a2) (α β: p=q)
           (v : PathOver b1 b2 p) :
  cp α v = cp β v
  := maponpaths (λ f, pr1weq f v) (cp_irrelevance_circle b1 b2 α β).

Definition cp_irrelevance_circle_1
           (A:=circle) (B:circle->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p:a1=a2) (α: p=p) :
  cp (b1:=b1) (b2:=b2) α = cp (b1:=b1) (b2:=b2) (idpath p)
  := cp_irrelevance_circle (B:=B) b1 b2 α (idpath p).

Section A.

  Context (A : circle -> Type) (a : A pt).

  Definition Q (p : PathOver a a loop) (X: Torsor ℤ) : Type                 (* 0.5.8 *)
    := ∑ (a' : A X),
        ∑ (h : ∏ (x:X), PathOver a a' (s x)),
         ∏ (x:X), h (1 + x) = cp (ε x) (p * h x).

  Lemma iscontr_Q (p : PathOver a a loop) (X: Torsor ℤ) (* 0.5.9 *) :
    iscontr_hProp (Q p X).
  Proof.
    use (hinhuniv _ (torsor_nonempty X)); intros x.
    use (iscontrweqb (Y := ∑ a', PathOver a a' (s x))).
    2 : { apply PathOverUniqueness. }
    apply weqfibtototal; intros a'.
    exact (ℤTorsorRecursion_weq
             (λ x, weqcomp (composePathOver_weq a' (s x) p) (cp (ε x)))
             x).
  Defined.

  Definition cQ (p : PathOver a a loop) (X:Torsor ℤ) := iscontrpr1 (iscontr_Q p X).

  Definition c (p : PathOver a a loop) (X:Torsor ℤ)
    : A X
    := pr1 (cQ p X).

  Definition c_tilde (p : PathOver a a loop) (X:Torsor ℤ) (x : X)
    : PathOver a (c p X) (s x)
    := pr12 (cQ p X) x.
  Arguments c_tilde : clear implicits.

  Definition c_hat (p : PathOver a a loop) (X:Torsor ℤ) (x : X)
    : c_tilde p X (1 + x) = cp (ε x) (p * c_tilde p X x)
    := pr22 (cQ p X) x.
  Arguments c_hat : clear implicits.

  Definition ε' (X Y : Torsor ℤ) (e : X = Y) (x : X) :
    ! s x @ s (transportf elem e x) = e.
  Proof.                        (* 0.5.10 *)
    induction e. apply pathsinv0l.
  Defined.

  Context (p : PathOver a a loop).

  Definition apd_comparison (X Y : Torsor ℤ) (e : X = Y) (x : X) : (* 0.5.11 *)
    apd (c p) e = cp (ε' e x) ( (c_tilde p X x)^-1
                                *
                                c_tilde p Y (transportf elem e x)).
  Proof.
    induction e.
    change (transportf elem (idpath X) x) with x.
    rewrite composePathOverLeftInverse.
    change (apd (c p) (idpath X)) with (identityPathOver (c p X)).
    change (ε' (idpath X) x) with (pathsinv0l (s x)).
    rewrite cp_inverse_cp.
    reflexivity.
  Defined.

  (* illustrate how to work around Coq not finding the right coercions:  *)
  Local Goal ∏ (Y : B ℤ), Type.        Proof. intros. Fail exact Y. exact (underlyingAction Y). Defined.
  Local Goal ∏ (X : circle), Type.     Proof. intros. Fail exact X. exact (underlyingAction X). Defined.
End A.

Arguments c_tilde {_ _} _ _ _.
Arguments c_hat {_ _} _ _ _.

Theorem circle_induction : CircleInduction circle pt loop.
Proof.
  unfold CircleInduction. intros A a p.
  set (f := c p). exists f.
  set (h := c_tilde p pt); fold f in h.
  set (e := ! cp s_compute_0 (h 0)). exists e.
  assert (q := c_hat p pt); fold h in q.
  set (s0 := s pt_0). unfold pt_0 in s0.
  set (s1 := s pt_1). unfold pt_1 in s1.
  set (one' := transportf elem loop pt_0). fold pt in one'.
  assert (r := apd_comparison p loop pt_0). fold pt h f one' in r; unfold pt_0 in r.
  refine (r @ _); clear r.
  assert (ss : one' = pt_1). (* needed for r? *)
  { change ( transportf elem
                        (invmap torsor_univalence (trivialTorsorRightMultiplication ℤ 1))
                        pt_0
             = 1 + pt_0).
    rewrite castTorsor_transportf. rewrite torsor_univalence_inv_comp_eval. reflexivity. }
  unfold pt_1 in ss.
  set (s0sm := λ m:ℤ¹, ! s0 @ s m).
  assert (b : cp (ε' loop 0) ((h 0)^-1 * h one') =
              cp (ε'' 0) ((h 0)^-1 * h (1 + pt_0))).
  { intermediate_path (cp (ε'' 0) (cp (maponpaths s0sm ss) ((h 0)^-1 * h one'))).
    - intermediate_path (cp (maponpaths s0sm ss @ ε'' 0) ((h 0)^-1 * h one')).
      + apply cp_irrelevance_circle_value.
      + apply cp_pathscomp0.
    - apply maponpaths. exact (cp_in_family _ (λ m, (h 0) ^-1 * h m)). }
  refine (b @ _); clear b. unfold pt_0. rewrite (q 0). clear q.
  set (h0 := h 0).
  set (α0 := invrot' (s_compute_0 : s pt_0 = ! idpath _)).
  set (ε0 := ε pt_0).
  transparent assert (α : (!s0 @ s1 = idpath pt @ (loop @ s0))).
  { exact (apstar α0 (!ε0)). }
  transparent assert (β : (idpath pt @ (loop @ s0) = idpath pt @ (loop @ idpath pt))).
  { exact (apstar (idpath _) (apstar (idpath loop) s_compute_0)). }
  transparent assert (γ : (idpath pt @ (loop @ idpath pt) = idpath pt @ loop)).
  { exact (apstar (idpath _) (pathscomp0rid _)). }
  intermediate_path (cp (α@β@γ) ((h 0)^-1 * cp ε0 (p * h 0))).
  { apply cp_irrelevance_circle_value. }
  fold h0. rewrite cp_pathscomp0. unfold α. rewrite cp_apstar. rewrite inverse_cp_p.
  set (Q := invrot (p:=s0) α0); change (!idpath pt) with (idpath pt) in Q.
  rewrite cp_pathscomp0. unfold β. rewrite cp_apstar.
  rewrite cp_idpath. unfold γ. rewrite cp_apstar.
  rewrite cp_idpath. rewrite cp_apstar.
  change (cp (idpath loop) p) with p.
  rewrite composePathOverPath_compute, composePathPathOver_compute.
  set (rid := pathscomp0rid).
  intermediate_path (cp (rid loop) (cp α0 (h0^-1) * p * cp s_compute_0 h0)).
  { rewrite cp_left. apply maponpaths.
    exact (assocPathOver (cp α0 (h0^-1)) p (cp s_compute_0 h0)). }
  apply (maponpaths (cp (rid loop))).
  rewrite cp_apstar'; fold s0.
  intermediate_path (∇ e * p * cp s_compute_0 h0).
  - apply (maponpaths (λ e, ∇ e * p * cp s_compute_0 h0)).
    unfold α0. rewrite invrotrot'. reflexivity.
  - apply maponpaths. apply pathsinv0. unfold e, h0.
    change ((! !(cp s_compute_0 (h 0))) = cp s_compute_0 (h 0)).
    apply pathsinv0inv0.
Defined.

Arguments circle_induction : clear implicits.
