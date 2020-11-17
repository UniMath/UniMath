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
      ∑ (f:∏ t:circle, X t) (r : x = f pt), r ⟤ apd f loop = p ⟥ r.
  Theorem circle_induction : CircleInduction circle pt loop.

  *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.MoreFoundations.Equivalences.
Require Import UniMath.MoreFoundations.PathsOver.
  Import PathsOverNotations.
Require Import UniMath.Algebra.Monoids.
  Import AddNotation.
Require Import UniMath.SyntheticHomotopyTheory.AffineLine.
Require Import UniMath.NumberSystems.Integers.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.GroupAction.
Require Import UniMath.Algebra.Groups.

Local Set Implicit Arguments.
Local Unset Strict Implicit.
Declare Scope circle.
Delimit Scope circle with circle.
Local Open Scope hz.
Local Open Scope addoperation.
Local Open Scope abgr.
Local Open Scope action_scope.
Local Open Scope pathsover.
Local Open Scope circle.
Local Notation "0" := (toℤ 0).
Local Notation "1" := (toℤ 1).
Local Definition elem (G:gr) (X:Torsor G) : Type := X.
Arguments elem {_} _.
Local Notation "ℤ¹" := (trivialTorsor ℤ) : circle.

(** Statements of circle recursion and induction *)

(* Circle "recursion" is the non-dependent induction principle  *)

Definition CircleRecursion (circle : Type) (pt : circle) (loop : pt = pt) :=
  ∏ (X:Type) (x:X) (p:x=x),
    ∑ (f:circle -> X) (r : f pt = x),
      PathOver (Y := λ t:X, t = t) r (maponpaths f loop) p.

Arguments CircleRecursion : clear implicits.

Definition CircleRecursion' (circle : Type) (pt : circle) (loop : pt = pt) :=
  ∏ (X:Type) (x:X) (p:x=x),
    ∑ (f:circle -> X) (r : x = f pt), r @ maponpaths f loop = p @ r.

Arguments CircleRecursion' : clear implicits.

Definition CircleInduction (circle : Type) (pt : circle) (loop : pt = pt) :=
  ∏ (X:circle->Type) (x:X pt) (p:PathOver loop x x),
    ∑ (f:∏ t:circle, X t) (r : f pt = x),
      PathOver (Y := λ t:X pt, PathOver loop t t) r (apd f loop) p.

Arguments CircleInduction : clear implicits.

Definition CircleInduction' (circle : Type) (pt : circle) (loop : pt = pt) :=
  ∏ (X:circle->Type) (x:X pt) (p:PathOver loop x x),
    ∑ (f:∏ t:circle, X t) (r : x = f pt), r ⟤ apd f loop = p ⟥ r.

Arguments CircleInduction' : clear implicits.

Lemma CircleRecursionEquiv (circle : Type) (pt : circle) (loop : pt = pt)
  : CircleRecursion circle pt loop ≃ CircleRecursion' circle pt loop.
Proof.
  unfold CircleRecursion', CircleRecursion.
  apply weqonsecfibers; intro X.
  apply weqonsecfibers; intro x.
  apply weqonsecfibers; intro p.
  apply weqfibtototal; intro f.
  intermediate_weq (∑ r : f pt = x, maponpaths f loop @ r = r @ p).
  - apply weqfibtototal; intro r.
    apply eqweqmap.
    induction r.
    change (PathOver (idpath (f pt)) (maponpaths f loop) p)
      with (maponpaths f loop = p).
    change (idpath (f pt) @ p) with p.
    apply (maponpaths (λ k, k=p)).
    apply pathsinv0.
    apply pathscomp0rid.
  - intermediate_weq (∑ r : f pt = x, (!r) @ maponpaths f loop = p @ (!r)).
    + apply weqfibtototal; intro r.
      apply invweq.
      intermediate_weq (maponpaths f loop = r @ (p @ !r)).
      * apply hornRotation_ll.
      * intermediate_weq (maponpaths f loop = (r @ p) @ !r).
        ++ apply eqweqmap.
           apply (maponpaths (λ k, maponpaths f loop = k)).
           apply path_assoc.
        ++ apply hornRotation_rr.
    + refine (weqfp (make_weq _ (isweqpathsinv0 (f pt) x)) _).
Defined.

Lemma CircleInductionEquiv (circle : Type) (pt : circle) (loop : pt = pt)
  : CircleInduction circle pt loop ≃ CircleInduction' circle pt loop.
Proof.
Abort.

Lemma CircleInduction_isaprop (circle : Type) (pt : circle) (loop : pt = pt) :
  isaprop (CircleInduction circle pt loop).
Proof.
Abort.

Lemma CircleInductionToRecursion' (circle : Type) (pt : circle) (loop : pt = pt) :
  CircleInduction' circle pt loop -> CircleRecursion' circle pt loop.
Proof.
  intros I. unfold CircleRecursion'. intros X x p.
  set (w := I (λ _, X) x (PathOverConstant_map1 _ p)). simpl in w.
  exists (pr1 w). exists (pr12 w).
  refine (_ @ maponpaths PathOverConstant_map2 (pr22 w) @ _).
  { apply pathsinv0. refine (PathOverConstant_map2_eq2 _ _ @ _).
    apply maponpaths. apply PathOverConstant_map2_apd. }
  { refine (PathOverConstant_map2_eq1 _ _ @ _).
    apply (maponpaths (λ t, t @ _)). apply PathOverConstant_map1_map2. }
Defined.

(** A "circle" is a type with a point and a loop at that point that satisfies the
    induction principle of the circle.  The type of all circles is called "Circle".  *)

Definition Circle  := ∑ (circle : Type) (pt : circle) (loop : pt = pt), CircleInduction circle pt loop.

Definition Circle' := ∑ (circle : Type) (pt : circle) (loop : pt = pt), CircleInduction' circle pt loop.

Definition CircleInductionMatch (C C' : Type) (pt : C) (pt' : C') (loop : pt = pt) (loop' : pt' = pt')
           (I : CircleInduction' C pt loop) (I' : CircleInduction' C' pt' loop')
           (g : C -> C')
           (r0 : g pt = pt')
           (r : r0 @ loop' = maponpaths g loop @ r0)
  : ∏ (X' : C' → Type) (x' : X' pt') (p' : PathOver loop' x' x'), Type.
Proof.
  intros.
  set (X := X' ∘ g); cbn beta in X.
  set (x := pullBackPointOver g r0 x'). change (X' ∘ g) with X in x.
  set (p := pullBackPathOver g r p'). fold x in p.
  (* set (J := I X x p). *)
  set (typeofJ := ∑ (f : ∏ t : C, X t) (r : x = f pt), r ⟤ apd f loop = p ⟥ r).
  (* Check ( J : typeofJ ). *)
  assert (J'' : typeofJ).
  {
    unfold typeofJ. clear typeofJ.
    set (J' := I' X' x' p').
    set (s' := pr1 J').
    set (s := s' ∘ g); change (∏ x, X x) in (type of s).
    set (k := pr12 J'); change (pr1 J') with (s') in (type of k).
    set (ρ := pr22 J'); cbn beta in ρ; fold s k s' in ρ.
    exists s.
    exists (pullBackPointOverWithSection' _ _ k).
    set (kk := pullBackPathOver g r (apd s' loop')).


Abort.

Lemma Circle_isaprop : isaprop Circle'.
Proof.
  apply invproofirrelevance.
  intros [C [pt [loop I]]] [C' [pt' [loop' I']]].
  set (R  := CircleInductionToRecursion' I ). set (R' := CircleInductionToRecursion' I').
  set (gre  := R  C' pt' loop').
  set (g := pr1 gre). set (r := pr12 gre). set (e := pr22 gre).
  set (gre' := R' C  pt  loop ).
  set (g' := pr1 gre'). set (r' := pr12 gre'). set (e' := pr22 gre').
  fold g in r, e; fold g' in r', e'; fold r in e; fold r' in e'.
  cbn beta in e, e'.
  set (fib := (pt ,, pathsinv0 r) : hfiber g pt').
  transparent assert (v : (pt = g' (g pt))).
  { refine (r' @ _). apply maponpaths. assumption. }
  transparent assert (v' : (pt' = g (g' pt'))).
  { refine (r  @ _). apply maponpaths. assumption. }
  assert (ie : isweq g).
  { apply (isweq_iso _ g').
    { intros x. apply pathsinv0. generalize x; clear x.
      simple refine (pr1 (I _ _ _)).
      - simpl. exact v.
      - set (Q := ! pathOverEquations (f := idfun _) (g := funcomp g g') v v loop).
        apply (cast Q); clear Q.
        intermediate_path (v @ maponpaths g' (maponpaths g loop)).
        + apply (maponpaths (λ k, v @ k)). apply pathsinv0, maponpathscomp.
        + rewrite maponpathsidfun. unfold v. rewrite <- path_assoc.
          rewrite <- maponpathscomp0. intermediate_path (r' @ maponpaths g' (loop' @ r)).
          * apply maponpaths. apply maponpaths. exact e.
          * rewrite maponpathscomp0. rewrite path_assoc.
            rewrite e'. rewrite path_assoc. reflexivity. }
    { intros x. apply pathsinv0. generalize x; clear x.
      simple refine (pr1 (I' _ _ _)).
      - simpl. exact v'.
      - set (Q := ! pathOverEquations (f := idfun _) (g := funcomp g' g) v' v' loop').
        apply (cast Q); clear Q.
        intermediate_path (v' @ maponpaths g (maponpaths g' loop')).
        + apply (maponpaths (λ k, v' @ k)). apply pathsinv0, maponpathscomp.
        + rewrite maponpathsidfun. unfold v'. rewrite <- path_assoc.
          rewrite <- maponpathscomp0.
          intermediate_path (r @ maponpaths g (loop @ r')).
          * apply maponpaths. apply maponpaths. exact e'.
          * rewrite maponpathscomp0. rewrite path_assoc.
            rewrite e. rewrite path_assoc. reflexivity. } }
  (* We'll use univalence on g to identify C with C'.
     Then r will provide the match between pt and pt',
     and e will provide the corresponding match between loop and loop'.
     The question remains, how will we define matching I with I'?
   *)
  unfold CircleInduction' in I, I'.


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

Section RelatedFacts.

  Definition fact0 (X Y : Torsor ℤ) (e : X = Y) (x : X) :
    s (transportf elem e x) = s x @ e.
  Proof.
    induction e. apply pathsinv0, pathscomp0rid.
  Defined.

  Lemma fact1 (X Y:Torsor ℤ) (e : X=Y) : loop' X @ e = e @ loop' Y.
  Proof.
    induction e.
    apply pathscomp0rid.
  Defined.

  Lemma fact2 (X: Torsor ℤ) (x:X) : s (transportf elem (loop' X) x) = s x @ loop' X.
  Proof.
    exact (fact0 (loop' X) x).
  Defined.

  Lemma fact3 (X: Torsor ℤ) (x:X) : loop' pt @ s x = s x @ loop' X.
  Proof.
    apply fact1.
  Defined.

  Lemma fact4 (X: Torsor ℤ) (x:X) : loop @ s x = s x @ loop' X.
  Proof.
    refine (_ @ fact3 x).
    apply (maponpaths (λ l, l @ s x)).
    apply loop_loop'.
  Defined.

  Lemma fact5 (X: Torsor ℤ) (x:X) : loop @ s x = s (transportf elem (loop' X) x).
  Proof.
    refine (_ @ !fact2 x).
    exact (fact4 x).
  Defined.

End RelatedFacts.

Definition ε' (X Y : Torsor ℤ) (e : X = Y) (x : X) :
  ! s x @ s (transportf elem e x) = e.
Proof.                          (* 0.5.10 *)
  induction e. apply pathsinv0l.
Defined.

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
           (A:=circle) (B:circle->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p q:a1=a2) (α β: p=q)
           (v : PathOver p b1 b2) :
  cp α v = cp β v.
Proof.
  apply (maponpaths (λ f, pr1weq f v)). apply cp_irrelevance. apply torsor_hlevel.
Defined.

Opaque PathOver.                (* see the discussion at https://github.com/UniMath/UniMath/pull/1329 *)
Section A.

  Context (A : circle -> Type) (a : A pt) (p : PathOver loop a a).

  Definition Q (X: Torsor ℤ) : Type                 (* 0.5.8 *)
    := ∑ (a' : A X),
        ∑ (h : ∏ (x:X), PathOver (s x) a a'),
         ∏ (x:X), h (1 + x) = cp (ε x) (p * h x).

  Lemma iscontr_Q (X: Torsor ℤ) (* 0.5.9 *) :
    iscontr_hProp (Q X).
  Proof.
    use (hinhuniv _ (torsor_nonempty X)). intros x.
    use (iscontrweqb (Y := ∑ a', PathOver (s x) a a')).
    2 : { apply PathOverUniqueness. }
    apply weqfibtototal; intros a'.
    exact (ℤTorsorRecursion_weq
             (λ x, weqcomp (composePathOver_weq a' (s x) p) (cp (ε x)))
             x).
  Qed.

  Definition cQ (X:Torsor ℤ) := iscontrpr1 (iscontr_Q X).

  Definition c (X:Torsor ℤ)
    : A X
    := pr1 (cQ X).

  Definition c_tilde (X:Torsor ℤ) (x : X)
    : PathOver (s x) a (c X)
    := pr12 (cQ X) x.
  Arguments c_tilde : clear implicits.

  Definition c_hat (X:Torsor ℤ) (x : X)
    : c_tilde X (1 + x) = cp (ε x) (p * c_tilde X x)
    := pr22 (cQ X) x.
  Arguments c_hat : clear implicits.

  Definition apd_comparison (X Y : Torsor ℤ) (e : X = Y) (x : X) : (* 0.5.11 *)
    apd c e = cp (ε' e x) ((c_tilde X x)^-1 * c_tilde Y (transportf elem e x)).
  Proof.
    induction e.
    change (transportf elem (idpath X) x) with x.
    change (apd c (idpath X)) with (identityPathOver (c X)).
    rewrite composePathOverLeftInverse.
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

Theorem circle_induction : CircleInduction' circle pt loop.
Proof.
  unfold CircleInduction'. intros A a p.
  set (f := c p). exists f.
  set (h := c_tilde p pt); fold f in h.
  set (h0 := h pt_0).
  set (e := Δ (cp s_compute_0 h0)).
  exists e.
  assert (q := c_hat p pt); fold h in q.
  set (s0 := s pt_0); unfold pt_0 in s0.
  set (s1 := s pt_1); unfold pt_1 in s1.
  set (one' := transportf elem loop pt_0); fold pt in one'.
  assert (r := apd_comparison p loop pt_0). fold pt h h0 f one' in r; unfold pt_0 in r.
  apply (pr2 (composePathPathOverRotate _ _ _)).
  rewrite composePathPathOverPath.
  refine (r @ _); clear r.
  assert (ss : one' = pt_1).
  { unfold one'.
    refine (castTorsor_transportf (invmap torsor_univalence _) _ @ _).
    apply torsor_univalence_inv_comp_eval. }
  unfold pt_1 in ss.
  set (s0sm := λ m:ℤ¹, ! s0 @ s m).
  assert (b : cp (ε' loop 0) (h0^-1 * h one') =
              cp (ε'' 0) (h0^-1 * h (1 + pt_0))).
  { intermediate_path (cp (ε'' 0) (cp (maponpaths s0sm ss) (h0^-1 * h one'))).
    - intermediate_path (cp (maponpaths s0sm ss @ ε'' 0) (h0^-1 * h one')).
      + apply cp_irrelevance_circle.
      + apply cp_pathscomp0.
    - apply maponpaths. exact (cp_in_family _ (λ m, h0^-1 * h m)). }
  refine (b @ _); clear s0sm b. unfold pt_0. rewrite (q 0). fold h0. clear q ss one'.
  set (α0 := invrot' (s_compute_0 : s0 = ! idpath _)).
  transparent assert (α : (!s0 @ s1 = idpath pt @ (loop @ s0))).
  { exact (apstar α0 (!ε pt_0)). }
  transparent assert (β : (idpath pt @ (loop @ s0) = idpath pt @ (loop @ idpath pt))).
  { exact (apstar (idpath _) (apstar (idpath loop) s_compute_0)). }
  transparent assert (γ : (idpath pt @ (loop @ idpath pt) = idpath pt @ loop)).
  { exact (apstar (idpath _) (pathscomp0rid _)). }
  intermediate_path (cp (α@β@γ) (h0^-1 * cp (ε pt_0) (p * h0))). (* try to make do with just two factors *)
  { apply cp_irrelevance_circle. }
  rewrite cp_pathscomp0. unfold α. rewrite cp_apstar. rewrite inverse_cp_p.
  rewrite cp_pathscomp0. unfold β. rewrite cp_apstar.
  rewrite cp_idpath. unfold γ. rewrite cp_apstar.
  rewrite cp_idpath. rewrite cp_apstar.
  change (cp s_compute_0 h0) with (∇ e).
  change (cp (idpath loop) p) with p.
  rewrite composePathOverPath_compute, composePathPathOver_compute.
  intermediate_path (cp (pathscomp0rid loop) (cp α0 (h0^-1) * p * ∇ e)).
  { rewrite cp_left. apply (maponpaths (cp (pathscomp0rid loop))).
    exact (assocPathOver (cp α0 (h0^-1)) p (cp s_compute_0 h0)). }
  rewrite cp_apstar'; fold s0.
  unfold α0. rewrite invrotrot'. change (cp s_compute_0 h0) with (∇ e).
  rewrite inversePathOverIdpath'.
  reflexivity.
Defined.                        (* too slow *)

Arguments circle_induction : clear implicits.
