(**

  In this file we formalize the approach of Marc Bezem and Ulrik Buchholtz for proving that the type
  of Z-torsors has the induction principle that the circle should have.  In my older approach, (see
  the file Circle.v), I managed to show only the recursion principle for the circle (where the
  family of types is constant), and the computations were complicated and onerous.  Their approach
  follows the same basic idea, goes further, and is simpler.  It is described in the file
  https://github.com/UniMath/SymmetryBook/blob/master/ZTors.tex, commit
  1ba615fa7625516ad79fe3ad9ef68e1fc001d485.

  *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids. Import AddNotation.
Require Import UniMath.SyntheticHomotopyTheory.AffineLine.
Require Import UniMath.NumberSystems.Integers.
Local Open Scope hz.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Groups.

Set Implicit Arguments.
Unset Strict Implicit.

Module Upstream.

Definition hornRotation {X:Type} {x y z : X} {p : x = z} {q : y = z} {r : x = y} :
  r = p @ !q ≃ r @ q = p.
Proof.
  (* Thanks to Ulrik Buchholtz for this proof. *)
  induction p, r. cbn. intermediate_weq (idpath x = !!q).
  - exact (weqonpaths (weqpathsinv0 _ _) _ _).
  - intermediate_weq ((!!q) = idpath x).
    + apply weqpathsinv0.
    + rewrite pathsinv0inv0. apply idweq.
Defined.

Corollary uniqueFiller (X:Type) (x y z : X) (p : x = z) (q : y = z) :
  ∃! r, r @ q = p.
Proof.
  refine (@iscontrweqf (∑ r, r = p @ !q) _ _ _).
  { apply weqfibtototal; intro r. exact hornRotation. }
  { apply iscontrcoconustot. }
Defined.

Lemma fillerEquation {X:Type} {x y z : X} {p : x = z} {q : y = z}
      (r : x = y) (k : r @ q = p) :
  @paths (∑ r, r@q=p)
         (r ,, k)
         ((p @ !q) ,, hornRotation (idpath _)).
Proof.
  apply proofirrelevance.
  apply isapropifcontr.
  apply uniqueFiller.
Defined.

Corollary isweqpathscomp0r' {X : UU} (x : X) {x' x'' : X} (e' : x' = x'') :
  isweq (λ e : x = x', e @ e').
Proof.
  (* make a direct proof of isweqpathscomp0r, without using isweq_iso *)
  intros p. use tpair. exists (p @ !e'). now apply hornRotation.
  cbn. intros [q l]. apply fillerEquation.
Defined.

Definition transportPathTotal {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x')
           (r : (x,,y) = (x',,y'))
           (T : ∏ (a:X) (b:Y a), Type) : T x y → T x' y'.
Proof.
  induction (total2_paths_equiv _ _ _ r) as [p q].
  change (x=x') in p. change (transportf _ p y = y') in q.
  induction p.
  change (y=y') in q.
  induction q.
  trivial.
Defined.

Definition inductionOnFiller {X:Type} {x y z:X} (p:x=z) (q:y=z)
           (S := λ r:x=y, r @ q = p)
           (T : ∏ r (e : S r), Type)
           (t : T (p @ !q) (hornRotation (idpath _))) :
  ∏ (r:x=y) (e : r @ q = p), T r e.
Proof.
  intros.
  use (transportPathTotal _ t).
  apply pathsinv0.
  apply fillerEquation.
Defined.

End Upstream.

(** First some simple facts about paths over paths *)

Definition PathOver {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :=
  transportf Y p y = y'.

Definition PathOverToPathPair {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :
  PathOver y y' p → PathPair (x,,y) (x',,y').
Proof.
  intros q. exact (p,,q).
Defined.

Definition apd {X:Type} {Y : X -> Type} (s : ∏ x, Y x) {x x':X} (p : x = x') :
  PathOver (s x) (s x') p.
Proof.
  now induction p.
Defined.

Definition PathOverToTotalPath {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :
  PathOver y y' p → (x,,y) = (x',,y').
Proof.
  intros q.
  exact (invmap (total2_paths_equiv  Y (x,, y) (x',, y'))
                (PathOverToPathPair q)).
Defined.

Lemma PathOverUniqueness  {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (p:x=x') :
  ∃! (y' : Y x'), PathOver y y' p.
Proof.
  apply iscontrcoconusfromt.
Defined.

Local Goal ∏ {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (p:x=x'),
       pr1 (PathOverUniqueness y p) = (transportf Y p y,, idpath _).
Proof.
  reflexivity.
Defined.

Definition stdPathOver {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (p:x=x')
  : PathOver y (transportf Y p y) p
  := idpath (transportf Y p y).

Definition stdPathOver' {X:Type} {x x':X} {Y : X -> Type} (y' : Y x') (p:x=x')
  : PathOver (transportb Y p y') y' p.
Proof.
  now induction p.
Defined.

Definition identityPathOver {X:Type} {x:X} {Y : X -> Type} (y : Y x) : PathOver y y (idpath x)
  := idpath y.

Definition inductionPathOver {X:Type} {x:X} {Y : X -> Type} (y : Y x)
           (T : ∏ x' (y' : Y x') (p : x = x'), PathOver y y' p → Type)
           (t : T x y (idpath x) (identityPathOver y)) :
  ∏ x' (y' : Y x') (p : x = x') (q : PathOver y y' p), T x' y' p q.
Proof.
  intros. induction q, p. exact t.
Defined.

Definition transportPathOver {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x')
           (q : PathOver y y' p)
           (T : ∏ (a:X) (b:Y a), Type) : T x y → T x' y'.
Proof.
  now induction q, p.
Defined.

Definition transportPathOver' {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x')
           (q : PathOver y y' p)
           (T : ∏ (a:X) (b:Y a), Type) : T x' y' → T x y.
Proof.
  now induction q, p.
Defined.

Definition composePathOver {X:Type} {x x' x'':X} {Y : X -> Type} {y : Y x} {y' : Y x'} {y'' : Y x''}
           {p:x=x'} {p':x'=x''} : PathOver y y' p → PathOver y' y'' p' → PathOver y y'' (p @ p').
Proof.
  induction p, p'. exact pathscomp0.
Defined.

Local Notation "x * y" := (composePathOver x y).

Definition composePathOverLeftUnit {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') (q:PathOver y y' p) :
  composePathOver (identityPathOver y) q = q.
Proof.
  now induction p.
Defined.

Definition composePathOverRightUnit {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') (q:PathOver y y' p) :
  composePathOver q (identityPathOver y') = transportb (PathOver y y') (pathscomp0rid _) q.
Proof.
  now induction p, q.
Defined.

Definition assocPathOver {X:Type} {x x' x'' x''':X}
           {Y : X -> Type} {y : Y x} {y' : Y x'} {y'' : Y x''} {y''' : Y x'''}
           {p:x=x'} {p':x'=x''} {p'':x''=x'''}
           (q : PathOver y y' p) (q' : PathOver y' y'' p') (q'' : PathOver y'' y''' p'') :
  transportf _ (path_assoc p p' p'') (composePathOver q (composePathOver q' q''))
  =
  composePathOver (composePathOver q q') q''.
Proof.
  induction p, p', p'', q, q', q''. reflexivity.
Defined.

Definition inversePathOver {X:Type} {x x':X} {Y : X -> Type} {y : Y x} {y' : Y x'} {p:x=x'} :
  PathOver y y' p → PathOver y' y (!p).
Proof.
  intros q. induction p, q. reflexivity.
Defined.

Local Notation "q '^-1'" := (inversePathOver q) (at level 10).

Definition inverseInversePathOver {X:Type} {Y : X -> Type} {x:X} {y : Y x} :
  ∏ {x':X} {y' : Y x'} {p:x=x'} (q : PathOver y y' p),
  transportf _ (pathsinv0inv0 p) (inversePathOver (inversePathOver q)) = q.
Proof.
  now use inductionPathOver.
Defined.

Lemma Lemma023 (A:Type) (B:A->Type) (a1 a2 a3:A)
      (b1:B a1) (b2:B a2) (b3:B a3)
      (p1:a1=a2) (p2:a2=a3)
      (q:PathOver b1 b2 p1) :
  isweq (composePathOver q : PathOver b2 b3 p2 -> PathOver b1 b3 (p1@p2)).
Proof.
  induction p1, p2, q. apply idisweq.
Defined.

Definition composePathOver_weq (A:Type) (a1 a2 a3:A) (B:A->Type)
      (b1:B a1) (b2:B a2) (b3:B a3)
      (p1:a1=a2) (p2:a2=a3)
      (q:PathOver b1 b2 p1)
  : PathOver b2 b3 p2 ≃ PathOver b1 b3 (p1@p2)
  := weqpair (composePathOver q) (Lemma023 _).

Lemma Lemma0_2_4 (A:Type) (B:A->Type) (a1 a2:A)
      (b1:B a1) (b2:B a2) (p q:a1=a2) (α : p=q) :
  isweq ((transportf (PathOver b1 b2) α) : PathOver b1 b2 p -> PathOver b1 b2 q).
Proof.
  induction α. apply idisweq.
Defined.

Definition cp                   (* "change path" *)
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p q:a1=a2) (α : p=q) :
  PathOver b1 b2 p ≃ PathOver b1 b2 q
  := weqpair (transportf _ α) (Lemma0_2_4 α).

Arguments cp {_ _ _ _ _ _ _ _} _.

Lemma cp_to_path_over_path_over (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p q:a1=a2) (α : p=q)
      (r : PathOver b1 b2 p) (s : PathOver b1 b2 q) :
  cp α r = s ≃ PathOver r s α.
Proof.
  apply idweq.
Defined.

Definition inverse_cp_p
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q) (t : PathOver b1 b2 p) :
  cp (! α) (cp α t) = t.
Proof.
  now induction α.
Defined.

Definition cp_inverse_cp
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q) (t : PathOver b1 b2 q) :
  cp α (cp (! α) t) = t.
Proof.
  now induction α.
Defined.

Definition composePathOverRightInverse {X:Type} {x x':X} {Y : X -> Type}
           {y : Y x} {y' : Y x'} {p:x=x'} (q : PathOver y y' p) :
  composePathOver q (inversePathOver q) = cp (!pathsinv0r p) (identityPathOver y).
Proof.
  now induction p, q.
Defined.

Definition composePathOverLeftInverse {X:Type} {x x':X} {Y : X -> Type}
           {y : Y x} {y' : Y x'} {p:x=x'} (q : PathOver y y' p) :
  composePathOver (inversePathOver q) q = cp (!pathsinv0l p) (identityPathOver y').
Proof.
  now induction p, q.
Defined.

Lemma Lemma_0_2_5
      (A:Type) (B:A->Type) (a1 a2:A)
      (b1:B a1) (b2:B a2) (p q r:a1=a2) (α : p=q) (β : q=r) :
  cp (b1:=b1) (b2:=b2) (α @ β) ~ cp β ∘ cp α.
Proof.
  now induction α.
Defined.

Definition apstar               (* 0.2.7 *)
      (A:Type) (a1 a2 a3:A) (p p':a1=a2) (q q':a2=a3) (α : p=p') (β : q=q') :
  p @ q = p' @ q'.
Proof.
  induction α, p. exact β.
Defined.

Definition Lemma_0_2_8
      (A:Type) (B:A->Type) (a1 a2 a3:A)
      (p p':a1=a2) (q q':a2=a3) (α : p=p') (β : q=q')
      (b1:B a1) (b2:B a2) (b3:B a3)
      (pp : PathOver b1 b2 p) (qq : PathOver b2 b3 q) :
  cp (apstar α β) (composePathOver pp qq) =
  composePathOver (cp α pp) (cp β qq).
Proof.
  now induction p, α, β.
Defined.

Definition Lemma031_weq (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) :
  (∑ (h:∏ z, P z), ∏ z, h(1+z) = f z (h z)) ≃ P 0
  := ℤBiRecursion_weq f.

Definition Lemma031 (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) :
  isweq ((λ hq, pr1 hq 0) : (∑ (h:∏ z, P z), ∏ z, h(1+z) = f z (h z)) -> P 0)
  :=
    pr2 (Lemma031_weq f).

Definition Lemma031_inverse (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) :
  P 0 -> ∑ (h:∏ z, P z), ∏ z, h(1+z) = f z (h z)
  :=
    invmap (Lemma031_weq f).

Delimit Scope circle with circle.
Local Open Scope circle.
Notation "f ^ z" := (λ p, pr1 (Lemma031_inverse f p) z) : circle.

Definition Lemma031_compute_zero (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) (p:P 0) :
  (f^0) p = p
  :=
    ℤBiRecursion_inv_compute f p.

Definition Lemma031_compute_next (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) (p:P 0) (z:ℤ) :
  (f^(1+z)) p = f z ((f^z) p)
  :=
    ℤBiRecursion_transition_inv f p z.

Definition Lemma031_compute_prev (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) (p:P 0) (z:ℤ) :
  (f^z) p = invmap (f z) ((f^(1+z)) p)
  :=
    ℤBiRecursion_transition_inv_reversed f p z.

Require Import UniMath.Algebra.GroupAction.
Local Open Scope abgr.
Local Open Scope action_scope.

Local Notation "0" := (toℤ 0).
Local Notation "1" := (toℤ 1).
Local Notation "-1" := (- (toℤ 1)).

Definition circle := B ℤ.

Theorem loops_circle : ℤ ≃ Ω circle.
Proof.
  apply loopsBG.
Defined.

Definition loop := loops_circle 1 : Ω circle.

Definition pt := basepoint circle.

Definition pt_0 : underlyingAction pt := 0.

Definition s {Z : Torsor ℤ} (x : Z) : pt = Z.
(* Def 0.5.6 *)
Proof.
  change (trivialTorsor ℤ = Z).
  apply (invmap torsor_univalence).
  now apply triviality_isomorphism.
Defined.

Lemma s_compute_0 : s pt_0 = idpath pt.
Proof.
  intermediate_path (invmap torsor_univalence (idActionIso (trivialTorsor ℤ))).
  - change (s pt_0) with (invmap torsor_univalence (triviality_isomorphism (trivialTorsor ℤ) 0)).
    apply maponpaths.
    exact (triviality_isomorphism_compute ℤ). (* too slow *)
  - apply torsor_univalence_id.
Defined.

Local Delimit Scope addoperation_scope with abgr.

Definition ε (* 0.5.7 *) {X : Torsor ℤ} (x : X) : loop @ s x = s (1 + x).
Proof.
  change ((invmap torsor_univalence (autos ℤ one)) @ s x = s (1 + x)).
  refine (invUnivalenceCompose _ _ @ _). unfold s. apply maponpaths.
  apply subtypeEquality.
  { intros w. apply propproperty. }
  apply subtypeEquality.
  { intros w. apply isapropisweq. }
  apply funextsec. intros n.
  change (((n + 1)%abgr + x) = (n + (1 + x))). apply ac_assoc.
Defined.

Definition ε'' (x : underlyingAction pt) : ! s x @ s (1 + x) = loop.
Proof.
  unfold s, loop, loops_circle, loopsBG.
  change ((invweq torsor_univalence ∘ autos ℤ)%weq 1) with
          (invmap torsor_univalence (autos ℤ 1)).
  set (succ := autos ℤ 1).
  set (succ' := pr1weq succ).
  apply path_inv_rotate_ll.
  apply pathsinv0.
  refine (invUnivalenceCompose _ _ @ _).
  apply maponpaths.
  apply subtypeEquality.
  { intros w. apply propproperty. }
  apply subtypeEquality.
  { intros w. apply isapropisweq. }
  apply funextsec. intros n.
  change (n+x+1 = n+(1+x))%addmonoid.
  intermediate_path (n+(x+1))%addmonoid.
  - apply assocax.
  - apply maponpaths, commax.
Defined.

Section A.

  Context (A : circle -> Type) (a : A pt).

  Definition Q (p : PathOver a a loop) (X: Torsor ℤ) : Type                 (* 0.5.8 *)
    := ∑ (a' : A X),
        ∑ (h : ∏ (x:X), PathOver a a' (s x)),
         ∏ (x:X), h (1 + x) = cp (ε x) (composePathOver p (h x)).

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
    : c_tilde p X (1 + x) = cp (ε x) (composePathOver p (c_tilde p X x))
    := pr22 (cQ p X) x.
  Arguments c_hat : clear implicits.

  Definition elem (X:Torsor ℤ) : Type := X.

  Definition ε' (X Y : Torsor ℤ) (e : X = Y) (x : X) :
    ! s x @ s (transportf elem e x) = e.
  Proof.                        (* 0.5.10 *)
    induction e. apply pathsinv0l.
  Defined.

  Context (p : PathOver a a loop).

  Definition Lemma_0_5_11 (X Y : Torsor ℤ) (e : X = Y) (x : X) : (* 0.5.11 *)
    apd (c p) e = cp (ε' e x) ( (c_tilde p X x) ^-1
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

  Lemma c_compute_1 : c p pt = transportf A (s pt_0) a.
  Proof.
    (* the presence of the transport is unpleasant, but seems to be unavoidable *)
    reflexivity.
  Qed.

  Lemma c_compute_1' : c p pt = a.
  Proof.
    (* not judgemental *)
    change (transportf _ (s pt_0) a = transportf _ (idpath _) a).
    apply (maponpaths (λ p, transportf A p a)).
    apply s_compute_0.
  Defined.

  Check (apd (c p) loop : PathOver (c p pt) (c p pt) loop).

  Check (transportf (λ x : circle, x=x) (s pt_0) loop : pt = pt).

  Lemma b : transportf (λ x : circle, x=x) (s pt_0) loop = loop.
  Proof.
    change (transportf (λ x : circle, x = x) (s pt_0) loop = transportf (λ x : circle, x = x) (idpath _) loop).
    apply (maponpaths (λ r, transportf (λ x : circle, x = x) r loop)).
    apply s_compute_0.
  Defined.

  (* illustrate how to work around Coq not finding the right coercions:  *)

  Local Goal ∏ (Y : B ℤ), Type.
  Proof.
    intros.
    Fail exact Y.
    exact (underlyingAction Y).
  Defined.

  Local Goal ∏ (X : circle), Type.
  Proof.
    intros.
    Fail exact X.
    exact (underlyingAction X).
  Defined.

  Local Goal ∏ (X : circle), Torsor ℤ.
  Proof.
    intros.
    exact X.
  Defined.

  Local Goal ∏ (X : Torsor ℤ), circle.
  Proof.
    intros.
    exact X.
  Defined.

  Goal unit.
    set (cen := cQ p pt).
    set (a' := c p pt).
    set (a'' := transportf A (s pt_0) a).
    set (e := c_compute_1).
    fold a' a'' in e.
    set (h := c_tilde p pt).
    fold a' in h.
    assert (q := c_hat p pt).
    assert (q0 := q 0).
    fold h in q, q0.
    set (p' := apd (c p) loop).
    fold pt a' in p'.

    assert (ss : transportf elem loop pt_0 = 1 + pt_0). (* needed for r below *)
    { unfold pt_0,loop,loops_circle,loopsBG.
      change ((invweq torsor_univalence ∘ autos ℤ)%weq 1) with
          (invmap torsor_univalence (autos ℤ 1)).
      set (succ := autos ℤ 1).
      now rewrite castTorsor_transportf, torsor_univalence_inv_comp_eval. }
    assert (r := Lemma_0_5_11 loop 0).
    change (apd (c p) loop) with p'.
    fold pt in r.
    fold h in r.
    fold p' in r.
    assert (b :
              cp (ε' loop 0) ((h 0) ^-1 * h (transportf elem loop 0)) =
              cp (ε'' 0) ((h 0) ^-1 * h 1)
           ).

    (* rewrite ss in r. *)
  Abort.

End A.
