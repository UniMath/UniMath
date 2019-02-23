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
  Theorem loops_circle : ℤ ≃ Ω circle.
  Definition loop := loops_circle 1 : Ω circle.
  Definition CircleInduction (circle : Type) (pt : circle) (loop : pt = pt) :=
    ∏ (X:circle->Type) (x:X pt) (p:PathOver x x loop),
      ∑ (f:∏ t:circle, X t) (r : f pt = x), apd f loop = r ⟤ p ⟥ !r.
  Arguments CircleInduction : clear implicits.
  Theorem circle_induction : CircleInduction circle pt loop.

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

Section Upstream.

Definition loop_transport (X:Type) (x y:X) (e : x = y) (p : x = x) :
  transportf (λ z:X, z=z) e p = !e @ p @ e.
Proof.
  induction e. change (p = p @ idpath x). exact (!pathscomp0rid p).
Defined.

Definition invrot (X:Type) (x y:X) (p:x=y) (p':y=x) : !p = p' -> p = !p'.
Proof.
  intros e. induction e. apply pathsinv0. apply pathsinv0inv0.
Defined.

Definition invrot' (X:Type) (x y:X) (p:x=y) (p':y=x) : p = !p' -> !p = p'.
Proof.
  intros e. induction (!e); clear e. apply pathsinv0inv0.
Defined.

Definition invrot'rot (X:Type) (x y:X) (p:x=y) (p':y=x) (e : !p = p') :
  invrot' (invrot e) = e.
Proof.
  now induction e,p.
Defined.

Definition invrotrot' (X:Type) (x y:X) (p:x=y) (p':y=x) (e : p = !p') :
  invrot (invrot' e) = e.
Proof.
  rewrite <- (pathsinv0inv0 e).
  generalize (!e); clear e.
  intros e.
  now induction e, p'.
Defined.

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

(** Some simple facts about paths over paths *)

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

Definition PathOver_inConstantFamily (X Y:Type) (x x':X) (y y':Y) (p:x=x') :
   y = y' -> PathOver (Y := (λ x, Y)) y y' p.
Proof.
  intros q.
  unfold PathOver.
  induction p.
  change (y=y').
  exact q.
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

Definition pathOverIdpath {X:Type} {x:X} {Y : X -> Type} (y y' : Y x) : PathOver y y' (idpath x) = (y = y')
  := idpath _.

Definition toPathOverIdpath {X:Type} {x:X} {Y : X -> Type} (y y' : Y x) : y = y' -> PathOver y y' (idpath x)
  := idfun _.

Notation "'∇' q" := (toPathOverIdpath q) (at level 10).

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

Definition composePathOverPath {X:Type} {x x':X} {Y : X -> Type} {y : Y x} {y' y'' : Y x'}
           {p:x=x'} : PathOver y y' p → y' = y'' → PathOver y y'' p.
Proof.
  intros q e. now induction e.
Defined.

Notation "q ⟥ e" := (composePathOverPath q e) (at level 56, left associativity).

Definition composePathPathOver {X:Type} {x' x'':X} {Y : X -> Type} {y y': Y x'} {y'' : Y x''}
           {p:x'=x''} : y = y' → PathOver y' y'' p → PathOver y y'' p.
Proof.
  intros e q. now induction e.
Defined.

Notation "e ⟤ q" := (composePathPathOver e q) (at level 56, left associativity).

Definition composePathOverLeftUnit {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') (q:PathOver y y' p) :
  identityPathOver y * q = q.
Proof.
  now induction p.
Defined.

Definition composePathOverRightUnit {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') (q:PathOver y y' p) :
  q * identityPathOver y' = transportb (PathOver y y') (pathscomp0rid _) q.
Proof.
  now induction p, q.
Defined.

Definition assocPathOver {X:Type} {x x' x'' x''':X}
           {Y : X -> Type} {y : Y x} {y' : Y x'} {y'' : Y x''} {y''' : Y x'''}
           {p:x=x'} {p':x'=x''} {p'':x''=x'''}
           (q : PathOver y y' p) (q' : PathOver y' y'' p') (q'' : PathOver y'' y''' p'') :
  transportf _ (path_assoc p p' p'') (q * composePathOver q' q'')
  =
  composePathOver q q' * q''.
Proof.
  induction p, p', p'', q, q', q''. reflexivity.
Defined.

Definition inversePathOver {X:Type} {x x':X} {Y : X -> Type} {y : Y x} {y' : Y x'} {p:x=x'} :
  PathOver y y' p → PathOver y' y (!p).
Proof.
  intros q. induction p, q. reflexivity.
Defined.

Definition inversePathOver' {X:Type} {x x':X} {Y : X -> Type} {y : Y x} {y' : Y x'} {p:x'=x} :
  PathOver y y' (!p) → PathOver y' y p.
Proof.
  intros q. induction p, q. reflexivity.
Defined.

Local Notation "q '^-1'" := (inversePathOver q) (at level 10).

Definition inverseInversePathOver {X:Type} {Y : X -> Type} {x:X} {y : Y x} :
  ∏ {x':X} {y' : Y x'} {p:x=x'} (q : PathOver y y' p),
  transportf _ (pathsinv0inv0 p) (q^-1^-1) = q.
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
           (A:Type) (a1 a2:A) (p q:a1=a2) (α : p=q)
           (B:A->Type) (b1:B a1) (b2:B a2) :
  PathOver b1 b2 p ≃ PathOver b1 b2 q
  := weqpair (transportf _ α) (Lemma0_2_4 α).

Arguments cp {_ _ _ _ _} _ {_ _ _}.

Definition composePathOverPath_compute {X:Type} {x x':X} {Y : X -> Type} {y : Y x} {y' y'' : Y x'}
           {p:x=x'} (q : PathOver y y' p) (e : y' = y'') :
  q ⟥ e = cp (pathscomp0rid p) (q * ∇ e).
Proof.
  now induction p, q, e.
Defined.

Definition composePathPathOver_compute {X:Type} {x' x'':X} {Y : X -> Type} {y y': Y x'} {y'' : Y x''}
           {p:x'=x''} (e : y = y') (q : PathOver y' y'' p) :
  e ⟤ q = ∇ e * q.
Proof.
  now induction p.
Defined.

Definition cp_idpath
           (A:Type) (a1 a2:A) (p:a1=a2)
           (B:A->Type) (b1:B a1) (b2:B a2) (u:PathOver b1 b2 p) :
  cp (idpath p) u = u.
Proof.
  reflexivity.
Defined.

Definition cp_left
           (A:Type) (a2 a3:A) (p p':a2=a3) (α:p=p')
           (B:A->Type) (b1 b2:B a2) (b3:B a3)
           (r:PathOver b1 b2 (idpath a2))
           (q:PathOver b2 b3 p) :
  r * cp α q = cp α (r*q).
Proof.
  now induction r, α.
Defined.

Definition cp_right
           (A:Type) (a1 a2:A) (p p':a1=a2) (α:p=p')
           (B:A->Type) (b1:B a1) (b2 b3:B a2)
           (q:PathOver b1 b2 p)
           (r:PathOver b2 b3 (idpath a2)) :
  cp α q * r = cp (maponpaths (λ p, p @ idpath a2) α) (q*r).
Proof.
  now induction r, α.
Defined.

Definition cp_in_family
           (A:Type) (a1 a2:A)
           (T:Type) (t0 t1:T) (v:t0=t1) (p:T->a1=a2)
           (B:A->Type) (b1:B a1) (b2:B a2) (s : ∏ t, PathOver b1 b2 (p t)) :
  cp (maponpaths p v) (s t0) = s t1.
Proof.
  now induction v.
Defined.

Definition cp_irrelevance
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p q:a1=a2) (α β: p=q) :
  isofhlevel 3 A -> cp (b1:=b1) (b2:=b2) α = cp (b1:=b1) (b2:=b2) β.
Proof.
  intros ih. apply (maponpaths (λ α, cp α)). apply ih.
Defined.

Local Goal ∏ (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p q:a1=a2) (α : p=q)
      (r : PathOver b1 b2 p) (s : PathOver b1 b2 q),
  (cp α r = s) = (PathOver r s α).
Proof.
  reflexivity.
Defined.

Definition inverse_cp_p
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q) (t : PathOver b1 b2 p) :
  cp (! α) (cp α t) = t.
Proof.
  now induction α.
Defined.

Definition inverse_cp_p'
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q)
           (t : PathOver b1 b2 p) (u : PathOver b1 b2 q) :
  PathOver t u α -> PathOver u t (!α).
Proof.
  exact inversePathOver.
Defined.

Definition inverse_cp_p''
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q)
           (t : PathOver b1 b2 p) (u : PathOver b1 b2 q) :
  PathOver t u α -> PathOver u t (!α).
Proof.
  intros k. induction k. exact (inverse_cp_p α t).
Defined.

Lemma inverse_cp_p_compare
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q)
           (t : PathOver b1 b2 p) (u : PathOver b1 b2 q)
           (k : PathOver t u α) :
  inverse_cp_p' k = inverse_cp_p'' k.
Proof.
  induction α. reflexivity.
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
  q * q^-1 = cp (!pathsinv0r p) (identityPathOver y).
Proof.
  now induction p, q.
Defined.

Definition composePathOverLeftInverse {X:Type} {x x':X} {Y : X -> Type}
           {y : Y x} {y' : Y x'} {p:x=x'} (q : PathOver y y' p) :
  q^-1 * q = cp (!pathsinv0l p) (identityPathOver y').
Proof.
  now induction p, q.
Defined.

(** Statement of circle induction *)

Definition CircleRecursion (circle : Type) (pt : circle) (loop : pt = pt) :=
  ∏ (X:Type) (x:X) (p:x=x),
    ∑ (f:circle -> X) (r : f pt = x), maponpaths f loop = r @ p @ !r.

Arguments CircleRecursion : clear implicits.

Definition CircleInduction (circle : Type) (pt : circle) (loop : pt = pt) :=
  ∏ (X:circle->Type) (x:X pt) (p:PathOver x x loop),
    ∑ (f:∏ t:circle, X t) (r : f pt = x), apd f loop = r ⟤ p ⟥ !r.

Arguments CircleInduction : clear implicits.

Goal ∏ (C : Type) (pt : C) (loop : pt = pt),
     CircleInduction C pt loop -> CircleRecursion C pt loop.
Proof.
  intros ? ? ? ci ? ? ?.
  assert (q := ci (λ c, X) x (PathOver_inConstantFamily loop p)); cbn beta in q.
  induction q as [F [R E]].
  exists F.
  exists R.
Abort.

(* In a well behaved circle, the witness r above to the equality [f pt = r] would be reflexivity,
   but we can't state that. *)

(** now start the formalization, following Marc and Ulrik *)

Lemma cp_pathscomp0               (* 0.2.5 *)
      (A:Type) (B:A->Type) (a1 a2:A)
      (b1:B a1) (b2:B a2) (p q r:a1=a2) (α : p=q) (β : q=r)
      (s : PathOver b1 b2 p) :
  cp (b1:=b1) (b2:=b2) (α @ β) s = cp β (cp α s).
Proof.
  now induction α.
Defined.

Definition apstar               (* 0.2.7 *)
           (A:Type) (a1 a2 a3:A) (p p':a1=a2) (q q':a2=a3) :
  p=p' -> q=q' -> p @ q = p' @ q'.
Proof.
  intros α β. induction α, p. exact β.
Defined.

(* ===
Definition apstar_idpath
           (A:Type) (a1 a2 a3:A) (p:a1=a2) (q q':a2=a3) (β:q=q') :
  apstar (idpath p) β = β.
*)

Definition Lemma_0_2_8          (* 0.2.8 *)
      (A:Type) (B:A->Type) (a1 a2 a3:A)
      (p p':a1=a2) (q q':a2=a3) (α : p=p') (β : q=q')
      (b1:B a1) (b2:B a2) (b3:B a3)
      (pp : PathOver b1 b2 p) (qq : PathOver b2 b3 q) :
  cp (apstar α β) (pp * qq) = cp α pp * cp β qq.
Proof.
  now induction p, α, β.
Defined.

Definition Lemma_0_2_8'
      (A:Type) (B:A->Type) (a1 a2:A)
      (p:a2=a1) (p':a1=a2) (α : !p=p')
      (b1:B a1) (b2:B a2)
      (pp : PathOver (Y:=B) b2 b1 p) :
  cp α (pp^-1) = inversePathOver' (cp (invrot α) pp).
Proof.
  now induction α, p.
Defined.

Definition Lemma031_weq (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) :
  (∑ (h:∏ z, P z), ∏ z, h(1+z) = f z (h z)) ≃ P 0
  := ℤBiRecursion_weq f.

Definition Lemma031 (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) :
  isweq ((λ hq, pr1 hq 0) : (∑ (h:∏ z, P z), ∏ z, h(1+z) = f z (h z)) -> P 0)
  := pr2 (Lemma031_weq f).

Definition Lemma031_inverse (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) :
  P 0 -> ∑ (h:∏ z, P z), ∏ z, h(1+z) = f z (h z)
  := invmap (Lemma031_weq f).

Delimit Scope circle with circle.
Local Open Scope circle.
Notation "f ^ z" := (λ p, pr1 (Lemma031_inverse f p) z) : circle.

Definition Lemma031_compute_zero (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) (p:P 0) :
  (f^0) p = p
  := ℤBiRecursion_inv_compute f p.

Definition Lemma031_compute_next (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) (p:P 0) (z:ℤ) :
  (f^(1+z)) p = f z ((f^z) p)
  := ℤBiRecursion_transition_inv f p z.

Definition Lemma031_compute_prev (P:ℤ→Type) (f : ∏ z, P z ≃ P (1+z)) (p:P 0) (z:ℤ) :
  (f^z) p = invmap (f z) ((f^(1+z)) p)
  := ℤBiRecursion_transition_inv_reversed f p z.

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
  change ((invmap torsor_univalence (trivialTorsorRightMultiplication ℤ one)) @ s x = s (1 + x)).
  refine (invUnivalenceCompose _ _ @ _). unfold s. apply maponpaths.
  apply underlyingIso_injectivity, pr1weq_injectivity, funextsec; intros n.
  change (((n + 1)%abgr + x) = (n + (1 + x))). apply ac_assoc.
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
  cp α v = cp β v.
Proof.
  exact (maponpaths (λ f, pr1weq f v) (cp_irrelevance_circle b1 b2 α β)).
Defined.

Definition cp_irrelevance_circle_1
           (A:=circle) (B:circle->Type) (a1 a2:A) (b1:B a1) (b2:B a2) (p:a1=a2) (α: p=p) :
  cp (b1:=b1) (b2:=b2) α = cp (b1:=b1) (b2:=b2) (idpath p).
Proof.
  apply cp_irrelevance_circle.
Defined.

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

  Definition elem (X:Torsor ℤ) : Type := X.

  Definition ε' (X Y : Torsor ℤ) (e : X = Y) (x : X) :
    ! s x @ s (transportf elem e x) = e.
  Proof.                        (* 0.5.10 *)
    induction e. apply pathsinv0l.
  Defined.

  Context (p : PathOver a a loop).

  Definition Lemma_0_5_11 (X Y : Torsor ℤ) (e : X = Y) (x : X) : (* 0.5.11 *)
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

  Lemma c_compute_1 : c p pt = transportf A (s pt_0) a.
  Proof.
    reflexivity.
  Qed.

  Lemma c_compute_1' : c p pt = a.
  Proof.
    (* not judgemental *)
    change (transportf _ (s pt_0) a = transportf _ (idpath _) a).
    apply (maponpaths (λ p, transportf A p a)).
    apply s_compute_0.
  Defined.

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

End A.

Arguments c_tilde {_ _} _ _ _.
Arguments c_hat {_ _} _ _ _.

Axiom cheat : ∏ X, X.

Theorem circle_induction : CircleInduction circle pt loop.
Proof.
  unfold CircleInduction.
  intros A a p.
  set (f := c p).
  exists f.
  set (h := c_tilde p pt); fold f in h.
  set (e := ! cp s_compute_0 (h 0)).
  exists e.
  assert (q := c_hat p pt); fold h in q.
  set (s0 := s pt_0). unfold pt_0 in s0.
  set (s1 := s pt_1). unfold pt_1 in s1.
  set (one' := transportf elem loop pt_0). fold pt in one'.
  assert (r := Lemma_0_5_11 p loop pt_0). fold pt h f one' in r; unfold pt_0 in r.
  refine (r @ _); clear r.

  assert (ss : one' = pt_1). (* needed for r? *)
  { change (
        transportf elem
                   (invmap torsor_univalence (trivialTorsorRightMultiplication ℤ 1))
                   pt_0
        = 1 + pt_0).
    now rewrite castTorsor_transportf, torsor_univalence_inv_comp_eval. }
  unfold pt_1 in ss.
  set (s0sm := λ m:trivialTorsor ℤ, ! s0 @ s m).
  assert (b :
            cp (ε' loop 0) ((h 0)^-1 * h one') =
            cp (ε'' 0) ((h 0)^-1 * h (1 + pt_0))
         ).
  { intermediate_path (cp (ε'' 0) (cp (maponpaths s0sm ss) ((h 0)^-1 * h one'))).
    - intermediate_path (cp (maponpaths s0sm ss @ ε'' 0) ((h 0)^-1 * h one')).
      + apply cp_irrelevance_circle_value.
      + apply cp_pathscomp0.
    - apply maponpaths.
      exact (cp_in_family _ (λ m, (h 0) ^-1 * h m)). }
  refine (b @ _); clear b.
  unfold pt_0. rewrite (q 0). clear q.
  set (h0 := h 0).

  set (α0 := invrot' (s_compute_0 : s pt_0 = ! idpath _)).
  set (ε0 := ε pt_0).
  transparent assert (α : (!s0 @ s1 = idpath pt @ (loop @ s0))).
  { exact (apstar α0 (!ε0)). }
  transparent assert (β : (idpath pt @ (loop @ s0) = idpath pt @ (loop @ idpath pt))).
  { exact (apstar (idpath _) (apstar (idpath loop) s_compute_0)). }
  transparent assert (γ : (idpath pt @ (loop @ idpath pt) = idpath pt @ loop)).
  { exact (apstar (idpath _) (pathscomp0rid _)). }
  intermediate_path (cp (α@β@γ) ((h 0) ^-1 * cp ε0 (p * h 0))).
  { apply cp_irrelevance_circle_value. }
  fold h0.
  rewrite cp_pathscomp0.
  unfold α. rewrite Lemma_0_2_8.
  rewrite inverse_cp_p.
  set (Q := invrot (p:=s0) α0); change (!idpath pt) with (idpath pt) in Q.
  rewrite cp_pathscomp0.
  unfold β. rewrite Lemma_0_2_8.
  rewrite cp_idpath.
  unfold γ. rewrite Lemma_0_2_8.
  rewrite cp_idpath.
  rewrite Lemma_0_2_8.
  change (cp (idpath loop) p) with p.
  rewrite composePathOverPath_compute, composePathPathOver_compute.
  set (rid := pathscomp0rid).
  intermediate_path (cp (rid loop) (cp α0 (h0 ^-1) * p * cp s_compute_0 h0)).
  { rewrite cp_left. apply maponpaths.
    exact (assocPathOver (cp α0 (h0 ^-1)) p (cp s_compute_0 h0)). }
  apply (maponpaths (cp (rid loop))).
  rewrite Lemma_0_2_8'; fold s0.
  unfold α0.
  intermediate_path (∇ e * p * cp s_compute_0 h0).
  - apply (maponpaths (λ e, ∇ e * p * cp s_compute_0 h0)).
    rewrite invrotrot'.
    reflexivity.
  - apply maponpaths.
    unfold e.
    unfold h0.
    apply pathsinv0.
    apply pathsinv0inv0.
Defined.