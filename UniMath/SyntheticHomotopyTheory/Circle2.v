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

Set Implicit Arguments.
Unset Strict Implicit.

Module Upstream.

Lemma iscontrcoconustot (T : UU) (t : T) : iscontr (coconustot T t).
Proof.
  (* move upstream, much simpler *)
  (* rename connectedcoconustot *)
  use (tpair _ (t,, idpath t)).
  now intros [u []].
Defined.

Lemma iscontrcoconusfromt (T : UU) (t : T) : iscontr (coconusfromt T t).
Proof.
  (* move upstream, much simpler *)
  (* rename connectedcoconusfromt *)
  use (tpair _ (t,, idpath t)).
  now intros [u []].
Defined.

Corollary isweqpathsinv0 {X : Type} (x y : X) : isweq (@pathsinv0 X x y).
  (* move upstream, much simpler *)
  (* make a direct proof of isweqpathsinv0, without using isweq_iso *)
Proof.
  intros.
  intros p.
  use tpair.
  - exists (!p). apply pathsinv0inv0.
  - cbn. intros [q k]. now induction q,k.
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

(** First some simple facts about paths over paths *)

Definition PathOver {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :=
  transportf Y p y = y'.

Definition PathOverToPathPair {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :
  PathOver y y' p → PathPair (x,,y) (x',,y').
Proof.
  intros q. exact (p,,q).
Defined.

Definition applySectionToPath {X:Type} {Y : X -> Type} (s : ∏ x, Y x) {x x':X} (p : x = x') :
  PathOver (s x) (s x') p.
Proof.
  induction p.
  exact (idpath (s x)).
Defined.

Definition PathOverToTotalPath {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :
  PathOver y y' p → (x,,y) = (x',,y').
Proof.
  intros q.
  exact (invmap (total2_paths_equiv  Y (x,, y) (x',, y'))
                (PathOverToPathPair q)).
Defined.

Definition stdPathOver {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (p:x=x')
  : PathOver y (transportf Y p y) p
  := idpath (transportf Y p y).

Definition stdPathOver' {X:Type} {x x':X} {Y : X -> Type} (y' : Y x') (p:x=x')
  : PathOver (transportb Y p y') y' p.
Proof.
  now induction p.
Defined.

Definition reflPathOver {X:Type} {x:X} {Y : X -> Type} (y : Y x) : PathOver y y (idpath x)
  := idpath y.

Definition inductionPathOver {X:Type} {x:X} {Y : X -> Type} (y : Y x)
           (T : ∏ x' (y' : Y x') (p : x = x'), PathOver y y' p → Type)
           (t : T x y (idpath x) (reflPathOver y)) :
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

Definition composePathOverLeftUnit {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') (q:PathOver y y' p) :
  composePathOver (reflPathOver y) q = q.
Proof.
  now induction p.
Defined.

Definition composePathOverRightUnit {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') (q:PathOver y y' p) :
  composePathOver q (reflPathOver y') = transportb (PathOver y y') (pathscomp0rid _) q.
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

Require Import UniMath.SyntheticHomotopyTheory.AffineLine.
Require Import UniMath.NumberSystems.Integers.
Local Open Scope hz.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Groups.

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

Definition s {Z : Torsor ℤ} (x : Z) : pt = Z.
(* Def 0.5.6 *)
Proof.
  change (trivialTorsor ℤ = Z).
  apply (invmap torsor_univalence).
  now apply triviality_isomorphism.
Defined.

Lemma s_compute : @s (trivialTorsor ℤ) 0 = idpath _.
Proof.
  intermediate_path (invmap torsor_univalence (idActionIso (trivialTorsor ℤ))).
  - change (@s (trivialTorsor ℤ) 0) with (invmap torsor_univalence (triviality_isomorphism (trivialTorsor ℤ) 0)).
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

Section A.

  Context (A : circle -> Type) (a : A pt).

  Definition Q (p : PathOver a a loop) (X: Torsor ℤ) : Type                 (* 0.5.8 *)
    := ∑ (a' : A X),
       ∑ (h : ∏ (x:X), PathOver a a' (s x)),
       ∏ (x:X),
         h (1 + x) = (cp (ε x) (composePathOver p (h x))).

  Lemma iscontr_Q (p : PathOver a a loop) (X: Torsor ℤ) (* 0.5.9 *) :
    iscontr_hProp (Q p X).
  Proof.
    use (predicateOnConnectedType (Torsor ℤ) (isconnBG ℤ) (λ X, iscontr_hProp (Q p X)) pt);
      clear X.
    cbn beta.
    use (iscontrweqb (Y := ∑ a', PathOver a a' (idpath pt))).
    2 : { apply iscontrcoconusfromt. }
    apply weqfibtototal; intros a'.
    intermediate_weq (PathOver a a' (@s pt 0)).
    2 : { apply eqweqmap. apply maponpaths. apply s_compute. }
    set (P := λ x : ℤ, PathOver a a' (@s pt x)).
    (* this change saves 1 second in the Qed below: *)
    change ((∑ h : ∏ x : trivialTorsor ℤ, P x,
               ∏ x : trivialTorsor ℤ,
                 h (1 + x) =
                 cp (ε x) (composePathOver_weq (B:=A) (b1:=a) (b2:=a) a' (p1:=loop) (s x) p (h x)))
             ≃ P 0).
    intermediate_weq (
        ∑ h : ∏ x : trivialTorsor ℤ, P x,
                      ∏ x : trivialTorsor ℤ,
                            h (1 + x)
                            =
                            weqcomp
                              (composePathOver_weq (B:=A) (b1:=a) (b2:=a) a' (p1:=loop) (s x) p)
                              (cp (ε x))
                              (h x)).
    * now apply eqweqmap.
    * change (ac_set (underlyingAction (trivialTorsor ℤ)))
        with (pr1setwithbinop (pr1monoid (grtomonoid (abgrtogr ℤ)))).
      Time apply ℤBiRecursion_weq. (* 6.7 seconds *)
  Time Qed.                          (* 14 seconds *)

End A.
