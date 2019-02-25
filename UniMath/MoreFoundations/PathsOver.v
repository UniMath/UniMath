(** This file contains the definition of paths over a path, together with some
    facts about them developed by Marc Bezem and Ulrik Buchholtz. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

(** ** Paths over paths in families of types *)

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Delimit Scope pathsover with pathsover.
Local Open Scope pathsover.

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

Notation "'∇' q" := (toPathOverIdpath q) (at level 10) : pathsover.

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

Notation "x * y" := (composePathOver x y) : pathsover.

Definition composePathOverPath {X:Type} {x x':X} {Y : X -> Type} {y : Y x} {y' y'' : Y x'}
           {p:x=x'} : PathOver y y' p → y' = y'' → PathOver y y'' p.
Proof.
  intros q e. now induction e.
Defined.

Notation "q ⟥ e" := (composePathOverPath q e) (at level 56, left associativity) : pathsover.

Definition composePathPathOver {X:Type} {x' x'':X} {Y : X -> Type} {y y': Y x'} {y'' : Y x''}
           {p:x'=x''} : y = y' → PathOver y' y'' p → PathOver y y'' p.
Proof.
  intros e q. now induction e.
Defined.

Notation "e ⟤ q" := (composePathPathOver e q) (at level 56, left associativity) : pathsover.

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

Notation "q '^-1'" := (inversePathOver q) : pathsover.

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

Lemma cp_pathscomp0
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

Definition cp_apstar
      (A:Type) (B:A->Type) (a1 a2 a3:A)
      (p p':a1=a2) (q q':a2=a3) (α : p=p') (β : q=q')
      (b1:B a1) (b2:B a2) (b3:B a3)
      (pp : PathOver b1 b2 p) (qq : PathOver b2 b3 q) :
  cp (apstar α β) (pp * qq) = cp α pp * cp β qq.
Proof.
  now induction p, α, β.
Defined.

Definition cp_apstar'
      (A:Type) (B:A->Type) (a1 a2:A)
      (p:a2=a1) (p':a1=a2) (α : !p=p')
      (b1:B a1) (b2:B a2)
      (pp : PathOver (Y:=B) b2 b1 p) :
  cp α (pp^-1) = inversePathOver' (cp (invrot α) pp).
Proof.
  now induction α, p.
Defined.
