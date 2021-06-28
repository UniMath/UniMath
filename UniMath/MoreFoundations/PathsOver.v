(** This file contains the definition of paths over a path, together with some
    facts about them developed by Marc Bezem and Ulrik Buchholtz. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

(** ** Paths over paths in families of types *)

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Declare Scope pathsover.
Delimit Scope pathsover with pathsover.
Local Open Scope pathsover.

(** A path in a family of types "over" a path in the base *)
Definition PathOver {X:Type}
           {x x':X} (p:x=x')
           {Y : X -> Type} (y : Y x) (y' : Y x') : Type.
Proof.
  induction p. exact (y=y').
Defined.

(** Paths-over versus path pairs *)
Definition PathOverToPathPair {X:Type} {x x':X} (p:x=x') {Y : X -> Type} (y : Y x) (y' : Y x') :
  PathOver p y y' → PathPair (x,,y) (x',,y').
Proof.
  intros q. induction p. exists (idpath x). cbn. exact q.
Defined.

Definition apd {X:Type} {Y : X -> Type} (s : ∏ x, Y x) {x x':X} (p : x = x') :
  PathOver p (s x) (s x').
Proof.
  now induction p.
Defined.

Definition PathOverToTotalPath {X:Type}
           {x x':X} (p:x=x')
           {Y : X -> Type} (y : Y x) (y' : Y x') :
  PathOver p y y' → (x,,y) = (x',,y').
Proof.
  intros q.
  exact (invmap (total2_paths_equiv  Y (x,, y) (x',, y')) (PathOverToPathPair q)).
Defined.

Lemma PathOverUniqueness  {X:Type} {x x':X} (p:x=x') {Y : X -> Type} (y : Y x) :
  ∃! (y' : Y x'), PathOver p y y'.
Proof.
  induction p. apply iscontrcoconusfromt.
Defined.

Definition stdPathOver {X:Type} {x x':X} (p:x=x') {Y : X -> Type} (y : Y x)
  : PathOver p y (transportf Y p y).
Proof.
  now induction p.
Defined.

Definition stdPathOver' {X:Type} {x x':X} (p:x=x') {Y : X -> Type} (y' : Y x')
  : PathOver p (transportb Y p y') y'.
Proof.
  now induction p.
Defined.

Definition identityPathOver {X:Type} {x:X} {Y : X -> Type} (y : Y x)
  : PathOver (idpath x) y y
  := idpath y.

Definition pathOverIdpath {X:Type} {x:X} {Y : X -> Type} (y y' : Y x)
  : PathOver (idpath x) y y' = (y = y')
  := idpath _.

Definition toPathOverIdpath {X:Type} {x:X} {Y : X -> Type} (y y' : Y x)
  : y = y' -> PathOver (idpath x) y y'
  := idfun _.

Local Notation "'∇' q" := (toPathOverIdpath q) (at level 10) : pathsover.

Definition fromPathOverIdpath {X:Type} {x:X} {Y : X -> Type} (y y' : Y x) : PathOver (idpath x) y y' -> y = y'
  := idfun _.

Local Notation "'Δ' q" := (fromPathOverIdpath q) (at level 10) : pathsover.

Definition inductionPathOver {X:Type} {x:X} {Y : X -> Type} (y : Y x)
           (T : ∏ x' (p : x = x') (y' : Y x'), PathOver p y y' → Type)
           (t : T x (idpath x) y (identityPathOver y)) :
  ∏ x' (y' : Y x') (p : x = x') (q : PathOver p y y'), T x' p y' q.
Proof.
  intros. induction p, q. exact t.
Defined.

Definition transportPathOver {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x')
           (q : PathOver p y y')
           (T : ∏ (a:X) (b:Y a), Type) : T x y → T x' y'.
Proof.
  now induction p, q.
Defined.

Definition transportPathOver' {X:Type} {x x':X} (p:x=x') {Y : X -> Type} (y : Y x) (y' : Y x')
           (q : PathOver p y y')
           (T : ∏ (a:X) (b:Y a), Type) : T x' y' → T x y.
Proof.
  now induction p, q.
Defined.

Definition composePathOver {X:Type}
           {x x' x'':X} {p:x=x'} {p':x'=x''}
           {Y : X -> Type} {y : Y x} {y' : Y x'} {y'' : Y x''}
  : PathOver p y y' → PathOver p' y' y'' → PathOver (p @ p') y y''.
Proof.
  induction p, p'. exact pathscomp0.
Defined.

Local Notation "x * y" := (composePathOver x y) : pathsover.

Definition composePathOverPath {X:Type}
           {x x':X} {p:x=x'}
           {Y : X -> Type} {y : Y x} {y' y'' : Y x'}
  : PathOver p y y' → y' = y'' → PathOver p y y''.
Proof.
  intros q e. now induction e.
Defined.

Local Notation "q ⟥ e" := (composePathOverPath q e) (at level 56, left associativity) : pathsover.

Definition composePathOverIdpath {X:Type}
           {x x':X} {p:x=x'}
           {Y : X -> Type} {y : Y x} {y': Y x'}
           (q : PathOver p y y')
  : q ⟥ idpath y' = q.
Proof.
  reflexivity.
Defined.

Definition composePathPathOver {X:Type}
           {x' x'':X} {p:x'=x''}
           {Y : X -> Type} {y y': Y x'} {y'' : Y x''}
  : y = y' → PathOver p y' y'' → PathOver p y y''.
Proof.
  intros e q. now induction e.
Defined.

Local Notation "e ⟤ q" := (composePathPathOver e q) (at level 56, left associativity) : pathsover.

Lemma composeIdpathPathOver {X:Type}
      {x' x'':X} {p:x'=x''}
      {Y : X -> Type} {y': Y x'} {y'' : Y x''}
      (q : PathOver p y' y'')
  : idpath y' ⟤ q = q.
Proof.
  reflexivity.
Defined.

Lemma composePathPathOverRotate {X:Type}
      {x' x'':X} {p:x'=x''}
      {Y : X -> Type} {y y': Y x'} (q : y = y') {y'' : Y x''}
      (r : PathOver p y' y'') (s : PathOver p y y'')
  : q ⟤ r = s <-> r = (!q) ⟤ s.
Proof.
  induction q. simpl. apply isrefl_logeq.
Defined.

Lemma composePathOverPathRotate {X:Type}
      {x x':X} {p:x=x'}
      {Y : X -> Type} {y : Y x} {y' y'': Y x'}
      (r : PathOver p y y') (q : y' = y'') (s : PathOver p y y'')
  : r ⟥ q = s <-> r = s ⟥ (!q).
Proof.
  induction q. simpl. apply isrefl_logeq.
Defined.

Lemma composePathPathOverPath {X:Type}
      {x x':X} {p:x=x'}
      {Y : X -> Type} {y y' : Y x} {y'' y''': Y x'} (q : y = y') (r : PathOver p y' y'') (s : y'' = y''')
  : q ⟤ (r ⟥ s) = (q ⟤ r) ⟥ s.
Proof.
  now induction q.
Defined.

Definition composePathOverLeftUnit {X:Type}
           {x x':X} (p:x=x')
           {Y : X -> Type} (y : Y x) (y' : Y x') (q:PathOver p y y') :
  identityPathOver y * q = q.
Proof.
  now induction p.
Defined.

Definition composePathOverRightUnit {X:Type}
           {x x':X} (p:x=x')
           {Y : X -> Type} (y : Y x) (y' : Y x') (q:PathOver p y y') :
  q * identityPathOver y' = transportb (λ p, PathOver p y y') (pathscomp0rid _) q.
Proof.
  now induction p, q.
Defined.

Definition assocPathOver {X:Type}
           {x x' x'' x''':X} {p:x=x'} {p':x'=x''} {p'':x''=x'''}
           {Y : X -> Type} {y : Y x} {y' : Y x'} {y'' : Y x''} {y''' : Y x'''}
           (q : PathOver p y y') (q' : PathOver p' y' y'') (q'' : PathOver p'' y'' y''') :
  transportf (λ ppp, PathOver ppp y y''') (path_assoc p p' p'') (q * (q' * q''))
  =
  (q * q') * q''.
Proof.
  induction p, p', p'', q, q', q''. reflexivity.
Defined.

Definition inversePathOver {X:Type}
           {x x':X} {p:x=x'}
           {Y : X -> Type} {y : Y x} {y' : Y x'}
  : PathOver p y y' → PathOver (!p) y' y.
Proof.
  intros q. induction p, q. reflexivity.
Defined.

Definition inversePathOver' {X:Type}
           {x x':X} {p:x'=x}
           {Y : X -> Type} {y : Y x} {y' : Y x'}
  : PathOver (!p) y y' → PathOver p y' y.
Proof.
  intros q. induction p, q. reflexivity.
Defined.

Definition inverseInversePathOver1 {X:Type}
           {x x':X} {p:x=x'}
           {Y : X -> Type} {y : Y x} {y' : Y x'}
           (s : PathOver p y y')
  : inversePathOver' (inversePathOver s) = s.
Proof.
  induction p, s. reflexivity.
Defined.

Definition inverseInversePathOver2 {X:Type}
           {x x':X} {p:x'=x}
           {Y : X -> Type} {y : Y x} {y' : Y x'}
           (s : PathOver (!p) y y')
  : inversePathOver (inversePathOver' s) = s.
Proof.
  induction p, s. reflexivity.
Defined.

Local Notation "q '^-1'" := (inversePathOver q) : pathsover.

Definition inversePathOverIdpath {X:Type} {x:X} {Y : X -> Type} (y y' : Y x) (e : y = y') :
  inversePathOver (∇ e) = ∇ (!e).
Proof.
  reflexivity.
Defined.

Definition inversePathOverIdpath' {X:Type} {x:X} {Y : X -> Type} (y y' : Y x) (e : y = y') :
  inversePathOver' (∇ e : PathOver (! idpath x) y y') = ∇ (!e).
Proof.
  reflexivity.
Defined.

Definition inverseInversePathOver {X:Type} {Y : X -> Type} {x:X} {y : Y x} :
  ∏ {x':X} {y' : Y x'} {p:x=x'} (q : PathOver p y y'),
  transportf (λ pp, PathOver pp y y') (pathsinv0inv0 p) (q^-1^-1) = q.
Proof.
  now use inductionPathOver.
Defined.

Definition inversePathOverWeq {X:Type}
           {x x':X} {p:x=x'}
           {Y : X -> Type} {y : Y x} {y' : Y x'}
  : PathOver p y y' ≃ PathOver (!p) y' y.
Proof.
  (* compare with weqpathsinv0 *)
  exists inversePathOver. intros s. use tpair.
  - exists (inversePathOver' s). apply inverseInversePathOver2.
  - cbn. induction p. intros [t []]. induction t. reflexivity.
Defined.

Lemma inversePathOverWeq' {X:Type}
           {x x':X} {p:x'=x}
           {Y : X -> Type} {y : Y x} {y' : Y x'}
  : PathOver (!p) y y' ≃ PathOver p y' y.
Proof.
  (* compare with weqpathsinv0 *)
  exists inversePathOver'. intros s. use tpair.
  - exists (inversePathOver s). apply inverseInversePathOver1.
  - cbn. induction p. intros [t []]. induction t. reflexivity.
Defined.

(** Paths-over in a constant family *)

Definition PathOverConstant_id {X:Type} {x x':X} (p:x=x') {Z : Type} (z : Z) (z' : Z)
  : (z = z') = (PathOver p z z').
Proof.
  now induction p.
Defined.

Definition PathOverConstant_map1 {X:Type} {x x':X} (p:x=x') {Z : Type} {z z' : Z}
  : z = z' -> PathOver p z z'.
Proof.
  now induction p.
Defined.

Definition PathOverConstant_map1_eq1 {X:Type}
           {x x':X} (p:x=x')
           {Z : Type} {z z' z'' : Z}
           (q: z = z') (r : z' = z'')
  : PathOverConstant_map1 p (q @ r) = PathOverConstant_map1 p q ⟥ r.
Proof.
  now induction r, q.
Defined.

Definition PathOverConstant_map1_eq2 {X:Type}
           {x x':X} (p:x=x')
           {Z : Type} {z z' z'' : Z}
           (q: z = z') (r : z' = z'')
  : PathOverConstant_map1 p (q @ r) = q ⟤ PathOverConstant_map1 p r.
Proof.
  now induction r, q.
Defined.

Definition PathOverConstant_map2 {X:Type}
           {x x':X} {p:x=x'}
           {Z : Type} {z z' : Z}
  : PathOver p z z' -> z = z'.
Proof.
  now induction p.
Defined.

Definition PathOverConstant_map2_apd {X:Type}
           {x x':X} {p:x=x'}
           {Z : Type} {f : X -> Z}
  : PathOverConstant_map2 (apd f p) = maponpaths f p.
Proof.
  now induction p.
Defined.

Definition PathOverConstant_map2_eq1 {X:Type}
           {x x':X} {p:x=x'}
           {Z : Type} {z z' z'' : Z}
           (q: PathOver p z z') (r : z' = z'')
  : PathOverConstant_map2 (q ⟥ r) = PathOverConstant_map2 q @ r.
Proof.
  induction r. change (q ⟥ idpath z') with q. apply pathsinv0, pathscomp0rid.
Defined.

Definition PathOverConstant_map2_eq2 {X:Type}
           {x x':X} (p:x=x')
           {Z : Type} {z z' z'' : Z}
           (r : z = z') (q: PathOver p z' z'')
  : PathOverConstant_map2 (r ⟤ q) = r @ PathOverConstant_map2 q.
Proof.
  now induction r.
Defined.

Lemma PathOverConstant_map1_map2 {X:Type}
      {x x':X} (p:x=x')
      {Z : Type} {z z' : Z} (q : z = z')
  : PathOverConstant_map2 (PathOverConstant_map1 p q) = q.
Proof.
  now induction p.
Defined.

(** lemmas *)

Lemma Lemma023 (A:Type) (B:A->Type) (a1 a2 a3:A)
      (b1:B a1) (b2:B a2) (b3:B a3)
      (p1:a1=a2) (p2:a2=a3)
      (q:PathOver p1 b1 b2) :
  isweq (composePathOver q : PathOver p2 b2 b3 -> PathOver (p1@p2) b1 b3).
Proof.
  induction p1, p2, q. apply idisweq.
Defined.

Definition composePathOver_weq (A:Type) (a1 a2 a3:A) (B:A->Type)
      (b1:B a1) (b2:B a2) (b3:B a3)
      (p1:a1=a2) (p2:a2=a3)
      (q:PathOver p1 b1 b2)
  : PathOver p2 b2 b3 ≃ PathOver (p1@p2) b1 b3
  := make_weq (composePathOver q) (Lemma023 _).

Lemma Lemma0_2_4 (A:Type) (B:A->Type) (a1 a2:A)
      (b1:B a1) (b2:B a2) (p q:a1=a2) (α : p=q) :
  isweq ((transportf (λ pp, PathOver pp b1 b2) α) : PathOver p b1 b2 -> PathOver q b1 b2).
Proof.
  induction α. apply idisweq.
Defined.

Definition cp                   (* "change path" *)
           (A:Type) (a1 a2:A) (p q:a1=a2) (α : p=q)
           (B:A->Type) (b1:B a1) (b2:B a2) :
  PathOver p b1 b2 ≃ PathOver q b1 b2
  := make_weq (transportf (λ pq, PathOver pq b1 b2) α) (Lemma0_2_4 α).

Arguments cp {_ _ _ _ _} _ {_ _ _}.

Definition composePathOverPath_compute {X:Type}
           {x x':X} {p:x=x'}
           {Y : X -> Type} {y : Y x} {y' y'' : Y x'}
           (q : PathOver p y y') (e : y' = y'') :
  q ⟥ e = cp (pathscomp0rid p) (q * ∇ e).
Proof.
  now induction p, q, e.
Defined.

Definition composePathPathOver_compute {X:Type}
           {x' x'':X} {p:x'=x''}
           {Y : X -> Type} {y y': Y x'} {y'' : Y x''}
           (e : y = y') (q : PathOver p y' y'') :
  e ⟤ q = ∇ e * q.
Proof.
  now induction p.
Defined.

Definition cp_idpath
           (A:Type) (a1 a2:A) (p:a1=a2)
           (B:A->Type) (b1:B a1) (b2:B a2) (u:PathOver p b1 b2) :
  cp (idpath p) u = u.
Proof.
  reflexivity.
Defined.

Definition cp_left
           (A:Type) (a2 a3:A) (p p':a2=a3) (α:p=p')
           (B:A->Type) (b1 b2:B a2) (b3:B a3)
           (r:PathOver (idpath a2) b1 b2)
           (q:PathOver p b2 b3) :
  r * cp α q = cp α (r*q).
Proof.
  now induction r, α.
Defined.

Definition cp_right
           (A:Type) (a1 a2:A) (p p':a1=a2) (α:p=p')
           (B:A->Type) (b1:B a1) (b2 b3:B a2)
           (q:PathOver p b1 b2)
           (r:PathOver (idpath a2) b2 b3) :
  cp α q * r = cp (maponpaths (λ p, p @ idpath a2) α) (q*r).
Proof.
  now induction r, α.
Defined.

Definition cp_in_family
           (A:Type) (a1 a2:A)
           (T:Type) (t0 t1:T) (v:t0=t1) (p:T->a1=a2)
           (B:A->Type) (b1:B a1) (b2:B a2) (s : ∏ t, PathOver (p t) b1 b2) :
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
      (r : PathOver p b1 b2) (s : PathOver q b1 b2),
  (cp α r = s) = (PathOver (Y := λ pq, PathOver pq _ _) α r s).
Proof.
  intros. induction α, p. reflexivity.
Defined.

Definition inverse_cp_p
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q) (t : PathOver p b1 b2) :
  cp (! α) (cp α t) = t.
Proof.
  now induction α.
Defined.

Definition inverse_cp_p'
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q)
           (t : PathOver p b1 b2) (u : PathOver q b1 b2) :
  PathOver (Y := λ pq, PathOver pq _ _) α t u -> PathOver (Y := λ pq, PathOver pq _ _) (!α) u t.
Proof.
  exact inversePathOver.
Defined.

Definition inverse_cp_p''
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q)
           (t : PathOver p b1 b2) (u : PathOver q b1 b2) :
  PathOver (Y := λ pq, PathOver pq _ _) α t u -> PathOver (Y := λ pq, PathOver pq _ _) (!α) u t.
Proof.
  intros k. induction α, p, k. reflexivity.
Defined.

Lemma inverse_cp_p_compare
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q)
           (t : PathOver p b1 b2) (u : PathOver q b1 b2)
           (k : PathOver α t u) :
  inverse_cp_p' k = inverse_cp_p'' k.
Proof.
  induction α,p. reflexivity.
Defined.

Definition cp_inverse_cp
           (A:Type) (B:A->Type) (a1 a2:A) (b1:B a1) (b2:B a2)
           (p q:a1=a2) (α : p=q) (t : PathOver q b1 b2) :
  cp α (cp (! α) t) = t.
Proof.
  now induction α.
Defined.

Definition composePathOverRightInverse {X:Type} {x x':X} {Y : X -> Type}
           {y : Y x} {y' : Y x'} {p:x=x'} (q : PathOver p y y') :
  q * q^-1 = cp (!pathsinv0r p) (identityPathOver y).
Proof.
  now induction p, q.
Defined.

Definition composePathOverLeftInverse {X:Type} {x x':X} {Y : X -> Type}
           {y : Y x} {y' : Y x'} {p:x=x'} (q : PathOver p y y') :
  q^-1 * q = cp (!pathsinv0l p) (identityPathOver y').
Proof.
  now induction p, q.
Defined.

Lemma cp_pathscomp0
      (A:Type) (B:A->Type) (a1 a2:A)
      (b1:B a1) (b2:B a2) (p q r:a1=a2) (α : p=q) (β : q=r)
      (s : PathOver p b1 b2) :
  cp (b1:=b1) (b2:=b2) (α @ β) s = cp β (cp α s).
Proof.
  now induction α.
Defined.

(* a frequently-useful specialisation of [maponpaths_12] *)
Definition apstar               (* 0.2.7 *)
           (A:Type) (a1 a2 a3:A) (p p':a1=a2) (q q':a2=a3) :
  p=p' -> q=q' -> p @ q = p' @ q'.
Proof.
  intros; apply maponpaths_12; assumption.
Defined.

Definition cp_apstar
      (A:Type) (B:A->Type) (a1 a2 a3:A)
      (p p':a1=a2) (q q':a2=a3) (α : p=p') (β : q=q')
      (b1:B a1) (b2:B a2) (b3:B a3)
      (pp : PathOver p b1 b2) (qq : PathOver q b2 b3) :
  cp (apstar α β) (pp * qq) = cp α pp * cp β qq.
Proof.
  now induction p, α, β.
Defined.

Definition cp_apstar'
      (A:Type) (B:A->Type) (a1 a2:A)
      (p:a2=a1) (p':a1=a2) (α : !p=p')
      (b1:B a1) (b2:B a2)
      (pp : PathOver (Y:=B) p b2 b1) :
  cp α (pp^-1) = inversePathOver' (cp (invrot α) pp).
Proof.
  now induction α, p.
Defined.

(* what a path-over is in a family of equations *)
Lemma pathOverEquations {X Y:Type} {f g : X -> Y} {x x' : X} (e : f x = g x) (e' : f x' = g x') (p : x = x')
  : PathOver (Y := λ x, f x = g x) p e e' = ( e @ maponpaths g p = maponpaths f p @ e' ).
Proof.
  induction p. simpl. apply (maponpaths (λ r, r = e')). apply pathsinv0, pathscomp0rid.
Defined.

Lemma pathOverEquations1 {X:Type} {f : X -> X} {x x' : X} (e : f x = x) (e' : f x' = x') (p : x = x')
  : PathOver (Y := λ x, f x = x) p e e' = ( e @ p = maponpaths f p @ e' ).
Proof.
  induction p. simpl. apply (maponpaths (λ r, r = e')). apply pathsinv0, pathscomp0rid.
Defined.

(* functoriality *)
Definition mapPathOver {X:Type} {x x':X} (p:x=x')
           {Y Y': X -> Type} (f : ∏ x, Y x -> Y' x)
           (y : Y x) (y' : Y x')
  : PathOver p y y' -> PathOver p (f x y) (f x' y').
Proof.
  induction p. simpl. intros []. reflexivity.
Defined.

Definition binopPathOver {X:Type}
           {x x':X} (p:x=x')
           {Y Z W : X -> Type} (f : ∏ x, Y x -> Z x -> W x)
           (y : Y x) (y' : Y x')
           (z : Z x) (z' : Z x')
  : PathOver p y y' -> PathOver p z z' -> PathOver p (f x y z) (f x' y' z').
Proof.
  induction p. simpl. intros [] []. reflexivity.
Defined.

Local Unset Implicit Arguments.

Definition pullBackFamily {X X':Type} (g : X -> X') (Y : X' -> Type)
  := λ x, Y (g x).

Definition pullBackSection {X X':Type} (g : X -> X') {Y : X' -> Type} (f : ∏ x', Y x')
  := λ x, f (g x).

Definition pullBackPointOver {X X':Type} (g : X -> X')
           {x:X} {x':X'} (r : g x = x')
           {Y : X' -> Type} (y : Y x')
  : (pullBackFamily g Y) (x).
Proof.
  induction r. exact y.
Defined.

Definition pullBackPointOverWithSection {X X':Type} (g : X -> X')
           {x:X} {x':X'} (r : g x = x') {Y : X' -> Type} (f : ∏ x', Y x')
  : pullBackPointOver g r (f x') = pullBackSection g f x.
Proof.
   induction r. reflexivity.
Defined.

Definition pullBackPointOverWithSection' (* redundant? *)
           {X X':Type} (g : X -> X')
           {x:X} {x':X'} (r : g x = x')
           {Y : X' -> Type} {y : Y x'}
           {f : ∏ x', Y x'} (k : y = f x')
  : pullBackPointOver g r y = pullBackSection g f x.
Proof.
  induction (!k), r. reflexivity.
Defined.

Definition pullBackPathOverPoint {X X':Type} (g : X -> X')
           {x:X} {x':X'} (r : g x = x')
           {Y : X' -> Type} {y y' : Y x'} (t : y = y')
  : pullBackPointOver g r y = pullBackPointOver g r y'.
Proof.
  apply maponpaths; assumption.
Defined.

Definition pullBackPathOver {X X':Type} (g : X -> X')
           {x1 x2:X} {x1' x2':X'} {r1 : g x1 = x1'} {r2 : g x2 = x2'}
           {s : x1 = x2} {s' : x1' = x2'}
           (r : r1 @ s' = maponpaths g s @ r2)
           {Y : X' -> Type}
           {y1 : Y x1'} {y2 : Y x2'}
           (q : PathOver s' y1 y2)
  : PathOver s (pullBackPointOver g r1 y1) (pullBackPointOver g r2 y2).
Proof.
  induction r1, r2. simpl in r; simpl.
  assert (k' : s' = maponpaths g s). { refine (r @ pathscomp0rid _). } clear r.
  induction (!k'); clear k'. induction s. simpl in q. simpl. exact q.
Defined.

Definition pullBackPathOverPath {X X':Type} (g : X -> X')
           {x1 x2:X} {x1' x2':X'} {r1 : g x1 = x1'} {r2 : g x2 = x2'}
           {s : x1 = x2} {s' : x1' = x2'}
           (r : r1 @ s' = maponpaths g s @ r2)
           {Y : X' -> Type}
           (y1 : Y x1') (y2 y3 : Y x2')
           (q : PathOver s' y1 y2)
           (t : y2 = y3)
  : pullBackPathOver g r (q ⟥ t) = pullBackPathOver g r q ⟥ pullBackPathOverPoint g r2 t.
Proof.
  induction t, r1, r2. reflexivity.
Defined.

Definition pullBackPathPathOver {X X':Type} (g : X -> X')
           {x1 x2:X} {x1' x2':X'} (r1 : g x1 = x1') (r2 : g x2 = x2')
           (s : x1 = x2) (s' : x1' = x2')
           (r : r1 @ s' = maponpaths g s @ r2)
           {Y : X' -> Type}
           (y0 y1 : Y x1') (y2 : Y x2')
           (q : PathOver s' y1 y2)
           (t : y0 = y1)
  : pullBackPathOver g r (t ⟤ q) = pullBackPathOverPoint g r1 t ⟤ pullBackPathOver g r q.
Proof.
  induction t, r1, r2. reflexivity.
Defined.





Module PathsOverNotations.
Notation "'Δ' q" := (fromPathOverIdpath q) (at level 10) : pathsover.
Notation "'∇' q" := (toPathOverIdpath q) (at level 10) : pathsover.
Notation "x * y" := (composePathOver x y) : pathsover.
Notation "q ⟥ e" := (composePathOverPath q e) (at level 56, left associativity) : pathsover.
Notation "e ⟤ q" := (composePathPathOver e q) (at level 56, left associativity) : pathsover.
Notation "q '^-1'" := (inversePathOver q) : pathsover.
End PathsOverNotations.
