(**

  In this file we formalize the approach of Marc Bezem and Ulrik Buchholtz for proving that the type
  of Z-torsors has the induction principle that the circle should have.  In my older approach, (see
  the file Circle.v), I managed to show only the recursion principle for the circle (where the
  family of types is constant), and the computations were complicated and onerous.  Their approach
  follows the same basic idea, but is simpler.  It is currently described in the file
  https://github.com/UniMath/SymmetryBook/blob/master/ZTors.tex, commit
  1ba615fa7625516ad79fe3ad9ef68e1fc001d485.

  *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Ktheory.Equivalences.
Require Import UniMath.Ktheory.AffineLine. (* to get bidirectional recursion over the integers *)

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

Corollary uniqueFiller {X:Type} {x y z : X} {p : x = z} {q : y = z} :
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

Corollary isweqpathscomp0r {X : UU} (x : X) {x' x'' : X} (e' : x' = x'') :
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
  use (transportPathTotal _ _ _ _ t).
  apply pathsinv0.
  apply fillerEquation.
Defined.

(** First some simple facts about paths over paths *)

Definition PathOver {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :=
  transportf Y p y = y'.

Definition PathOverToPathPair {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :
  PathOver y y' p → PathPair (x,,y) (x',,y').
Proof.
  intros q. exact (p,,q).
Defined.

Definition PathOverToTotalPath {X:Type} {x x':X} {Y : X -> Type} (y : Y x) (y' : Y x') (p:x=x') :
  PathOver y y' p → (x,,y) = (x',,y').
Proof.
  intros q.
  exact (invmap (total2_paths_equiv  Y (x,, y) (x',, y'))
                (PathOverToPathPair y y' p q)).
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
