(** * Utilities concerning paths, hlevel, and logic *)

Require Export UniMath.Foundations.PartD.
Require Export UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Export UniMath.Ktheory.Tactics.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Notations.

(** ** Null homotopies, an aid for proving things about propositional truncation *)

Local Open Scope transport.

Definition nullHomotopyTo {X Y} (f:X->Y) (y:Y) := ∏ x:X, f x = y.
Definition NullHomotopyTo {X Y} (f:X->Y) := total2 (nullHomotopyTo f).
Definition NullHomotopyTo_center {X Y} (f:X->Y) : NullHomotopyTo f -> Y := pr1.
Definition NullHomotopyTo_path {X Y} {f:X->Y} (r:NullHomotopyTo f) := pr2 r.

Definition nullHomotopyFrom {X Y} (f:X->Y) (y:Y) := ∏ x:X, y = f x.
Definition NullHomotopyFrom {X Y} (f:X->Y) := total2 (nullHomotopyFrom f).
Definition NullHomotopyFrom_center {X Y} (f:X->Y) : NullHomotopyFrom f -> Y := pr1.
Definition NullHomotopyFrom_path {X Y} {f:X->Y} (r:NullHomotopyFrom f) := pr2 r.

Definition nullHomotopyTo_transport {X Y} {f:X->Y} {y:Y} (h : nullHomotopyTo f y)
           {y':Y} (p:y = y') (x:X) : (p # h) x = h x @ p.
Proof.
  intros. induction p. apply pathsinv0. apply pathscomp0rid.
Defined.

Lemma isaset_NullHomotopyTo {X Y} (i:isaset Y) (f:X->Y) : isaset (NullHomotopyTo f).
Proof.
  intros. apply (isofhleveltotal2 2).
  { apply i. }
  intros y. apply impred; intros x. apply isasetaprop. apply i.
Defined.

Lemma isaprop_nullHomotopyTo {X Y} (is:isaset Y) (f:X->Y) (y:Y) :
  isaprop (nullHomotopyTo f y).
Proof.
  apply impred; intros x. apply is.
Defined.

Lemma isaprop_NullHomotopyTo {X} {Y} (is:isaset Y) (f:X->Y) :
  ∥ X ∥ -> isaprop (NullHomotopyTo f).
Proof.
  apply factor_through_squash.
  apply isapropisaprop.
  intros x. apply invproofirrelevance. intros [r i] [s j].
  apply subtypePairEquality.
  - intros n. apply (isaprop_nullHomotopyTo is).
  - exact (!i x @ j x).
Defined.

(** We can get a map from '∥ X ∥' to any type 'Y' provided paths
    are given that allow us to map first into a cone in 'Y'.  *)

Definition cone_squash_map {X Y} (f:X->Y) (y:Y) :
  nullHomotopyTo f y -> ∥ X ∥ -> Y.
Proof.
  intros e h. exact (point_from (h (paths_to_prop y) (λ x, f x,,e x))).
Defined.

Goal ∏ X Y (y:Y) (f:X->Y) (e:∏ m:X, f m = y),
       f = funcomp squash_element (cone_squash_map f y e).
Proof.
  reflexivity.
Qed.

(* paths *)
Definition confun T {Y} (y:Y) := λ _:T, y.
Definition path_type {X} {x x':X} (p:x = x') := X.
Definition path_start {X} {x x':X} (p:x = x') := x.
Definition path_end {X} {x x':X} (p:x = x') := x'.

Definition uniqueness {T} (i:iscontr T) (t:T) : t = iscontrpr1 i.
Proof.
  intros. exact (pr2 i t).
Defined.

Definition uniqueness' {T} (i:iscontr T) (t:T) : iscontrpr1 i = t.
Proof.
  intros. exact (! (pr2 i t)).
Defined.

Definition path_inverse_to_right {X} {x y:X} (p q:x = y) : p = q -> !q@p = idpath _.
Proof.
  intros e. induction e. induction p. reflexivity.
Defined.

Definition path_inverse_to_right' {X} {x y:X} (p q:x = y) : p = q -> p@!q = idpath _.
Proof.
  intros e. induction e. induction p. reflexivity.
Defined.

Definition cast {T U:Type} : T = U -> T -> U.
Proof.
  intros p t. induction p. exact t.
Defined.

Definition app {X} {P:X->Type} {x x':X} {e e':x = x'} (q:e = e') (p:P x) :
   e#p = e'#p.
Proof.
  intros. induction q. reflexivity.
Defined.

(** ** Paths *)

Definition pathsinv0_to_right {X} {x y z:X} (p:y = x) (q:y = z) (r:x = z) :
  q = p @ r -> !p @ q = r.
Proof.
  intros e. induction p, q. exact e.
Defined.

Definition pathsinv0_to_right' {X} {x y:X} (p:y = x) (r:x = y) :
  idpath _ = p @ r -> !p = r.
Proof.
  intros e. induction p. exact e.
Defined.

Definition pathsinv0_to_right'' {X} {x:X} (p:x = x) :
  idpath _ = p -> !p = idpath _.
Proof.
  intros e. apply pathsinv0_to_right'. rewrite pathscomp0rid. exact e.
Defined.

Definition loop_power_nat {Y} {y:Y} (l:y = y) (n:nat) : y = y.
Proof.
  intros. induction n as [|n p].
  { exact (idpath _). }
  { exact (p@l). }
Defined.

Definition pathscomp0_linj {X} {x y z:X} {p:x = y} {q q':y = z} (r:p@q = p@q') : q = q'.
Proof.
  intros. induction p. exact r.
Defined.

Definition pathscomp0_rinj {X} {x y z:X} {p p':x = y} {q:y = z} (r:p@q = p'@q) : p = p'.
Proof.
  intros. induction q. exact (! pathscomp0rid p @ r @ pathscomp0rid p').
Defined.

Lemma irrel_paths {X} (irr:∏ x y:X, x = y) {x y:X} (p q:x = y) : p = q.
Proof.
  intros.
  assert (k : ∏ z:X, ∏ r:x = z, r @ irr z z = irr x z).
  { intros. induction r. reflexivity. }
  exact (pathscomp0_rinj (k y p @ !k y q)).
Defined.

Definition path_inv_rotate_2 {X} {a b c d:X} (p:a = b) (p':c = d) (q:a = c) (q':b = d) :
  q @ p' = p @ q' -> p' @ ! q' = !q @ p.
Proof.
  induction q,q'. simpl. repeat rewrite pathscomp0rid. apply idfun.
Defined.

Definition maponpaths_naturality {X Y : UU} {f : X -> Y}
           {x x' x'' : X} {p : x = x'} {q : x' = x''}
           {p': f x = f x'} {q': f x' = f x''}
           (r : maponpaths f p = p') (s : maponpaths f q = q') :
  maponpaths f (p @ q) = p' @ q'.
Proof.
  intros. induction r, s. apply maponpathscomp0.
Defined.

Definition maponpaths_naturality' {X Y : UU} {f : X -> Y}
           {x x' x'' : X} {p : x' = x} {q : x' = x''}
           {p' : f x' = f x} {q' : f x' = f x''}
           (r : maponpaths f p = p') (s : maponpaths f q = q') :
  maponpaths f (!p @ q) = (!p') @ q'.
Proof.
  intros. induction r, s, p, q. reflexivity.
Defined.


(** ** Pairs *)

Definition pr2_of_hfiberpair {X Y} {f:X->Y} {x:X} {y:Y} {e:f x = y} :
  pr2 (hfiberpair f x e) = e.
Proof.
  reflexivity.
Defined.

Definition pr2_of_pair {X} {P:X->Type} (x:X) (p:P x) : pr2 (tpair P x p) = p.
Proof.
  reflexivity.
Defined.

Definition pr2_of_weqpair {X Y} (f:X->Y) (i:isweq f) : pr2 (weqpair f i) = i.
Proof.
  reflexivity.
Defined.

(** ** Paths between pairs *)

(* replace all uses of this by uses of subtypePairEquality *)
Definition pair_path_props {X} {P:X->Type} {x y:X} {p:P x} {q:P y} :
  x = y -> (∏ z, isaprop (P z)) -> x,,p = y,,q.
Proof.
  intros e is. now apply subtypePairEquality.
Abort.

Definition pair_path2 {A} {B:A->UU} {a a1 a2} {b1:B a1} {b2:B a2}
           (p:a1 = a) (q:a2 = a) (e:p#b1 = q#b2) : a1,,b1 = a2,,b2.
Proof.
  intros. induction p,q; compute in e. induction e. reflexivity.
Defined.

Lemma simple_pair_path {X Y} {x x':X} {y y':Y} (p : x = x') (q : y = y') :
  x,,y = x',,y'.
Proof.
  intros. induction p. induction q. apply idpath.
Defined.

(** ** Projections from pair types *)

Definition pair_path_in2_comp1 {X} (P:X->Type) {x:X} {p q:P x} (e:p = q) :
  maponpaths pr1 (maponpaths (tpair P _) e) = idpath x.
Proof.
  intros. induction e. reflexivity.
Defined.

Definition total2_paths2_comp1 {X} {Y:X->Type} {x} {y:Y x} {x'} {y':Y x'}
           (p:x = x') (q:p#y = y') : maponpaths pr1 (two_arg_paths_f (f := tpair Y) p q) = p.
Proof.
  intros. induction p. induction q. reflexivity.
Defined.

Definition total2_paths2_comp2 {X} {Y:X->Type} {x} {y:Y x} {x'} {y':Y x'}
           (p:x = x') (q:p#y = y') :
  ! app (total2_paths2_comp1 p q) y @ fiber_paths (two_arg_paths_f p q) = q.
Proof.
  intros. induction p, q. reflexivity.
Defined.

(** ** Maps from pair types *)

Definition from_total2 {X} {P:X->Type} {Y} : (∏ x, P x->Y) -> total2 P -> Y.
Proof.
  intros f [x p]. exact (f x p).
Defined.

(** ** Sections and functions *)

Notation homotsec := homot.

(* compare with [adjev] *)
Definition evalat {T} {P:T->UU} (t:T) (f:∏ t:T, P t) := f t.

Definition apfun {X Y} {f f':X->Y} (p:f = f') {x x'} (q:x = x') : f x = f' x'.
  intros. induction q. exact (eqtohomot p x).
Defined.

Definition aptwice {X Y Z} (f:X->Y->Z) {a a' b b'} (p:a = a') (q:b = b') : f a b = f a' b'.
  intros. exact (apfun (maponpaths f p) q).
Defined.

Definition fromemptysec { X : empty -> UU } (nothing:empty) : X nothing.
(* compare with [fromempty] in u00 *)
Proof.
  induction nothing.
Defined.

Definition maponpaths_idpath {X Y} {f:X->Y} {x:X} : maponpaths f (idpath x) = idpath (f x).
Proof.
  intros. reflexivity.
Defined.

(** ** Transport *)

Definition transport_type_path {X Y:Type} (p:X = Y) (x:X) :
  transportf (λ T:Type, T) p x = cast p x.
Proof.
  intros. induction p. reflexivity.
Defined.

Definition transport_fun_path {X Y} {f g:X->Y} {x x':X} {p:x = x'} {e:f x = g x} {e':f x' = g x'} :
  e @ maponpaths g p = maponpaths f p @ e' ->
  transportf (λ x, f x = g x) p e = e'.
Proof.
  intros k. induction p. rewrite maponpaths_idpath in k. rewrite maponpaths_idpath in k.
  rewrite pathscomp0rid in k. exact k.
Defined.

Definition transportf_pathsinv0' {X} (P:X->UU) {x y:X} (p:x = y) (u:P x) (v:P y) :
  p # u = v -> !p # v = u.
Proof.
  intros e. induction p, e. reflexivity.
Defined.

Lemma transport_idfun {X} (P:X->UU) {x y:X} (p:x = y) (u:P x) :
  transportf P p u = transportf (idfun UU) (maponpaths P p) u.
(* same as HoTT.PathGroupoids.transport_idmap_ap *)
Proof.
  intros. induction p. reflexivity.
Defined.

Lemma transport_functions {X} {Y:X->Type} {Z:∏ x (y:Y x), Type}
      {f f':∏ x : X, Y x} (p:f = f') (z:∏ x, Z x (f x)) x :
    transportf (λ f, ∏ x, Z x (f x)) p z x =
    transportf (Z x) (toforallpaths _ _ _ p x) (z x).
Proof.
  intros. induction p. reflexivity.
Defined.

Definition transport_funapp {T} {X Y:T->Type}
           (f:∏ t, X t -> Y t) (x:∏ t, X t)
           {t t':T} (p:t = t') :
  transportf _ p ((f t)(x t))
  = (transportf (λ t, X t -> Y t) p (f t)) (transportf _ p (x t)).
Proof.
  intros. induction p. reflexivity.
Defined.

Definition helper_A {T} {Y} (P:T->Y->Type) {y y':Y} (k:∏ t, P t y) (e:y = y') t :
  transportf (λ y, P t y) e (k t)
  =
  (transportf (λ y, ∏ t, P t y) e k) t.
Proof.
  intros. induction e. reflexivity.
Defined.

Definition helper_B {T} {Y} (f:T->Y) {y y':Y} (k:∏ t, y = f t) (e:y = y') t :
  transportf (λ y, y = f t) e (k t)
  =
  (transportf (λ y, ∏ t, y = f t) e k) t.
Proof.
  intros. exact (helper_A _ k e t).
Defined.

Definition transport_invweq {T} {X Y:T->Type} (f:∏ t, (X t) ≃ (Y t))
           {t t':T} (p:t = t') :
  transportf (λ t, (Y t) ≃ (X t)) p (invweq (f t))
  =
  invweq (transportf (λ t, (X t) ≃ (Y t)) p (f t)).
Proof.
  intros. induction p. reflexivity.
Defined.

Definition transport_invmap {T} {X Y:T->Type} (f:∏ t, (X t) ≃ (Y t))
           {t t':T} (p:t=t') :
  transportf (λ t, Y t -> X t) p (invmap (f t))
  =
  invmap (transportf (λ t, (X t) ≃ (Y t)) p (f t)).
Proof.
  intros. induction p. reflexivity.
Defined.

  (** *** Double transport *)

  Definition transportf2 {X} {Y:X->Type} (Z:∏ x, Y x->Type)
             {x x'} (p:x = x')
             (y:Y x) (z:Z x y) : Z x' (p#y).
  Proof.
    intros. induction p. exact z.
Defined.

  Definition transportb2 {X} {Y:X->Type} (Z:∏ x, Y x->Type)
             {x x'} (p:x=x')
             (y':Y x') (z':Z x' y') : Z x (p#'y').
  Proof.
    intros. induction p. exact z'.
Defined.

  Definition maponpaths_pr1_pr2 {X} {P:X->UU} {Q:∏ x, P x->Type}
             {w w': ∑ x p, Q x p}
             (p : w = w') :
    transportf P (maponpaths pr1 p) (pr1 (pr2 w)) = pr1 (pr2 w').
  Proof.
    intros. induction p. reflexivity.
Defined.

  (** *** Transport a pair *)

  (* replace this with transportf_total2 (?) : *)
  Definition transportf_pair X (Y:X->Type) (Z:∏ x, Y x->Type)
             x x' (p:x = x') (y:Y x) (z:Z x y) :
    transportf (λ x, total2 (Z x)) p (tpair (Z x) y z)
    =
    tpair (Z x') (transportf Y p y) (transportf2 _ p y z).
  Proof.
    intros. induction p. reflexivity.
Defined.

  Definition transportb_pair X (Y:X->Type) (Z:∏ x, Y x->Type)
             x x' (p:x = x')
             (y':Y x') (z':Z x' y')
             (z'' : (Z x' y')) :
    transportb (λ x, total2 (Z x)) p (tpair (Z x') y' z')
    =
    tpair (Z x) (transportb Y p y') (transportb2 _ p y' z').
  Proof.
    intros. induction p. reflexivity.
Defined.

(** ** h-levels and paths *)

Lemma isaprop_wma_inhab X : (X -> isaprop X) -> isaprop X.
Proof.
  intros f. apply invproofirrelevance. intros x y. apply (f x).
Qed.

Lemma isaprop_wma_inhab' X : (X -> iscontr X) -> isaprop X.
Proof.
  intros f. apply isaprop_wma_inhab. intro x. apply isapropifcontr.
       apply (f x).
Qed.

Goal ∏ (X:hSet) (x y:X) (p q:x = y), p = q.
Proof.
  intros. apply setproperty.
Defined.

Goal ∏ (X:Type) (x y:X) (p q:x = y), isaset X -> p = q.
Proof.
  intros * is. apply is.
Defined.

Definition funset X (Y:hSet) : hSet
  := hSetpair (X->Y) (impredfun 2 _ _ (setproperty Y)).

(** ** Connected types *)

Definition isconnected X := ∏ (x y:X), nonempty (x = y).

Lemma base_connected {X} (t:X) : (∏ y:X, nonempty (t = y)) -> isconnected X.
Proof.
  intros p x y. assert (a := p x). assert (b := p y). clear p.
  apply (squash_to_prop a). apply propproperty. clear a. intros a.
  apply (squash_to_prop b). apply propproperty. clear b. intros b.
  apply hinhpr. exact (!a@b).
Defined.

(** ** Applications of univalence *)

(** Compare the following two definitions with [transport_type_path]. *)

Require Import UniMath.Foundations.UnivalenceAxiom.

Definition pr1_eqweqmap { X Y } ( e: X = Y ) : cast e = pr1 (eqweqmap e).
Proof.
  intros. induction e. reflexivity.
Defined.

Definition pr1_eqweqmap2 { X Y } ( e: X = Y ) :
  pr1 (eqweqmap e) = transportf (λ T:Type, T) e.
Proof.
  intros. induction e. reflexivity.
Defined.

Definition weqonsec {X Y} (P:X->Type) (Q:Y->Type)
           (f:X ≃ Y) (g:∏ x, weq (P x) (Q (f x))) :
  (∏ x:X, P x) ≃ (∏ y:Y, Q y).
Proof.
  intros.
  exact (weqcomp (weqonsecfibers P (λ x, Q(f x)) g)
                 (invweq (weqonsecbase Q f))).
Defined.

Definition weq_transportf {X} (P:X->Type) {x y:X} (p:x = y) : (P x) ≃ (P y).
Proof.
  intros. induction p. apply idweq.
Defined.

Definition weq_transportf_comp {X} (P:X->Type) {x y:X} (p:x = y) (f:∏ x, P x) :
  weq_transportf P p (f x) = f y.
Proof.
  intros. induction p. reflexivity.
Defined.

Definition weqonpaths2 {X Y} (w:X ≃ Y) {x x':X} {y y':Y} :
  w x = y -> w x' = y' -> (x = x') ≃ (y = y').
Proof.
  intros p q. induction p,q. apply weqonpaths.
Defined.

Definition eqweqmap_ap {T} (P:T->Type) {t t':T} (e:t = t') (f:∏ t:T, P t) :
  eqweqmap (maponpaths P e) (f t) = f t'. (* move near eqweqmap *)
Proof.
  intros. induction e. reflexivity.
Defined.

Definition eqweqmap_ap' {T} (P:T->Type) {t t':T} (e:t = t') (f:∏ t:T, P t) :
  invmap (eqweqmap (maponpaths P e)) (f t') = f t. (* move near eqweqmap *)
Proof.
  intros. induction e. reflexivity.
Defined.

Definition weqpath_transport {X Y} (w : X ≃ Y) :
  transportf (idfun UU) (weqtopaths w) = pr1 w.
Proof.
  intros. exact (!pr1_eqweqmap2 _ @ maponpaths pr1 (weqpathsweq w)).
Defined.

Definition weqpath_cast {X Y} (w : X ≃ Y) : cast (weqtopaths w) = w.
Proof.
  intros. exact (pr1_eqweqmap _ @ maponpaths pr1 (weqpathsweq w)).
Defined.

Definition switch_weq {X Y} (f:X ≃ Y) {x y} : y = f x -> invweq f y = x.
Proof.
  intros p. exact (maponpaths (invweq f) p @ homotinvweqweq f x).
Defined.

Definition switch_weq' {X Y} (f:X ≃ Y) {x y} : invweq f y = x -> y = f x.
Proof.
  intros p. exact (! homotweqinvweq f y @ maponpaths f p).
Defined.

Definition weqbandfrel {X Y T}
           (e:Y->T) (t:T) (f : X ≃ Y)
           (P:X -> Type) (Q: Y -> Type)
           (g:∏ x:X, weq (P x) (Q (f x))) :
  weq (hfiber (λ xp:total2 P, e(f(pr1 xp))) t)
      (hfiber (λ yq:total2 Q, e(  pr1 yq )) t).
Proof.
  intros. refine (weqbandf (weqbandf f _ _ g) _ _ _).
  intros [x p]. simpl. apply idweq.
Defined.

Definition weq_over_sections {S T} (w:S ≃ T)
           {s0:S} {t0:T} (k:w s0 = t0)
           {P:T->Type}
           (p0:P t0) (pw0:P(w s0)) (l:k#pw0 = p0)
           (H:(∏ t, P t) -> UU)
           (J:(∏ s, P(w s)) -> UU)
           (g:∏ f:(∏ t, P t), weq (H f) (J (maponsec1 P w f))) :
  weq (hfiber (λ fh:total2 H, pr1 fh t0) p0 )
      (hfiber (λ fh:total2 J, pr1 fh s0) pw0).
Proof.
  intros. simple refine (weqbandf _ _ _ _).
  { simple refine (weqbandf _ _ _ _).
    { exact (weqonsecbase P w). }
    { unfold weqonsecbase; simpl. exact g. } }
  { intros [f h]. simpl. unfold maponsec1; simpl.
    induction k, l; simpl. unfold transportf; simpl.
    unfold idfun; simpl. apply idweq. }
Defined.

Definition weq_total2_prod {X Y} (Z:Y->Type) : (∑ y, X × Z y) ≃ (X × ∑ y, Z y).
Proof.
  (* move upstream *)
  intros. simple refine (weqpair _ (isweq_iso _ _ _ _)).
  { intros [y [x z]]. exact (x,,y,,z). }
  { intros [x [y z]]. exact (y,,x,,z). }
  { intros [y [x z]]. reflexivity. }
  { intros [x [y z]]. reflexivity. }
Defined.

(* associativity of ∑ *)
Definition totalAssociativity {X:UU} {Y: ∏ (x:X), UU} (Z: ∏ (x:X) (y:Y x), UU) : (∑ (x:X) (y:Y x), Z x y) ≃ (∑ (p:∑ (x:X), Y x), Z (pr1 p) (pr2 p)).
Proof.
  (* move upstream *)
  intros. simple refine (_,,isweq_iso _ _ _ _).
  { intros [x [y z]]. exact ((x,,y),,z). }
  { intros [[x y] z]. exact (x,,(y,,z)). }
  { intros [x [y z]]. reflexivity. }
  { intros [[x y] z]. reflexivity. }
Defined.

(** ** Pointed types *)

Definition PointedType := ∑ X, X.

Definition pointedType X x := X,,x : PointedType.

Definition underlyingType (X:PointedType) := pr1 X.

Coercion underlyingType : PointedType >-> UU.

Definition basepoint (X:PointedType) := pr2 X.

Definition loopSpace (X:PointedType) :=
  pointedType (basepoint X = basepoint X) (idpath _).

Definition underlyingLoop {X:PointedType} (l:loopSpace X) : basepoint X = basepoint X.
Proof.
  intros. exact l.
Defined.

Definition Ω := loopSpace.

(** ** Direct products with several factors *)

Definition paths3 {X Y Z} {x x':X} {y y':Y} {z z':Z} :
  x = x' -> y = y' -> z = z' -> @paths (_×_×_) (x,,y,,z) (x',,y',,z').
Proof.
  intros p q r. induction p, q, r. reflexivity.
Defined.

Definition paths4 {W X Y Z} {w w':W} {x x':X} {y y':Y} {z z':Z} :
  w = w' -> x = x' -> y = y' -> z = z' -> @paths (_×_×_×_) (w,,x,,y,,z) (w',,x',,y',,z').
Proof.
  intros o p q r. induction o, p, q, r. reflexivity.
Defined.

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/Utilities.vo"
End:
*)
