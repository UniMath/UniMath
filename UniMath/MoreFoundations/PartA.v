(** This file contain various results that could be upstreamed to Foundations/PartA.v *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Tactics.

Lemma maponpaths_for_constant_function {T1 T2 : UU} (x : T2) {t1 t2 : T1}
      (e: t1 = t2): maponpaths (fun _: T1 => x) e = idpath x.
Proof.
  induction e.
  apply idpath.
Qed.

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
  eapply pathscomp0.
  2: { apply maponpaths. exact H. }
  eapply pathscomp0.
  2: { symmetry. apply transport_f_f. }
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


Lemma transportf_set {A : UU} (B : A → UU)
      {a : A} (e : a = a) (b : B a)
      (X : isaset A)
  : transportf B e b = b.
Proof.
  apply transportf_comp_lemma_hset.
  - apply X.
  - apply idpath.
Defined.


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

Lemma pr1_transportf {A : UU} {B : A -> UU} {P : ∏ a, B a -> UU}
   {a a' : A} (e : a = a') (xs : ∑ b : B a, P _ b):
   pr1 (transportf (λ x, ∑ b : B x, P _ b) e xs) =
     transportf (λ x, B x) e (pr1 xs).
Proof.
  apply pathsinv0.
  apply (transport_map (λ a, pr1 (P := P a))).
Defined.

Lemma pr2_transportf {A} {B1 B2 : A → UU}
    {a a' : A} (e : a = a') (xs : B1 a × B2 a)
  : pr2 (transportf (λ a, B1 a × B2 a) e xs) = transportf _ e (pr2 xs).
Proof.
  apply pathsinv0.
  apply (transport_map (λ a, pr2 (P := λ _, B2 a))).
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

(** Flip the arguments of a function *)
Definition flipsec {A B : UU} {C : A -> B -> UU} (f : ∏ a b, C a b) : ∏ b a, C a b :=
  λ x y, f y x.
Notation flip := flipsec.

(** Flip is a weak equivalence (in fact, it is an involution) *)
Lemma isweq_flipsec {A B : UU} {C : A -> B -> UU} : isweq (@flipsec A B C).
Proof.
  apply (isweq_iso _ flipsec); reflexivity.
Defined.

Definition flipsec_weq {A B : UU} {C : A -> B -> UU} :
  (∏ a b, C a b) ≃ (∏ b a, C a b) := make_weq flipsec isweq_flipsec.

(** The subtypes of a type of hlevel S n are also of hlevel S n.
    This doesn't work for types of hlevel 0: a subtype of a contractible
    type might be empty, not contractible! *)
Lemma isofhlevel_hsubtype {X : UU} {n : nat} (isof : isofhlevel (S n) X) :
  ∏ subt : hsubtype X, isofhlevel (S n) subt.
Proof.
  intros subt.
  apply isofhleveltotal2.
  - assumption.
  - intro.
    apply isofhlevelsnprop.
    apply propproperty.
Defined.

(** Homotopy equivalence on total spaces.

  This result combines weqfp and weqfibtototal conveniently.
  *)
Lemma weqtotal2 {X Y:Type} {P:X->Type} {Q:Y->Type} (f : X ≃ Y) :
  (∏ x, P x ≃ Q (f x)) -> (∑ x:X, P x) ≃ (∑ y:Y, Q y).
Proof.
  intros e. exists (λ xp, (f(pr1 xp),,e (pr1 xp) (pr2 xp))).
  exact (twooutof3c _ _ (isweqfibtototal P (Q ∘ f) e) (pr2 (weqfp f Q))).
Defined.

Lemma hlevel_total2 n {A : UU} {B : A → UU} :
  isofhlevel n (∑ (x :A), B x) → isofhlevel (S n) A → ∏ (x : A), isofhlevel n (B x).
Proof.
  intros ic ia x.
  exact (isofhlevelweqf _ (invweq (ezweqpr1 _ _)) (isofhlevelffromXY _ _ ic ia _)).
Defined.

Definition path_sigma_hprop
           {A : UU}
           (B : A → UU)
           (x y : ∑ (z : A), B z)
           (HB : isaprop (B (pr1 y)))
  : x = y ≃ pr1 x = pr1 y.
Proof.
  refine (weqpr1 _ _ ∘ total2_paths_equiv _ _ _)%weq.
  intros.
  apply HB.
Defined.

(** ** Pointed types *)

Section PointedTypes.
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
End PointedTypes.

(** associativity of ∑ *)

Definition weq_total2_prod {X Y} (Z:Y->Type) : (∑ y, X × Z y) ≃ (X × ∑ y, Z y).
Proof.
  (* move upstream *)
  intros. simple refine (make_weq _ (isweq_iso _ _ _ _)).
  { intros [y [x z]]. exact (x,,y,,z). }
  { intros [x [y z]]. exact (y,,x,,z). }
  { intros [y [x z]]. reflexivity. }
  { intros [x [y z]]. reflexivity. }
Defined.

Definition totalAssociativity {X:UU} {Y: ∏ (x:X), UU} (Z: ∏ (x:X) (y:Y x), UU) : (∑ (x:X) (y:Y x), Z x y) ≃ (∑ (p:∑ (x:X), Y x), Z (pr1 p) (pr2 p)).
Proof.
  intros. simple refine (_,,isweq_iso _ _ _ _).
  { intros [x [y z]]. exact ((x,,y),,z). }
  { intros [[x y] z]. exact (x,,(y,,z)). }
  { intros [x [y z]]. reflexivity. }
  { intros [[x y] z]. reflexivity. }
Defined.

(* direct product of 3 paths; extends pathsdirprod *)
Definition paths3 {X Y Z} {x x':X} {y y':Y} {z z':Z} :
  x = x' -> y = y' -> z = z' -> @paths (_×_×_) (x,,y,,z) (x',,y',,z').
Proof.
  intros p q r. induction p, q, r. reflexivity.
Defined.

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

Definition app {X} {P:X->Type} {x x':X} {e e':x = x'} (q:e = e') (p:P x) :
  transportf P e p = transportf P e' p.
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

Lemma irrel_paths {X} (irr:∏ x y:X, x = y) {x y:X} (p q:x = y) : p = q.
Proof.
  intros.
  assert (k : ∏ z:X, ∏ r:x = z, r @ irr z z = irr x z).
  { intros. induction r. reflexivity. }
  assert (l := k y p @ !k y q).
  apply (pathscomp_cancel_right _ _ _ l).
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

Definition pr2_of_make_hfiber {X Y} {f:X->Y} {x:X} {y:Y} {e:f x = y} :
  pr2 (make_hfiber f x e) = e.
Proof.
  reflexivity.
Defined.

Definition pr2_of_pair {X} {P:X->Type} (x:X) (p:P x) : pr2 (tpair P x p) = p.
Proof.
  reflexivity.
Defined.

Definition pr2_of_make_weq {X Y} (f:X->Y) (i:isweq f) : pr2 (make_weq f i) = i.
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

Local Open Scope transport.

Definition pair_path2 {A} {B:A->UU} {a a1 a2} {b1:B a1} {b2:B a2}
           (p:a1 = a) (q:a2 = a) (e:p#b1 = q#b2) : a1,,b1 = a2,,b2.
Proof.
  intros. induction p,q; compute in e. induction e. reflexivity.
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

Definition cast {T U:Type} : T = U -> T -> U
  := transportf (λ T:Type, T).

Definition transport_type_path {X Y:Type} (p:X = Y) (x:X) :
  transportf (λ T:Type, T) p x = cast p x.
Proof.
  reflexivity.
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

(* (* replace this with transportf_total2 (?) : *) *)
(* Definition transportf_pair X (Y:X->Type) (Z:∏ x, Y x->Type) *)
(*            x x' (p:x = x') (y:Y x) (z:Z x y) : *)
(*   transportf (λ x, total2 (Z x)) p (tpair (Z x) y z) *)
(*   = *)
(*   tpair (Z x') (transportf Y p y) (transportf2 _ p y z). *)
(* Proof. *)
(*   intros. induction p. reflexivity. *)
(* Defined. *)

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
  := make_hSet (X->Y) (impredfun 2 _ _ (setproperty Y)).

Lemma eq_equalities_between_pairs (A : UU) (B : A -> UU)(x y : total2 (λ x, B x))
    (p q : x = y) (H : base_paths _ _ p = base_paths _ _ q)
    (H2 : transportf (fun p : pr1 x = pr1 y =>  transportf _ p (pr2 x) = pr2 y )
         H (fiber_paths p) = fiber_paths q) :  p = q.
Proof.
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )).
  apply (total2_paths_f (B:=(fun p : pr1 x = pr1 y =>
          transportf (λ x : A, B x) p (pr2 x) = pr2 y))
          (s  := (total2_paths_equiv B x y) p)
          (s' := (total2_paths_equiv B x y) q) H).
  assumption.
Defined.

(* perhaps consider name *)
Lemma total2_reassoc_paths {A} {B : A → UU} {C : (∑ a, B a) -> UU}
    (BC : A -> UU := λ a, ∑ b, C (a,,b))
    {a1 a2 : A} (bc1 : BC a1) (bc2 : BC a2)
    (ea : a1 = a2)
    (eb : transportf _ ea (pr1 bc1) = pr1 bc2)
    (ec : transportf C (two_arg_paths_f (*was total2_paths2*) ea eb) (pr2 bc1) = pr2 bc2)
  : transportf _ ea bc1 = bc2.
Proof.
  destruct ea, bc1 as [b1 c1], bc2 as [b2 c2].
  cbn in *; destruct eb, ec.
  apply idpath.
Defined.

(* perhaps consider name *)
Lemma total2_reassoc_paths' {A} {B : A → UU} {C : (∑ a, B a) -> UU}
    (BC : A -> UU := λ a, ∑ b, C (a,,b))
    {a1 a2 : A} (bc1 : BC a1) (bc2 : BC a2)
    (ea : a1 = a2)
    (eb : pr1 bc1 = transportb _ ea (pr1 bc2))
    (ec : pr2 bc1 = transportb C (total2_paths2_b ea eb) (pr2 bc2))
  : bc1 = transportb _ ea bc2.
Proof.
  destruct ea, bc1 as [b1 c1], bc2 as [b2 c2].
  cbn in eb; destruct eb; cbn in ec; destruct ec.
  apply idpath.
Defined.

Section InvRot.

  (** moving pathsinv0 to the other side in equations *)

  Local Set Implicit Arguments.
  Local Unset Strict Implicit.

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

End InvRot.

Section Weqpaths.

  (** a more basic approach to proving isweqpathscomp0r *)

  Local Set Implicit Arguments.
  Local Unset Strict Implicit.

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

End Weqpaths.