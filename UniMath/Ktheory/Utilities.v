(** * Utilities concerning paths, hlevel, and logic *)

Global Unset Automatic Introduction.
Require Export UniMath.Foundations.Basics.All.
Require Export UniMath.Foundations.Sets.
Require Import UniMath.Foundations.FunctionalExtensionality.
Require Export UniMath.Ktheory.Tactics.

Notation "'∃!'  x .. y , P" := (iscontr (Σ x , .. (Σ y , P) .. )) (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "'not' X" := (X -> empty) (at level 35).
Notation set_to_type := pr1hSet.
Notation ap := maponpaths.
(* see table 3.1 in the coq manual for parsing levels *)
Notation "g ∘ f" := (funcomp f g) (at level 50).
Notation "f ;; g" := (funcomp f g) (at level 50).
(* funcomp' is like funcomp, but with the arguments in the other order *)
Definition funcomp' { X Y Z : UU } ( g : Y -> Z ) ( f : X -> Y ) := fun x : X => g ( f x ) . 
Notation "p # x" := (transportf _ p x) (right associativity, at level 65) : transport_scope.
Notation "p #' x" := (transportb _ p x) (right associativity, at level 65) : transport_scope.
Notation "p # x" := (transportf _ p x) (right associativity, at level 65) : transport_scope.
Notation "p #' x" := (transportb _ p x) (right associativity, at level 65) : transport_scope.
Open Scope transport_scope.

Notation totalSpace := total2.

(* some jargon reminders: *)
Goal forall X (i:isaprop X) (x x':X), x = x'.
Proof. apply proofirrelevance. Defined.

Goal forall X (i:iscontr X) (x x':X), x = x'.
Proof. intros. apply proofirrelevancecontr. assumption. Defined.

Definition an_inclusion_is_injective {X Y} (f:X->Y) (inj:isincl f) x x': f x = f x' -> x = x'.
Proof. intros ? ? ? ? ? ?. exact (invmaponpathsincl _ inj _ _). Defined.

Lemma isaprop_hProp (X:hProp) : isaprop X.
Proof. intro. exact (pr2 X). Qed.

(* paths *)
Definition confun T {Y} (y:Y) := fun _:T => y.
Definition path_type {X} {x x':X} (p:x = x') := X.
Definition path_start {X} {x x':X} (p:x = x') := x.
Definition path_end {X} {x x':X} (p:x = x') := x'.
Definition paths_from {X} (x:X) := totalSpace (paths x).
Definition point_to {X} {x:X} : paths_from x -> X := pr1.
Definition paths_from_path {X} {x:X} (w:paths_from x) := pr2 w.
Definition paths' {X} (x:X) := fun y => paths y x.
Definition idpath' {X} (x:X) := idpath x : paths' x x.
Definition paths_to {X} (x:X) := totalSpace (paths' x).
Definition point_from {X} {x:X} : paths_to x -> X := pr1.
Definition paths_to_path {X} {x:X} (w:paths_to x) := pr2 w.
Definition iscontr_paths_to {X} (x:X) : iscontr (paths_to x).
Proof. apply iscontrcoconustot. Defined.
Definition paths_to_prop {X} (x:X) := 
  hProppair (paths_to x) (isapropifcontr (iscontr_paths_to x)).
Definition iscontr_paths_from {X} (x:X) : iscontr (paths_from x).
Proof. apply iscontrcoconusfromt. Defined.
Definition paths_from_prop {X} (x:X) := 
  hProppair (paths_from x) (isapropifcontr (iscontr_paths_from x)).

Definition thePoint {T} : iscontr T -> T.
Proof. intros ? is. exact (pr1 is). Defined.

Definition uniqueness {T} (i:iscontr T) (t:T) : t = thePoint i.
Proof. intros. exact (pr2 i t). Defined.

Definition uniqueness' {T} (i:iscontr T) (t:T) : thePoint i = t.
Proof. intros. exact (! (pr2 i t)). Defined.

Definition path_inverse_to_right {X} {x y:X} (p q:x = y) : p = q -> !q@p = idpath _.
Proof. intros ? ? ? ? ? e. destruct e. destruct p. reflexivity. Defined.

Definition path_inverse_to_right' {X} {x y:X} (p q:x = y) : p = q -> p@!q = idpath _.
Proof. intros ? ? ? ? ? e. destruct e. destruct p. reflexivity. Defined.

Definition cast {T U:Type} : T = U -> T -> U.
Proof. intros ? ? p t. destruct p. exact t. Defined.

Definition app {X} {P:X->Type} {x x':X} {e e':x = x'} (q:e = e') (p:P x) : 
   e#p = e'#p.
Proof. intros. destruct q. reflexivity. Defined.

(** ** Paths *)

Definition pathsinv0_to_right {X} {x y z:X} (p:y = x) (q:y = z) (r:x = z) :
  q = p @ r -> !p @ q = r.
Proof. intros ? ? ? ? ? ? ? e. destruct p, q. exact e. Defined.

Definition pathsinv0_to_right' {X} {x y:X} (p:y = x) (r:x = y) :
  idpath _ = p @ r -> !p = r.
Proof. intros ? ? ? ? ? e. destruct p. exact e. Defined.

Definition pathsinv0_to_right'' {X} {x:X} (p:x = x) :
  idpath _ = p -> !p = idpath _.
Proof. intros ? ? ? e. apply pathsinv0_to_right'. rewrite pathscomp0rid.
       exact e. Defined.

Definition path_inverse_from_right {X} {x y:X} (p q:x = y) : !q@p = idpath _ -> p = q.
Proof. intros ? ? ? ? ? e. destruct q. exact e. Defined.

Definition path_inverse_from_right' {X} {x y:X} (p q:x = y) : p@!q = idpath _ -> p = q.
Proof. intros ? ? ? ? ? e. destruct q.
       intermediate_path (p @ idpath x).
       { apply pathsinv0. apply pathscomp0rid. } exact e. Defined.

Definition loop_power_nat {Y} {y:Y} (l:y = y) (n:nat) : y = y.
Proof. intros. induction n as [|n p]. 
       { exact (idpath _). } { exact (p@l). } Defined.

Definition post_cat {X} {x y z:X} {q:y = z} : x = y -> x = z.
Proof. intros ? ? ? ? p q. exact (pathscomp0 q p). Defined.

Definition pre_cat {X} {x y z:X} {q:x = y} : y = z -> x = z.
Proof. intros ? ? ? ? p q. exact (pathscomp0 p q). Defined.

Ltac ap_pre_post_cat := 
  repeat rewrite path_assoc; repeat apply (ap post_cat); repeat rewrite <- path_assoc; 
  repeat apply (ap pre_cat); repeat rewrite path_assoc; repeat rewrite maponpathsinv0; 
  try reflexivity.

Definition pathscomp0_linj {X} {x y z:X} {p:x = y} {q q':y = z} (r:p@q = p@q') : q = q'.
Proof. intros. destruct p. exact r. Defined.

Definition pathscomp0_rinj {X} {x y z:X} {p p':x = y} {q:y = z} (r:p@q = p'@q) : p = p'.
Proof. intros. destruct q. exact (! pathscomp0rid p @ r @ pathscomp0rid p').
Defined.                           

Lemma irrel_paths {X} (irr:∀ x y:X, x = y) {x y:X} (p q:x = y) : p = q.
Proof. intros. 
       assert (k : ∀ z:X, ∀ r:x = z, r @ irr z z = irr x z). 
       { intros. destruct r. reflexivity. }
       exact (pathscomp0_rinj (k y p @ !k y q)). Defined.

Definition path_inv_rotate_lr {X} {a b c:X} (r:a = b) (p:b = c) (q:a = c) :
  q = r @ p -> q @ !p = r.
Proof. intros ? ? ? ? ? ? ? e. destruct p. destruct q. rewrite pathscomp0rid in e. 
       exact e. Defined.

Definition path_inv_rotate_rr {X} {a b c:X} (r:a = b) (p:b = c) (q:a = c) :
  r @ p = q -> r = q @ !p.
Proof. intros ? ? ? ? ? ? ? e. destruct p. destruct q. rewrite pathscomp0rid in e. 
       exact e. Defined.

Definition path_inv_rotate_ll {X} {a b c:X} (p:a = b) (r:b = c) (q:a = c) :
  q = p @ r -> !p @ q = r.
Proof. intros ? ? ? ? ? ? ? e. destruct p. destruct q. exact e. Defined.

Definition path_inv_rotate_rl {X} {a b c:X} (p:a = b) (r:b = c) (q:a = c) :
  p @ r = q -> r = !p @ q.
Proof. intros ? ? ? ? ? ? ? e. destruct p. destruct q. exact e. Defined.

Definition path_inv_rotate_2 {X} {a b c d:X} (p:a = b) (p':c = d) (q:a = c) (q':b = d) :
  q @ p' = p @ q' -> p' @ ! q' = !q @ p.
Proof. intros ? ? ? ? ? ? ? ? ?. destruct q,q'. simpl.
       repeat rewrite pathscomp0rid. apply idfun. Defined.

Definition path_comp_inv_inv {X} {a b c:X} (p:a = b) (q:b = c) :
  ! q @ ! p = ! (p @ q).
Proof. intros. destruct p,q. reflexivity. Defined.

(** ** Pairs *)

Definition pr2_of_hfiberpair {X Y} {f:X->Y} {x:X} {y:Y} {e:f x = y} :
  pr2 (hfiberpair f x e) = e.
Proof. reflexivity. Defined.

Definition pr2_of_pair {X} {P:X->Type} (x:X) (p:P x) : pr2 (tpair P x p) = p.
Proof. reflexivity. Defined.

Definition pr2_of_weqpair {X Y} (f:X->Y) (i:isweq f) : pr2 (weqpair f i) = i.
Proof. reflexivity. Defined.

(** ** Paths between pairs *)

Definition pair_path_in2 {X} (P:X->Type) {x:X} {p q:P x} (e:p = q) : x,,p = x,,q.
Proof. intros. destruct e. reflexivity. Defined.

Lemma total2_paths2' {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1} 
    {a2 : A} {b2 : B a2} (p : a1 = a2) 
    (q : b1 = transportb (fun x => B x) p b2) : 
    tpair (fun x => B x) a1 b1 = tpair (fun x => B x) a2 b2.
Proof. intros. destruct p. apply pair_path_in2. exact q. Defined.

(* We prefer [pair_path_props] to [total2_paths2]. *)
Definition pair_path_props {X} {P:X->Type} {x y:X} {p:P x} {q:P y} :
  x = y -> (∀ z, isaprop (P z)) -> x,,p = y,,q.
Proof. intros ? ? ? ? ? ? e is. 
       exact (total2_paths2 e (pr1 (is _ _ _))). Defined.

Definition pair_path2 {A} {B:A->UU} {a a1 a2} {b1:B a1} {b2:B a2}
           (p:a1 = a) (q:a2 = a) (e:p#b1 = q#b2) : a1,,b1 = a2,,b2.
Proof. intros. destruct p,q; compute in e. destruct e. reflexivity. Defined.

Lemma simple_pair_path {X Y} {x x':X} {y y':Y} (p : x = x') (q : y = y') :
  x,,y = x',,y'.
Proof. intros. destruct p. destruct q. apply idpath. Defined.

(** ** Projections from pair types *)

Definition pair_path_in2_comp1 {X} (P:X->Type) {x:X} {p q:P x} (e:p = q) : 
  ap pr1 (pair_path_in2 P e) = idpath x.
Proof. intros. destruct e. reflexivity. Defined.

Definition ap_pr2 {X} {P:X->UU} {w w':totalSpace P} (p : w = w') :
  transportf P (ap pr1 p) (pr2 w) = pr2 w'.
Proof. intros. destruct p. reflexivity. Defined.

Definition total2_paths2_comp1 {X} {Y:X->Type} {x} {y:Y x} {x'} {y':Y x'}
           (p:x = x') (q:p#y = y') : ap pr1 (total2_paths2 p q) = p.
Proof. intros. destruct p. destruct q. reflexivity. Defined.

Definition total2_paths2_comp2 {X} {Y:X->Type} {x} {y:Y x} {x'} {y':Y x'}
           (p:x = x') (q:p#y = y') :
  ! app (total2_paths2_comp1 p q) y @ ap_pr2 (total2_paths2 p q) = q.
Proof. intros. destruct p, q. reflexivity. Defined.

(** ** Maps from pair types *)

Definition from_total2 {X} {P:X->Type} {Y} : (∀ x, P x->Y) -> totalSpace P -> Y.
Proof. intros ? ? ? f [x p]. exact (f x p). Defined.

(** ** Sections and functions *)

Definition Section {T} (P:T->UU) := ∀ t:T, P t.

Definition homotsec {T} {P:T->UU} (f g:Section P) := ∀ t, f t = g t.

Definition evalat {T} {P:T->UU} (t:T) (f:Section P) := f t.

Definition apevalat {T} {P:T->UU} (t:T) {f g:Section P}
  : f = g -> f t = g t
  := ap (evalat t).

Definition apfun {X Y} {f f':X->Y} (p:f = f') {x x'} (q:x = x') : f x = f' x'.
  intros. destruct q. exact (apevalat x p). Defined.

Definition aptwice {X Y Z} (f:X->Y->Z) {a a' b b'} (p:a = a') (q:b = b') : f a b = f a' b'.
  intros. exact (apfun (ap f p) q). Defined.

Definition fromemptysec { X : empty -> UU } (nothing:empty) : X nothing.
(* compare with [fromempty] in u00 *)
Proof. intros X H.  destruct H. Defined. 

Definition ap_idpath {X Y} {f:X->Y} {x:X} : ap f (idpath x) = idpath (f x).
Proof. intros. reflexivity. Defined.

(** ** Transport *)

Definition transport_type_path {X Y:Type} (p:X = Y) (x:X) : 
  transportf (fun T:Type => T) p x = cast p x.
Proof. intros. destruct p. reflexivity. Defined.

Definition idpath_transportf {X} (P:X->Type) {x:X} (p:P x) :
  transportf P (idpath x) p = p.
Proof. reflexivity. Defined.

Definition transportbfinv {T} (P:T->Type) {t u:T} (e:t = u) (p:P t) : e#'e#p = p.
Proof. intros. destruct e. reflexivity. Defined.

Definition transportfbinv {T} (P:T->Type) {t u:T} (e:t = u) (p:P u) : e#e#'p = p.
Proof. intros. destruct e. reflexivity. Defined.

Lemma transportf_fun_idpath {X Y} {f:X->Y} x x' (w:x = x') (t:f x = f x) :
              transportf (fun x' => f x' = f x) w (idpath (f x)) = ap f (!w).
Proof. intros ? ? k. destruct w. reflexivity. Qed.

Definition transport_fun_path {X Y} {f g:X->Y} {x x':X} {p:x = x'} {e:f x = g x} {e':f x' = g x'} :
  e @ ap g p = ap f p @ e' -> 
  transportf (fun x => f x = g x) p e = e'.
Proof. intros ? ? ? ? ? ? ? ? ? k. destruct p. rewrite ap_idpath in k. rewrite ap_idpath in k.
       rewrite pathscomp0rid in k. exact k. Defined.

Definition transportf_pathsinv0 {X} (P:X->UU) {x y:X} (p:x = y) (u:P x) (v:P y) :
  !p # v = u -> p # u = v.
Proof. intros ? ? ? ? ? ? ? e. destruct p, e. reflexivity. Defined.

Definition transportf_pathsinv0' {X} (P:X->UU) {x y:X} (p:x = y) (u:P x) (v:P y) :
  p # u = v -> !p # v = u.
Proof. intros ? ? ? ? ? ? ? e. destruct p, e. reflexivity. Defined.

Lemma transport_idfun {X} (P:X->UU) {x y:X} (p:x = y) (u:P x) : 
  transportf P p u = transportf (idfun _) (ap P p) u.
(* same as HoTT.PathGroupoids.transport_idmap_ap *)
Proof. intros. destruct p. reflexivity. Defined.

Lemma transport_functions {X} {Y:X->Type} {Z:∀ x (y:Y x), Type}
      {f f':Section Y} (p:f = f') (z:∀ x, Z x (f x)) x :
    transportf (fun f => ∀ x, Z x (f x)) p z x =
    transportf (Z x) (toforallpaths _ _ _ p x) (z x).
Proof. intros. destruct p. reflexivity. Defined.

Definition transport_funapp {T} {X Y:T->Type} 
           (f:∀ t, X t -> Y t) (x:∀ t, X t)
           {t t':T} (p:t = t') : 
  transportf _ p ((f t)(x t)) 
  = (transportf (fun t => X t -> Y t) p (f t)) (transportf _ p (x t)).
Proof. intros. destruct p. reflexivity. Defined.

Definition helper_A {T} {Y} (P:T->Y->Type) {y y':Y} (k:∀ t, P t y) (e:y = y') t :
  transportf (fun y => P t y) e (k t)
  = 
  (transportf (fun y => ∀ t, P t y) e k) t.
Proof. intros. destruct e. reflexivity. Defined.

Definition helper_B {T} {Y} (f:T->Y) {y y':Y} (k:∀ t, y = f t) (e:y = y') t :
  transportf (fun y => y = f t) e (k t)
  = 
  (transportf (fun y => ∀ t, y = f t) e k) t.
Proof. intros. exact (helper_A _ k e t). Defined.

Definition transport_invweq {T} {X Y:T->Type} (f:∀ t, weq (X t) (Y t))
           {t t':T} (p:t = t') : 
  transportf (fun t => weq (Y t) (X t)) p (invweq (f t))
  = 
  invweq (transportf (fun t => weq (X t) (Y t)) p (f t)).
Proof. intros. destruct p. reflexivity. Defined.

Definition transport_invmap {T} {X Y:T->Type} (f:∀ t, weq (X t) (Y t))
           {t t':T} (p:t=t') : 
  transportf (fun t => Y t -> X t) p (invmap (f t))
  = 
  invmap (transportf (fun t => weq (X t) (Y t)) p (f t)).
Proof. intros. destruct p. reflexivity. Defined.

Definition ap_fun_fun_natl {X Y Z} {g g':X->Y} {f f':Y->Z} 
           (q:homot g g') (p:homot f f') x :
  ap f (q x) @ p (g' x) = p (g x) @ ap f' (q x).
Proof. intros. destruct (q x). simpl. rewrite pathscomp0rid. reflexivity. Defined.

Definition ap_fun_fun_fun_natl {X Y Z W} {g g':X->Y}
           (q:homot g g') (h:Y->Z) {f f':Z->W} (p:homot f f') x :
  ap f (ap h (q x)) @ p (h (g' x)) = p (h (g x)) @ ap f' (ap h (q x)).
Proof. intros. destruct (q x). simpl. rewrite pathscomp0rid. reflexivity. Defined.

Definition ap_natl {X Y} {f:X->Y}
           {x x' x'':X} {p:x = x'} {q:x' = x''}
           {p':f x = f x'} {q':f x' = f x''}
           (r:ap f p = p') (s:ap f q = q') :
  ap f (p @ q) = p' @ q'.
Proof. intros. destruct r, s. apply maponpathscomp0. Defined.

Definition ap_natl' {X Y} {f:X->Y}
           {x x' x'':X} {p:x' = x} {q:x' = x''}
           {p':f x' = f x} {q':f x' = f x''}
           (r:ap f p = p') (s:ap f q = q') :
  ap f (!p @ q) = (!p') @ q'.
Proof. intros. destruct r, s, p, q. reflexivity. Defined.

  (** *** Double transport *)

  Definition transportf2 {X} {Y:X->Type} (Z:∀ x, Y x->Type)
             {x x'} (p:x = x')
             (y:Y x) (z:Z x y) : Z x' (p#y).
  Proof. intros. destruct p. exact z. Defined.

  Definition transportb2 {X} {Y:X->Type} (Z:∀ x, Y x->Type)
             {x x'} (p:x=x')
             (y':Y x') (z':Z x' y') : Z x (p#'y').
  Proof. intros. destruct p. exact z'. Defined.

  Definition ap_pr1_pr2 {X} {P:X->UU} {Q:∀ x, P x->Type}
             {w w': Σ x p, Q x p}
             (p : w = w') :
    transportf P (ap pr1 p) (pr1 (pr2 w)) = pr1 (pr2 w').
  Proof. intros. destruct p. reflexivity. Defined.

  (** *** Transport a pair *)

  Definition transportf_pair X (Y:X->Type) (Z:∀ x, Y x->Type)
             x x' (p:x = x') (y:Y x) (z:Z x y) :
    transportf (fun x => totalSpace (Z x)) p (tpair (Z x) y z)
    =
    tpair (Z x') (transportf Y p y) (transportf2 _ p y z).
  Proof. intros. destruct p. reflexivity. Defined.

  Definition transportb_pair X (Y:X->Type) (Z:∀ x, Y x->Type)
             x x' (p:x = x')
             (y':Y x') (z':Z x' y') 
             (z' : (Z x' y')) :
    transportb (fun x => totalSpace (Z x)) p (tpair (Z x') y' z')
    =
    tpair (Z x) (transportb Y p y') (transportb2 _ p y' z').
  Proof. intros. destruct p. reflexivity. Defined.

(** ** Decidability *)

Definition decidable X := coprod X (not X).
Definition LEM := ∀ P, isaprop P -> decidable P.
Lemma LEM_for_sets X : LEM -> isaset X -> isdeceq X.
Proof. intros X lem is x y. exact (lem (x = y) (is x y)). Qed.

(** ** h-levels and paths *)

Lemma isaprop_wma_inhab X : (X -> isaprop X) -> isaprop X.
Proof. intros ? f. apply invproofirrelevance. intros x y. apply (f x). Qed.

Lemma isaprop_wma_inhab' X : (X -> iscontr X) -> isaprop X.
Proof. intros ? f. apply isaprop_wma_inhab. intro x. apply isapropifcontr. 
       apply (f x). Qed.

Goal ∀ (X:hSet) (x y:X) (p q:x = y), p = q.
Proof. intros. apply setproperty. Defined.

Goal ∀ (X:Type) (x y:X) (p q:x = y), isaset X -> p = q.
Proof. intros ? ? ? ? ? is. apply is. Defined.

Definition funset X (Y:hSet) : hSet
  := hSetpair (X->Y) (impredfun 2 _ _ (setproperty Y)).

(** ** Null homotopies *)

Definition nullHomotopyTo {X Y} (f:X->Y) (y:Y) := ∀ x:X, f x = y.
Definition NullHomotopyTo {X Y} (f:X->Y) := totalSpace (nullHomotopyTo f).
Definition NullHomotopyTo_center {X Y} (f:X->Y) : NullHomotopyTo f -> Y := pr1.
Definition NullHomotopyTo_path {X Y} {f:X->Y} (r:NullHomotopyTo f) := pr2 r.

Definition nullHomotopyFrom {X Y} (f:X->Y) (y:Y) := ∀ x:X, y = f x.
Definition NullHomotopyFrom {X Y} (f:X->Y) := totalSpace (nullHomotopyFrom f).
Definition NullHomotopyFrom_center {X Y} (f:X->Y) : NullHomotopyFrom f -> Y := pr1.
Definition NullHomotopyFrom_path {X Y} {f:X->Y} (r:NullHomotopyFrom f) := pr2 r.

Definition nullHomotopyTo_transport {X Y} {f:X->Y} {y:Y} (h : nullHomotopyTo f y)
           {y':Y} (p:y = y') (x:X) : (p # h) x = h x @ p.
Proof. intros. destruct p. apply pathsinv0. apply pathscomp0rid. Defined.

Lemma isaset_NullHomotopyTo {X Y} (i:isaset Y) (f:X->Y) : isaset (NullHomotopyTo f).
Proof. intros. apply (isofhleveltotal2 2). { apply i. }
       intros y. apply impred; intros x. apply isasetaprop. apply i. Defined.

Lemma isaprop_nullHomotopyTo {X Y} (is:isaset Y) (f:X->Y) (y:Y) :
  isaprop (nullHomotopyTo f y).
Proof. intros ? ? ? ? ?. apply impred; intros x. apply is. Defined.

Lemma isaprop_NullHomotopyTo_0 {X} {Y} (is:isaset Y) (f:X->Y) : 
  X -> isaprop (NullHomotopyTo f).
(** The point of X is needed, for when X is empty, then NullHomotopyTo f is
    equivalent to Y. *)
Proof. intros ? ? ? ? x. apply invproofirrelevance. intros [r i] [s j].
       apply (pair_path_props (!i x @ j x)).
       apply (isaprop_nullHomotopyTo is). Defined.

(** ** Squashing *)

Notation squash := ishinh_UU.
Notation squash_fun := hinhfun.
Lemma squash_fun2 {X Y Z} : (X -> Y -> Z) -> (squash X -> squash Y -> squash Z).
Proof. intros ? ? ? f x y P h.
  exact (y P 
           (x (hProppair 
                 (Y -> P) 
                 (impred 1 _ (fun _ => propproperty P))) 
              (fun a b => h (f a b)))). Qed.

Definition squash_element {X} : X -> squash X.
Proof. intros ? x P f. exact (f x). Defined.

Definition squash_to_prop {X Y} : squash X -> isaprop Y -> (X -> Y) -> Y.
  intros ? ? h is f. exact (h (Y,,is) f). Defined.

Definition squash_to_prop_compute {X Y} (x:X) (is:isaprop Y) (f:X->Y) :
  squash_to_prop (squash_element x) is f = f x.
Proof. reflexivity. Defined.

Lemma isaprop_squash X : isaprop (squash X).
Proof. prop_logic. Qed.

Lemma squash_path {X} (x y:X) : squash_element x = squash_element y.
Proof. intros. apply isaprop_squash. Defined.

Lemma factor_through_squash {X Q} : isaprop Q -> (X -> Q) -> (squash X -> Q).
Proof. intros ? ? i f h. apply (h (hProppair _ i)). intro x. exact (f x). Defined.

Lemma isaprop_NullHomotopyTo {X} {Y} (is:isaset Y) (f:X->Y) :
  squash X -> isaprop (NullHomotopyTo f).
Proof. intros ? ? ? ?. apply factor_through_squash. apply isapropisaprop. 
       apply isaprop_NullHomotopyTo_0. exact is. Defined.

(** We can get a map from 'squash X' to any type 'Y' provided paths
    are given that allow us to map first into a cone in 'Y'.  *)

Definition cone_squash_map {X Y} (f:X->Y) (y:Y) : 
  nullHomotopyTo f y -> squash X -> Y.
Proof. intros ? ? ? ? e h. 
       exact (point_from (h (paths_to_prop y) (fun x => f x,,e x))). Defined.

Goal ∀ X Y (y:Y) (f:X->Y) (e:∀ m:X, f m = y),
       f = funcomp squash_element (cone_squash_map f y e).
Proof. reflexivity. Qed.

(** ** Factoring maps through squash *)
 
Lemma squash_uniqueness {X} (x:X) (h:squash X) : squash_element x = h.
Proof. intros. apply isaprop_squash. Qed.

Goal ∀ X Q (i:isaprop Q) (f:X -> Q) (x:X),
   factor_through_squash i f (squash_element x) = f x.
Proof. reflexivity. Defined.

Lemma factor_dep_through_squash {X} {Q:squash X->UU} : 
  (∀ h, isaprop (Q h)) -> 
  (∀ x, Q(squash_element x)) -> 
  (∀ h, Q h).
Proof.
  intros ? ? i f ?.  apply (h (hProppair (Q h) (i h))). 
  intro x. simpl. destruct (squash_uniqueness x h). exact (f x).
Defined.

Lemma factor_through_squash_hProp {X} : ∀ hQ:hProp, (X -> hQ) -> (squash X -> hQ).
Proof. intros ? [Q i] f h. apply h. assumption. Defined.

Lemma funspace_isaset {X Y} : isaset Y -> isaset (X -> Y).
Proof. intros ? ? is. apply (impredfun 2). assumption. Defined.    

Lemma iscontr_if_inhab_prop {P} : isaprop P -> P -> iscontr P.
Proof. intros ? i p. exists p. intros p'. apply i. Defined.

(** ** Show that squashing is a set-quotient *)

Definition squash_to_set {X Y} (is:isaset Y)
  (f:X->Y) (e:∀ x x', f x = f x') : squash X -> Y.
Proof. intros ? ? ? ? ? h. apply (NullHomotopyTo_center f).
  refine (factor_through_squash _ _ h).
  { apply isaprop_NullHomotopyTo. exact is. exact h. }
  intros x. exists (f x). intros x'. apply e. Defined.

(** Verify that the map factors judgmentally. *)
Goal ∀ X Y (is:isaset Y) (f:X->Y) (e:∀ x x', f x = f x'),
       f = funcomp squash_element (squash_to_set is f e).
Proof. reflexivity. Qed.

(** Note: the hypothesis in [squash_to_set] that Y is a set cannot be removed.
    Consider, for example, the inclusion map f for the vertices of a triangle,
    and let e be given by the edges and reflexivity. *)

(** From Voevodsky, an idea for another proof of squash_to_set:

    "I think one can get another proof using "isapropimeqclass" (hSet.v) with "R :=
    fun x1 x1 => unit". This Lemma will show that under your assumptions "Im f" is
    a proposition. Therefore "X -> Im f" factors through "squash X"." 

    Here is a start.

Definition True := hProppair unit (isapropifcontr iscontrunit).

Proof. intros ? ? ? ? ?. 
       set (R := (fun _ _ => True) : hrel X).
       assert (ic : iscomprelfun R f). { intros x x' _. exact (e x x'). }
       assert (im := isapropimeqclass R (hSetpair Y is) f ic).
Defined.
*)

Lemma squash_map_uniqueness {X S} (ip : isaset S) (g g' : squash X -> S) : 
  g ∘ squash_element ~ g' ∘ squash_element -> g ~ g'.
Proof.
  intros ? ? ? ? ? h.
  set ( Q := fun y => g y = g' y ).
  unfold homot.
  apply (@factor_dep_through_squash X). intros y. apply ip.
  intro x. apply h.
Qed.

Lemma squash_map_epi {X S} (ip : isaset S) (g g' : squash X -> S) : 
  g ∘ squash_element = g'∘ squash_element -> g = g'.
Proof.
  intros ? ? ? ? ? e.
  apply funextsec.
  apply squash_map_uniqueness. exact ip.
  intro x. destruct e. apply idpath.
Qed.

Lemma isaxiomfuncontr { X : UU } (P:X -> UU) : 
  isaprop ((∀ x:X, iscontr (P x)) -> iscontr (∀ x:X, P x)).
Proof.                         (* the statement of [funcontr] is a proposition *)
  intros. apply impred; intro. apply isapropiscontr. Defined.

(** ** Connected types *)

Definition isconnected X := ∀ (x y:X), nonempty (x = y).

Lemma base_connected {X} (t:X) : (∀ y:X, nonempty (t = y)) -> isconnected X.
Proof. intros ? ? p x y. assert (a := p x). assert (b := p y). clear p.
       apply (squash_to_prop a). apply propproperty. clear a. intros a.
       apply (squash_to_prop b). apply propproperty. clear b. intros b.
       apply hinhpr. exact (!a@b). Defined.

(** ** Applications of univalence *)

(** Compare the following two definitions with [transport_type_path]. *)

Require Import UniMath.Foundations.FunctionalExtensionality.

Definition pr1_eqweqmap { X Y } ( e: X = Y ) : cast e = pr1 (eqweqmap e).
Proof. intros. destruct e. reflexivity. Defined.

Definition pr1_eqweqmap2 { X Y } ( e: X = Y ) : 
  pr1 (eqweqmap e) = transportf (fun T:Type => T) e.
Proof. intros. destruct e. reflexivity. Defined.

Definition weqonsec {X Y} (P:X->Type) (Q:Y->Type)
           (f:X ≃ Y) (g:∀ x, weq (P x) (Q (f x))) :
  weq (Section P) (Section Q).
Proof. intros.
       exact (weqcomp (weqonsecfibers P (fun x => Q(f x)) g)
                      (invweq (weqonsecbase Q f))). Defined.

Definition weq_transportf {X} (P:X->Type) {x y:X} (p:x = y) : weq (P x) (P y).
Proof. intros. destruct p. apply idweq. Defined.

Definition weq_transportf_comp {X} (P:X->Type) {x y:X} (p:x = y) (f:Section P) :
  weq_transportf P p (f x) = f y.
Proof. intros. destruct p. reflexivity. Defined.

Definition weqonpaths2 {X Y} (w:X ≃ Y) {x x':X} {y y':Y} :
  w x = y -> w x' = y' -> weq (x = x') (y = y').
Proof. intros ? ? ? ? ? ? ? p q. destruct p,q. apply weqonpaths. Defined.

Definition eqweqmap_ap {T} (P:T->Type) {t t':T} (e:t = t') (f:Section P) :
  eqweqmap (ap P e) (f t) = f t'. (* move near eqweqmap *)
Proof. intros. destruct e. reflexivity. Defined.

Definition eqweqmap_ap' {T} (P:T->Type) {t t':T} (e:t = t') (f:Section P) :
  invmap (eqweqmap (ap P e)) (f t') = f t. (* move near eqweqmap *)
Proof. intros. destruct e. reflexivity. Defined.

Definition weqpath_transport {X Y} (w:X ≃ Y) (x:X) :
  transportf (fun T => T) (weqtopaths w) = pr1 w.
Proof. intros. exact (!pr1_eqweqmap2 _ @ ap pr1 (weqpathsweq w)). Defined.

Definition weqpath_cast {X Y} (w:X ≃ Y) (x:X) : cast (weqtopaths w) = w.
Proof. intros. exact (pr1_eqweqmap _ @ ap pr1 (weqpathsweq w)). Defined.

Definition swequiv {X Y} (f:X ≃ Y) {x y} : y = f x -> invweq f y = x.
Proof. intros ? ? ? ? ? p. exact (ap (invweq f) p @ homotinvweqweq f x). Defined.

Definition swequiv' {X Y} (f:X ≃ Y) {x y} : invweq f y = x -> y = f x.
Proof. intros ? ? ? ? ? p. exact (! homotweqinvweq f y @ ap f p). Defined.

Definition weqbandfrel {X Y T} 
           (e:Y->T) (t:T) (f : X ≃ Y) 
           (P:X -> Type) (Q: Y -> Type)
           (g:∀ x:X, weq (P x) (Q (f x))) :
  weq (hfiber (fun xp:totalSpace P => e(f(pr1 xp))) t)
      (hfiber (fun yq:totalSpace Q => e(  pr1 yq )) t).
Proof. intros. refine (weqbandf (weqbandf f _ _ g) _ _ _).
       intros [x p]. simpl. apply idweq. Defined.

Definition weq_over_sections {S T} (w:S ≃ T) 
           {s0:S} {t0:T} (k:w s0 = t0)
           {P:T->Type} 
           (p0:P t0) (pw0:P(w s0)) (l:k#pw0 = p0)
           (H:Section P -> Type) 
           (J:Section (funcomp w P) -> Type)
           (g:∀ f:Section P, weq (H f) (J (maponsec1 P w f))) :
  weq (hfiber (fun fh:totalSpace H => pr1 fh t0) p0 )
      (hfiber (fun fh:totalSpace J => pr1 fh s0) pw0).
Proof. intros. refine (weqbandf _ _ _ _).
       { refine (weqbandf _ _ _ _).
         { exact (weqonsecbase P w). }
         { unfold weqonsecbase; simpl. exact g. } }
       { intros [f h]. simpl. unfold maponsec1; simpl.
         destruct k, l; simpl. unfold transportf; simpl.
         unfold idfun; simpl. apply idweq. } Defined.

Definition weq_total2_prod {X Y} (Z:Y->Type) : (Σ y, X × Z y) ≃ (X × Σ y, Z y).
Proof. intros. refine (weqpair _ (gradth _ _ _ _)).
       { intros [y [x z]]. exact (x,,y,,z). }
       { intros [x [y z]]. exact (y,,x,,z). }
       { intros [y [x z]]. reflexivity. }
       { intros [x [y z]]. reflexivity. } Defined.

(** ** Pointed types *)

Definition PointedType := Σ X, X.

Definition pointedType X x := X,,x : PointedType.

Definition underlyingType (X:PointedType) := pr1 X.

Coercion underlyingType : PointedType >-> Sortclass.

Definition basepoint (X:PointedType) := pr2 X.

Definition loopSpace (X:PointedType) := 
  pointedType (basepoint X = basepoint X) (idpath _).

Definition underlyingLoop {X:PointedType} (l:loopSpace X) : basepoint X = basepoint X.
Proof. intros. exact l. Defined.

Definition Ω := loopSpace.

(** ** Direct products with several factors *)

Definition paths3 {X Y Z} {x x':X} {y y':Y} {z z':Z} :
  x = x' -> y = y' -> z = z' -> @paths (_×_×_) (x,,y,,z) (x',,y',,z').
Proof. intros ? ? ? ? ? ? ? ? ? p q r. destruct p, q, r. reflexivity.
Defined.       

Definition paths4 {W X Y Z} {w w':W} {x x':X} {y y':Y} {z z':Z} :
  w = w' -> x = x' -> y = y' -> z = z' -> @paths (_×_×_×_) (w,,x,,y,,z) (w',,x',,y',,z').
Proof. intros ? ? ? ? ? ? ? ? ? ? ? ? o p q r. destruct o, p, q, r. reflexivity.
Defined.

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/Utilities.vo"
End:
*)
