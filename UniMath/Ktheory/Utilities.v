(** * Utilities concerning paths, hlevel, and logic *)

Unset Automatic Introduction.

Require RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.pathnotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import Foundations.hlevel2.hSet.
        Import RezkCompletion.pathnotations.PathNotations.

(* this lemma must be somewhere in Foundations *)
Lemma path_assoc {X} {a b c d:X}
        (f : a == b) (g : b == c) (h : c == d)
      : f @ (g @ h) == (f @ g) @ h.
Proof. intros. destruct f. reflexivity. Defined.
Lemma path_assoc_opaque {X} {a b c d:X} 
        (f : a == b) (g : b == c) (h : c == d)
      : f @ (g @ h) == (f @ g) @ h.
Proof. intros. destruct f. reflexivity. Qed.

Set Default Timeout 50.

Definition two_cases {X Y T} : coprod X Y -> (X->T) -> (Y->T) -> T.
  exact (fun X Y T xy f g => sum_rect (fun _ => T) f g xy). Defined.

Ltac exact_op x := (* from Jason Gross: same as "exact", but with unification the opposite way *)
  let T := type of x in
  let G := match goal with |- ?G => constr:(G) end in
  exact ((@id G : T -> G) x).

Definition paths_from {X} (x:X) := total2 (paths x).
Definition point_to {X} {x:X} : paths_from x -> X := pr1.
Definition paths_from_path {X} {x:X} (w:paths_from x) := pr2 w.
Definition paths' {X} (x:X) := fun y => paths y x.
Definition idpath' {X} (x:X) := idpath x : paths' x x.
Definition paths_to {X} (x:X) := total2 (paths' x).
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

Module Import Notation.
  Notation "'not' X" := (X -> empty) (at level 35).
  Notation "x != y" := (not (x == y)) (at level 40).
  Notation set_to_type := hSet.pr1hSet.
  Notation ap := maponpaths.
  (* see table 3.1 in the coq manual for parsing levels *)
  Notation "f ~ g" := (uu0.homot f g) (at level 70).
  Notation "g ∘ f" := (uu0.funcomp f g) (at level 50).
  Notation "f ;; g" := (uu0.funcomp f g) (at level 50).
  Notation "x ,, y" := (tpair _ x y) (at level 69, right associativity).
  (* funcomp' is like funcomp, but with the arguments in the other order *)
  Definition funcomp' { X Y Z : UU } ( g : Y -> Z ) ( f : X -> Y ) := fun x : X => g ( f x ) . 
  Notation "p # x" := (transportf _ p x) (right associativity, at level 65).
  Notation "p #' x" := (transportb _ p x) (right associativity, at level 65).
End Notation.

Module Import NatNotation.
  Require hnat.
  Notation "m <= n" := (hnat.natleh m n).
  Notation "m >= n" := (hnat.natgeh m n).
  Notation "m > n" := (hnat.natgth m n).
  Notation "m < n" := (hnat.natlth m n).
End NatNotation.

(* We prefer [pair_path_props] to [total2_paths2]. *)
Definition pair_path_props {X:UU} {P:X->UU} {x y:X} {p:P x} {q:P y} :
  x==y -> (forall z, isaprop (P z)) -> x,,p==y,,q.
Proof. intros ? ? ? ? ? ? e is. 
       exact (total2_paths2 e (pr1 (is _ _ _))). Defined.

Definition pair_path2 {A} {B:A->UU} {a a1 a2} {b1:B a1} {b2:B a2}
           (p:a1==a) (q:a2==a) (e:p#b1 == q#b2) : a1,,b1 == a2,,b2.
Proof. intros. destruct p,q; compute in e. destruct e. reflexivity. Defined.

Definition cast {T U:Type} : T==U -> T->U.
Proof. intros ? ? p t. destruct p. exact t. Defined.

Definition transport_type_path {X Y:Type} (p:X==Y) (x:X) : 
  transportf (fun T:Type => T) p x == cast p x.
Proof. intros. destruct p. reflexivity. Defined.

Definition app {X} {P:X->Type} {x x':X} {e e':x==x'} (q:e==e') (p:P x) : 
   e#p==e'#p.
Proof. intros. destruct q. reflexivity. Defined.

(** * Projections from pair types *)

Definition pr2_pair {X} {P:X->UU} {w w':total2 P} (p : w == w') :
  transportf P (ap pr1 p) (pr2 w) == pr2 w'.
Proof. intros. destruct p. reflexivity. Defined.

Definition total2_paths2_comp1 {X} {Y:X->Type} {x} {y:Y x} {x'} {y':Y x'}
           (p:x==x') (q:p#y==y') : ap pr1 (total2_paths2 p q) == p.
Proof. intros. destruct p. destruct q. reflexivity. Defined.

Definition total2_paths2_comp2 {X} {Y:X->Type} {x} {y:Y x} {x'} {y':Y x'}
           (p:x==x') (q:p#y==y') :
  ! app (total2_paths2_comp1 p q) y @ pr2_pair (total2_paths2 p q) == q.
Proof. intros. destruct p, q. reflexivity. Defined.

(** ** Maps from pair types *)

Definition from_total2 {X} {P:X->Type} {Y} : (forall x, P x->Y) -> total2 P -> Y.
Proof. intros ? ? ? f [x p]. exact (f x p). Defined.

(** * Sections *)

Definition sections {T} (P:T->UU) := forall t:T, P t.
Definition homotsec {T} {P:T->UU} (f g:sections P) := forall t, f t == g t.
Definition evalat {T} {U} (t:T) (f:T->U) := f t.
Definition apevalat {T} {U} (t:T) {f g:T->U}
  : f == g -> f t == g t
  := ap (evalat t).
Definition evalsecat {T} {P:T->UU} (t:T) (f:sections P) := f t.
Definition apevalsecat {T} {P:T->UU} (t:T) {f g:sections P}
  : f == g -> f t == g t
  := ap (evalsecat t).
Definition apfun {X Y} {f f':X->Y} (p:f==f') {x x'} (q:x==x') : f x == f' x'.
  intros. destruct q. exact (apevalat x p). Defined.
Definition aptwice {X Y Z} (f:X->Y->Z) {a a' b b'} (p:a==a') (q:b==b') : f a b == f a' b'.
  intros. exact (apfun (ap f p) q). Defined.
Definition fromemptysec { X : empty -> UU } (nothing:empty) : X nothing.
(* compare with [fromempty] in u00 *)
Proof. intros X H.  destruct H. Defined. 

(** ** Transport *)

Lemma transport_idfun {X} (P:X->UU) {x y:X} (p:x==y) (u:P x) : 
  transportf P p u == transportf (idfun _) (ap P p) u.
(* same as HoTT.PathGroupoids.transport_idmap_ap *)
Proof. intros. destruct p. reflexivity. Defined.

Lemma transport_functions {X} {Y:X->Type} {Z:forall x (y:Y x), Type}
      {f f':sections Y} (p:f==f') (z:forall x, Z x (f x)) x :
    (transportf (fun f => forall x, Z x (f x)) p z) x ==
    transportf (Z x) (toforallpaths _ _ _ p x) (z x).
Proof. intros. destruct p. reflexivity. Defined.

(** * Decidability *)

Definition decidable X := coprod X (not X).
Definition LEM := forall P, isaprop P -> decidable P.
Lemma LEM_for_sets X : LEM -> isaset X -> isdeceq X.
Proof. intros X lem is x y. exact (lem (x==y) (is x y)). Qed.

(** * h-levels and paths *)

Definition post_cat {X} {x y z:X} {q:y==z} : x==y -> x==z.
Proof. intros ? ? ? ? p q. exact (pathscomp0 q p). Defined.
Definition pre_cat {X} {x y z:X} {q:x==y} : y==z -> x==z.
Proof. intros ? ? ? ? p q. exact (pathscomp0 p q). Defined.

Lemma isaprop_wma_inhab X : (X -> isaprop X) -> isaprop X.
Proof. intros ? f. apply invproofirrelevance. intros x y. apply (f x). Qed.
Lemma isaprop_wma_inhab' X : (X -> iscontr X) -> isaprop X.
Proof. intros ? f. apply isaprop_wma_inhab. intro x. apply isapropifcontr. 
       apply (f x). Qed.

Ltac prop_logic := 
  intros; simpl;
  repeat (try (apply isapropdirprod);try (apply isapropishinh);apply impred ;intro); 
  try (apply isapropiscontr); try assumption.

Definition propProperty (P:hProp) := pr2 P : isaprop (pr1 P).

Ltac intermediate_path x := apply @pathscomp0 with (b := x).

Ltac intermediate_weq y := apply @weqcomp with (Y := y).

Definition isaset_if_isofhlevel2 {X} : isofhlevel 2 X -> isaset X.
(* The use of this lemma ahead of something like 'impred' can be avoided by
   providing 2 as first argument. *)
Proof. trivial. Qed.

Definition isofhlevel2_if_isaset {X} : isaset X -> isofhlevel 2 X.
Proof. trivial. Qed.

Definition isaprop_hProp (X:hProp) : isaprop X.
Proof. intro. exact (pr2 X). Qed.

Definition the {T} : iscontr T -> T.
Proof. intros ? is. exact (pr1 is). Defined.

Definition uniqueness {T} (i:iscontr T) (t:T) : t == the i.
Proof. intros. exact (pr2 i t). Defined.

Definition uniqueness' {T} (i:iscontr T) (t:T) : the i == t.
Proof. intros. exact (! (pr2 i t)). Defined.

Definition equality_proof_irrelevance {X:hSet} {x y:X} (p q:x==y) : p==q.
Proof. intros. destruct (the (setproperty _ _ _ p q)). reflexivity. Qed.

Definition equality_proof_irrelevance' {X:Type} {x y:X} (p q:x==y) : 
  isaset X -> p==q.
Proof. intros ? ? ? ? ? is. apply is. Defined.

Definition funset X (Y:hSet) : hSet := hSetpair (X->Y) (impredfun 2 _ _ (pr2 Y)).

Definition path_start {X} {x x':X} (p:x == x') := x.
Definition path_end {X} {x x':X} (p:x == x') := x'.

Definition pr1hSet_injectivity (X Y:hSet) : weq (X==Y) (pr1hSet X==pr1hSet Y).
Proof. intros. apply weqonpathsincl. apply isinclpr1; intro T.
       apply isapropisaset. Defined.

Module AdjointEquivalence.
  Record data X Y := make {
           f :> X -> Y; g : Y -> X;
           p : forall y, f(g y) == y;
           q : forall x, g(f x) == x;
           h : forall x, ap f (q x) == p(f x) }.
End AdjointEquivalence.

Lemma helper {X Y} {f:X->Y} x x' (w:x==x') (t:f x==f x) :
              transportf (fun x' => f x' == f x) w (idpath (f x)) == ap f (!w).
Proof. intros ? ? k. destruct w. reflexivity. Qed.

Definition weq_to_AdjointEquivalence X Y : weq X Y -> AdjointEquivalence.data X Y.
  intros ? ? [f r].
  set (g := fun y => hfiberpr1 f y (the (r y))).
  set (p := fun y => pr2 (pr1 (r y))).
  set (L := fun x => pr2 (r (f x)) (hfiberpair f x (idpath (f x)))).
  set (q := fun x => ap pr1 (L x)).
  set (q' := fun x => !q x).  
  refine (AdjointEquivalence.make X Y f g p q' _).
  intro x.
  exact ( !(helper x (pr1 (pr1 (r (f x)))) (q x) (idpath (f x)))
               @ (pr2_pair (L x))).
Defined.

Definition AdjointEquivalence_to_weq X Y : AdjointEquivalence.data X Y -> weq X Y.
Proof. intros ? ? [f g p q h]. exists f. unfold isweq. intro y.
       exists (g y,,p y). intros [x r]. destruct r. 
       apply (total2_paths2 (!q x)). refine (_ @ h x). generalize (q x); intro qx.
       destruct qx. reflexivity. Defined.

Module AdjointEquivalence'.
  Record data X Y := make {
         f :> X -> Y; g : Y -> X;
         p : forall y, f(g y) == y;
         q : forall x, x == g(f x);
         h : forall x y (r:f x == y), 
             transportf (fun x':X => f x'==y) (q x @ ap g r) r == p y }.
End AdjointEquivalence'.

Definition AdjointEquivalence_to_weq' X Y : AdjointEquivalence'.data X Y -> weq X Y.
Proof. intros ? ? a. destruct a. exists f. unfold isweq. intro y.
       exists (g y,,p y). 
       intros [x r]. exact (total2_paths2 (q x @ ap g r) (h x y r)). Defined.

(* Definition weqfunsrc {X Y} {P:Y->Type} (w:AdjointEquivalence'.data X Y) :  *)
(*   AdjointEquivalence'.data  *)
(*     (forall y, P y)  *)
(*     (forall x, P (AdjointEquivalence'.f _ _ w x)). *)
(* Proof. intros ? ? ? [f g p q h]; simpl. *)
(*        refine (AdjointEquivalence'.make _ _ _ _ _ _ _). *)
(*        { intros G x. exact (G (f x)). } *)
(*        { intros F y. exact (p y # F (g y)). } *)
(*        { intros F.  *)
(*          (* Unset Printing Implicits. Unset Printing Notations. *) *)
(*          apply funextsec; intro x. *)

(* Defined. *)

(** * Squashing. *)

Notation squash := ishinh_UU.
Notation nonempty := ishinh.
Notation squash_fun := hinhfun.
Lemma squash_fun2 {X Y Z} : (X -> Y -> Z) -> (squash X -> squash Y -> squash Z).
Proof. intros ? ? ? f x y P h.
  exact (y P 
           (x (hProppair 
                 (Y -> P) 
                 (impred 1 _ (fun _ => propProperty P))) 
              (fun a b => h (f a b)))). Qed.

Definition squash_element {X} : X -> squash X.
Proof. intros ? x P f. exact (f x). Defined.

Definition squash_to_prop {X Y} : squash X -> isaprop Y -> (X -> Y) -> Y.
  intros ? ? h is f. exact (h (Y,,is) f). Defined.

Lemma isaprop_squash X : isaprop (squash X).
Proof. prop_logic. Qed.

Lemma squash_path {X} (x y:X) : squash_element x == squash_element y.
Proof. intros. apply isaprop_squash. Defined.

Lemma factor_through_squash {X Q} : isaprop Q -> (X -> Q) -> (squash X -> Q).
Proof. intros ? ? i f h. apply (h (hProppair _ i)). intro x. exact (f x). Defined.

Definition nullHomotopyTo {X Y} (f:X->Y) (y:Y) := forall x:X, f x == y.
Definition NullHomotopyTo {X Y} (f:X->Y) := total2 (nullHomotopyTo f).
Definition NullHomotopyTo_center {X Y} (f:X->Y) : NullHomotopyTo f -> Y := pr1.
Definition NullHomotopyTo_path {X Y} {f:X->Y} (r:NullHomotopyTo f) := pr2 r.

Definition nullHomotopyFrom {X Y} (f:X->Y) (y:Y) := forall x:X, y == f x.
Definition NullHomotopyFrom {X Y} (f:X->Y) := total2 (nullHomotopyFrom f).
Definition NullHomotopyFrom_center {X Y} (f:X->Y) : NullHomotopyFrom f -> Y := pr1.
Definition NullHomotopyFrom_path {X Y} {f:X->Y} (r:NullHomotopyFrom f) := pr2 r.

Definition nullHomotopyTo_transport {X Y} {f:X->Y} {y:Y} (h : nullHomotopyTo f y)
           {y':Y} (p:y==y') (x:X) : (p # h) x == h x @ p.
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

Goal forall X Y (y:Y) (f:X->Y) (e:forall m:X, f m == y),
       f == funcomp squash_element (cone_squash_map f y e).
Proof. reflexivity. Qed.

Definition interval := squash bool.
Definition left := hinhpr _ true : interval.
Definition right := hinhpr _ false : interval.
Definition interval_path : left == right := squash_path true false.
Definition interval_map {Y} {y y':Y} : y == y' -> interval -> Y.
Proof. intros ? ? ? e. set (f := fun t:bool => if t then y else y').
       refine (cone_squash_map f (f false) _).
       intros v. induction v. { exact e. } { reflexivity. } Defined.

(** ** An easy proof of functional extensionality for sections using the interval *)

Definition funextsec2 X (Y:X->Type) (f g:forall x,Y x) :
           (forall x, f x==g x) -> f == g.
Proof. intros ? ? ? ? e.
       exact (maponpaths (fun h x => interval_map (e x) h) interval_path).
Defined.

(** * The real line *)
Require Import Foundations.hlevel2.hz.
Notation ℤ := hz.hzaddabgr.
Definition line := squash ℤ.
Notation ℝ := line.
Definition line_vertex : ℤ -> ℝ := squash_element.
Definition line_path (m n:ℤ) : line_vertex m == line_vertex n := squash_path m n.
Definition line_map {Y} {y:Y} (f:forall m:ℤ, Y) (e:forall m:ℤ, f m == y) :
  line -> Y := cone_squash_map f y e.
Goal forall Y (y:Y) (f:forall m:ℤ, Y) (e:forall m:ℤ, f m == y),
       forall n, line_map f e (line_vertex n) == f n.
Proof. reflexivity. Qed.

(** ** Factoring maps through squash *)
 
Lemma squash_uniqueness {X} (x:X) (h:squash X) : squash_element x == h.
Proof. intros. apply isaprop_squash. Qed.

Goal forall X Q (i:isaprop Q) (f:X -> Q) (x:X),
   factor_through_squash i f (squash_element x) == f x.
Proof. reflexivity. Defined.

Lemma factor_dep_through_squash {X} {Q:squash X->UU} : 
  (forall h, isaprop (Q h)) -> 
  (forall x, Q(squash_element x)) -> 
  (forall h, Q h).
Proof.
  intros ? ? i f ?.  apply (h (hProppair (Q h) (i h))). 
  intro x. simpl. destruct (squash_uniqueness x h). exact (f x).
Defined.

Lemma factor_through_squash_hProp {X} : forall hQ:hProp, (X -> hQ) -> (squash X -> hQ).
Proof. intros ? [Q i] f h. apply h. assumption. Defined.

Lemma funspace_isaset {X Y} : isaset Y -> isaset (X -> Y).
Proof. intros ? ? is. apply (impredfun 2). assumption. Defined.    

Lemma simple_pair_path {X Y} {x x':X} {y y':Y} (p : x == x') (q : y == y') :
  x,,y == x',,y'.
Proof. intros. destruct p. destruct q. apply idpath. Defined.

Lemma iscontr_if_inhab_prop {P} : isaprop P -> P -> iscontr P.
Proof. intros ? i p. exists p. intros p'. apply i. Defined.

Ltac isaprop_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaprop(G)).

Ltac isaset_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaset(G)).

(** ** Show that squashing is a set-quotient *)

Definition squash_to_set {X Y} (is:isaset Y)
  (f:X->Y) (e:forall x x', f x == f x') : squash X -> Y.
Proof. intros ? ? ? ? ? h. apply (NullHomotopyTo_center f).
  refine (factor_through_squash _ _ h).
  { apply isaprop_NullHomotopyTo. exact is. exact h. }
  intros x. exists (f x). intros x'. apply e. Defined.

(** Verify that the map factors judgmentally. *)
Goal forall X Y (is:isaset Y) (f:X->Y) (e:forall x x', f x == f x'),
       f == funcomp squash_element (squash_to_set is f e).
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
  set ( Q := fun y => g y == g' y ).
  unfold homot.
  apply (@factor_dep_through_squash X). intros y. apply ip.
  intro x. apply h.
Qed.

Lemma squash_map_epi {X S} (ip : isaset S) (g g' : squash X -> S) : 
  g ∘ squash_element == g'∘ squash_element -> g == g'.
Proof.
  intros ? ? ? ? ? e.
  apply funextsec.
  apply squash_map_uniqueness. exact ip.
  intro x. destruct e. apply idpath.
Qed.

Lemma isaxiomfuncontr { X : UU } (P:X -> UU) : 
  isaprop ((forall x:X, iscontr (P x)) -> iscontr (forall x:X, P x)).
Proof.                         (* the statement of [funcontr] is a proposition *)
  intros. apply impred; intro. apply isapropiscontr. Defined.

(* from Vladimir, two lemmas, possibly useful for eta-correction: *)
Definition fpmaphomotfun {X: UU} {P Q: X -> UU} (h: homot P Q) (xp: total2 P): total2 Q.
Proof. intros ? ? ? ? [x p]. split with x.  destruct (h x). exact p. Defined.

Definition fpmaphomothomot {X: UU} {P Q: X -> UU} (h1 h2: P ~ Q) (H: forall x: X, h1 x == h2 x) :
  fpmaphomotfun h1 ~ fpmaphomotfun h2.
Proof. intros. intros [x p]. apply (maponpaths (tpair _ x)).  
       destruct (H x). apply idpath. Defined.

(** * Connected types *)

Definition isconnected X := forall (x y:X), nonempty (x==y).

Lemma base_connected {X} (t:X) : (forall y:X, nonempty (t==y)) -> isconnected X.
Proof. intros ? ? p x y. assert (a := p x). assert (b := p y). clear p.
       apply (squash_to_prop a). apply propproperty. clear a. intros a.
       apply (squash_to_prop b). apply propproperty. clear b. intros b.
       apply hinhpr. exact (!a@b). Defined.

(** * Applications of univalence *)

(** Compare the following two definitions with [transport_type_path]. *)

Require Import Foundations.Proof_of_Extensionality.funextfun.

Definition pr1_eqweqmap { X Y } ( e: X==Y ) : cast e == pr1 (eqweqmap e).
Proof. intros. destruct e. reflexivity. Defined.

Definition pr1_eqweqmap2 { X Y } ( e: X==Y ) : 
  pr1 (eqweqmap e) == transportf (fun T:Type => T) e.
Proof. intros. destruct e. reflexivity. Defined.

Definition weqpath_transport {X Y} (w:weq X Y) (x:X) :
  transportf (fun T => T) (weqtopaths w) == pr1 w.
Proof. intros. exact (!pr1_eqweqmap2 _ @ ap pr1 (weqpathsweq w)). Defined.

Definition weqpath_cast {X Y} (w:weq X Y) (x:X) : cast (weqtopaths w) == w.
Proof. intros. exact (pr1_eqweqmap _ @ ap pr1 (weqpathsweq w)). Defined.

(** * Pointed types *)

Definition PointedType := total2 (fun X => X).
Definition pointedType X x := X,,x : PointedType.
Definition underlyingType (X:PointedType) := pr1 X.
Coercion underlyingType : PointedType >-> Sortclass.
Definition basepoint (X:PointedType) := pr2 X.
Definition loopSpace (X:PointedType) := 
  pointedType (basepoint X == basepoint X) (idpath _).
Notation Ω := loopSpace.
(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/Utilities.vo"
End:
*)
