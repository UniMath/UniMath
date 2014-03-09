(** * Utilities concerning paths, hlevel, and logic *)

Unset Automatic Introduction.

Require RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.pathnotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import Foundations.hlevel2.hSet.
        Import RezkCompletion.pathnotations.PathNotations.

(* this lemma must be somewhere in Foundations *)
Lemma path_assoc (X:UU) (a b c d:X) 
        (f : a == b) (g : b == c) (h : c == d)
      : f @ (g @ h) == (f @ g) @ h.
Proof. intros. destruct f. reflexivity. Defined.
Lemma path_assoc_opaque (X:UU) (a b c d:X) 
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

Definition paths_from {X} (x:X) := coconusfromt X x.
Definition point_to {X} {x:X} : paths_from x -> X := pr1.
Definition paths_to {X} (x:X) := coconustot X x.
Definition point_from {X} {x:X} : paths_to x -> X := pr1.
Definition iscontr_paths_to {X} (x:X) : iscontr (paths_to x).
Proof. apply iscontrcoconustot. Defined.
Definition paths_to_prop {X} (x:X) := 
  hProppair (paths_to x) (isapropifcontr (iscontr_paths_to x)).
Definition iscontr_paths_from {X} (x:X) : iscontr (paths_from x).
Proof. apply iscontrcoconusfromt. Defined.
Definition paths_from_prop {X} (x:X) := 
  hProppair (paths_from x) (isapropifcontr (iscontr_paths_from x)).

Module Import Notation.
  Notation set_to_type := hSet.pr1hSet.
  Notation pair_path := auxiliary_lemmas_HoTT.total2_paths2.
  Notation ap := maponpaths.
  (* see table 3.1 in the coq manual for parsing levels *)
  Notation "f ~ g" := (uu0.homot f g) (at level 70).
  Notation "g ∘ f" := (uu0.funcomp f g) (at level 50).
  Notation "f ;; g" := (uu0.funcomp f g) (at level 50).
  Notation "x ,, y" := (tpair _ x y) (at level 69, right associativity).
  (* funcomp' is like funcomp, but with the arguments in the other order *)
  Definition funcomp' { X Y Z : UU } ( g : Y -> Z ) ( f : X -> Y ) := fun x : X => g ( f x ) . 
  Notation transport := transportf.
  Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).
End Notation.

Definition cast {T U:Type} : T==U -> T->U.
Proof. intros ? ? p t. destruct p. exact t. Defined.

Definition transport_type_path {X Y:Type} (p:X==Y) (x:X) : 
  transportf (fun T:Type => T) p x == cast p x.
Proof. intros. destruct p. reflexivity. Defined.

Definition app {X} {P:X->Type} {x x':X} {e e':x==x'} (q:e==e') (p:P x) : 
   e#p==e'#p.
Proof. intros. destruct q. reflexivity. Defined.

(** * Projections from pair types *)

Definition pr2_pair {X:UU} {P:X->UU} {w w':total2 P} (p : w == w') :
  transport P (ap pr1 p) (pr2 w) == pr2 w'.
Proof. intros. destruct p. reflexivity. Defined.

Definition pair_path_comp1 {X} {Y:X->Type} {x} {y:Y x} {x'} {y':Y x'}
           (p:x==x') (q:p#y==y') : ap pr1 (pair_path p q) == p.
Proof. intros. destruct p. destruct q. reflexivity. Defined.

Definition pair_path_comp2 {X} {Y:X->Type} {x} {y:Y x} {x'} {y':Y x'}
           (p:x==x') (q:p#y==y') :
  ! app (pair_path_comp1 p q) y @ pr2_pair (pair_path p q) == q.
Proof. intros. destruct p, q. reflexivity. Defined.

(** ** Maps from pair types *)

Definition from_total2 {X} {P:X->Type} {Y} : (forall x, P x->Y) -> total2 P -> Y.
Proof. intros ? ? ? f [x p]. exact (f x p). Defined.

(** ** Transport *)

Lemma transport_idfun {X:UU} (P:X->UU) {x y:X} (p:x==y) (u:P x) : 
  transport P p u == transport (idfun _) (ap P p) u.
(* same as HoTT.PathGroupoids.transport_idmap_ap *)
Proof. intros. destruct p. reflexivity. Defined.

(** * Sections *)

Definition sections {T:UU} (P:T->UU) := forall t:T, P t.
Definition evalat {T:UU} {U:UU} (t:T) (f:T->U) := f t.
Definition apevalat {T:UU} {U:UU} (t:T) {f g:T->U}
  : f == g -> f t == g t
  := ap (evalat t).
Definition evalsecat {T:UU} {P:T->UU} (t:T) (f:sections P) := f t.
Definition apevalsecat {T:UU} {P:T->UU} (t:T) {f g:sections P}
  : f == g -> f t == g t
  := ap (evalsecat t).
Definition apfun {X Y} {f f':X->Y} (p:f==f') {x x'} (q:x==x') : f x == f' x'.
  intros. destruct q. exact (apevalat x p). Defined.
Definition aptwice {X Y Z} (f:X->Y->Z) {a a' b b'} (p:a==a') (q:b==b') : f a b == f a' b'.
  intros. exact (apfun (ap f p) q). Defined.
Definition fromemptysec { X : empty -> UU } (nothing:empty) : X nothing.
(* compare with [fromempty] in u00 *)
Proof. intros X H.  destruct H. Defined. 

(** * Decidability *)

Definition not X := X -> empty.
Definition decidable X := coprod X (not X).
Definition LEM := forall P, isaprop P -> decidable P.
Lemma LEM_for_sets X : LEM -> isaset X -> isdeceq X.
Proof. intros X lem is x y. exact (lem (x==y) (is x y)). Qed.

(** * h-levels and paths *)

Lemma isaprop_wma_inhab (X:UU) : (X -> isaprop X) -> isaprop X.
Proof. intros ? f. apply invproofirrelevance. intros x y. apply (f x). Qed.
Lemma isaprop_wma_inhab' (X:UU) : (X -> iscontr X) -> isaprop X.
Proof. intros ? f. apply isaprop_wma_inhab. intro x. apply isapropifcontr. 
       apply (f x). Qed.

Ltac prop_logic := 
  intros; simpl;
  repeat (try (apply isapropdirprod);try (apply isapropishinh);apply impred ;intro); 
  try (apply isapropiscontr); try assumption.

Definition propProperty (P:hProp) := pr2 P : isaprop (pr1 P).

Ltac intermediate x := apply @pathscomp0 with (b := x).

Definition isaset_if_isofhlevel2 {X:UU} : isofhlevel 2 X -> isaset X.
(* The use of this lemma ahead of something like 'impred' can be avoided by
   providing 2 as first argument. *)
Proof. trivial. Qed.

Definition isofhlevel2_if_isaset {X:UU} : isaset X -> isofhlevel 2 X.
Proof. trivial. Qed.

Definition isaprop_hProp (X:hProp) : isaprop X.
Proof. intro. exact (pr2 X). Qed.

Definition the {T:UU} : iscontr T -> T.
Proof. intros ? is. exact (pr1 is). Defined.

Definition uniqueness {T:UU} (i:iscontr T) (t:T) : t == the i.
Proof. intros. exact (pr2 i t). Defined.

Definition uniqueness' {T:UU} (i:iscontr T) (t:T) : the i == t.
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
         f : X -> Y; g : Y -> X;
         p : forall y, f(g y) == y;
         q : forall x, g(f x) == x;
         h : forall x, ap f (q x) == p(f x) }.
End AdjointEquivalence.

Lemma helper {X Y} {f:X->Y} x x' (w:x==x') (t:f x==f x) :
              transport (fun x' => f x' == f x) w (idpath (f x)) == ap f (!w).
Proof. intros ? ? k. destruct w. reflexivity. Qed.

Definition weq_to_AdjointEquivalence X Y : weq X Y -> AdjointEquivalence.data X Y.
  intros ? ? [f r].
  set (g := fun y => hfiberpr1 f y (the (r y))).
  set (p := fun y => pr2 (pr1 (r y))).
  set (L := fun x => pr2 (r (f x)) (hfiberpair f x (idpath (f x)))).
  set (q := fun x => ap pr1 (L x)).
  set (q' := fun x => !q x).  
  exact (AdjointEquivalence.make
           X Y f g p q'
           (fun x => 
              !(helper x (pr1 (pr1 (r (f x)))) (q x) (idpath (f x)))
               @ (pr2_pair (L x)))).
Defined.

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

Definition squash_to_prop {X Y:UU} : squash X -> isaprop Y -> (X -> Y) -> Y.
  intros ? ? h is f. exact (h (Y,,is) f). Defined.

Lemma isaprop_squash (X:UU) : isaprop (squash X).
Proof. prop_logic. Qed.

Lemma squash_path {X} (x y:X) : squash_element x == squash_element y.
Proof. intros. apply isaprop_squash. Defined.

Lemma factor_through_squash {X Q:UU} : isaprop Q -> (X -> Q) -> (squash X -> Q).
Proof. intros ? ? i f h. apply (h (hProppair _ i)). intro x. exact (f x). Defined.

Definition nullHomotopy {X Y} (f:X->Y) (y:Y) := forall x:X, f x == y.
Definition NullHomotopy {X Y} (f:X->Y) := total2 (nullHomotopy f).
Definition NullHomotopy_center {X Y} (f:X->Y) : NullHomotopy f -> Y := pr1.
Definition NullHomotopy_path {X Y} {f:X->Y} (r:NullHomotopy f) := pr2 r.
Definition guidedNullHomotopy {X Y} (f:X->Y) (e:forall x x', f x==f x') :=
  fun h:NullHomotopy f =>
    forall x x', e x x' == NullHomotopy_path h x @ ! NullHomotopy_path h x'.
Definition GuidedNullHomotopy {X Y} (f:X->Y) (e:forall x x', f x==f x') :=
  total2 (guidedNullHomotopy f e).
Definition toNullHomotopy {X Y} {f:X->Y} {e:forall x x', f x==f x'} :
  GuidedNullHomotopy f e -> NullHomotopy f := pr1.
Definition GuidedNullHomotopy_center {X Y} {f:X->Y} {e:forall x x', f x==f x'}
           (h:GuidedNullHomotopy f e) :=
  NullHomotopy_center _ (toNullHomotopy h).
Definition GuidedNullHomotopy_path {X Y} {f:X->Y} {e:forall x x', f x==f x'}
           (h:GuidedNullHomotopy f e) :=
  NullHomotopy_path (toNullHomotopy h).

Definition nullHomotopy_transport {X Y} {f:X->Y} {y:Y} (h : nullHomotopy f y)
           {y':Y} (p:y==y') (x:X) : (p # h) x == h x @ p.
Proof. intros. destruct p. apply pathsinv0. apply pathscomp0rid. Defined.

Lemma isapropGuidedNullHomotopy {X Y} (f:X->Y) (e:forall x x', f x==f x') :
  nonempty X -> isaprop (GuidedNullHomotopy f e).
Proof. intros ? ? ? ? sx.
       apply (squash_to_prop sx); clear sx; intro x0. { apply isapropisaprop. } 
       apply invproofirrelevance; intros [[y h] g] [[y' h'] g'].
       set (p := ! h x0 @ h' x0 : y == y').
       refine (pair_path _ _).
       { refine (pair_path _ _).
         { exact p. }
         { apply funextsec; intro x.
           intermediate (h x @ p).
           { apply nullHomotopy_transport. }
           unfold p.
           intermediate ((h x @ ! h x0) @ h' x0).
           { apply path_assoc. }
           unfold guidedNullHomotopy in g,g'; simpl in g,g'.
           rewrite <- (g x x0).
           rewrite (g' x x0).
           rewrite <- path_assoc.
           rewrite pathsinv0l.
           apply pathscomp0rid. } }
       admit.
Defined.

Lemma isaset_NullHomotopy {X Y} (i:isaset Y) (f:X->Y) : isaset (NullHomotopy f).
Proof. intros. apply (isofhleveltotal2 2). { apply i. }
       intros y. apply impred; intros x. apply isasetaprop. apply i. Defined.

Lemma isaprop_nullHomotopy {X Y} (is:isaset Y) (f:X->Y) (y:Y) :
  isaprop (nullHomotopy f y).
Proof. intros ? ? ? ? ?. apply impred; intros x. apply is. Defined.

Lemma isaprop_NullHomotopy_0 {X} {Y} (is:isaset Y) (f:X->Y) : 
  X -> isaprop (NullHomotopy f).
(** The point of X is needed, for when X is empty, then NullHomotopy f is
    equivalent to Y. *)
Proof. intros ? ? ? ? x. apply invproofirrelevance. intros [r i] [s j].
  refine (pair_path _ _). { exact (!i x @ j x). } 
  { apply (isaprop_nullHomotopy is). } Defined.

Lemma isaprop_NullHomotopy {X} {Y} (is:isaset Y) (f:X->Y) :
  squash X -> isaprop (NullHomotopy f).
Proof. intros ? ? ? ?. apply factor_through_squash. apply isapropisaprop. 
       apply isaprop_NullHomotopy_0. exact is. Defined.

(** We can get a map from 'squash X' to any type 'Y' provided paths
    are given that allow us to map first into a cone in 'Y'.  *)

Definition cone_squash_map {X Y} (f:X->Y) (y:Y) : 
  nullHomotopy f y -> squash X -> Y.
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

Goal forall Y (y y':Y) (e:y == y'), 
       funcomp (hinhpr _) (interval_map e) == bool_rect (fun _ => Y) y y'.
Proof. reflexivity. Qed.

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
 
Lemma squash_uniqueness {X:UU} (x:X) (h:squash X) : squash_element x == h.
Proof. intros. apply isaprop_squash. Qed.

Goal forall X Q (i:isaprop Q) (f:X -> Q) (x:X),
   factor_through_squash i f (squash_element x) == f x.
Proof. reflexivity. Defined.

Lemma factor_dep_through_squash {X:UU} {Q:squash X->UU} : 
  (forall h, isaprop (Q h)) -> 
  (forall x, Q(squash_element x)) -> 
  (forall h, Q h).
Proof.
  intros ? ? i f ?.  apply (h (hProppair (Q h) (i h))). 
  intro x. simpl. destruct (squash_uniqueness x h). exact (f x).
Defined.

Lemma factor_through_squash_hProp {X:UU} : forall hQ:hProp, (X -> hQ) -> (squash X -> hQ).
Proof. intros ? [Q i] f h. apply h. assumption. Defined.

Lemma funspace_isaset {X Y:UU} : isaset Y -> isaset (X -> Y).
Proof. intros ? ? is. apply (impredfun 2). assumption. Defined.    

Lemma simple_pair_path {X Y:UU} {x x':X} {y y':Y} (p : x == x') (q : y == y') : x ,, y == x' ,, y'.
Proof. intros. destruct p. destruct q. apply idpath. Defined.

Lemma iscontr_if_inhab_prop {P:UU} : isaprop P -> P -> iscontr P.
Proof. intros ? i p. exists p. intros p'. apply i. Defined.

Ltac isaprop_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaprop(G)).

Ltac isaset_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaset(G)).

(** ** Show that squashing is a set-quotient *)

Definition True := hProppair unit (isapropifcontr iscontrunit).

Definition squash_to_set {X Y} (is:isaset Y)
  (f:X->Y) (e:forall x x', f x == f x') : squash X -> Y.
Proof. intros ? ? ? ? ? h. apply (NullHomotopy_center f).
  refine (factor_through_squash _ _ h).
  { apply isaprop_NullHomotopy. exact is. exact h. }
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

Proof. intros ? ? ? ? ?. 
       set (R := (fun _ _ => True) : hrel X).
       assert (ic : iscomprelfun R f). { intros x x' _. exact (e x x'). }
       assert (im := isapropimeqclass R (hSetpair Y is) f ic).
Defined.
*)

Lemma squash_map_uniqueness {X S:UU} (ip : isaset S) (g g' : squash X -> S) : 
  g ∘ squash_element ~ g' ∘ squash_element -> g ~ g'.
Proof.
  intros ? ? ? ? ? h.
  set ( Q := fun y => g y == g' y ).
  unfold homot.
  apply (@factor_dep_through_squash X). intros y. apply ip.
  intro x. apply h.
Qed.

Lemma squash_map_epi {X S:UU} (ip : isaset S) (g g' : squash X -> S) : 
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
