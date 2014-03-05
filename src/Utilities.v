(** * utilities concerning paths, hlevel, and logic *)

Unset Automatic Introduction.

Require RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.pathnotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import Foundations.hlevel2.hSet.
        Import RezkCompletion.pathnotations.PathNotations.

Set Default Timeout 50.

Definition two_cases {X Y T} : coprod X Y -> (X->T) -> (Y->T) -> T.
  exact (fun X Y T xy f g => sum_rect (fun _ => T) f g xy). Defined.

Ltac exact_op x := (* from Jason Gross: same as "exact", but with unification the opposite way *)
  let T := type of x in
  let G := match goal with |- ?G => constr:(G) end in
  exact ((@id G : T -> G) x).

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

Lemma transport_idpath {X:UU} (P:X->UU) {x y:X} (p:x==y) (u:P x) : 
  transport P p u == transport (idfun _) (ap P p) u.
(* same as HoTT.PathGroupoids.transport_idmap_ap *)
Proof. intros. destruct p. reflexivity. Defined.

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

(** * decidability *)

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

Definition proj2 {X:UU} {P:X->UU} {w w':total2 P} (p : w == w') :
  transport P (ap pr1 p) (pr2 w) == pr2 w'.
Proof. intros. destruct p. reflexivity. Defined.

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
               @ (proj2 (L x)))).
Defined.

(** * Squashing. *)

Notation squash := ishinh_UU.
Notation squash_fun := hinhfun.
Lemma squash_fun2 {X Y Z} : (X -> Y -> Z) -> (squash X -> squash Y -> squash Z).
Proof. intros ? ? ? f x y P h.
  exact (y P 
           (x (hProppair 
                 (Y -> P) 
                 (impred 1 _ (fun _ => propProperty P))) 
              (fun a b => h (f a b)))). Qed.

Definition squash_element {X:UU} : X -> squash X.
Proof. intros ? x P f. exact (f x). Defined.

Lemma isaprop_squash (X:UU) : isaprop (squash X).
Proof. prop_logic. Qed.
 
Lemma squash_uniqueness {X:UU} (x:X) (h:squash X) : squash_element x == h.
Proof. intros. apply isaprop_squash. Qed.

Lemma factor_through_squash {X Q:UU} : isaprop Q -> (X -> Q) -> (squash X -> Q).
Proof. intros ? ? i f h. apply (h (hProppair _ i)). intro x. exact (f x). Defined.

Lemma factor_through_squash_factors {X Q:UU} (i:isaprop Q) (f:X -> Q) (x:X)
   : factor_through_squash i f (squash_element x) == f x.
Proof. trivial. Defined.

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

Definition squash_to_prop {X Y:UU} : squash X -> isaprop Y -> (X -> Y) -> Y.
  intros ? ? h is f. exact (h (Y,,is) f). Defined.

(** ** Connected types *)

Definition isconnected X := forall (x y:X), ishinh (x==y).

Lemma base_connected X (t:X) : (forall y:X, ishinh (t==y)) -> isconnected X.
Proof. intros ? ? p x y. assert (a := p x). assert (b := p y). clear p.
       apply (squash_to_prop a). apply propproperty. clear a. intros a.
       apply (squash_to_prop b). apply propproperty. clear b. intros b.
       apply hinhpr. exact (!a@b). Defined.

(** ** Show that squashing is a set-quotient *)

Definition squash_to_set {X Y:UU} (h:squash X) (is:isaset Y)
  (f:X->Y) (e:forall x x', f x == f x') : Y.

(** from Voevodsky, for future work:

    I think one can get another proof using "isapropimeqclass" (hSet.v) with "R :=
    fun x1 x1 => unit". This Lemma will show that under your assumptions "Im f" is
    a proposition. Therefore "X -> Im f" factors through "squash X". *)

Proof.
  intros. generalize h; clear h.
  set (L := fun y:Y => forall x:X, f x == y).
  set (P := total2 L).
  assert(ip : isaset P).
   apply (isofhleveltotal2 2). exact is.
   intros y. apply impred.
   intros t. apply isasetaprop. apply is.
  assert(m : X -> forall y:Y, isaprop (L y)).
   intros a z. apply impred.
   intros t. apply is.
  assert(h : X -> isaprop P).
   intros a.
   apply invproofirrelevance.
   intros [r i] [s j].
   assert(k : r == s). 
     intermediate (f a). 
     apply pathsinv0; apply i.
     apply j.
   apply (pair_path k). apply m. exact a.
  assert(h' : squash X -> isaprop P).
   apply factor_through_squash. apply isapropisaprop.
   exact h.
  assert(k : squash X -> P).
   intros z.
   apply (@factor_through_squash X _ (h' z)).
    intros x. exists (f x). intros x'. apply e.
   exact z.
  intro z. apply (pr1 (k z)).
Defined.

Goal forall (X Y:UU) (f : X -> Y) (is : isaset Y) (eq: forall x x', f x == f x'),
       forall x, f x == squash_to_set (squash_element x) is f eq.
Proof. reflexivity. (* verify computation is definitional *) Defined.

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
  apply funextfunax.
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
