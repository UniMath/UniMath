(* -*- coding: utf-8 *)

(** * Group actions *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.algebra1b.
Require Import Foundations.Proof_of_Extensionality.funextfun.
Require RezkCompletion.pathnotations.
Import pathnotations.PathNotations. 
Require Import Ktheory.Utilities.
Require RezkCompletion.precategories.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Import Utilities.Notation.

(** ** Definitions *)

Definition action_op G X := G -> X -> X.

Record ActionStructure (G:gr) (X:hSet) :=
  make {
      act_mult : action_op G X;
      act_unit : forall x, act_mult (unel _) x == x;
      act_assoc : forall g h x, act_mult (op g h) x == act_mult g (act_mult h x)
    }.
Arguments act_mult {G _} _ g x.

Module Pack.
  Definition ActionStructure' (G:gr) (X:hSet) := total2 ( fun
         act_mult : action_op G X => total2 ( fun
         act_unit : forall x, act_mult (unel _) x == x => 
      (* act_assoc : *) forall g h x, act_mult (op g h) x == act_mult g (act_mult h x))).
  Definition pack {G:gr} {X:hSet} : ActionStructure' G X -> ActionStructure G X
    := fun ac => make G X (pr1 ac) (pr1 (pr2 ac)) (pr2 (pr2 ac)).
  Definition unpack {G:gr} {X:hSet} : ActionStructure G X -> ActionStructure' G X
    := fun ac => (act_mult ac,,(act_unit _ _ ac,,act_assoc _ _ ac)).
  Definition h {G:gr} {X:hSet} (ac:ActionStructure' G X) : unpack (pack ac) == ac
    := match ac as t return (unpack (pack t) == t)
       with (act_mult,,(act_unit,,act_assoc)) => idpath (act_mult,,(act_unit,,act_assoc)) end.
  Definition k {G:gr} {X:hSet} (ac:ActionStructure G X) : pack (unpack ac) == ac
    := match ac as i return (pack (unpack i) == i)
       with make _ _ act_mult act_unit act_assoc => idpath _ end.
  Lemma weq (G:gr) (X:hSet) : weq (ActionStructure' G X) (ActionStructure G X).
  Proof. intros. exists pack. intros ac. exists (unpack ac,,k ac). intros [ac' m].
         destruct m. assert (H := h ac'). destruct H. reflexivity. Qed.
End Pack.

Lemma isaset_ActionStructure (G:gr) (X:hSet) : isaset (ActionStructure G X).
Proof. intros. apply (isofhlevelweqf 2 (Pack.weq G X)).
       apply isofhleveltotal2.
       { apply impred; intro g. apply impred; intro x. apply setproperty. }
       intro op. apply isofhleveltotal2.
       { apply impred; intro x. apply hlevelntosn. apply setproperty. }
       intro un. apply impred; intro g. apply impred; intro h. apply impred; intro x. 
       apply hlevelntosn. apply setproperty. Qed.

Definition Action (G:gr) := total2 (ActionStructure G). 
Definition makeAction {G:gr} (X:hSet) (ac:ActionStructure G X) :=
  X,,ac : Action G.

Definition ac_set {G:gr} (X:Action G) := pr1 X.
Coercion ac_set : Action >-> hSet.
Definition ac_type {G:gr} (X:Action G) := pr1hSet (ac_set X).
Definition ac_str {G:gr} (X:Action G) := pr2 X : ActionStructure G (ac_set X).
Definition ac_mult {G:gr} (X:Action G) := act_mult (pr2 X).
Delimit Scope action_scope with action.
Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Open Scope action_scope.
Definition ac_assoc {G:gr} (X:Action G) := act_assoc _ _ (pr2 X) : forall g h x, (op g h)*x == g*(h*x).

Definition right_mult {G:gr} {X:Action G} (x:X) := fun g => g*x.
Definition left_mult {G:gr} {X:Action G} (g:G) := fun x:X => g*x.

Definition is_equivariant {G:gr} {X Y:Action G} (f:X->Y) := 
  forall g x, f (g*x) == g*(f x).

Definition is_equivariant_isaprop {G:gr} {X Y:Action G} (f:X->Y) : 
  isaprop (is_equivariant f).
Proof. intros. apply impred; intro g. apply impred; intro x. 
       apply setproperty. Defined.               

(** The following fact is fundamental: it shows that our definition of
    [is_equivariant] captures all of the structure.  The proof reduces to
    showing that if G acts on a set X in two ways, and the identity function is
    equivariant, then the two actions are equal.  A similar fact will hold in
    other cases: groups, rings, monoids, etc.  Refer to section 9.8 of the HoTT
    book, on the "structure identity principle", a term coined by Peter Aczel. *)

Definition is_equivariant_identity {G:gr} {X Y:Action G}
           (p:ac_set X == ac_set Y) :
  weq (p # ac_str X == ac_str Y) (is_equivariant (cast (ap pr1hSet p))).
Proof. intros ? [X [Xm Xu Xa]] [Y [Ym Yu Ya]] ? .
       simpl in p. destruct p; simpl. unfold transportf; simpl. unfold idfun; simpl.
       refine (weqpair _ _).
       { intros p g x. simpl in x. simpl. 
         exact (apevalat x (apevalat g (ap act_mult p))). }
       refine (gradth _ _ _ _).
       { unfold cast; simpl.
         intro i.
         assert (p:Xm==Ym).
         { apply funextsec; intro g. apply funextsec; intro x; simpl in x.
           exact (i g x). } 
         destruct p. clear i. assert (p:Xu==Yu).
         { apply funextsec; intro x; simpl in x. apply setproperty. }
         destruct p. assert (p:Xa==Ya).
         { apply funextsec; intro g. apply funextsec; intro h.
           apply funextsec; intro x. apply setproperty. }
         destruct p. reflexivity. }
       { intro p. apply isaset_ActionStructure. }
       { intro is. apply is_equivariant_isaprop. } Defined.

Definition is_equivariant_comp {G:gr} {X Y Z:Action G} 
           (p:X->Y) (i:is_equivariant p)
           (q:Y->Z) (j:is_equivariant q) : is_equivariant (funcomp p q).
Proof. intros. intros g x. exact (ap q (i g x) @ j g (p x)). Defined.

Definition ActionMap {G:gr} (X Y:Action G) := total2 (@is_equivariant _ X Y).
Definition underlyingFunction {G:gr} {X Y:Action G} (f:ActionMap X Y) := pr1 f.
Definition equivariance {G:gr} {X Y:Action G} (f:ActionMap X Y) := pr2 f.
Coercion underlyingFunction : ActionMap >-> Funclass.

Definition composeActionMap {G:gr} (X Y Z:Action G)
           (p:ActionMap X Y) (q:ActionMap Y Z) : ActionMap X Z.
Proof. intros ? ? ? ? [p i] [q j]. exists (funcomp p q).
       apply is_equivariant_comp. assumption. assumption. Defined.

Definition ActionIso {G:gr} (X Y:Action G) := 
  total2 (fun f:weq (ac_set X) (ac_set Y) => is_equivariant f).
Definition underlyingIso {G:gr} {X Y:Action G} (e:ActionIso X Y) := pr1 e.
Coercion underlyingIso : ActionIso >-> weq.
Lemma underlyingIso_incl {G:gr} {X Y:Action G} :
  isincl (underlyingIso : ActionIso X Y -> weq X Y).
Proof. intros. apply isinclpr1; intro f. apply is_equivariant_isaprop. Defined.
Lemma underlyingIso_injectivity {G:gr} {X Y:Action G}
      (e f:ActionIso X Y) :
  weq (e == f) (underlyingIso e == underlyingIso f).
Proof. intros. apply weqonpathsincl. apply underlyingIso_incl. Defined.

Definition underlyingActionMap {G:gr} {X Y:Action G} (e:ActionIso X Y) := 
  pr1weq _ _ (pr1 e),, pr2 e.
Definition idActionIso {G:gr} (X:Action G) : ActionIso X X.
Proof. intros. exists (idweq _). intros g x. reflexivity. Defined.
Definition composeActionIso {G:gr} {X Y Z:Action G}
           (e:ActionIso X Y) (f:ActionIso Y Z) : ActionIso X Z.
Proof. intros ? ? ? ? [e i] [f j]. exists (weqcomp e f).
       destruct e as [e e'], f as [f f']; simpl.
       apply is_equivariant_comp. exact i. exact j. Defined.
Definition path_to_ActionIso {G:gr} {X Y:Action G} (e:X==Y) : ActionIso X Y.
Proof. intros. destruct e. exact (idActionIso X). Defined.

(** ** Applications of univalence *)

Lemma Action_univalence {G:gr} {X Y:Action G} : weq (X==Y) (ActionIso X Y).
Proof. intros.
       refine (weqcomp (total_paths_equiv (ActionStructure G) X Y) _).
       refine (weqbandf _ _ _ _).
       { refine (weqcomp (pr1hSet_injectivity _ _) (weqpair (@eqweqmap (pr1 X) (pr1 Y)) (univalenceaxiom _ _))). }
       simpl. intro p. refine (weqcomp (is_equivariant_identity p) _).
       exact (eqweqmap (ap is_equivariant (pr1_eqweqmap (ap set_to_type p)))).
Defined.

(** ** Torsors *)

Definition is_torsor {G:gr} (X:Action G) := 
  dirprod (nonempty X) (forall x:X, isweq (right_mult x)).

Lemma is_torsor_isaprop {G:gr} (X:Action G) : isaprop (is_torsor X).
Proof. intros. apply isofhleveldirprod. { apply propproperty. }
       { apply impred; intro x. apply isapropisweq. } Qed.

Definition Torsor (G:gr) := total2 (@is_torsor G).

Definition underlyingAction {G} (X:Torsor G) := pr1 X : Action G.
Coercion underlyingAction : Torsor >-> Action.
Definition is_torsor_prop {G} (X:Torsor G) := pr2 X.
Definition torsor_nonempty {G} (X:Torsor G) := pr1 (is_torsor_prop X).
Definition torsor_splitting {G} (X:Torsor G) := pr2 (is_torsor_prop X).
Definition torsor_mult_weq {G} (X:Torsor G) (x:X) := 
  weqpair (right_mult x) (torsor_splitting X x) : weq G X.

Lemma underlyingAction_incl {G:gr} :
  isincl (underlyingAction : Torsor G -> Action G).
Proof. intros. apply isinclpr1; intro X. apply is_torsor_isaprop. Defined.

Lemma underlyingAction_injectivity {G:gr} {X Y:Torsor G} :
      weq (X==Y) (underlyingAction X==underlyingAction Y).
Proof. intros. apply weqonpathsincl. apply underlyingAction_incl. Defined.

Definition PointedTorsor (G:gr) := total2 (fun X:Torsor G => X).
Definition underlyingTorsor {G} (X:PointedTorsor G) := pr1 X : Torsor G.
Coercion underlyingTorsor : PointedTorsor >-> Torsor.
Definition underlyingPoint {G} (X:PointedTorsor G) := pr2 X : X.

Lemma is_quotient {G} (X:Torsor G) (y x:X) : iscontr (total2 (fun g => g*x == y)).
Proof. intros. exact (pr2 (is_torsor_prop X) x y). Defined.

Definition quotient {G} (X:Torsor G) (y x:X) := pr1 (the (is_quotient X y x)) : G.
Local Notation "y / x" := (quotient _ y x) : action_scope.

Lemma quotient_times {G} (X:Torsor G) (y x:X) : (y/x)*x == y.
Proof. intros. exact (pr2 (the (is_quotient _ y x))). Defined.

Lemma quotient_uniqueness {G} (X:Torsor G) (y x:X) (g:G) : g*x == y -> g == y/x.
Proof. intros ? ? ? ? ? e. 
       exact (ap pr1 (uniqueness (is_quotient _ y x) (g,,e))). Defined.

Lemma quotient_product {G} (X:Torsor G) (z y x:X) : op (z/y) (y/x) == z/x.
Proof. intros. apply quotient_uniqueness.
       exact (ac_assoc _ _ _ _ 
            @ ap (left_mult (z/y)) (quotient_times _ y x)
            @ quotient_times _ z y). Defined.

Definition trivialTorsor (G:gr) : Torsor G.
Proof. 
  intros. exists (makeAction G (make G G op (lunax G) (assocax G))).
  exact (hinhpr _ (unel G),, 
         fun x => gradth 
           (fun g => op g x) 
           (fun g => op g (grinv _ x))
           (fun g => assocax _ g x (grinv _ x) @ ap (op g) (grrinvax G x) @ runax _ g)
           (fun g => assocax _ g (grinv _ x) x @ ap (op g) (grlinvax G x) @ runax _ g)).
Defined.

Definition pointedTrivialTorsor (G:gr) : PointedTorsor G.
Proof. intros. exists (trivialTorsor G). exact (unel G). Defined.

Definition univ_function {G:gr} (X:Torsor G) (x:X) : trivialTorsor G -> X.
Proof. intros ? ? ?. apply right_mult. assumption. Defined.

Definition univ_function_pointed {G:gr} (X:Torsor G) (x:X) :
  univ_function X x (unel _) == x.
Proof. intros. apply act_unit. Defined.

Definition univ_function_is_equivariant {G:gr} (X:Torsor G) (x:X) : 
  is_equivariant (univ_function X x).
Proof. intros. intros g h. apply act_assoc. Defined.

Definition triviality_isomorphism {G:gr} (X:Torsor G) (x:X) :
  ActionIso (trivialTorsor G) X.
Proof. intros. 
       exact (torsor_mult_weq X x,, univ_function_is_equivariant X x). Defined.

Definition trivialTorsorEquiv (G:gr) (g:G) : weq (trivialTorsor G) (trivialTorsor G).
Proof. intros. exists (fun h => op h g). apply (gradth _ (fun h => op h (grinv G g))).
       { exact (fun h => assocax _ _ _ _ @ ap (op _) (grrinvax _ _) @ runax _ _). }
       { exact (fun h => assocax _ _ _ _ @ ap (op _) (grlinvax _ _) @ runax _ _). }
Defined.

Definition trivialTorsorAuto (G:gr) (g:G) : 
  ActionIso (trivialTorsor G) (trivialTorsor G).
Proof. intros. exists (trivialTorsorEquiv G g).
       intros h x. simpl.  exact (assocax _ h x g). Defined.

Lemma pr1weq_injectivity {X Y} (f g:weq X Y) : weq (f==g) (pr1weq _ _ f==pr1weq _ _ g).
Proof. intros. apply weqonpathsincl. apply isinclpr1weq.  Defined.

Definition autos (G:gr) : weq G (ActionIso (trivialTorsor G) (trivialTorsor G)).
Proof. intros. exists (trivialTorsorAuto G). refine (gradth _ _ _ _).
       { intro f. exact (f (unel G)). } { intro g; simpl. exact (lunax _ g). }
       { intro f; simpl. apply (invweq (underlyingIso_injectivity _ _)); simpl.
         apply (invweq (pr1weq_injectivity _ _)). apply funextsec; intro g.
         simpl. exact ((! (pr2 f) g (unel G)) @ (ap (pr1 f) (runax G g))).
       } Defined.

Lemma trivialTorsorAuto_unit (G:gr) : 
  trivialTorsorAuto G (unel _) == idActionIso _.
Proof. intros. refine (pair_path _ _).
       { refine (pair_path _ _).
         { apply funextsec; intro x; simpl. exact (runax G x). }
         { apply isapropisweq. } }
       { apply is_equivariant_isaprop. } Defined.

Lemma trivialTorsorAuto_mult (G:gr) (g h:G) :
  composeActionIso (trivialTorsorAuto G g) (trivialTorsorAuto G h) 
  == (trivialTorsorAuto G (op g h)).
Proof. intros. refine (pair_path _ _).
       { refine (pair_path _ _).
         { apply funextsec; intro x; simpl. exact (assocax _ x g h). }
         { apply isapropisweq. } }
       { apply is_equivariant_isaprop. } Defined.

(** ** Applications of univalence *)

Definition Torsor_univalence {G:gr} {X Y:Torsor G} : weq (X==Y) (ActionIso X Y).
Proof. intros. refine (weqcomp underlyingAction_injectivity _).
       apply Action_univalence. Defined.

Definition torsor_eqweq_to_path {G:gr} {X Y:Torsor G} : ActionIso X Y -> X == Y.
Proof. intros ? ? ? f. exact ((invweq Torsor_univalence) f). Defined.

Definition PointedActionIso {G:gr} (X Y:PointedTorsor G) 
           := total2 (fun
                         f:ActionIso X Y => 
                         f (underlyingPoint X) == underlyingPoint Y).

Definition pointed_triviality_isomorphism {G:gr} (X:PointedTorsor G) :
  PointedActionIso (pointedTrivialTorsor G) X.
Proof. intros ? [X x]. exists (triviality_isomorphism X x).
       simpl. apply univ_function_pointed. Defined.       

Definition PointedTorsor_univalence {G:gr} {X Y:PointedTorsor G} : 
  weq (X==Y) (PointedActionIso X Y).
Proof. intros.
       refine (weqcomp (total_paths_equiv _ X Y) _). 
       refine (weqbandf _ _ _ _).
       { intros. 
         exact (weqcomp (weqonpathsincl underlyingAction underlyingAction_incl X Y)
                        Action_univalence). }
       destruct X as [X x], Y as [Y y]; simpl. intro p. destruct p; simpl.
       exact (idweq _). Defined.

Definition ClassifyingSpace G := pointedType (Torsor G) (trivialTorsor G).
Local Notation E := PointedTorsor.
Local Notation B := ClassifyingSpace.
Definition π {G:gr} := underlyingTorsor : E G -> B G.

Lemma isconnBG (G:gr) : isconnected (B G).
Proof. intros. apply (base_connected (trivialTorsor _)).
  intros X. apply (squash_to_prop (torsor_nonempty X)). { apply propproperty. }
  intros x. apply hinhpr. exact (torsor_eqweq_to_path (triviality_isomorphism X x)). 
Defined.

Lemma iscontrEG (G:gr) : iscontr (E G).
Proof. intros. exists (pointedTrivialTorsor G). intros [X x].
       apply pathsinv0. apply (invweq PointedTorsor_univalence).
       apply pointed_triviality_isomorphism. Defined.

Theorem loopsBG (G:gr) : weq (Ω (B G)) G.
Proof. intros. refine (weqcomp Torsor_univalence _). 
       apply invweq. apply autos. Defined.

(** Theorem [loopsBG] also follows from the main theorem of the RezkCompletion
    package.  To see that, regard G as a category with one object.  Consider a
    merely representable functor F : G^op -> Set.  Let X be F of the object *.
    Apply F to the arrows to get an action of G on X.  Try to prove that X is a
    torsor.  Since being a torsor is a mere property, we may assume F is
    actually representable.  There is only one object *, so F is isomorphic to
    h_*.  Apply h_* to * and we get Hom(*,*), which is G, regarded as a G-set.
    That's a torsor.  So the Rezk completion RCG is equivalent to BG, the type
    of G-torsors.  Now the theorem also says there is an equivalence G -> RCG.
    So RCG is connected and its loop space is G.

    A formalization of that argument should be added eventually. *)

Require Import Foundations.hlevel2.hz.
Notation ℕ := nat.
Notation ℤ := hzaddabgr.
Definition circle := B ℤ.

Theorem loops_circle : weq (Ω circle) ℤ.
Proof. apply loopsBG. Defined.

(** * Powers of paths *) 

Definition loop_power_nat {Y} {y:Y} (l:y==y) (n:ℕ) : y==y.
Proof. intros. induction n as [|n p]. 
       { exact (idpath _). } { exact (p@l). }
Defined.

Local Notation "l ^ n" := (loop_power_nat l n) : paths_nat_scope.

Definition loop_power {Y} {y:Y} (l:y==y) (n:ℤ) : y==y.
Proof. intros. assert (m := loop_power_nat l (hzabsval n)).
       destruct (hzlthorgeh n 0%hz). { exact (!m). } { exact m. } Defined.

Delimit Scope paths_scope with paths.
Open Scope paths_scope.
Local Notation "l ^ n" := (loop_power l n) : paths_scope.

(** * The induction principle for the circle. *)

Module N.
  Local Notation "h [ n ]" :=(NullHomotopyFrom_path h n) (at level 0).
  Definition stable {Y} (f:ℕ->Y) := forall n, f n==f(S n).
  Definition stableNullHomotopyFrom {Y} (f:ℕ->Y) (s:stable f) (h:NullHomotopyFrom f) :=
      forall n, h[S n] == h[n] @ s n.
  Definition StableNullHomotopyFrom {Y} (f:ℕ->Y) (s:stable f) :=
    total2 (stableNullHomotopyFrom f s).
  Definition toNullHomotopyFrom {Y} {f:ℕ->Y} {s:stable f} :
    StableNullHomotopyFrom f s -> NullHomotopyFrom f := pr1.
  Definition StableNullHomotopyFrom_center {Y} {f:ℕ->Y} {s:stable f}
             (h:StableNullHomotopyFrom f s) :=
    NullHomotopyFrom_center _ (toNullHomotopyFrom h).
  Definition StableNullHomotopyFrom_path {Y} {f:ℕ->Y} {s:stable f}
             (h:StableNullHomotopyFrom f s) n := (toNullHomotopyFrom h)[n].
  Definition h_triv {Y} {f:ℕ->Y} (s:stable f) {y:Y} (h0:y==f 0) :
    forall n, y == f (S n).
  Proof. intros. induction n.
         { exact (h0 @ s 0). } { exact (IHn @ s (S n)). } Defined.
  Definition F {Y} {f:ℕ->Y} (s:stable f) {y} (h:nullHomotopyFrom f y) :
    stableNullHomotopyFrom f s (y,,h) -> forall n, h(S n) == h_triv s (h 0) n.
  Proof. intros ? ? ? ? ? t ?. induction n. 
         { exact (t 0). } { exact (t (S n) @ ap post_cat IHn). } Defined.
  Definition F' {Y} {f:ℕ->Y} (s:stable f) {y} (h:nullHomotopyFrom f y) :
     (forall n, h(S n) == h_triv s (h 0) n) -> stableNullHomotopyFrom f s (y,,h).
  Proof. intros ? ? ? ? ? t ?. simpl. 
         { induction n.
           { exact (t 0). } { exact (t (S n) @ ! ap post_cat (t n)). } } Defined.
  Lemma u {X} {x y:X} (p q:x==y) : p==q -> !q@p==idpath _.
  Proof. intros ? ? ? ? ? e. destruct e. destruct p. reflexivity. Defined.
  Lemma A {Y} {f:ℕ->Y} (s:stable f) {y} (h:nullHomotopyFrom f y) :
    isweq (F s h).
  Proof. intros. apply (gradth _ (F' _ _)).
         { intro t. apply funextsec; intro n. induction n.
           { reflexivity. }
           { unfold F,F'; simpl. refine (!path_assoc _ _ _ @ _).
             refine (ap pre_cat (pathsinv0r _) @ _). apply pathscomp0rid. } }
         { intro t. apply funextsec; intro n. induction n.
           { reflexivity. }
           { unfold F, F'; simpl. refine (!path_assoc _ _ _ @ _).
             refine (_ @ pathscomp0rid _). apply (ap pre_cat). apply u. 
             apply (ap (ap post_cat)). assumption. } } Defined.
  Definition ic {Y} {f:ℕ->Y} (s:stable f) : iscontr (StableNullHomotopyFrom f s).
  Proof. 

    admit.
  Defined.
End N.

Module BZ.

  Local Notation "n + x" := (ac_mult _ n x) : action_scope.
  Local Notation "n - m" := (quotient _ n m) : action_scope.


  Definition one := 1%hz : ℤ.
  Definition stable {T:Torsor ℤ} {Y} (f:T->Y) := forall t, f t==f(one+t).
  Definition stableComp {T:Torsor ℤ} {Y} (f:T->Y) (s:stable f) :
    forall t t', f t==f t'.
  Proof. intros. unfold stable in s.
         set (n := t' - t).
         destruct (hzlthorgeh n 0%hz).
         { admit. }
         { assert (r := quotient_times _ t' t : n + t == t').
           set (m := hzabsval n).
           assert (F := hzabsvalgeh0 h).
           intermediate (f (n+t)).
           { intermediate (f ((nattohz m : ℤ)+t)).
             { induction m.
               { assert (w : 0%hz == nattohz 0). { reflexivity. }
                 destruct w.
                 admit. }
               admit. }
             admit. }
           admit. }
  Defined.

  Definition stableNullHomotopyTo {T:Torsor ℤ} {Y} (f:T->Y) (s:stable f)
             (h:NullHomotopyTo f) :=
      forall t, s t == NullHomotopyTo_path h t @ ! NullHomotopyTo_path h (one+t).
  Definition StableNullHomotopyTo {T:Torsor ℤ} {Y} (f:T->Y) (s:stable f) :=
    total2 (stableNullHomotopyTo f s).
  Definition toNullHomotopyTo {T:Torsor ℤ} {Y} {f:T->Y} {s:stable f} :
    StableNullHomotopyTo f s -> NullHomotopyTo f := pr1.
  Definition StableNullHomotopyTo_center {T:Torsor ℤ} {Y} {f:T->Y} {s:stable f}
             (h:StableNullHomotopyTo f s) :=
    NullHomotopyTo_center _ (toNullHomotopyTo h).
  Definition StableNullHomotopyTo_path {T:Torsor ℤ} {Y} {f:T->Y} {s:stable f}
             (h:StableNullHomotopyTo f s) :=
    NullHomotopyTo_path (toNullHomotopyTo h).

  Definition makeStableNullHomotopyTo {T:Torsor ℤ} {Y} (f:T->Y) (s:stable f) :
    T -> StableNullHomotopyTo f s.
  Proof. intros ? ? ? ? t0.
         admit.
  Defined.

  Lemma isapropStableNullHomotopyTo {T:Torsor ℤ} {Y} (f:T->Y) (s:stable f) :
    iscontr (StableNullHomotopyTo f s).
  Proof. intros ? ? ? ?.
         apply (squash_to_prop (torsor_nonempty T)); intro t0. { apply isapropiscontr. } 
         admit.
  Defined.

  Definition H {T:Torsor ℤ} {Y} {y:Y} (l:y==y) : squash T -> Y.
  Proof. intros ? ? ? ?. 
         admit.
  Defined.

End BZ.

(*
Local Variables:
compile-command: "make -C ../.. Packages/Ktheory/GroupAction.vo"
End:
*)
