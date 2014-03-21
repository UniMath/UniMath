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

Lemma quotient_mult {G} (X:Torsor G) (g:G) (x:X) : (g*x)/x == g.
Proof. intros. apply pathsinv0. apply quotient_uniqueness. reflexivity. Defined.

Lemma quotient_1 {G} (X:Torsor G) (x:X) : x/x == 1%multmonoid.
Proof. intros. apply pathsinv0. apply quotient_uniqueness. apply act_unit.
Defined.

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
Proof. intros. refine (pair_path_props _ _).
       { refine (pair_path_props _ _).
         { apply funextsec; intro x; simpl. exact (runax G x). }
         { apply isapropisweq. } }
       { intro k. apply is_equivariant_isaprop. } Defined.

Lemma trivialTorsorAuto_mult (G:gr) (g h:G) :
  composeActionIso (trivialTorsorAuto G g) (trivialTorsorAuto G h) 
  == (trivialTorsorAuto G (op g h)).
Proof. intros. refine (pair_path_props _ _).
       { refine (pair_path_props _ _).
         { apply funextsec; intro x; simpl. exact (assocax _ x g h). }
         { apply isapropisweq. } }
       { intro k. apply is_equivariant_isaprop. } Defined.

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
Definition ℕtoℤ (n:ℕ) : ℤ := nattohz n.
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

(** * The induction principle for the half line. *)
Module Halfline.

  Definition target_paths {Y} (f:ℕ->Y) := forall n, f n==f(S n).

  Definition gHomotopy {Y} (f:ℕ->Y) (s:target_paths f) y (h:nullHomotopyFrom f y) :=
    forall n, h(S n) == h n @ s n.

  Definition GHomotopy {Y} (f:ℕ->Y) (s:target_paths f) y := total2 (gHomotopy f s y).

  Definition GuidedHomotopy {Y} (f:ℕ->Y) (s:target_paths f) := total2 (GHomotopy f s).

  Definition isolate_0_in_nat : weq (coprod unit ℕ) ℕ.
  Proof. refine (_,,gradth _ _ _ _).
         { intro m. induction m as [|m]. { exact 0. } { exact (S m). } }
         { intro n. induction n. { exact (inl tt). } { exact (inr n). } }
         { intro n. induction n as [[]|n]. { reflexivity. } { reflexivity. } }
         { intro n. induction n. { reflexivity. } { reflexivity. } }
  Defined.

  Definition isolate0 {P:ℕ->Type} : 
    weq (forall n, P n) (dirprod (P 0) (forall n, P (S n))).
  Proof. intros. intermediate_weq (forall n, P (isolate_0_in_nat n)).
         { apply weqonsecbase. }
         intermediate_weq (dirprod (forall t, P (isolate_0_in_nat (inl t))) (forall n, P (isolate_0_in_nat (inr n)))).
         { apply weqsecovercoprodtoprod. }
         apply weqdirprodf. { apply weqsecoverunit. } { apply idweq. }
  Defined.

  Definition isolate0fam (P:ℕ->Type) (Z:forall n, P 0 -> P (S n) -> Type) :
    forall (f:forall n, P n), Type.
  Proof. intros. exact (forall n, Z n (f 0) (f (S n))). Defined.

  Definition isolate0fam' (P:ℕ->Type) (Z:forall n, P 0 -> P (S n) -> Type) :
    forall (f:dirprod (P 0) (forall n, P (S n))), Type.
  Proof. intros. exact (forall n, Z n (pr1 f) (pr2 f n)). Defined.

  Definition check_refl (P:ℕ->Type) (Z:forall n, P 0 -> P (S n) -> Type) :
    funcomp isolate0 (isolate0fam' P Z) == isolate0fam P Z.
  Proof. reflexivity. Defined.

  Definition isolate0_weq (P:ℕ->Type) (Z:forall n, P 0 -> P (S n) -> Type) :
    weq (total2 (isolate0fam P Z)) (total2 (isolate0fam' P Z)).
  Proof. intros. 
         change (weq (total2 (funcomp isolate0 (isolate0fam' P Z)))
                     (total2 (isolate0fam' P Z))).
         apply weqfp. Defined.

  Definition h_triv {Y} {f:ℕ->Y} (s:target_paths f) {y:Y} (h0:y==f 0) : nullHomotopyFrom f y.
  Proof. intros. intro n. induction n. { exact (h0). } { exact (IHn @ s _). } Defined.

  Definition gHomotopy' {Y} (f:ℕ->Y) (s:target_paths f) y :=
    isolate0fam (fun n => y == f n) (fun n h0 hSn => hSn == h_triv s h0 (S n)).

  Definition GHomotopy' {Y} (f:ℕ->Y) (s:target_paths f) y := total2 (gHomotopy' f s y).

  Definition F {Y} {f:ℕ->Y} (s:target_paths f) {y} (h:nullHomotopyFrom f y) :
    gHomotopy f s y h -> gHomotopy' f s y h.
  Proof. intros ? ? ? ? ? t ?. induction n. 
         { exact (t 0). } { exact (t (S n) @ ap post_cat IHn). } Defined.

  Definition F' {Y} {f:ℕ->Y} (s:target_paths f) {y} (h:nullHomotopyFrom f y) :
     gHomotopy' f s y h -> gHomotopy f s y h.
  Proof. intros ? ? ? ? ? t ?. simpl. 
         { induction n.
           { exact (t 0). } { exact (t (S n) @ ! ap post_cat (t n)). } } Defined.

  Lemma u {X} {x y:X} (p q:x==y) : p==q -> !q@p==idpath _.
  Proof. intros ? ? ? ? ? e. destruct e. destruct p. reflexivity. Defined.

  Lemma A {Y} {f:ℕ->Y} (s:target_paths f) {y} (h:nullHomotopyFrom f y) : 
    weq (gHomotopy f s y h) (gHomotopy' f s y h).
  Proof. intros. exists (F s h). apply (gradth _ (F' s h)).
         { intro t. apply funextsec; intro n. induction n. { reflexivity. }
           { unfold F,F'; simpl. refine (!path_assoc _ _ _ @ _).
             refine (ap pre_cat (pathsinv0r _) @ _). apply pathscomp0rid. } }
         { intro t. apply funextsec; intro n. induction n. { reflexivity. }
           { unfold F, F'; simpl. refine (!path_assoc _ _ _ @ _).
             refine (_ @ pathscomp0rid _). apply (ap pre_cat). apply u. 
             apply (ap (ap post_cat)). assumption. } } Defined.
  (** The proof above works only by accident; there ought to be a better way. *)

  Lemma B {Y} {f:ℕ->Y} (s:target_paths f) {y} : weq (GHomotopy f s y) (GHomotopy' f s y).
  Proof. intros. apply weqfibtototal; intro h. apply A. Defined.

  Definition GHomotopy'' {Y} (f:ℕ->Y) (s:target_paths f) y := 
    total2 (isolate0fam' (fun n => y == f n)
                         (fun n h0 hSn => hSn == h_triv s h0 (S n))).

  Lemma C {Y} {f:ℕ->Y} (s:target_paths f) {y} : weq (GHomotopy' f s y) (GHomotopy'' f s y).
  Proof. intros. apply isolate0_weq. Defined.

  Definition GHomotopy''' {Y} (f:ℕ->Y) (s:target_paths f) y := total2 (fun 
               h0:y==f 0 => total2 (fun
               h:forall n:ℕ, y == f (S n) => 
                 forall n:ℕ, h n == h_triv s h0 (S n))).

  Lemma D {Y} {f:ℕ->Y} (s:target_paths f) {y} : 
    weq (GHomotopy'' f s y) (GHomotopy''' f s y).
  Proof. intros. apply weqtotal2asstor. Defined.

  Definition GHomotopy'''' {Y} (f:ℕ->Y) (s:target_paths f) y := total2 (fun 
               h0:y==f 0 => total2 (fun
               h:forall n:ℕ, y == f (S n) => 
                 h == fun n => h_triv s h0 (S n))).
  
  Lemma E {Y} {f:ℕ->Y} (s:target_paths f) {y} : 
    weq (GHomotopy''' f s y) (GHomotopy'''' f s y).
  Proof. intros. apply weqfibtototal; intro h0. apply weqfibtototal; intro h.
         apply weqfunextsec. Defined.

  Lemma G {Y} {f:ℕ->Y} (s:target_paths f) {y} : 
    weq (GHomotopy'''' f s y) (y==f 0).
  Proof. intros. exists pr1. apply isweqpr1; intro h0. apply iscontrcoconustot.
  Defined.

  Local Notation "f @@ g" := (weqcomp f g) (left associativity, at level 50).

  Lemma H {Y} {f:ℕ->Y} (s:target_paths f) : 
    weq (total2 (GHomotopy f s)) (paths_to (f 0)).
  Proof. intros. apply weqfibtototal; intro y.
         exact (B s @@ C s @@ D s @@ E s @@ G s). Defined.

  Theorem finally {Y} {f:ℕ->Y} (s:target_paths f) : iscontr (GuidedHomotopy f s).
  Proof. intros. apply (iscontrweqb (H s)). apply iscontrcoconustot. Defined.

  (** ** construction of the half line *)

  Definition halfline := squash ℕ.

  Definition map {Y} {f:ℕ->Y} (s:target_paths f) : 
    halfline -> GuidedHomotopy f s.
  Proof. intros ? ? ? r. apply (squash_to_prop r).
         { apply isapropifcontr. apply finally. } 
         { intro n. exists (f n). induction n.
           { exists (h_triv s (idpath _)). intro n. reflexivity. }
           { exact (s n#IHn). } } Defined.           

  Definition map_path_check {Y} {f:ℕ->Y} (s:target_paths f) (n:ℕ) :
    forall p : map s (squash_element n) ==
               map s (squash_element (S n)),
      ap pr1 p == s n.
  Proof. intros. 
         set (q := total2_paths2 (s n) (idpath _) 
                   : map s (squash_element n) == map s (squash_element (S n))).
         assert (u : q==p). 
         { apply (hlevelntosn 1). apply (hlevelntosn 0). apply finally. }
         destruct u. apply total2_paths2_comp1. Defined.

  (** ** universal property for the half line *)

  Definition halfline_map {Y} {target_points:ℕ->Y} (s:target_paths target_points) : 
    halfline -> Y.
  Proof. intros ? ? ? r. exact (pr1 (map s r)). Defined.

  Definition check_values {Y} {target_points:ℕ->Y} 
             (s:target_paths target_points) (n:ℕ) :
    halfline_map s (squash_element n) == target_points n.
  Proof. reflexivity. Defined.

  Definition check_paths {Y} {target_points:ℕ->Y} 
             (s:target_paths target_points) (n:ℕ) :
    ap (halfline_map s) (squash_path n (S n)) == s n.
  Proof. intros. refine (_ @ map_path_check s n _).
         apply pathsinv0. apply maponpathscomp. Defined.

End Halfline.

Module AffineLine.

  Definition zero := ℕtoℤ 0.
  Definition one := ℕtoℤ 1.

  Variable T : Torsor ℤ.

  Local Notation "n + x" := (ac_mult _ (n%hz:ℤ) x) : action_scope.
  Local Notation "n - m" := (quotient _ n m) : action_scope.

  Definition target_paths {Y} (f:T->Y) := forall t, f t==f(one + t).

  Definition gHomotopy {Y} (f:T->Y) (s:target_paths f) y (h:nullHomotopyFrom f y) :=
    forall n, h(one + n) == h n @ s n.

  Definition GHomotopy {Y} (f:T->Y) (s:target_paths f) y := total2 (gHomotopy f s y).

  Definition GuidedHomotopy {Y} (f:T->Y) (s:target_paths f) := total2 (GHomotopy f s).

  Definition ℕuℕ := coprod unit (coprod ℕ ℕ).
  Definition p0 : ℕuℕ := inl tt.
  Definition inj (n:ℕ) : ℕuℕ := inr (inl n).
  Definition inj' (n:ℕ) : ℕuℕ := inr (inr n).

  Definition ℕuℕtoT (t0:T) (w:ℕuℕ) : T.
  Proof. intros. destruct w as [[]|[m|m']]. 
         { exact t0. }
         { exact (ℕtoℤ(S m) + t0). } { exact (- ℕtoℤ(S m') + t0). } Defined.

  Definition Ttoℕuℕ (t0 t:T) : ℕuℕ.
  Proof. intros. set (z := t - t0). destruct (isdeceqhz z zero) as [i|ne].
         { exact p0. }
         { destruct (hzneqchoice _ _ ne).
           { exact (inj (S (hzabsval z))). }
           { exact (inj' (S (hzabsval z))). } } Defined.

  Definition isolate_t0_in_T (t0:T) : weq ℕuℕ T.
  Proof. intros. refine (ℕuℕtoT t0,,gradth _ (Ttoℕuℕ t0) _ _).
         { intro w. induction w as [[]|p]. 
           { simpl.
             unfold Ttoℕuℕ.
             destruct (isdeceqhz (t0 - t0) zero) as [i|ne].
             { reflexivity. }
             { destruct (hzneqchoice (t0 - t0) zero ne).
               { apply fromempty; clear h. apply ne; clear ne.
                 apply (quotient_1 _ t0). }
               { apply fromempty; clear h. apply ne; clear ne.
                 apply (quotient_1 _ t0). } } }
           { destruct p as [n|n'].
             { simpl. unfold Ttoℕuℕ. destruct (isdeceqhz (ℕtoℤ (S n) * t0 - t0) zero).
               { apply fromempty. apply (negpathssx0 n).
                 apply (invmaponpathsincl _ isinclnattohz (S n) 0).
                 exact (! quotient_mult _ (ℕtoℤ (S n)) t0 @ i). }
               { admit. } }
             { admit. } } }
         { admit. }
  Defined.

  Definition isolate0 {P:T->Type} (t0:T) : 
    weq (forall n, P n) 
        (dirprod (P t0) 
                 (dirprod (forall n, P   (ℕtoℤ (S n) + t0))
                          (forall n, P (- ℕtoℤ (S n) + t0)))).
  Proof. intros. intermediate_weq (forall n, P (isolate_t0_in_T t0 n)).
         { apply weqonsecbase. }
         intermediate_weq (
           dirprod (forall t, P (isolate_t0_in_T t0 (inl t)))
                   (forall w, P (isolate_t0_in_T t0 (inr w)))).
         { apply weqsecovercoprodtoprod. } apply weqdirprodf. 
         { apply weqsecoverunit. } { apply weqsecovercoprodtoprod. } Defined.

(*
  Definition isolate0fam (P:T->Type) (t0:T) (Z:forall n, P 0 -> P (one + n) -> Type) :
    forall (f:forall n, P n), Type.
  Proof. intros. exact (forall n, Z n (f 0) (f (one + n))). Defined.

  Definition isolate0fam' (P:T->Type) (Z:forall n, P 0 -> P (one + n) -> Type) :
    forall (f:dirprod (P 0) (forall n, P (one + n))), Type.
  Proof. intros. exact (forall n, Z n (pr1 f) (pr2 f n)). Defined.

  Definition check_refl (P:T->Type) (Z:forall n, P 0 -> P (one + n) -> Type) :
    funcomp isolate0 (isolate0fam' P Z) == isolate0fam P Z.
  Proof. reflexivity. Defined.

  Definition isolate0_weq (P:T->Type) (Z:forall n, P 0 -> P (one + n) -> Type) :
    weq (total2 (isolate0fam P Z)) (total2 (isolate0fam' P Z)).
  Proof. intros. 
         change (weq (total2 (funcomp isolate0 (isolate0fam' P Z)))
                     (total2 (isolate0fam' P Z))).
         apply weqfp. Defined.

  Definition h_triv {Y} {f:T->Y} (s:target_paths f) {y:Y} (h0:y==f 0) : nullHomotopyFrom f y.
  Proof. intros. intro n. induction n. { exact (h0). } { exact (IHn @ s _). } Defined.

  Definition gHomotopy' {Y} (f:T->Y) (s:target_paths f) y :=
    isolate0fam (fun n => y == f n) (fun n h0 hSn => hSn == h_triv s h0 (one + n)).

  Definition GHomotopy' {Y} (f:T->Y) (s:target_paths f) y := total2 (gHomotopy' f s y).

  Definition F {Y} {f:T->Y} (s:target_paths f) {y} (h:nullHomotopyFrom f y) :
    gHomotopy f s y h -> gHomotopy' f s y h.
  Proof. intros ? ? ? ? ? t ?. induction n. 
         { exact (t 0). } { exact (t (one + n) @ ap post_cat IHn). } Defined.

  Definition F' {Y} {f:T->Y} (s:target_paths f) {y} (h:nullHomotopyFrom f y) :
     gHomotopy' f s y h -> gHomotopy f s y h.
  Proof. intros ? ? ? ? ? t ?. simpl. 
         { induction n.
           { exact (t 0). } { exact (t (one + n) @ ! ap post_cat (t n)). } } Defined.

  Lemma u {X} {x y:X} (p q:x==y) : p==q -> !q@p==idpath _.
  Proof. intros ? ? ? ? ? e. destruct e. destruct p. reflexivity. Defined.

  Lemma A {Y} {f:T->Y} (s:target_paths f) {y} (h:nullHomotopyFrom f y) : 
    weq (gHomotopy f s y h) (gHomotopy' f s y h).
  Proof. intros. exists (F s h). apply (gradth _ (F' s h)).
         { intro t. apply funextsec; intro n. induction n. { reflexivity. }
           { unfold F,F'; simpl. refine (!path_assoc _ _ _ @ _).
             refine (ap pre_cat (pathsinv0r _) @ _). apply pathscomp0rid. } }
         { intro t. apply funextsec; intro n. induction n. { reflexivity. }
           { unfold F, F'; simpl. refine (!path_assoc _ _ _ @ _).
             refine (_ @ pathscomp0rid _). apply (ap pre_cat). apply u. 
             apply (ap (ap post_cat)). assumption. } } Defined.
  (** The proof above works only by accident; there ought to be a better way. *)

  Lemma B {Y} {f:T->Y} (s:target_paths f) {y} : weq (GHomotopy f s y) (GHomotopy' f s y).
  Proof. intros. apply weqfibtototal; intro h. apply A. Defined.

  Definition GHomotopy'' {Y} (f:T->Y) (s:target_paths f) y := 
    total2 (isolate0fam' (fun n => y == f n)
                         (fun n h0 hSn => hSn == h_triv s h0 (one + n))).

  Lemma C {Y} {f:T->Y} (s:target_paths f) {y} : weq (GHomotopy' f s y) (GHomotopy'' f s y).
  Proof. intros. apply isolate0_weq. Defined.

  Definition GHomotopy''' {Y} (f:T->Y) (s:target_paths f) y := total2 (fun 
               h0:y==f 0 => total2 (fun
               h:forall n:T, y == f (one + n) => 
                 forall n:T, h n == h_triv s h0 (one + n))).

  Lemma D {Y} {f:T->Y} (s:target_paths f) {y} : 
    weq (GHomotopy'' f s y) (GHomotopy''' f s y).
  Proof. intros. apply weqtotal2asstor. Defined.

  Definition GHomotopy'''' {Y} (f:T->Y) (s:target_paths f) y := total2 (fun 
               h0:y==f 0 => total2 (fun
               h:forall n:T, y == f (one + n) => 
                 h == fun n => h_triv s h0 (one + n))).
  
  Lemma E {Y} {f:T->Y} (s:target_paths f) {y} : 
    weq (GHomotopy''' f s y) (GHomotopy'''' f s y).
  Proof. intros. apply weqfibtototal; intro h0. apply weqfibtototal; intro h.
         apply weqfunextsec. Defined.

  Lemma G {Y} {f:T->Y} (s:target_paths f) {y} : 
    weq (GHomotopy'''' f s y) (y==f 0).
  Proof. intros. exists pr1. apply isweqpr1; intro h0. apply iscontrcoconustot.
  Defined.

  Local Notation "f @@ g" := (weqcomp f g) (left associativity, at level 50).

  Lemma H {Y} {f:T->Y} (s:target_paths f) : 
    weq (total2 (GHomotopy f s)) (paths_to (f 0)).
  Proof. intros. apply weqfibtototal; intro y.
         exact (B s @@ C s @@ D s @@ E s @@ G s). Defined.

  Theorem finally {Y} {f:T->Y} (s:target_paths f) : iscontr (GuidedHomotopy f s).
  Proof. intros. apply (iscontrweqb (H s)). apply iscontrcoconustot. Defined.

  (** ** construction of the half line *)

  Definition halfline := squash T.

  Definition map {Y} {f:T->Y} (s:target_paths f) : 
    halfline -> GuidedHomotopy f s.
  Proof. intros ? ? ? r. apply (squash_to_prop r).
         { apply isapropifcontr. apply finally. } 
         { intro n. exists (f n). induction n.
           { exists (h_triv s (idpath _)). intro n. reflexivity. }
           { exact (s n#IHn). } } Defined.           

  Definition map_path_check {Y} {f:T->Y} (s:target_paths f) (n:T) :
    forall p : map s (squash_element n) ==
               map s (squash_element (one + n)),
      ap pr1 p == s n.
  Proof. intros. 
         set (q := total2_paths2 (s n) (idpath _) 
                   : map s (squash_element n) == map s (squash_element (one + n))).
         assert (u : q==p). 
         { apply (hlevelntosn 1). apply (hlevelntosn 0). apply finally. }
         destruct u. apply total2_paths2_comp1. Defined.

  (** ** universal property for the half line *)

  Definition halfline_map {Y} {target_points:T->Y} (s:target_paths target_points) : 
    halfline -> Y.
  Proof. intros ? ? ? r. exact (pr1 (map s r)). Defined.

  Definition check_values {Y} {target_points:T->Y} 
             (s:target_paths target_points) (n:T) :
    halfline_map s (squash_element n) == target_points n.
  Proof. reflexivity. Defined.

  Definition check_paths {Y} {target_points:T->Y} 
             (s:target_paths target_points) (n:T) :
    ap (halfline_map s) (squash_path n (one + n)) == s n.
  Proof. intros. refine (_ @ map_path_check s n _).
         apply pathsinv0. apply maponpathscomp. Defined.
 *)

End AffineLine.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/GroupAction.vo"
End:
*)
