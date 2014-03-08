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
       with make act_mult act_unit act_assoc => idpath _ end.
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

Definition SetWithAction (G:gr) := total2 (ActionStructure G). 
Definition makeSetWithAction {G:gr} (X:hSet) (ac:ActionStructure G X) :=
  X,,ac : SetWithAction G.

Definition ac_set {G:gr} (X:SetWithAction G) := pr1 X.
Coercion ac_set : SetWithAction >-> hSet.
Definition ac_type {G:gr} (X:SetWithAction G) := pr1hSet (ac_set X).
Definition ac_str {G:gr} (X:SetWithAction G) := pr2 X : ActionStructure G (ac_set X).
Definition ac_mult {G:gr} (X:SetWithAction G) := act_mult (pr2 X).
Local Notation "g * x" := (ac_mult _ g x).

Definition is_equivariant {G:gr} {X Y:SetWithAction G} (f:X->Y) := 
  forall g x, f (g*x) == g*(f x).

Definition is_equivariant_isaprop {G:gr} {X Y:SetWithAction G} (f:X->Y) : 
  isaprop (is_equivariant f).
Proof. intros. apply impred; intro g. apply impred; intro x. 
       apply setproperty. Defined.               

(** The following fact is fundamental: it shows that our definition of
    [is_equivariant] captures all of the structure.  The proof reduces to the
    showing that if G acts on a set X in two ways, and the identity function is
    equivariant, then the two actions are equal.  A similar fact will hold in
    other cases: groups, rings, monoids, etc. *)

Definition is_equivariant_identity {G:gr} {X Y:SetWithAction G}
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
         { apply funextfunax; intro g. apply funextfunax; intro x; simpl in x.
           exact (i g x). } 
         destruct p. clear i. assert (p:Xu==Yu).
         { apply funextsec; intro x; simpl in x. apply setproperty. }
         destruct p. assert (p:Xa==Ya).
         { apply funextsec; intro g. apply funextsec; intro h.
           apply funextsec; intro x. apply setproperty. }
         destruct p. reflexivity. }
       { intro p. apply isaset_ActionStructure. }
       { intro is. apply is_equivariant_isaprop. } Defined.

Definition is_equivariant_comp {G:gr} {X Y Z:SetWithAction G} 
           (p:X->Y) (i:is_equivariant p)
           (q:Y->Z) (j:is_equivariant q) : is_equivariant (funcomp p q).
Proof. intros. intros g x. exact (ap q (i g x) @ j g (p x)). Defined.

Definition EquivariantMap {G:gr} (X Y:SetWithAction G) := total2 (@is_equivariant _ X Y).
Definition underlyingFunction {G:gr} {X Y:SetWithAction G} (f:EquivariantMap X Y) := pr1 f.
Definition equivariantProperty {G:gr} {X Y:SetWithAction G} (f:EquivariantMap X Y) := pr2 f.
Coercion underlyingFunction : EquivariantMap >-> Funclass.

Definition composeEquivariantMap {G:gr} (X Y Z:SetWithAction G)
           (p:EquivariantMap X Y) (q:EquivariantMap Y Z) : EquivariantMap X Z.
Proof. intros ? ? ? ? [p i] [q j]. exists (funcomp p q).
       apply is_equivariant_comp. assumption. assumption. Defined.

Definition EquivariantEquiv {G:gr} (X Y:SetWithAction G) := 
  total2 (fun f:weq X Y => is_equivariant f).
Definition underlyingEquiv {G:gr} {X Y:SetWithAction G} (e:EquivariantEquiv X Y) := pr1 e.
Coercion underlyingEquiv : EquivariantEquiv >-> weq.
Lemma underlyingEquiv_incl {G:gr} {X Y:SetWithAction G} :
  isincl (underlyingEquiv : EquivariantEquiv X Y -> weq X Y).
Proof. intros. apply isinclpr1; intro f. apply is_equivariant_isaprop. Defined.
Lemma underlyingEquiv_injectivity {G:gr} {X Y:SetWithAction G}
      (e f:EquivariantEquiv X Y) :
  weq (e == f) (underlyingEquiv e == underlyingEquiv f).
Proof. intros. apply weqonpathsincl. apply underlyingEquiv_incl. Defined.

Definition underlyingEquivariantMap {G:gr} {X Y:SetWithAction G} (e:EquivariantEquiv X Y) := 
  pr1weq _ _ (pr1 e),, pr2 e.
Definition idEquivariantEquiv {G:gr} (X:SetWithAction G) : EquivariantEquiv X X.
Proof. intros. exists (idweq _). intros g x. reflexivity. Defined.
Definition composeEquivariantEquiv {G:gr} {X Y Z:SetWithAction G}
           (e:EquivariantEquiv X Y) (f:EquivariantEquiv Y Z) : EquivariantEquiv X Z.
Proof. intros ? ? ? ? [e i] [f j]. exists (weqcomp e f).
       destruct e as [e e'], f as [f f']; simpl.
       apply is_equivariant_comp. exact i. exact j. Defined.
Definition path_to_EquivariantEquiv {G:gr} {X Y:SetWithAction G} (e:X==Y) :
  EquivariantEquiv X Y.
Proof. intros. destruct e. exact (idEquivariantEquiv X). Defined.

Definition mult_map {G:gr} {X:SetWithAction G} (x:X) := fun g => g*x.

(** ** Applications of univalence *)

Lemma id_to_eqweq {G:gr} {X Y:SetWithAction G} : weq (X==Y) (EquivariantEquiv X Y).
Proof. intros.
       refine (weqcomp (total_paths_equiv (ActionStructure G) X Y) _).
       refine (weqbandf _ _ _ _).
       { refine (weqcomp (pr1hSet_injectivity _ _) (weqpair (@eqweqmap (pr1 X) (pr1 Y)) (univalenceaxiom _ _))). }
       simpl. intro p. refine (weqcomp (is_equivariant_identity p) _).
       exact (eqweqmap (ap is_equivariant (pr1_eqweqmap (ap set_to_type p)))).
Defined.

(** ** Torsors *)

Definition is_torsor {G:gr} (X:SetWithAction G) := 
  dirprod (ishinh X) (forall x:X, isweq (mult_map x)).

Lemma is_torsor_isaprop {G:gr} (X:SetWithAction G) : isaprop (is_torsor X).
Proof. intros. apply isofhleveldirprod.
       { apply propproperty. }
       { apply impred; intro x. apply isapropisweq. } Qed.

Definition Torsor (G:gr) := total2 (@is_torsor G).
Definition underlyingAction {G} (X:Torsor G) := pr1 X : SetWithAction G.
Coercion underlyingAction : Torsor >-> SetWithAction.
Definition is_torsor_prop {G} (X:Torsor G) := pr2 X.
Definition torsor_nonempty {G} (X:Torsor G) := pr1 (is_torsor_prop X).
Definition torsor_splitting {G} (X:Torsor G) := pr2 (is_torsor_prop X).
Definition torsor_mult_weq {G} (X:Torsor G) (x:X) := 
  weqpair (mult_map x) (torsor_splitting X x) : weq G X.
Definition PointedTorsor (G:gr) := total2 (fun X:Torsor G => X).
Definition underlyingTorsor {G} (X:PointedTorsor G) := pr1 X : Torsor G.
Coercion underlyingTorsor : PointedTorsor >-> Torsor.
Definition underlyingPoint {G} (X:PointedTorsor G) := pr2 X : X.

Lemma is_quotient {G} (X:Torsor G) (y x:X) : iscontr (total2 (fun g => g*x == y)).
Proof. intros. exact (pr2 (is_torsor_prop X) x y). Defined.

Definition quotient {G} (X:Torsor G) (y x:X) := pr1 (the (is_quotient X y x)) : G.
Local Notation "y / x" := (quotient _ y x).

Lemma quotient_eq {G} (X:Torsor G) (y x:X) : (y/x)*x == y.
Proof. intros. exact (pr2 (the (is_quotient X y x))). Defined.

Definition trivialTorsor (G:gr) : Torsor G.
Proof. 
  intros. exists (makeSetWithAction G (make G G op (lunax G) (assocax G))).
  exact (hinhpr _ (unel G),, 
         fun x => precategories.iso_set_isweq 
           (fun g => op g x) 
           (fun g => op g (grinv _ x))
           (fun g => assocax _ g x (grinv _ x) @ ap (op g) (grrinvax G x) @ runax _ g)
           (fun g => assocax _ g (grinv _ x) x @ ap (op g) (grlinvax G x) @ runax _ g)).
Defined.

Definition pointedTrivialTorsor (G:gr) : PointedTorsor G.
Proof. intros. exists (trivialTorsor G). exact (unel G). Defined.

Definition univ_function {G:gr} (X:Torsor G) (x:X) : trivialTorsor G -> X.
Proof. intros ? ? ?. apply mult_map. assumption. Defined.

Definition univ_function_pointed {G:gr} (X:Torsor G) (x:X) :
  univ_function X x (unel _) == x.
Proof. intros. apply act_unit. Defined.

Definition univ_function_is_equivariant {G:gr} (X:Torsor G) (x:X) : 
  is_equivariant (univ_function X x).
Proof. intros. intros g h. apply act_assoc. Defined.

Definition triviality_isomorphism {G:gr} (X:Torsor G) (x:X) :
  EquivariantEquiv (trivialTorsor G) X.
Proof. intros. 
       exact (torsor_mult_weq X x,, univ_function_is_equivariant X x). Defined.

Definition trivialTorsorEquiv (G:gr) (g:G) : weq (trivialTorsor G) (trivialTorsor G).
Proof. intros. exists (fun h => op h g). apply (gradth _ (fun h => op h (grinv G g))).
       { exact (fun h => assocax _ _ _ _ @ ap (op _) (grrinvax _ _) @ runax _ _). }
       { exact (fun h => assocax _ _ _ _ @ ap (op _) (grlinvax _ _) @ runax _ _). }
Defined.

Definition trivialTorsorAuto (G:gr) (g:G) : 
  EquivariantEquiv (trivialTorsor G) (trivialTorsor G).
Proof. intros. exists (trivialTorsorEquiv G g).
       intros h x. simpl.  exact (assocax _ h x g). Defined.

Lemma pr1weq_injectivity {X Y} (f g:weq X Y) : weq (f==g) (pr1weq _ _ f==pr1weq _ _ g).
Proof. intros. apply weqonpathsincl. apply isinclpr1weq.  Defined.

Definition autos (G:gr) : weq G (EquivariantEquiv (trivialTorsor G) (trivialTorsor G)).
Proof. intros. exists (trivialTorsorAuto G). refine (gradth _ _ _ _).
       { intro f. exact (f (unel G)). } { intro g; simpl. exact (lunax _ g). }
       { intro f; simpl. apply (invweq (underlyingEquiv_injectivity _ _)); simpl.
         apply (invweq (pr1weq_injectivity _ _)). apply funextfunax; intro g.
         simpl. exact ((! (pr2 f) g (unel G)) @ (ap (pr1 f) (runax G g))).
       } Defined.

Lemma trivialTorsorAuto_unit (G:gr) : 
  trivialTorsorAuto G (unel _) == idEquivariantEquiv _.
Proof. intros. refine (pair_path _ _).
       { refine (pair_path _ _).
         { apply funextsec; intro x; simpl. exact (runax G x). }
         { apply isapropisweq. } }
       { apply is_equivariant_isaprop. } Defined.

Lemma trivialTorsorAuto_mult (G:gr) (g h:G) :
  composeEquivariantEquiv (trivialTorsorAuto G g) (trivialTorsorAuto G h) 
  == (trivialTorsorAuto G (op g h)).
Proof. intros. refine (pair_path _ _).
       { refine (pair_path _ _).
         { apply funextsec; intro x; simpl. exact (assocax _ x g h). }
         { apply isapropisweq. } }
       { apply is_equivariant_isaprop. } Defined.

(** ** Applications of univalence *)

Definition torsor_id_to_eqweq {G:gr} {X Y:Torsor G} : weq (X==Y) (EquivariantEquiv X Y).
Proof. admit.
Defined.

Definition torsor_eqweq_to_path {G:gr} {X Y:Torsor G} : EquivariantEquiv X Y -> X == Y.
Proof. intros ? ? ? f. exact ((invweq torsor_id_to_eqweq) f). Defined.

Definition PointedEquivariantEquiv {G:gr} (X Y:PointedTorsor G) 
           := total2 (fun
                         f:EquivariantEquiv X Y => 
                         f (underlyingPoint X) == underlyingPoint Y).

Definition pointed_triviality_isomorphism {G:gr} (X:PointedTorsor G) :
  PointedEquivariantEquiv (pointedTrivialTorsor G) X.
Proof. intros ? [X x]. exists (triviality_isomorphism X x).
       simpl. apply univ_function_pointed. Defined.       

Definition pointed_torsor_id_to_eqweq {G:gr} {X Y:PointedTorsor G} : 
  weq (X==Y) (PointedEquivariantEquiv X Y).
Proof. admit.
Defined.

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
       apply pathsinv0. apply (invweq pointed_torsor_id_to_eqweq).
       apply pointed_triviality_isomorphism. Defined.

Theorem loopsBG (G:gr) : weq (Ω (B G)) G.
Proof. intros. refine (weqcomp torsor_id_to_eqweq _). 
       apply invweq. apply autos. Defined.

Require Import Foundations.hlevel2.hz.
Definition ℤ := hzaddabgr.
Definition circle := B ℤ.

Theorem loops_circle : weq (Ω circle) ℤ.
Proof. apply loopsBG. Defined.
