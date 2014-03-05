(** * Group actions *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.algebra1b.
Require Import Foundations.Proof_of_Extensionality.funextfun.
Require RezkCompletion.pathnotations.
Import pathnotations.PathNotations. 
Require Import Ktheory.Utilities.
Require RezkCompletion.precategories.
Require RezkCompletion.auxiliary_lemmas_HoTT.
Import Utilities.Notation.

(** ** Definitions *)

Definition action_op G X := G -> X -> X.

Record Action (G:gr) :=
  make {
      act_set :> hSet;
      act_mult : action_op G act_set;
      act_unit : forall x, act_mult (unel _) x == x;
      act_assoc : forall g h x, act_mult (op g h) x == act_mult g (act_mult h x)
    }.
Arguments act_set {G} _.
Arguments act_mult {G} _ g x.

Definition is_equivariant {G:gr} {X Y:Action G} (f:X->Y) :=
  forall g x, f (act_mult X g x) == act_mult Y g (f x).

Definition is_equivariant_isaprop {G:gr} {X Y:Action G} (f:X->Y) : 
  isaprop (is_equivariant f).
Proof. intros. apply impred; intro g. apply impred; intro x. 
       apply setproperty. Defined.               

Definition equivariant_map {G:gr} (X Y:Action G) := total2 (@is_equivariant _ X Y).
Definition equivariant_map_to_function {G:gr} {X Y:Action G}
  (f:equivariant_map X Y) := pr1 f.
Coercion equivariant_map_to_function : equivariant_map >-> Funclass.

Definition equivariant_weq {G:gr} (X Y:Action G) := 
  total2 (fun f:weq X Y => is_equivariant f).

Definition mult_map {G:gr} {X:Action G} (x:X) := fun g => act_mult _ g x.

(** *** Applications of univalence *)

Definition action_eq {G:gr} {X Y:Action G} (p: (X:Type) == (Y:Type)) :
  is_equivariant (eqweqmap p) -> X == Y.
Proof. intros ? ? ? ? i.
       destruct X as [[X iX] Xm Xu Xa]; destruct Y as [[Y iY] Ym Yu Ya];
       simpl in Xu, Yu, Xa, Ya, p. destruct p.
       simpl in i. assert (p := pr1 (isapropisaset _ iX iY)). destruct p.
       assert (p : Xm == Ym).
       { apply funextfunax; intro g. apply funextfunax; intro x; simpl in x.
         exact (i g x). } 
       destruct p. clear i. assert (p : Xu == Yu).
       { apply funextsec; intro x; simpl in x. apply iX. }
       destruct p. assert (p:Xa == Ya).
       { apply funextsec; intro g. apply funextsec; intro h.
         apply funextsec; intro x. apply iX. }
       destruct p. reflexivity. Defined.

Definition eqweq_to_id {G:gr} {X Y:Action G} : equivariant_weq X Y -> X == Y.
Proof. intros ? ? ? f. destruct f as [f ie]. set (p := weqtopaths f).
       exact (action_eq p 
                (cast (!ap is_equivariant (ap (pr1weq _ _) (weqpathsweq f))) ie
          : is_equivariant (eqweqmap p))). Defined.

(** ** Torsors *)

Definition is_torsor {G:gr} (X:Action G) := 
  dirprod (ishinh X) (forall x:X, isweq (mult_map x)).

Lemma is_torsor_isaprop {G:gr} (X:Action G) : isaprop (is_torsor X).
Proof. intros. apply isofhleveldirprod.
       { apply auxiliary_lemmas_HoTT.propproperty. }
       { apply impred; intro x. apply isapropisweq. } Qed.

Definition Torsor (G:gr) := total2 (@is_torsor G).
Definition underlying_action {G:gr} (X:Torsor G) := pr1 X.
Definition is_torsor_prop {G:gr} (X:Torsor G) := pr2 X.
Definition torsor_nonempty {G:gr} (X:Torsor G) := pr1 (is_torsor_prop X).
Definition torsor_splitting {G:gr} (X:Torsor G) := pr2 (is_torsor_prop X).
Coercion underlying_action : Torsor >-> Action.

Definition trivialTorsor (G:gr) : Torsor G.
Proof. 
  intros. exists (make G G op (lunax G) (assocax G)).
  exact (hinhpr _ (unel G),, 
         fun x => precategories.iso_set_isweq 
           (fun g => op g x) 
           (fun g => op g (grinv _ x))
           (fun g => assocax _ g x (grinv _ x) @ ap (op g) (grrinvax G x) @ runax _ g)
           (fun g => assocax _ g (grinv _ x) x @ ap (op g) (grlinvax G x) @ runax _ g)).
Defined.

Definition univ_function {G:gr} (X:Torsor G) (x:X) : trivialTorsor G -> X.
Proof. intros ? ? ?. apply mult_map. assumption. Defined.

Definition univ_function_is_equivariant {G:gr} (X:Torsor G) (x:X) : 
  is_equivariant (univ_function X x).
Proof. intros. intros g h. apply act_assoc. Defined.

Definition univ_map {G:gr} (X:Torsor G) (x:X) : equivariant_map (trivialTorsor G) X.
Proof. intros ? ? ?. exists (univ_function X x).
       apply univ_function_is_equivariant. Defined.

Definition triviality_isomorphism {G:gr} (X:Torsor G) (x:X) :
  equivariant_weq (trivialTorsor G) X.
Proof. intros. exact ((univ_function X x,, 
                       torsor_splitting X x),,
                       univ_function_is_equivariant X x). Defined.

(** *** Applications of univalence *)

Definition torsor_eqweq_to_id {G:gr} {X Y:Torsor G} : equivariant_weq X Y -> X == Y.
Proof. intros ? ? ? f. assert (p := eqweq_to_id f). destruct X as [X iX]. 
       destruct Y as [Y iY]. simpl in p. destruct p.
       assert(p : iX == iY). { apply is_torsor_isaprop. }
       destruct p. reflexivity. Defined.

Lemma torsor_type_connectedness (G:gr) : isconnected(Torsor G).
Proof. intros. apply (base_connected (trivialTorsor _)).
  intros X. apply (squash_to_prop (torsor_nonempty X)). 
  { apply auxiliary_lemmas_HoTT.propproperty. }
  intros x. apply hinhpr. apply (torsor_eqweq_to_id (triviality_isomorphism X x)). 
Defined.
