(** * Group actions *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.algebra1b.
Require Import Foundations.Proof_of_Extensionality.funextfun.
Require RezkCompletion.pathnotations.
Import pathnotations.PathNotations. 
Require Import Ktheory.Utilities.
Require RezkCompletion.precategories.
Import Utilities.Notation.

Goal forall X Y (f:weq X Y), eqweqmap (weqtopaths f) == f.
Proof. intros.
       (* an example that shows how computation can get stuck on an axiom: *)
       compute. 
       (* "reflexivity" would not work here *) 
       apply weqpathsweq. Defined.

Definition A {X Y:hSet} (e:set_to_type X==set_to_type Y) : X==Y.
Proof. intros [X i] [Y j] ?.
       apply (pair_path e (pr1 (isapropisaset Y (e#i) j))). Defined.       

Definition A' {X Y:hSet} (e:set_to_type X==set_to_type Y) : 
  ap set_to_type (A e) == e.
Proof. intros [X i] [Y j] e. apply pair_path_comp1. Defined.

(* verify transport on idpath computes *)
Goal forall X (P:X->Type) (x:X) (p:P x), idpath x # p == p.
Proof. reflexivity. Defined.

Definition acts_on G X := G -> X -> X.

Record type (G:gr) :=
  make {
      act_set :> hSet;
      act_mult : acts_on G act_set;
      act_unit : forall x, act_mult (unel _) x == x;
      act_assoc : forall g h x, act_mult (op g h) x == act_mult g (act_mult h x)
    }.
Arguments act_set {G} _.
Arguments act_mult {G} _ g x.
Local Notation action := type.

Definition is_equivariant {G:gr} {X Y:action G} (f:X->Y) :=
  forall g x, f (act_mult X g x) == act_mult Y g (f x).

Definition is_equivariant_isaprop {G:gr} {X Y:action G} (f:X->Y) : 
  isaprop (is_equivariant f).
Proof. intros. apply impred; intro g. apply impred; intro x. 
       apply setproperty. Defined.               

Definition equivariant_map {G:gr} (X Y:action G) := total2 (@is_equivariant _ X Y).

Definition mult_map {G:gr} {X:action G} (x:X) := fun g => act_mult _ g x.

Definition is_torsor (G:gr) (X:action G) := 
  dirprod (ishinh X) (forall x:X, isweq (mult_map x)).

Definition Torsor (G:gr) := total2 (is_torsor G).
Definition underlying_action {G:gr} (X:Torsor G) := pr1 X.
Coercion underlying_action : Torsor >-> action.

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

Definition univ_map {G:gr} (X:Torsor G) (x:X) : equivariant_map (trivialTorsor G) X.
Proof. intros ? ? ?. exists (univ_function X x).
       intros g h. apply act_assoc. Defined.

Definition triviality_isomorphism {G:gr} (X:Torsor G) (x:X) :
  weq (trivialTorsor G) X.
Proof. intros. exists (univ_function X x). apply (pr2 (pr2 X)). Defined.

Definition action_eq {G:gr} {X Y:action G} (p: (X:Type) == (Y:Type)) :
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

Definition cast {T U:Type} (p:T==U) (t:T) : U.
Proof. intros. destruct p. exact t. Defined.

Definition B {G:gr} {X Y:action G} (f:weq X Y) (ie:is_equivariant (pr1 f)) : 
  X == Y.
Proof. intros. set (p := weqtopaths f).
       assert (ip := cast (!ap is_equivariant (ap pr1 (weqpathsweq f))) ie
                  : is_equivariant (eqweqmap p)).
       exact (action_eq p ip). Defined.

Lemma is_connected_classifying_space (G:gr) : isconnected(Torsor G).
Proof.                          (* this uses univalence *)
  intros ?. apply (base_connected (trivialTorsor _)).
  intros X. apply (squash_to_prop (pr1 (pr2 X))). 
  { apply pr2. }
  { intros x. apply hinhpr. assert (q : pr1(trivialTorsor G) == pr1 X).
    { assert (r : act_set(pr1(trivialTorsor G)) == act_set(pr1 X)).
      { apply A. apply weqtopaths. 
        apply triviality_isomorphism. exact x. }
      admit. }
    { admit. } } Defined.
