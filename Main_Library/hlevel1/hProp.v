(** * Generalities on hProp.  

In this file we introduce the hProp - an analog of Prop defined based on the univalent semantics. We further introduce the hProp version of the "inhabited" construction - i.e. for any [ T ] in [ UU0 ] we construct an object  [ ishinh T ] and a function [ hinhpr : T -> ishinh T ] which plays the role of [ inhabits ] from the Coq standard library.  The semantic meaning of  [ hinhpr ] is that it should be universal among functions from [ T ]  to objects of hProp. Howevere, we can not prove that [ ishinh  T ] is in [ hProp ]. While we can check that it is [ uu1.isaprop ] we can not show that it lies in [ UU0 ]. To place [ ishinh _ ] to [ UU0 ] requires global impredicativity of [ hProp ]. In the future this should be proved using one of the "resizing axioms". At the moment we do all that is possible to do without resizing axioms in this file and then in the next file of the library collect the results and constructions for which this global impredicativity is necessary. The later file does not compile without a patch provided by Hugo Herbelin which turns off the universe consistency verification. We do however keep track of universes in our development "by hand" to ensure that when the resizing axioms will become available the current proofs will verify correctly.

One can achieve similar results with a combination of usual axioms which imitate the resizing axioms, however unlike the usual axioms the resizing axioms do not affect the computation/normalization abilities of Coq which makes them the prefrred choice in this situation.

Using the hinhabited construction we implement the intuitionistic logic on hProp. The part of the logic related to disjunction again requires us to know the global impredicativity of [ hProp ] and is considered in the next file. 


*)



(** *** Preambule *)

Add Rec LoadPath "../Generalities".


Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export uu1uu0.


(** *** Type of properties in [ UU0 ] *)




Definition hProp:= (uu1.total2 UU0 (fun X:UU0 => isaprop X)).
Definition hProppair:= (uu1.tpair  UU0 (fun X:UU0 => isaprop X)).
Definition hptouu0 := uu1.pr21  UU0 (fun X:UU0 => isaprop X): hProp -> UU0.
Coercion hptouu0: hProp >-> UU0.


(** *** Canonical structures of a type of h-level 1 on [ iscontr ] and other standard constructions. *)


Definition iscontr_hprop (X:UU0) := hProppair (iscontr X) (isapropiscontr X). 
Canonical Structure iscontr_hprop.


Definition isofhlevel_hprop ( n: nat ) ( X : UU0 ) := hProppair (isofhlevel n X) (isapropisofhlevel n X).
Canonical Structure isofhlevel_hprop.

Definition isaprop_hprop ( X : UU0 ) := hProppair (isaprop X) (isapropisaprop X).
Canonical Structure isaprop_hprop.





(** *** The [ hProp ] version of the "inhabited" construction. *)



Definition ishinh (X:UU0) := forall P: hProp, ((X->P)->P). 

Theorem uu1isapropishinh (X : UU0) : uu1.isaprop (ishinh X). 
Proof. intro. apply uu1.impred. intro x. apply uu1.impred.  intro. apply (u0isaproptou1isaprop _ (uu1.pr22 _ _ x)). Defined.  



Definition hinhpr (X:UU0): X -> ishinh X := fun x:X => fun P: hProp  => adjev X P x.
Definition hinhfunct (X Y:UU0)(f:X -> Y) : ishinh X -> ishinh Y := fun inx1: ishinh X => fun P:_ =>  fun yp: Y -> P => (inx1 P (fun x: X => yp (f x))).
Definition hinhuniv (X:UU0)(P: hProp ) : (X -> P) -> ((ishinh X) -> P) := fun xp:_ => fun inx1:_ => inx1 P xp.
Definition hinhand (X Y:UU0)(inx1: ishinh X)(iny1: ishinh Y) : ishinh (dirprod X Y):= fun P:_  => ddualand X Y P (inx1 P) (iny1 P).
Definition hinhfunct2 (X Y Z:UU0): (X -> Y -> Z) -> (ishinh X -> ishinh Y -> ishinh Z).
Proof. intros X Y Z X0 X1 X2. apply (hinhfunct _ _ (fun xy: dirprod X Y => X0 (pr21 _ _ xy) (pr22 _ _ xy)) (hinhand _ _ X1 X2)).  Defined. 


Definition hinhunivcor1 (P:hProp): ishinh P -> P := hinhuniv P P (fun p:P => p).



(** *** Intuitionistic logic on [ hProp ]. *)



Definition htrue : hProp := hProppair unit isapropunit.
Canonical Structure htrue.

Definition hfalse : hProp := hProppair empty isapropempty.
Canonical Structure hfalse.


Definition hconj (P Q : hProp) : hProp := hProppair (dirprod P Q) (isofhleveldirprod (S O) _ _ (uu1.pr22 _ _ P) (uu1.pr22 _ _ Q)). 
Canonical Structure hconj.

Definition uu1hdisj (P Q : hProp) :=  ishinh (coprod P Q). 


Definition hneg (P: hProp) : hProp.
Proof. intro. split with (P -> empty). apply impred. intro. apply isapropempty. Defined.
Canonical Structure hneg.

Definition himpl (P Q : hProp) : hProp.
Proof. intros. split with (P -> Q). apply impred. intro. apply (uu1.pr22 _ _ Q). Defined. 
Canonical Structure himpl.  


Definition hforall (X : UU0) (P: X -> hProp) : hProp.
Proof. intros. split with (forall x:X, P x). apply impred. intro.  apply (uu1.pr22 _ _ (P t)). Defined.

Definition hexists (X:UU0) (P: X -> hProp) := ishinh (total2 X P).

Definition wittohexists (X : UU0)(P: X -> hProp)(x:X)(is: P x): hexists X P := hinhpr (total2 X P) (tpair _ _ x is).




(** *** The double negation version of [ hinhabited ]. *)


Definition isinhdneg (X:UU0) : UU0 := dneg X.
Definition inhdnegpr (X:UU0): X -> isinhdneg X := todneg X.
Definition inhdnegfunct (X Y:UU0)(f:X -> Y): isinhdneg X -> isinhdneg Y := dnegf _ _ f.
Definition inhdneguniv (X: UU0)(P:UU0)(is:isweq _ _ (todneg P)): (X -> P) -> ((isinhdneg X) -> P) := fun xp:_ => fun inx0:_ => (invmap _ _ _ is (dnegf _ _ xp inx0)).
Definition inhdnegand (X Y:UU0)(inx0: isinhdneg X)(iny0: isinhdneg Y) : isinhdneg (dirprod X Y) := dneganddnegimpldneg _ _ inx0 iny0.


Definition hinhimplinhdneg (X:UU0)(inx1: ishinh X): isinhdneg X := inx1 hfalse.





(* End of the file hlevel1_UU0_generalities.v *)




(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)