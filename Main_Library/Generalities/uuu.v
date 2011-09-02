(** * Introduction ( by Vladimir Voevodsky , Feb. 2010 - Jun. 2011 ) 

This is the first of the group of files which contain the (current state of) the mathematical library for the proof assistant Coq based on the Univalent Foundations.
This particular files contains only definitions and results which do not depend on the concept of equality and dependent sums.

Univalent Foundations are inspired by the univalent model of type theory which interprets types as homotopy types, Martin-Lof equality as paths spaces and universes as bases of universal ("univalent") fibrations. For a detailed overview of the content see the table of content in toc.html . In has been modified from the eralier version in a several places but most importantly the part of the earlier file concerning the h-version of the inhabited construction and constructions related to finite sets have been moved to separate files.  

I tried to keep the notations such that the names of types which are (expected to be) a property in the sense of being of h-level 1 start with "is" but I have not been very consistent about it.

There is an increasing number of theorems which have very short proofs based on the univalence axiom  which are given much longer proofs here. One hopes that eventually a mechnaical procedure for the replacement of proofs using the univalence axiom by proofs which only use it in some computationally uninformative ways will be found but until then I am not using the univalence axiom in any of the constructions. 


IMPORTANT: for those who may want to add to these files. There are some rules which have to be followed in creating new definitions and theorems which at the moment are not tracked by the proof checker.

1. The current system of Coq is not completely compatible with the univalent semantics. The problem (the only one as far as I know) lies in the way the universe levels (u-levels) are assigned to the objects defined by the inductive definitions of the form

Inductive Ind (...)...(...): A -> Type := ...


The current u-level assignemet takes into account the u-levels of the constructors but not the u-level of A. To ensure compatibility with the univalent model the u-level of Ind should be no less than the u-level of A. The u-levels of the parameters (the types appearing in (...)...(...) ) do not matter. 

A particular case of this problem is the "singleton elimination" rule which provides a good example of this incompatibility. The inductive definition of the identity types which uses one of the points as a parametr has A=:T (the underlying type) but since no mention of T appears in the constructor the system considers that there are no u-level restrictions on the resulting object and in particular that it can be placed in Prop while still having the full Ind_rect elimninator (see elimination, singleton elimination in the Index to the Refernce Manual). 

Since in the present approach the universe management is made explicit one has:

RULE 1 Do not use inductive definitions of the form 

Inductive Ind (...)...(...): A -> UU := ...

unless all the "arguments" of A can be typed to UU.


2. While it does not lead directly to any contradictions the shape of the foundations suggests very strongly that at the moment it is best to completely avoid the use of the universes Prop and Set. Instead we should use the the conditions isaprop and isaset which are applicable to the types of any of the type universes.  

Note on implicit arguments : In the latest version of my univalent library I started to systematically use implicit arguments.  The rules which I am using for assessing which arguments should be made implicit are somewhat different from the rules which the automatic Coq system for detection of implicit arguments is using. For example given arguments ( X : Type ) ( x : X ) , the Coq command Implicit Arguments would assign implicit ( although *not* strict implicit ) status to X . I do not consider X to be an implicit argument in this case due to the existence of subtyping for universes . On the other hand I do make the type argument of [ paths ] to be implicit because [ paths X X' ] is in fact independent from the universe in which X and X' are considered. 

*)




(** Preambule. *)

Unset Automatic Introduction.  (** This line has to be removed for the file to compile with Coq8.2 *)


(** The empty type is introduced in Coq.Init.Datatypes by the line :

Inductive Empty_set : Set := .

*)


Notation UUU := Set .
Notation empty := Empty_set. 

(** Idenity types are introduced in Coq.Init.Datatypes by the lines : 

Inductive identity ( A:Type ) (a:A) : A -> Type := identity_refl : identity _ a a.
Hint Resolve identity_refl : core. 

*)

Notation paths := identity .
Notation idpath := identity_refl .

(**  *** Dependent sums (fibrations) *)

Record total2 { T: Type } ( P: T -> Type ) := tpair { pr21_c : T ; pr22_c : P pr21_c }. 

Definition pr21 { T: Type } { P : T -> Type } ( tp : total2 P ) := match tp with tpair t p => t end .
Definition pr22 { T: Type } { P : T -> Type } ( tp : total2 P ) := match tp as a return P ( pr21 a ) with tpair t p => p end . 

Implicit Arguments tpair [ T ] .
(* Implicit Arguments pr21 [ T P ] .
Implicit Arguments pr22 [ T P ] . *)


(** One can not use a new record each time one needs it because the general theorems about this construction would not apply to new instances of "Record" due to the "generativity" of inductive definitions in Coq. One could use "Inductive" instead of "Record" here but using "Record" which is equivalent to "Structure" allows us later to use the mechanism of canonical structures with total2. *)


(** [ sum A B ], written [ A + B ], is the disjoint sum of [A] and [B] . The lest and right inclusions are denoted by [ inl ] and [ inr ] in Coq.Init.Datatypes  *)

Notation coprod := sum .

Notation ii1fun := inl .
Notation ii2fun := inr .

Notation ii1 := inl .
Notation ii2 := inr .
Implicit Arguments ii1 [ A B ] .
Implicit Arguments ii2 [ A B ] .


Check (paths O O) .
























(* End of the file uuu.v *)






(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)


