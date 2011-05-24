(** * Introduction 

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

*)




(** Preambule. *)

Unset Automatic Introduction.  (** This line has to be removed for the file to compile with Coq8.2 *)

Definition UUU:= Type.

Identity Coercion UUtoType:UUU >-> Sortclass.


(** We introduce our own definitions for unit (one point set), empty type and nat (the set of natural numbers) to be used throught the library. *)

Inductive empty : UUU := .

Inductive unit : UUU := tt : unit .

Inductive nat : UUU := O : nat | S : nat -> nat .

Inductive bool : UUU := true : bool | false : bool .




Inductive identity (A:Type) (a:A) : A -> Type :=
  identity_refl : identity _ a a.
Hint Resolve identity_refl: core.

Notation paths := identity .
Notation idpath := identity_refl .


Check (paths nat O O) .
























(* End of the file uuu.v *)






(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)


