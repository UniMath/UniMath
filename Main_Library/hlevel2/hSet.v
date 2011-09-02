(** * Generalities on [ hSet ] .  Vladimir Voevodsky. Feb. - Sep. 2011 

In this file we introduce the type [ hSet ] of h-sets i.e. of types of h-level 2 as well as a number of constructions such as type of (monic) subtypes, images, surjectivity etc. which, while they formally apply to functions between arbitrary types actually only depend on the behavior of the function on the sets of connected componenets of these types. 

While it is possible to write a part of this file in a form which does not require RR1 it seems like a waste of effort since it would require to repeat a lot of things twice. Accordingly we assume RR1 from the start in dealing with sets. The drawback is that all the subsequent files will not compile at the moment without the Type in Type patch.

*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export hProp .


(** ** The type of sets i.e. of types of h-level 2 in [ UU ] *) 

Definition hSet:= total2 (fun X : UU => isaset X) .
Definition hSetpair := tpair (fun X : UU => isaset X).
Definition pr21hSet:= @pr21 UU (fun X : UU => isaset X) : hSet -> Type.
Coercion pr21hSet: hSet >-> Sortclass.

Definition eqset { X : hSet } ( x x' : X ) : hProp := hProppair _ ( pr22 X x x' ) . 

Definition setproperty ( X : hSet ) := pr22 X . 

Definition setdirprod ( X Y : hSet ) : hSet .
Proof . intros . split with ( dirprod X Y ) . apply ( isofhleveldirprod 2 ) .  apply ( pr22 X ) . apply ( pr22 Y ) . Defined . 

(** Booleans as a set *)

Definition boolset : hSet := hSetpair bool isasetbool .


(** ** Types [ X ] which satisfy " weak " axiom of choice for all families [ P : X -> UU0 ] 

Weak axiom of choice for [ X ] is the condition that for any family [ P : X -> UU0 ] over [ X ] such that all members of the family are inhabited the space of sections of the family is inhabited . Equivalently one can formulate it as an assertion that for any surjection ( see below ) [ p : Y -> X ] the space of sections of this surjection i.e. functions [ s : X -> Y ] together with a homotopy from [ funcomp s p ] to [ idfun X ] is inhabited . It does not provide a choice of a section for such a family or a surjection . In topos-theoretic semantics this condition corresponds to " local projectivity " of [ X ] . It automatically holds for the point [ unit ] but need not hold for sub-objects of [ unit ] i.e. for types of h-level 1 ( propositions ) . In particular it does not have to hold for general types with decidable equality . 

Intuition based on standard univalent models suggests that any type satisfying weak axiom of choice is a set . Indeed it seems to be possible to show that if both a type and the set of connected components of this type ( see below ) satisfy weak  axiom of choice then the type is a set . In particular , if one imposes weak axiom of choice for sets as an axiom then it would follow that every type satisfying weak axiom of choice is a set . I do not know however if there are models which would validate a possibility of types other than sets to satisfy weak axiom of choice . 


*)

Definition ischoicebase_uu1 ( X : UU0 ) := forall P : X -> UU0 , ( forall x : X , ishinh ( P x ) ) -> ishinh ( forall x : X , P x ) .

Lemma isapropischoicebase ( X : UU0 ) : isaprop ( ischoicebase_uu1 X ) .  (** Uses RR1 *)
Proof .  intro . apply impred . intro P .  apply impred . intro fs . apply ( pr22 ( ishinh _ ) ) .  Defined . 

Definition ischoicebase ( X : UU0 ) : hProp := hProppair _ ( isapropischoicebase X ) . 


Lemma ischoicebaseweqf { X Y : UU0 } ( w : weq X Y ) ( is : ischoicebase X ) : ischoicebase Y .
Proof . intros . unfold ischoicebase . intros Q fs . apply ( hinhfun ( invweq ( weqonsecbase Q w ) ) ) .   apply ( is ( funcomp w Q ) ( fun x : X => fs ( w x ) ) ) .  Defined . 

Lemma ischoicebaseweqb { X Y : UU0 } ( w : weq X Y ) ( is : ischoicebase Y ) : ischoicebase X .
Proof . intros . apply ( ischoicebaseweqf ( invweq w ) is ) . Defined . 

Lemma ischoicebaseunit : ischoicebase unit .
Proof . unfold ischoicebase . intros P fs .  apply ( hinhfun ( tosecoverunit P ) ) .  apply ( fs tt ) .  Defined .

Lemma ischoicebasecontr { X : UU0 } ( is : iscontr X ) : ischoicebase X .
Proof . intros . apply ( ischoicebaseweqb ( weqcontrtounit is )  ischoicebaseunit ) . Defined . 

Lemma ischoicebaseempty : ischoicebase empty .
Proof . unfold ischoicebase . intros P fs .  apply ( hinhpr _ ( fun x : empty => fromempty x ) ) .  Defined .

Lemma ischoicebaseempty2 { X : UU0 } ( is : neg X ) : ischoicebase X .
Proof . intros . apply ( ischoicebaseweqb ( weqtoempty is ) ischoicebaseempty ) . Defined .

Lemma ischoicebasecoprod { X Y : UU0 } ( isx : ischoicebase X ) ( isy : ischoicebase Y ) :  ischoicebase ( coprod X Y ) .
Proof . intros .  unfold ischoicebase .  intros P fs .  apply ( hinhfun ( invweq ( weqsecovercoprodtoprod P ) ) ) .  apply hinhand . apply ( isx _ ( fun x : X => fs ( ii1 x ) ) ) . apply ( isy _ ( fun y : Y => fs ( ii2 y ) ) ) .  Defined . 








(** ** The type of monic sybtypes of a type (subsets of the set of connected components) *)


(** *** Genneral definitions *)

Definition hsubtypes ( X : UU0 ) :=  X -> hProp .
Identity Coercion id_hsubtypes :  hsubtypes >-> Funclass . 
Definition carrier { X : UU0 } ( A : hsubtypes X ) := total2 A.
Coercion carrier : hsubtypes >-> Sortclass. 
Definition carrierpair { X : UU0 } ( A : hsubtypes X ) := tpair A.
Definition pr21carrier { X:UU0 } ( A : hsubtypes X ) := @pr21 _ _  : carrier A -> X .

Lemma isinclpr21carrier { X : UU0 } ( A : hsubtypes X ) : isincl ( @pr21carrier X A ) .
Proof . intros . apply ( isinclpr21 A ( fun x : _ => pr22 ( A x ) ) ) . Defined . 

Lemma isasethsubtypes (X:UU0): isaset (hsubtypes X).
Proof. intro . change ( isofhlevel 2 ( hsubtypes X ) ) .  apply impred . intro. apply isasethProp. Defined.

Definition totalsubtype ( X : UU0 ) : hsubtypes X := fun x => htrue .

Definition weqtotalsubtype ( X : UU0 ) : weq ( totalsubtype X ) X .
Proof . intro . apply weqpr21 .   intro . apply iscontrunit .  Defined . 


(** *** Direct product of two subtypes *)

Definition subtypesdirprod { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) : hsubtypes ( dirprod X Y ) := fun xy : _ => hconj ( A ( pr21 xy ) ) ( B ( pr22 xy ) ) .

Definition fromdsubtypesdirprodcarrier { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) ( xyis : subtypesdirprod A B ) : dirprod A B .
Proof . intros . set ( xy := pr21 xyis ) . set ( is := pr22 xyis ) .  set ( x := pr21 xy ) . set ( y := pr22 xy ) . simpl in is . simpl in y . apply ( dirprodpair ( tpair A x ( pr21 is ) ) ( tpair B y ( pr22 is ) ) ) . Defined .

Definition tosubtypesdirprodcarrier { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) ( xisyis : dirprod A B ) : subtypesdirprod A B . 
Proof . intros . set ( xis := pr21 xisyis ) . set ( yis := pr22 xisyis ) . set ( x := pr21 xis ) . set ( isx := pr22 xis ) . set ( y := pr21 yis ) . set ( isy := pr22 yis ) . simpl in isx . simpl in isy . apply ( tpair ( subtypesdirprod A B ) ( dirprodpair x y ) ( dirprodpair isx isy ) ) .  Defined .  

Lemma weqsubtypesdirprod { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) : weq ( subtypesdirprod A B ) ( dirprod A B ) .
Proof . intros .  set ( f := fromdsubtypesdirprodcarrier A B ) . set ( g :=  tosubtypesdirprodcarrier A B ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . destruct a as [ xy is ] . destruct xy as [ x y ] . destruct is as [ isx isy ] . apply idpath . 
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . destruct a as [ xis yis ] . destruct xis as [ x isx ] . destruct yis as [ y isy ] . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .  

Lemma ishinhsubtypesdirprod  { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) ( isa : ishinh A ) ( isb : ishinh B ) : ishinh ( subtypesdirprod A B ) .  
Proof . intros . apply ( hinhfun ( invweq ( weqsubtypesdirprod A B ) ) ) .  apply hinhand .  apply isa . apply isb . Defined . 



(** *** A a subtype of with a paths between any every two elements is an h-prop. *)


Lemma isapropsubtype { X : UU0 } ( A : hsubtypes X ) ( is : forall ( x1 x2 : X ) , A x1 -> A x2 -> paths x1 x2 ) : isaprop ( carrier A ) . 
Proof. intros.  apply invproofirrelevance. intros x x' .  
assert ( isincl ( @pr21 _ A )).  apply isinclpr21. intro x0. apply ( pr22 ( A x0 )).  
apply ( invmaponpathsincl ( @pr21 _ A ) X0 ). destruct x as [ x0 is0 ]. destruct x' as [ x0' is0' ] . simpl. apply is. assumption. assumption. Defined. 


(* End of " the type of monic subtypes of a type " . *)







(** ** Relations on types ( or equivalently relations on the sets of connected components) *)


(** *** General definitions *)

Definition hrel ( X : UU0 ) := X -> X -> hProp.

Definition istrans { X : UU0 } ( R : hrel X ) := forall x1 x2 x3 : X, forall (f1: R  x1 x2) (f2: R x2 x3), R x1 x3.

Definition isrefl { X : UU0 } ( R : hrel X ) := forall x:X, R x x.

Definition issymm { X : UU0 } ( R : hrel X ) := forall x1 x2 : X, R x1 x2 -> R x2 x1.


(** *** Direct product of two relations *)

Definition hreldirprod { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) : hrel ( dirprod X Y ) := fun xy xy' : dirprod X Y => hconj ( RX ( pr21 xy ) ( pr21 xy' ) ) ( RY ( pr22 xy ) ( pr22 xy' ) ) .

Definition istransdirprod { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( isx : istrans RX ) ( isy : istrans RY ) : istrans ( hreldirprod RX RY ) := fun xy1 xy2 xy3 : _ => fun is12 : _  => fun is23 : _ => dirprodpair ( isx _ _ _ ( pr21 is12 ) ( pr21 is23 ) ) ( isy _ _ _ ( pr22 is12 ) ( pr22 is23 ) ) . 

Definition isrefldirprod { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( isx : isrefl RX ) ( isy : isrefl RY ) : isrefl ( hreldirprod RX RY ) := fun xy : _ => dirprodpair ( isx _ ) ( isy _ ) .

Definition   issymmdirprod { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( isx : issymm RX ) ( isy : issymm RY ) : issymm ( hreldirprod RX RY ) :=  fun xy1 xy2 : _ => fun is12 : _ => dirprodpair ( isx _ _ ( pr21 is12 ) ) ( isy _ _ ( pr22 is12 ) ) . 

(** *** Partial orderings and associated types . *)


Definition ispo { X : UU0 } ( R : hrel X ) := dirprod ( istrans R ) ( isrefl R ) .

Definition po ( X : UU0 ) := total2 ( fun R : hrel X => ispo R ) .
Definition popair { X : UU0 } ( R : hrel X ) ( is : ispo R ) : po X := tpair ( fun R : hrel X => ispo R ) R is .
Definition carrierofpo ( X : UU0 ) :  po X  -> ( X -> X -> hProp ) :=  @pr21 _ ( fun R : hrel X => ispo R ) .
Coercion carrierofpo : po >-> Funclass  . 

Definition Poset := total2 ( fun X : hSet => po X ) .
Definition Posetpair ( X : hSet ) ( R : po X ) : Poset := tpair ( fun X : hSet => po X ) X R .
Definition carrierofposet : Poset -> hSet := @pr21 _ _ .
Coercion carrierofposet : Poset >-> hSet . 

Definition isaposetmorphism { X Y : Poset } ( f : X -> Y ) := forall x x' : X , ( pr21 ( pr22 X ) x x' ) -> ( pr21 ( pr22 Y ) ( f x ) ( f x' ) ) .
Definition posetmorphism ( X Y : Poset ) := total2 ( fun f : X -> Y => isaposetmorphism f ) .
Definition posetmorphismpair ( X Y : Poset ) := tpair ( fun f : X -> Y => isaposetmorphism f ) .
Definition carrierofposetmorphism ( X Y : Poset ) : posetmorphism X Y -> ( X -> Y ) := @pr21 _ _ .
Coercion  carrierofposetmorphism : posetmorphism >-> Funclass . 


(** *** Eqivalence relations and associated types . *)

Definition iseqrel { X : UU0 } ( R : hrel X ) := dirprod ( ispo R ) ( issymm R ) .
Definition iseqrelconstr { X : UU0 } { R : hrel X } ( trans0 : istrans R ) ( refl0 : isrefl R ) ( symm0 : issymm R ) : iseqrel R := dirprodpair ( dirprodpair trans0 refl0 ) symm0 .

Definition eqrel ( X : UU0 ) := total2 ( fun R : hrel X => iseqrel R ) .
Definition eqrelpair { X : UU0 } ( R : hrel X ) ( is : iseqrel R ) : eqrel X := tpair ( fun R : hrel X => iseqrel R ) R is .
Definition eqrelconstr { X : UU0 } ( R : hrel X ) ( is1 : istrans R ) ( is2 : isrefl R ) ( is3 : issymm R ) : eqrel X := eqrelpair R ( dirprodpair ( dirprodpair is1 is2 ) is3 ) .  
Definition pr21eqrel ( X : UU0 ) : eqrel X -> ( X -> ( X -> hProp ) ) := @pr21 _ _ .
Coercion pr21eqrel : eqrel >-> Funclass . 

Definition eqreltrans { X : UU0 } ( R : eqrel X )  := pr21 ( pr21 ( pr22 R ) ) . 
Definition eqrelrefl { X : UU0 } ( R : eqrel X ) := pr22 ( pr21 ( pr22 R ) ) . 
Definition eqrelsymm { X : UU0 } ( R : eqrel X ) := pr22 ( pr22 R )  . 

(** *** Direct product of two equivalence relations *)

Definition eqreldirprod { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) : eqrel ( dirprod X Y ) := eqrelconstr ( hreldirprod RX RY ) ( istransdirprod _ _ ( eqreltrans RX ) ( eqreltrans RY ) ) ( isrefldirprod  _ _ ( eqrelrefl RX ) ( eqrelrefl RY ) ) ( issymmdirprod  _ _ ( eqrelsymm RX ) ( eqrelsymm RY ) ) . 



(** *** Equivalence classes with respect to a given relation *)



Definition iseqclass { X : UU0 } ( R : hrel X ) ( A : hsubtypes X ) := dirprod ( ishinh ( carrier A ) ) ( dirprod ( forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 ) ( forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) ).
Definition iseqclassconstr { X : UU0 } ( R : hrel X ) { A : hsubtypes X } ( ax0 : ishinh ( carrier A ) ) ( ax1 : forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 ) ( ax2 : forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) : iseqclass R A := dirprodpair ax0 ( dirprodpair ax1 ax2 ) . 

Definition eqax0 { X : UU0 } { R : hrel X } { A : hsubtypes X }  : iseqclass R A -> ishinh ( carrier A ) := fun is : iseqclass R A =>  pr21 is .
Definition eqax1 { X : UU0 } { R : hrel X } { A : hsubtypes X } : iseqclass R A ->  forall x1 x2 : X,  R x1 x2 -> A x1 -> A x2 := fun is: iseqclass R A => pr21 ( pr22 is) .
Definition eqax2 { X : UU0 } { R : hrel X } { A : hsubtypes X } : iseqclass R A ->  forall x1 x2 : X,  A x1 -> A x2 -> R x1 x2 := fun is: iseqclass R A => pr22 ( pr22 is) .

Lemma isapropiseqclass  { X : UU0 } ( R : hrel X ) ( A : hsubtypes X ) : isaprop ( iseqclass R A ) .
Proof. intros. unfold iseqclass. apply isofhleveldirprod. apply (isapropishinh (carrier A)). apply isofhleveldirprod. apply impredtwice. intros t t' . apply impred. intro. apply impred.  intro.  
apply (pr22 (A t')).  apply impredtwice. intros. apply impred. intro. apply impred.  intro.  apply (pr22 (R t t')).  Defined. 


(** *** Direct product of equivalence classes *)

Lemma iseqclassdirprod { X Y : UU0 } { R : hrel X } { Q : hrel Y } { A : hsubtypes X } { B : hsubtypes Y } ( isa : iseqclass R A ) ( isb : iseqclass Q B ) : iseqclass ( hreldirprod R Q ) ( subtypesdirprod A B ) .
Proof . intros . set ( XY := dirprod X Y ) . set ( AB := subtypesdirprod A B ) . set ( RQ := hreldirprod R Q ) . 
set ( ax0 := ishinhsubtypesdirprod  A B ( eqax0 isa ) ( eqax0 isb ) ) .
assert ( ax1 : forall xy1 xy2 : XY , RQ xy1 xy2 -> AB xy1 -> AB xy2 ) . intros xy1 xy2 rq ab1 . apply ( dirprodpair ( eqax1 isa _ _ ( pr21 rq ) ( pr21 ab1 ) ) ( eqax1 isb _ _ ( pr22 rq ) ( pr22 ab1 ) ) ) .    
assert ( ax2 : forall xy1 xy2 : XY ,  AB xy1 -> AB xy2 -> RQ xy1 xy2 ) . intros xy1 xy2 ab1 ab2 . apply ( dirprodpair ( eqax2 isa _ _ ( pr21 ab1 ) ( pr21 ab2 ) ) ( eqax2 isb _ _ ( pr22 ab1 ) ( pr22 ab2 ) ) ) .
apply ( iseqclassconstr _ ax0 ax1 ax2 ) . Defined .     







(** ** Images and surjectivity for functions between types (both depend only on the behavior of the corresponding function between the sets of connected components) **)

Definition image { X Y : UU0 } ( f : X -> Y ) := total2 ( fun y : Y => ishinh ( hfiber f y ) ) .
Definition imagepair { X Y : UU0 } (f: X -> Y) := tpair ( fun y : Y => ishinh ( hfiber f y ) ) .
Definition pr21image { X Y : UU0 } ( f : X -> Y ) := @pr21 _  ( fun y : Y => ishinh ( hfiber f y ) ) .


Definition prtoimage { X Y : UU0 } (f : X -> Y) : X -> image f.
Proof. intros X Y f X0. apply (imagepair _ (f X0) (hinhpr _ (hfiberpair f X0 (idpath _ )))). Defined. 

Definition issurjective { X Y : UU0 } (f : X -> Y ) := forall y:Y, ishinh (hfiber f y). 

Lemma isapropissurjective { X Y : UU0 } ( f : X -> Y) : isaprop (issurjective f).
Proof. intros.  apply impred. intro t. apply  (pr22 (ishinh (hfiber f t))). Defined. 

Lemma isinclpr21image { X Y : UU0 } (f:X -> Y): isincl (pr21image f).
Proof. intros. apply isofhlevelfpr21. intro. apply ( pr22 ( ishinh ( hfiber f x ) ) ) . Defined.

Lemma issurjprtoimage { X Y : UU0 } ( f : X -> Y) : issurjective (prtoimage f ).
Proof. intros. intro z.  set (f' := prtoimage f ). set (g:= pr21image f ). set (gf':= fun x:_ => g ( f' x )).
assert (e: paths f gf'). apply etacorrection .  
assert (ff: hfiber gf' (pr21 z) -> hfiber f' z).   apply ( invweq ( samehfibers _ _ ( isinclpr21image f ) z ) ) .  
assert (is2: ishinh (hfiber gf' (pr21 z))). destruct e.  apply (pr22 z). 
apply (hinhfun ff is2). Defined. 


(** *** Surjections to sets are epimorphisms  *)

Theorem surjectionisepitosets { X Y Z : UU0 } ( f : X -> Y ) ( g1 g2 : Y -> Z ) ( is1 : issurjective f ) ( is2 : isaset Z ) ( isf : forall x : X , paths ( g1 ( f x ) ) ( g2 ( f x ) ) ) : forall y : Y , paths ( g1 y ) ( g2 y ) .
Proof. intros . set (P1:= hProppair (paths (g1 y) (g2 y)) (is2 (g1 y) (g2 y))). unfold issurjective in is1. 
assert (s1: (hfiber f y)-> paths (g1 y) (g2 y)). intro X1. destruct X1 as [t x ]. induction x. apply (isf t). 
assert (s2: ishinh (paths (g1 y) (g2 y))). apply (hinhfun s1 (is1 y)).  
set (is3:= is2 (g1 y) (g2 y)). simpl in is3. apply (@hinhuniv (paths (g1 y) (g2 y)) (hProppair _ is3)). intro X1.  assumption. assumption. Defined. 

(** *** The two-out-of-three properties of surjections *)

Lemma issurjcomp { X Y Z : UU0 } ( f : X -> Y ) ( g : Y -> Z ) ( isf : issurjective f ) ( isg : issurjective g ) : issurjective ( funcomp f g ) .
Proof . intros . unfold issurjective .  intro z . apply ( fun ff => hinhuniv ff ( isg z ) ) . intro ye .  apply ( hinhfun ( hfibersftogf f g z ye ) ) .  apply ( isf ) .   Defined . 

Notation issurjtwooutof3c := issurjcomp . 

Lemma issurjtwooutof3b { X Y Z : UU0 } ( f : X -> Y ) ( g : Y -> Z ) ( isgf : issurjective ( funcomp f g ) ) : issurjective g .  
Proof . intros . unfold issurjective .  intro z .  apply ( hinhfun ( hfibersgftog f g z ) ( isgf z ) ) .  Defined . 

(** *** A function between hsets which is an inclusion and a surjection is a weak equivalence *)

Lemma isweqinclandsurj { X Y : hSet } ( f : X -> Y ) ( is1 : isincl f ) ( is1 : issurjective f ) : isweq f .
Proof . intros . unfold isweq . intro y . 

assert ( isp : isaprop ( hfiber f y ) ) . apply ( is1 y ) .
apply iscontraprop1 . apply isp . apply ( @hinhuniv _ ( hProppair _ isp ) ( idfun _ ) ( is0 y ) ) .  Defined .


 




(** ** Set quotients of types. 

In this file we study the set quotients of types by equivalence relations. While the general notion of a quotient of a type by a relation is complicated due to the existence of different kinds of quotients (e.g. homotopy quotients or categorical quotients in the homotopy category which are usually different from each other) there is one particular class of quotients which is both very important for applications and semantically straightforward. These quotients are the universal functions from a type to an hset which respect a given relation. Some of the proofs in this section depend on the proerties of the hinhabited construction and some also depend on the univalence axiom for [ hProp ] which allows us to prove that the type of monic subtypes of a type is a set. 

Our main construction is analogous to the usual construction of quotient as a set of equivalence classes. Wev also consider another construction of [ setquot ] which is analogous ( on the next h-level ) to our construction of [ ishinh ] . Both have generalizations to the "higher" quotients (i.e. groupoid quotients etc.) which will be considered separately. In particular, the quotients the next h-level appear to be closely related to the localizations of categories and will be considered in the section about types of h-level 3.  


*)



(** ** Setquotient defined in terms of equivalence classes *)


Definition setquot { X : UU0 } ( R : hrel X ) := total2 ( fun A : _ => iseqclass R A ) .
Definition setquotpair { X : UU0 } ( R : hrel X ) := tpair (fun A : _ => iseqclass R A ) .
Definition pr21setquot { X : UU0 } ( R : hrel X ) : setquot R -> ( X -> hProp ) := @pr21 _ ( fun A : _ => iseqclass R A ) .
Coercion pr21setquot : setquot >-> Funclass . 

Lemma isinclpr21setquot { X : UU0 } ( R : hrel X ) : isincl ( pr21setquot R ) .
Proof . intros . apply isinclpr21.  intro x0. apply isapropiseqclass. Defined .  

Definition setquottouu0 { X : UU0 } ( R : hrel X ) ( a : setquot R )  := carrier ( pr21 a ).
Coercion setquottouu0 : setquot >-> Sortclass.


Theorem isasetsetquot { X : UU0 } ( R : hrel X ) : isaset ( setquot R ) .
Proof. intros.  apply ( isasetsubset ( @pr21 _ _ )  ( isasethsubtypes X )  ) . apply isinclpr21.  intro.  apply isapropiseqclass.  Defined. 

Definition setquotinset { X : UU0 } ( R : hrel X ) : hSet := hSetpair _ ( isasetsetquot R ) . 

Theorem setquotpr { X : UU0 } ( R : eqrel X ) : X -> setquot R.
Proof. intros X R X0. set ( rax:= eqrelrefl R ). set ( sax := eqrelsymm R  ) . set (tax:= eqreltrans R ). split with (fun x:X =>  R X0 x). split with (hinhpr _ (tpair _ X0 (rax X0))).  
assert (a1: (forall x1 x2 : X, R x1 x2 -> R X0 x1 -> R X0 x2)). intros x1 x2 X1 X2.  apply (tax X0 x1 x2 X2 X1). split with a1.
assert (a2: (forall x1 x2 : X, R X0 x1 -> R X0 x2 -> R x1 x2)). intros x1 x2 X1 X2. apply (tax x1 X0 x2 (sax X0 x1 X1) X2). 
assumption. Defined. 

Lemma setquotl0 { X : UU0 } ( R : eqrel X ) ( c : setquot R ) ( x : c ) : paths ( setquotpr R ( pr21 x ) ) c .
Proof . intros . apply ( invmaponpathsincl _ ( isinclpr21setquot R ) ) .  simpl . apply funextsec . intro x0 . destruct c as [ A iseq ] .  destruct x as [ x is ] .  simpl in is . simpl .  apply uahp . intro r . apply ( eqax1 iseq _ _ r is ) .  intro a . apply ( eqax2 iseq _ _ is a ) .  Defined . 


(* Lemma test { X : UU0 } ( R : eqrel X ) ( x0 : X ) ( x : setquotpr R x0 ) : paths ( pr21 ( setquotpr R ( pr21 x ) ) ) ( pr21 ( setquotpr R x0 ) ) .
Proof . intros . simpl .  apply idpath . *)

Theorem issurjsetquotpr { X : UU0 } ( R : eqrel X)  : issurjective (setquotpr R ).
Proof. intros. unfold issurjective. intro c.  apply ( @hinhuniv ( carrier ( pr21 c ) ) ) .  intro x . apply hinhpr .  split with ( pr21 x ) . apply setquotl0 .  apply ( eqax0 ( pr22 c ) ) .  
Defined . 





(** *** Universal property of [ seqtquot R ] for functions to sets satisfying compatibility condition [ iscomprelfun ] *)


Definition iscomprelfun { X Y : UU0 } ( R : hrel X ) ( f : X -> Y ) := forall x x' : X , R x x' -> paths ( f x ) ( f x' ) .

Lemma isapropimeqclass { X : UU0 } ( R : hrel X ) ( Y : hSet ) ( f : X -> Y ) ( is : iscomprelfun R f ) ( c : setquot R ) : isaprop ( image ( fun x : c => f ( pr21 x ) ) ) .
Proof. intros. apply isapropsubtype .  intros y1 y2 . simpl . apply ( @hinhuniv2 _ _ ( hProppair ( paths y1 y2 ) ( pr22 Y y1 y2 ) ) ) .  intros x1 x2 . simpl . destruct c as [ A iseq ] . destruct x1 as [ x1 is1 ] . destruct x2 as [ x2 is2 ] . destruct x1 as [ x1 is1' ] . destruct x2 as [ x2 is2' ] . simpl in is1 .  simpl in is2 . simpl in is1' .  simpl in is2' .  assert ( r : R x1 x2 ) . apply ( eqax2 iseq _ _ is1' is2' ) .  apply ( pathscomp0 ( pathsinv0 is1 )  ( pathscomp0 ( is _ _ r ) is2 ) ) .  Defined .  


Theorem setquotuniv  { X : UU0 } ( R : hrel X ) ( Y : hSet ) ( f : X -> Y ) ( is : iscomprelfun R f ) ( c : setquot R ) : Y .
Proof. intros.   apply ( pr21image ( fun x : c => f ( pr21 x ) ) ) . apply ( @hinhuniv ( pr21 c ) ( hProppair _ ( isapropimeqclass R Y f is c ) ) ( prtoimage ( fun x : c => f ( pr21 x ) ) ) ) .  apply ( eqax0 ( pr22 c ) ) .  Defined . 


(** Note: the axioms rax, sax and trans are not used in the proof of setquotuniv. If we consider a relation which is not an equivalence relation then setquot will still be the set of subsets which are equivalence classes. Now however such subsets need not to cover all of the type. In fact their set can be empty. Nevertheless setquotuniv will apply. *)


Theorem setquotunivcomm  { X : UU0 } ( R : eqrel X ) ( Y : hSet ) ( f : X -> Y ) ( is : iscomprelfun R f ) : forall x : X , paths ( setquotuniv R Y f is ( setquotpr R x ) )  ( f x ) .
Proof. intros. unfold setquotuniv . unfold setquotpr .  simpl .  apply idpath .  Defined.

Lemma iscompsetquotpr { X : UU0 } ( R : eqrel X ) ( x x' : X ) ( a : R x x' ) : paths ( setquotpr R x ) ( setquotpr R x' ) .
Proof. intros. apply ( invmaponpathsincl _ ( isinclpr21setquot R ) ) . simpl . apply funextsec . intro x0 . apply uahp .  intro r0 . apply ( eqreltrans R _ _ _ ( eqrelsymm R _ _ a ) r0 ) .  intro x0' . apply ( eqreltrans R _ _ _ a x0' ) . Defined .  

Theorem weqpathsinsetquot { X : UU0 } ( R : eqrel X ) ( x x' : X ) : weq ( R x x' ) ( paths ( setquotpr R x ) ( setquotpr R x' ) ) .
Proof .  intros . split with ( iscompsetquotpr R x x' ) .  apply isweqimplimpl .  intro e .  set ( e' := maponpaths ( pr21setquot R ) e ) .  unfold pr21setquot in e' . unfold setquotpr in e' . simpl in e' . assert ( e'' := maponpaths ( fun f : _ => f x' ) e' ) .  simpl in e'' . apply ( eqweqmaphProp ( pathsinv0 e'' ) ( eqrelrefl R x' ) ) .  apply ( pr22 ( R x x' ) ) .  set ( int := isasetsetquot R (setquotpr R x) (setquotpr R x') ) .  assumption . Defined .




(** *** Functoriality of [ setquot ] for functions mapping one relation to another *)


Definition iscomprelrelfun { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( f : X -> Y ) := forall x x' : X , RX x x' -> RY ( f x ) ( f x' ) .

Definition  setquotfun  { X Y : UU0 } ( RX : hrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is : iscomprelrelfun RX RY f ) ( cx : setquot RX ) : setquot RY .
Proof . intros . set ( ff := funcomp f ( setquotpr RY ) ) . assert ( isff : iscomprelfun RX ff ) .  intros x x' .  intro r .  apply ( weqpathsinsetquot RY ( f x ) ( f x' ) ) .  apply is . apply r . apply ( setquotuniv RX ( setquotinset RY ) ff isff cx) .  Defined . 

Definition setquotfuncomm  { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is : iscomprelrelfun RX RY f ) : forall x : X , paths ( setquotfun RX RY f is ( setquotpr RX x ) ) ( setquotpr RY ( f x ) ) .
Proof . intros . simpl . apply idpath .  Defined . 



(** *** Universal property of [ setquot ] for predicates with 1 , 2 and 3 variables *)


Theorem setquotunivprop { X : UU0 } ( R : eqrel X ) ( P : setquot R -> hProp ) ( is : forall x : X , P ( setquotpr R x ) ) : forall c : setquot R ,  P c .
Proof . intros .  apply ( @hinhuniv ( carrier ( pr21 c ) ) ( P c ) ) .  intro x .  set ( e := setquotl0 R c x ) .  apply ( eqweqmaphProp ( maponpaths P e ) ) .   apply ( is ( pr21 x ) ) .  apply ( eqax0 ( pr22 c ) ) .  Defined . 

Theorem setquotuniv2prop { X : UU0 } ( R : eqrel X ) ( P : setquot R -> setquot R -> hProp ) ( is : forall x x' : X ,  P ( setquotpr R x ) ( setquotpr R x' ) ) : forall c c' : setquot R ,  P c c' .
Proof . intros . assert ( int1 : forall c0' : _ , P c c0' ) .  apply ( setquotunivprop R ( fun c0' => P c c0' ) ) .  intro x . apply ( setquotunivprop R ( fun c0 : _ => P c0 ( setquotpr R x ) ) ) .  intro x0 . apply ( is x0 x ) . apply ( int1 c' ) .  Defined . 

Theorem setquotuniv3prop { X : UU0 } ( R : eqrel X ) ( P : setquot R -> setquot R -> setquot R -> hProp ) ( is : forall x x' x'' : X ,  P  ( setquotpr R x ) ( setquotpr R x' ) ( setquotpr R x'' ) ) : forall c c' c'' : setquot R , P c c' c''  .
Proof . intros . assert ( int1 : forall c0' c0'' : _ , P c c0' c0'' ) .  apply ( setquotuniv2prop R ( fun c0' c0'' => P c c0' c0'' ) ) .  intros x x' . apply ( setquotunivprop R ( fun c0 : _ => P c0 ( setquotpr R x ) ( setquotpr R x' ) ) ) .  intro x0 . apply ( is x0 x x' ) . apply ( int1 c' c'' ) .  Defined . 

(** Important note : theorems proved above can not be used ( al least at the moment ) to construct terms whose complete normalization ( evaluation ) is important . For example they should not be used * directly * to construct [ isdeceq ] property of [ setquot ] since [ isdeceq ] is in turn used to construct boolean equality [ booleq ] and evaluation of [ booleq x y ] is important for computational purposes . Terms produced using these universality theorems will not fully normalize even in simple cases due to the following steps in the proof of [ setquotunivprop ] . As a part of the proof term of this theorem there appears the composition of an application of [ uahp ] , transfer of the resulting term of the identity type by [ maponpaths ] along [ P ] followed by the reconstruction of a equivalence ( two directional implication ) between the corresponding propositions through [  eqweqmaphProp ] . The resulting implications are " opaque " and the proofs of disjunctions [ P \/ Q ]  produced with the use of such implications can not be evaluated to one of the summands of the disjunction . An example is given by the following theorem [ isdeceqsetquot_non_constr ] which , as simple experiments show, can not be used to compute the value of [ isdeceqsetquot ] . Below we give another proof of [ isdeceq ( setquot R ) ] using the same assumptions which is " constructive " i.e. usable for the evaluation purposes . *)




(** *** The case when the function between quotients defined by [ setquotfunt ] is a surjection , inclusion or a weak equivalence  *)

Lemma issurjsetquotfun { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is : issurjective f ) ( is1 : forall x x' : X , RX x x' -> RY ( f x ) ( f x' ) ) : issurjective ( setquotfun RX RY f is1 ) .
Proof . intros . apply ( issurjtwooutof3b ( setquotpr RX ) ) . apply ( issurjcomp f ( setquotpr RY ) is ( issurjsetquotpr RY ) ) .   Defined . 


Lemma isinclsetquotfun { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is1 : forall x x' : X , RX x x' -> RY ( f x ) ( f x' ) )  ( is2 : forall x x' : X , RY ( f x ) ( f x' ) -> RX x x' ) : isincl ( setquotfun RX RY f is1 ) .
Proof . intros . apply isinclbetweensets . apply isasetsetquot .   apply isasetsetquot .
assert ( is : forall x x' : setquot RX , isaprop ( paths (setquotfun RX RY f is1 x) (setquotfun RX RY f is1 x') -> paths x x' ) ) . intros . apply impred .  intro . apply isasetsetquot .  
apply ( setquotuniv2prop RX ( fun x x' => hProppair _ ( is x x' ) ) ) .  simpl . intros x x' .  intro e .  set ( e' := invweq ( weqpathsinsetquot RY ( f x ) ( f x' ) ) e ) .  apply ( weqpathsinsetquot RX _ _ ( is2 x x' e' ) ) .  Defined .

Definition setquotincl { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is1 : forall x x' : X , RX x x' -> RY ( f x ) ( f x' ) )  ( is2 : forall x x' : X , RY ( f x ) ( f x' ) -> RX x x' ) := inclpair ( setquotfun RX RY f is1 ) ( isinclsetquotfun RX RY f is1 is2 ) . 

Definition  weqsetquotweq { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : weq X Y ) ( is1 : forall x x' : X , RX x x' -> RY ( f x ) ( f x' ) )  ( is2 : forall x x' : X , RY ( f x ) ( f x' ) -> RX x x' ) : weq ( setquot RX ) ( setquot RY )  .
Proof . intros . set ( ff := setquotfun RX RY f is1 ) . split with ff .
assert ( is2' : forall y y' : Y , RY y y' -> RX ( invmap f y ) ( invmap f y' ) ) . intros y y' .  rewrite ( pathsinv0 ( homotweqinvweq f y ) ) .  rewrite ( pathsinv0 ( homotweqinvweq f y' ) ) .  rewrite ( homotinvweqweq f ( invmap f y ) ) . rewrite ( homotinvweqweq f ( invmap f y' ) ) .  apply ( is2 _ _ ) .  set ( gg := setquotfun RY RX ( invmap f ) is2' ) .

assert ( egf : forall a , paths ( gg ( ff a ) ) a ) . apply ( setquotunivprop RX ( fun a0 => hProppair _ ( isasetsetquot RX ( gg ( ff a0 ) ) a0 ) ) ) .    simpl .  intro x .  unfold ff . unfold gg .  apply ( maponpaths ( setquotpr RX ) ( homotinvweqweq f x ) ) . 

assert ( efg : forall a , paths ( ff ( gg a ) ) a ) . apply ( setquotunivprop RY ( fun a0 => hProppair _ ( isasetsetquot RY ( ff ( gg a0 ) ) a0 ) ) ) .    simpl .  intro x .  unfold ff . unfold gg .  apply ( maponpaths ( setquotpr RY ) ( homotweqinvweq f x ) ) .

apply ( gradth _ _ egf efg ) . Defined .

Definition weqsetquotsurj  { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is : issurjective f ) ( is1 : forall x x' : X , RX x x' -> RY ( f x ) ( f x' ) )  ( is2 : forall x x' : X , RY ( f x ) ( f x' ) -> RX x x' ) : weq ( setquot RX ) ( setquot RY )  .
Proof . intros . set ( ff := setquotfun RX RY f is1 ) . split with ff .  apply ( @isweqinclandsurj ( setquotinset RX ) ( setquotinset RY ) ff ) .  apply ( isinclsetquotfun RX RY f is1 is2 ) .  apply ( issurjsetquotfun RX RY f is is1 ) .  Defined . 



(** *** [ setquot ] with respect to the product of two relations *)



Definition setquottodirprod { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( cc : setquot ( eqreldirprod RX RY ) ) : dirprod ( setquot RX ) ( setquot RY ) .
Proof . intros .  set ( RXY := eqreldirprod RX RY ) . apply ( dirprodpair ( setquotuniv RXY ( setquotinset RX ) ( funcomp ( @pr21 _ ( fun x : _ => Y ) ) ( setquotpr RX ) ) ( fun xy xy' : dirprod X Y => fun rr : RXY xy xy' => iscompsetquotpr RX _ _ ( pr21 rr ) ) cc )  ( setquotuniv RXY ( setquotinset RY ) ( funcomp ( @pr22 _ ( fun x : _ => Y ) ) ( setquotpr RY ) ) ( fun xy xy' : dirprod X Y => fun rr : RXY xy xy' =>  iscompsetquotpr RY _ _ ( pr22 rr ) ) cc ) )  . Defined .   

Definition dirprodtosetquot { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) (cd : dirprod ( setquot RX ) ( setquot RY ) ) : setquot ( hreldirprod RX RY ) := setquotpair _ _ ( iseqclassdirprod ( pr22 ( pr21 cd ) ) ( pr22 ( pr22 cd ) ) ) . 


Theorem weqsetquottodirprod { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) : weq ( setquot ( eqreldirprod RX RY ) ) ( dirprod ( setquot RX ) ( setquot RY ) ) .
Proof . intros . set ( f := setquottodirprod  RX RY ) . set ( g := dirprodtosetquot RX RY ) . split with f .

assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . apply ( setquotunivprop _ ( fun a : _ => ( hProppair _ ( isasetsetquot _ ( g ( f a ) ) a ) ) ) ) . intro xy . destruct xy as [ x y ] . simpl . apply ( invmaponpathsincl _ ( isinclpr21setquot _ ) ) . simpl . apply funextsec .  intro xy' .  destruct xy' as [ x' y' ] . apply idpath .

assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . destruct a as [ ax ay ] . apply pathsdirprod . generalize ax .  clear ax . apply ( setquotunivprop RX ( fun ax : _ => ( hProppair _ ( isasetsetquot _ _ _ ) ) ) ) . intro x . simpl .  generalize ay .  clear ay . apply ( setquotunivprop RY ( fun ay : _ => ( hProppair _ ( isasetsetquot _ _ _ ) ) ) ) . intro y . simpl .   apply ( invmaponpathsincl _ ( isinclpr21setquot _ ) ) . apply funextsec .  intro x0 . simpl . apply idpath . generalize ax .  clear ax . apply ( setquotunivprop RX ( fun ax : _ => ( hProppair _ ( isasetsetquot _ _ _ ) ) ) ) . intro x . simpl .  generalize ay .  clear ay . apply ( setquotunivprop RY ( fun ay : _ => ( hProppair _ ( isasetsetquot _ _ _ ) ) ) ) . intro y . simpl .   apply ( invmaponpathsincl _ ( isinclpr21setquot _ ) ) . apply funextsec .  intro x0 . simpl . apply idpath . 

apply ( gradth _ _ egf efg ) . Defined .  



(** *** Universal property of [ setquot ] for functions of two variables *) 

Definition iscomprelfun2 { X Y : UU0 } ( R : hrel X ) ( f : X -> X -> Y ) := forall x x' x0 x0' : X , R x x' ->  R x0 x0' ->  paths ( f x x0 ) ( f x' x0' ) .

Definition setquotuniv2  { X : UU0 } ( R : hrel X ) ( Y : hSet ) ( f : X -> X -> Y ) ( is : iscomprelfun2 R f ) ( c c0 : setquot R ) : Y .
Proof. intros .  set ( ff := fun xy : dirprod X X => f ( pr21 xy ) ( pr22 xy ) ) . set ( RR := hreldirprod R R ) . 
assert ( isff : iscomprelfun RR ff ) . intros xy x'y' . simpl . intro dp .  destruct dp as [ r r'] .  apply ( is _ _ _ _ r r' ) . apply ( setquotuniv RR Y ff isff ( dirprodtosetquot R R ( dirprodpair c c0 ) ) ) . Defined .   

Theorem setquotuniv2comm  { X : UU0 } ( R : eqrel X ) ( Y : hSet ) ( f : X -> X -> Y ) ( is : iscomprelfun2 R f ) : forall x x' : X , paths ( setquotuniv2 R Y f is ( setquotpr R x ) ( setquotpr R x' ) )  ( f x x' ) .
Proof. intros.   apply idpath .  Defined.



(** *** Functoriality of [ setquot ] for functions of two variables mapping one relation to another *)


Definition iscomprelrelfun2 { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( f : X -> X -> Y ) := forall x x' x0 x0' : X , RX x x' -> RX x0 x0' ->  RY ( f x x0 ) ( f x' x0' ) .

Definition  setquotfun2  { X Y : UU0 } ( RX : hrel X ) ( RY : eqrel Y ) ( f : X -> X -> Y ) ( is : iscomprelrelfun2 RX RY f ) ( cx cx0 : setquot RX ) : setquot RY .
Proof . intros . set ( ff := fun x x0 : X => setquotpr RY ( f x x0 ) ) . assert ( isff : iscomprelfun2 RX ff ) .  intros x x' x0 x0' .  intros r r0  .  apply ( weqpathsinsetquot RY ( f x x0 ) ( f x' x0' ) ) .  apply is . apply r . apply r0 . apply ( setquotuniv2 RX ( setquotinset RY ) ff isff cx cx0 ) .  Defined . 

Theorem setquotfun2comm  { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> X -> Y ) ( is : iscomprelrelfun2 RX RY f ) : forall x x' : X , paths ( setquotfun2 RX RY f is ( setquotpr RX x ) ( setquotpr RX x' ) )  ( setquotpr RY ( f x x' ) ) .
Proof. intros.   apply idpath .  Defined.



(** *** Set quotients with respect to decidable equivalence relations have decidable equality *)


Theorem isdeceqsetquot_non_constr { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) : isdeceq ( setquot R ) . 
Proof . intros .  apply isdeceqif . intros x x' .  apply ( setquotuniv2prop R ( fun x0 x0' => hProppair _ ( isapropisdecprop ( paths x0 x0' ) ) ) ) .  intros x0 x0' .  simpl .  apply ( isdecpropweqf ( weqpathsinsetquot R x0 x0' ) ( is x0 x0' ) ) .  Defined . 

Definition setquotbooleqint { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) ( x x' : X ) : bool .
Proof . intros . destruct ( pr21 ( is x x' ) ) . apply true . apply false . Defined .

Lemma  setquotbooleqintcomp { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) : iscomprelfun2 R ( setquotbooleqint R is ) .
Proof . intros . unfold iscomprelfun2 .    intros x x' x0 x0' r r0 .  unfold setquotbooleqint . destruct ( pr21 ( is x x0 ) ) as [ r1 | nr1 ]  .   destruct ( pr21 ( is x' x0' ) ) as [ r1' | nr1' ] . apply idpath . destruct ( nr1' ( eqreltrans R _ _ _ ( eqreltrans R _ _ _ ( eqrelsymm R _ _ r ) r1 ) r0 ) )  .   destruct ( pr21 ( is x' x0' ) ) as [ r1' | nr1' ] . destruct ( nr1 ( eqreltrans R _ _ _ r ( eqreltrans R _ _ _ r1' ( eqrelsymm R _ _ r0 ) ) ) ) . apply idpath .   Defined . 


Definition setquotbooleq { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) : setquot R -> setquot R -> bool := setquotuniv2 R ( hSetpair _ ( isasetbool ) ) ( setquotbooleqint R is ) ( setquotbooleqintcomp R is ) .

Lemma setquotbooleqtopaths  { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) ( x x' : setquot R ) : paths ( setquotbooleq R is x x' ) true  -> paths x x' . 
Proof . intros X R is . assert ( isp : forall x x' : setquot R , isaprop ( paths ( setquotbooleq R is x x' ) true  -> paths x x' ) ) . intros x x' . apply impred . intro . apply ( isasetsetquot R x x' ) .     apply ( setquotuniv2prop R ( fun x x' => hProppair _ ( isp x x' ) ) ) . simpl .    intros x x' .  change ( paths (setquotbooleqint R is x x' ) true -> paths (setquotpr R x) (setquotpr R x') ) . unfold setquotbooleqint .  destruct ( pr21 ( is x x' ) ) as [ i1 | i2 ] . intro .  apply ( weqpathsinsetquot R _ _ i1 ) .  intro H . destruct ( nopathsfalsetotrue H ) .  Defined .  

Lemma setquotpathstobooleq  { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) ( x x' : setquot R ) : paths x x' -> paths ( setquotbooleq R is x x' ) true .
Proof . intros X R is x x' e . destruct e . generalize x .  apply ( setquotunivprop R ( fun x => hProppair _ ( isasetbool (setquotbooleq R is x x) true ) ) ) .  simpl .  intro x0 .  change ( paths ( setquotbooleqint R is x0 x0 ) true ) .  unfold setquotbooleqint .  destruct ( pr21 ( is x0 x0 ) ) as [ i1 | i2 ] .  apply idpath .  destruct ( i2 ( eqrelrefl R x0 ) ) .  Defined . 

Definition  isdeceqsetquot { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) : isdeceq ( setquot R ) .
Proof . intros . intros x x' .  destruct ( boolchoice ( setquotbooleq R is x x' ) ) as [ i | ni ] .  apply ( ii1 ( setquotbooleqtopaths R is x x' i ) ) . apply ii2 .   intro e .  destruct ( falsetonegtrue _ ni ( setquotpathstobooleq R is x x' e ) ) . Defined . 





(** *** The set of connected components of type. *)



Definition pathshrel ( X : UU0 ) := fun x x' : X  =>  ishinh ( paths x x' )  .
Definition istranspathshrel ( X : UU0 ) : istrans ( pathshrel X ) := fun x x' x'' : _ => fun a : _ => fun b : _ =>  hinhfun2 (fun e1 : paths x x' => fun e2 : paths x' x'' => pathscomp0 e1 e2 ) a b .
Definition isreflpathshrel ( X : UU0 ) : isrefl ( pathshrel X ) := fun x : _ =>  hinhpr _ ( idpath x ) .
Definition issymmpathshrel ( X : UU0 ) : issymm ( pathshrel X ) := fun x x': _ => fun a : _ => hinhfun ( fun e : paths x x' => pathsinv0 e ) a . 

Definition pathseqrel ( X : UU0 ) := eqrelconstr ( pathshrel X ) ( istranspathshrel X ) ( isreflpathshrel X ) ( issymmpathshrel X ) . 

Definition pi0 ( X : UU0 ) := setquot ( pathshrel X ) . 
Definition pi0pr ( X : UU0 ) := setquotpr ( pathseqrel X ) .





















(** **  Set quotients. Construction 2. 


****************** THIS SECTION IS UNFINISHED ******************


The following construction of the set quotient is based on the following idea. Let X be a set. Then we have the obvious "double evaluation map" from X to the product over all sets Y of the sets ((X -> Y) -> Y). This is always an inclusion and in particular X is isomorphic to the image of this map. Suppore now we have a relation (which need not be an equivalence relation) R on X. Then we know that (X/R -> Y) is a subset of (X -> Y) which consists of functions compatible with the relation even if we do not know what X/R is. Thus we may consider the image of X in the product over all Y of ((X/R -> Y) ->Y) and it must be isomorphic to X/R. This ideas are realized in the definitions given below. There are two advantages to this approach. One is that the relation need not be an equivalence relation. Another one is that it can be more easily generalized to the higher quotients of type.


We also show that two constructions of set-quotients of types - the one given in set_quotients and the one given here agree up to an isomorphism (weak equivalence). *)




(** *** Functions compatible with a relation *)

Definition compfun { X : UU0 }  ( R : hrel X ) ( S : hSet ) : UU0 := total2  (fun F: X -> S => forall x x' : X, R x x' -> paths (F x ) (F x')).
Definition compfunpair { X : UU0 }  ( R : hrel X ) ( S : hSet ) := tpair  (fun F: X -> S => forall x x' : X, R x x' -> paths (F x ) (F x')).

Definition compevmap { X : UU0 } ( R : hrel X ) : X -> forall S: hSet, (compfun R S) -> S := fun x:X => fun S:_ => fun f: compfun R S => pr21 f x.




(** *** The quotient set of a type by a relation. *)

Definition setquot2 { X : UU0 } ( R : hrel X ) : UU0 := image  (compevmap R). (* We will be asuming below that setquot2 is in UU0.  In the future it should be proved using [ issurjsetquot2pr ] below and a resizing axiom. The appropriate resizing axiom for this should say that if X -> Y is a surjection, Y is an hset and X:UU then Y:UU . *)  

Definition setquot2pr { X : UU0 }  ( R : hrel X ) : X -> setquot2 R := fun x:X => imagepair  (compevmap R)_ (hinhpr _ (hfiberpair  (compevmap R)  x (idpath _ ))).

Lemma iscompsetquot2pr { X : UU0 } ( R : hrel X ) ( x x' : X ) ( a : R x x' ) : paths (setquot2pr R x) (setquot2pr R x').
Proof. intros. 
assert (e1: paths (compevmap R x) (compevmap R x')).  apply funextsec. intro S.  apply funextsec.  intro f.   unfold compfun in f. apply (pr22 f x x' a). 
apply (invmaponpathsincl _ (isinclpr21image (compevmap R) ) (setquot2pr R x) (setquot2pr R x') e1). Defined. 


Lemma issurjsetquot2pr { X : UU0 } ( R : hrel X ) : issurjective  (setquot2pr R).
Proof. intros. apply issurjprtoimage. Defined.    

Definition setquot2univ { X : UU0 } ( Y : hSet ) ( R : hrel X ) ( F : X -> Y ) (iscomp : forall x x' : X, R x x' -> paths (F x ) (F x')) : setquot2 R -> Y := fun q : _ => pr21 q Y ( compfunpair _ _ F iscomp ) .  


Theorem setquot2univcomm  { X : UU0 } ( Y : hSet ) ( R : hrel X ) ( F : X -> Y ) (iscomp : forall x x' : X, R x x' -> paths (F x ) (F x')) ( x : X) : paths (setquot2univ _ _ F iscomp ( setquot2pr R x )) (F x).  
Proof. intros. apply idpath. Defined.  

Theorem isasetsetquot2 { X : UU0 } ( R : hrel X ) : isaset ( setquot2 R ) .
Proof. intros. 
assert (is1: isofhlevel 2 ( forall S: hSet, (compfun R S) -> S )).  apply impred.  intro.  apply impred.  intro X0.  apply (pr22 t).
apply (isasetsubset _ is1 (isinclpr21image _ )).  Defined. 


(** The previous results show that setquot2 as constructed is indeed the categorical quotient of X with respect to R. What we can not direcly show for this construction is that for  [ (X : UU0) (R : hrel X) ( x x' : X) ( e: paths (setquot2pr _ R x) (setquot2pr _ R x')) (is : iseqrel X R) ] one has [ R x x' ]. For this we will need to define setquot2 in terms of equivalence classes and then show that the two constructions agree. *)







(* *** Comparison of setquot2 and setquot.  *)



Definition setquottosetquot2 (X: UU0) (R: hrel X) (is: iseqrel R) : setquot R -> setquot2 R.
Proof. intros X R is X0. apply (setquotuniv R (hSetpair _ (isasetsetquot2 R)) (setquot2pr R) (iscompsetquot2pr R) X0).  Defined.










(* End of the file hSet.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)