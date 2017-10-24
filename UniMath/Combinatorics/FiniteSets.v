(** * Finite sets. Vladimir Voevodsky . Apr. - Sep. 2011.

This file contains the definition and main properties of finite sets. At the end of the file there are several elementary examples which are used as test cases to check that our constructions do not prevent Coq from normalizing terms of type nat to numerals.

*)





(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** Imports. *)

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.DecidablePropositions.
Require Export UniMath.Combinatorics.StandardFiniteSets .




(** ** Sets with a given number of elements. *)

(** *** Structure of a set with [ n ] elements on [ X ] defined as a term in [ weq ( stn n ) X ]  *)

Definition nelstruct ( n : nat ) ( X : UU ) := weq ( stn n ) X .

Definition nelstructToFunction {n} {X} (S : nelstruct n X) : stn n -> X := pr1weq S.

Coercion nelstructToFunction : nelstruct >-> Funclass.

Definition nelstructonstn ( n : nat ) : nelstruct n ( stn n ) := idweq _ .

Definition nelstructweqf { X Y : UU } { n : nat } ( w : X ≃ Y ) ( sx : nelstruct n X ) : nelstruct n Y := weqcomp sx w .

Definition nelstructweqb { X Y : UU } { n : nat } ( w : X ≃ Y ) ( sy : nelstruct n Y ) : nelstruct n X := weqcomp sy ( invweq w ) .

Definition nelstructonempty : nelstruct 0 empty := weqstn0toempty .

Definition nelstructonempty2 { X : UU } ( is : neg X ) : nelstruct 0 X :=  weqcomp weqstn0toempty ( invweq ( weqtoempty is ) ) .

Definition nelstructonunit : nelstruct 1 unit := weqstn1tounit .

Definition nelstructoncontr { X : UU } ( is : iscontr X ) : nelstruct 1 X := weqcomp weqstn1tounit ( invweq ( weqcontrtounit is ) ) .

Definition nelstructonbool : nelstruct 2 bool := weqstn2tobool .

Definition nelstructoncoprodwithunit { X : UU } { n : nat } ( sx : nelstruct n X ) : nelstruct ( S n ) ( coprod X unit ) :=  weqcomp ( invweq ( weqdnicoprod n lastelement ) ) ( weqcoprodf sx ( idweq unit ) ) .

Definition nelstructoncompl {X} {n} (x:X) : nelstruct (S n) X -> nelstruct n (compl X x).
Proof.
  intros ? ? ? sx.
  refine (invweq ( weqoncompl ( invweq sx ) x) ∘ _ ∘ weqdnicompl (invweq sx x))%weq.
  apply compl_weq_compl_ne.
Defined.

Definition nelstructoncoprod { X  Y : UU } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( n + m ) ( coprod X Y ) := weqcomp ( invweq ( weqfromcoprodofstn n m ) ) ( weqcoprodf sx sy ) .

Definition nelstructontotal2 { X : UU } ( P : X -> UU ) ( f : X -> nat ) { n : nat } ( sx : nelstruct n X ) ( fs : ∏ x : X , nelstruct ( f x ) ( P x ) ) : nelstruct ( stnsum ( funcomp ( pr1 sx ) f ) ) ( total2 P )  := weqcomp ( invweq ( weqstnsum ( funcomp ( pr1 sx ) P ) ( funcomp ( pr1 sx ) f ) ( λ i : stn n, fs ( ( pr1 sx ) i ) ) ) )  ( weqfp sx P )  .

Definition nelstructondirprod { X Y : UU } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( n * m ) ( dirprod X Y ) := weqcomp ( invweq ( weqfromprodofstn n m ) ) ( weqdirprodf sx sy ) .

(** For a generalization of [ weqfromdecsubsetofstn ] see below *)

Definition nelstructonfun { X Y : UU } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( natpower m n ) ( X -> Y ) := weqcomp ( invweq ( weqfromfunstntostn n m ) ) ( weqcomp ( weqbfun _ ( invweq sx ) ) ( weqffun _ sy ) )  .

Definition nelstructonforall { X : UU } ( P : X -> UU ) ( f : X -> nat ) { n : nat } ( sx : nelstruct n X ) ( fs : ∏ x : X , nelstruct ( f x ) ( P x ) ) : nelstruct ( stnprod ( funcomp ( pr1 sx ) f ) ) ( ∏ x : X , P x )  := invweq ( weqcomp ( weqonsecbase P sx ) ( weqstnprod ( funcomp ( pr1 sx ) P ) ( funcomp ( pr1 sx ) f ) ( λ i : stn n, fs ( ( pr1 sx ) i ) ) ) )  .

Definition nelstructonweq { X : UU } { n : nat } ( sx : nelstruct n X ) : nelstruct ( factorial n ) ( X ≃ X ) := weqcomp ( invweq ( weqfromweqstntostn n ) ) ( weqcomp ( weqbweq _ ( invweq sx ) ) ( weqfweq _ sx ) ) .



(** *** The property of [ X ] to have [ n ] elements *)

Definition isofnel ( n : nat ) ( X : UU ) : hProp := ishinh ( weq ( stn n ) X ) .

Lemma isofneluniv { n : nat} { X : UU }  ( P : hProp ) : ( ( nelstruct n X ) -> P ) -> ( isofnel n X -> P ) .
Proof. intros.  apply @hinhuniv with ( weq ( stn n ) X ) . assumption. assumption. Defined.

Definition isofnelstn ( n : nat ) : isofnel n ( stn n ) := hinhpr ( nelstructonstn n ) .

Definition isofnelweqf { X Y : UU } { n : nat } ( w : X ≃ Y ) ( sx : isofnel n X ) : isofnel n Y := hinhfun ( λ sx0 : _,  nelstructweqf w sx0 ) sx .

Definition isofnelweqb { X Y : UU } { n : nat } ( w : X ≃ Y ) ( sy : isofnel n Y ) : isofnel n X :=  hinhfun ( λ sy0 : _, nelstructweqb w sy0 ) sy .

Definition isofnelempty : isofnel 0 empty := hinhpr nelstructonempty .

Definition isofnelempty2 { X : UU } ( is : neg X ) : isofnel 0 X :=  hinhpr ( nelstructonempty2 is ) .

Definition isofnelunit : isofnel 1 unit := hinhpr nelstructonunit  .

Definition isofnelcontr { X : UU } ( is : iscontr X ) : isofnel 1 X := hinhpr ( nelstructoncontr is ) .

Definition isofnelbool : isofnel 2 bool := hinhpr nelstructonbool .

Definition isofnelcoprodwithunit { X : UU } { n : nat } ( sx : isofnel n X ) : isofnel ( S n ) ( coprod X unit ) :=   hinhfun ( λ sx0 : _,  nelstructoncoprodwithunit sx0 ) sx .

Definition isofnelcompl { X : UU } { n : nat } ( x : X ) ( sx : isofnel ( S n ) X ) : isofnel n ( compl X x ) := hinhfun ( λ sx0 : _,  nelstructoncompl x sx0 ) sx .

Definition isofnelcoprod { X  Y : UU } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( n + m ) ( coprod X Y ) :=  hinhfun2 ( λ sx0 : _, λ sy0 : _,  nelstructoncoprod sx0 sy0 ) sx sy .

(** For a result corresponding to [ nelstructontotal2 ] see below . *)

Definition isofnelondirprod { X Y : UU } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( n * m ) ( dirprod X Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _,  nelstructondirprod sx0 sy0 ) sx sy .

Definition isofnelonfun { X Y : UU } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( natpower m n ) ( X -> Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _,  nelstructonfun sx0 sy0 ) sx sy .

(** For a result corresponding to [ nelstructonforall ] see below . *)

Definition isofnelonweq { X : UU } { n : nat } ( sx : isofnel n X ) : isofnel ( factorial n ) ( X ≃ X ) := hinhfun ( λ sx0 : _,  nelstructonweq sx0 ) sx .




(** ** General finite sets. *)

(** *** Finite structure on a type [ X ] defined as a pair [ ( n , w ) ] where [ n : nat ] and [ w : weq ( stn n ) X ] *)


Definition finstruct  ( X : UU ) := total2 ( λ n : nat, nelstruct n X ) .

Definition finstructToFunction {X} (S : finstruct X) := pr2 S : nelstruct (pr1 S) X.

Coercion finstructToFunction : finstruct >-> nelstruct.

Definition finstructpair  ( X : UU )  := tpair ( λ n : nat, nelstruct n X ) .

Definition finstructonstn ( n : nat ) : finstruct ( stn n ) := tpair _ n ( nelstructonstn n ) .

Definition finstructweqf { X Y : UU } ( w : X ≃ Y ) ( sx : finstruct X ) : finstruct Y := tpair _ ( pr1 sx ) ( nelstructweqf w ( pr2 sx ) ) .

Definition finstructweqb { X Y : UU } ( w : X ≃ Y ) ( sy : finstruct Y ) : finstruct X :=  tpair _ ( pr1 sy ) ( nelstructweqb w ( pr2 sy ) ) .

Definition finstructonempty : finstruct empty := tpair _ 0 nelstructonempty .

Definition finstructonempty2 { X : UU } ( is : neg X ) : finstruct X :=  tpair _ 0 ( nelstructonempty2 is ) .

Definition finstructonunit : finstruct unit := tpair _ 1 nelstructonunit .

Definition finstructoncontr { X : UU } ( is : iscontr X ) : finstruct X := tpair _ 1 ( nelstructoncontr is ) .

(** It is not difficult to show that a direct summand of a finite set is a finite set . As a corrolary it follows that a proposition ( a type of h-level 1 ) is a finite set if and only if it is decidable . *)

Definition finstructonbool : finstruct bool := tpair _ 2 nelstructonbool .

Definition finstructoncoprodwithunit { X : UU }  ( sx : finstruct X ) : finstruct ( coprod X unit ) :=  tpair _ ( S ( pr1 sx ) ) ( nelstructoncoprodwithunit ( pr2 sx ) ) .

Definition finstructoncompl { X : UU } ( x : X ) ( sx : finstruct X ) : finstruct ( compl X x ) .
Proof . intros . unfold finstruct .  unfold finstruct in sx . destruct sx as [ n w ] . destruct n as [ | n ] .  destruct ( negstn0 ( invweq w x ) ) . split with n .   apply ( nelstructoncompl x w ) .  Defined .

Definition finstructoncoprod { X  Y : UU } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( coprod X Y ) := tpair _ ( ( pr1 sx ) + ( pr1 sy ) ) ( nelstructoncoprod ( pr2 sx ) ( pr2 sy ) ) .

Definition finstructontotal2 { X : UU } ( P : X -> UU )   ( sx : finstruct X ) ( fs : ∏ x : X , finstruct ( P x ) ) : finstruct ( total2 P ) := tpair _ ( stnsum ( funcomp ( pr1 ( pr2 sx ) ) ( λ x : X,  pr1 ( fs x ) ) ) ) ( nelstructontotal2 P ( λ x : X, pr1 ( fs x ) ) ( pr2 sx ) ( λ x : X, pr2 ( fs x ) ) ) .

Definition finstructondirprod { X Y : UU } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( dirprod X Y ) := tpair _ ( ( pr1 sx ) * ( pr1 sy ) ) ( nelstructondirprod ( pr2 sx ) ( pr2 sy ) ) .

Definition finstructondecsubset { X : UU }  ( f : X -> bool ) ( sx : finstruct X ) : finstruct ( hfiber f true ) := tpair _ ( pr1 ( weqfromdecsubsetofstn ( funcomp ( pr1 ( pr2 sx ) ) f ) ) ) ( weqcomp ( invweq ( pr2 ( weqfromdecsubsetofstn ( funcomp ( pr1 ( pr2 sx ) ) f ) ) ) ) ( weqhfibersgwtog ( pr2 sx ) f true ) ) .


Definition finstructonfun { X Y : UU } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( X -> Y ) := tpair _ ( natpower ( pr1 sy ) ( pr1 sx ) ) ( nelstructonfun ( pr2 sx ) ( pr2 sy ) ) .

Definition finstructonforall { X : UU } ( P : X -> UU )  ( sx : finstruct X ) ( fs : ∏ x : X , finstruct ( P x ) ) : finstruct ( ∏ x : X , P x )  := tpair _ ( stnprod ( funcomp ( pr1 ( pr2 sx ) ) ( λ x : X,  pr1 ( fs x ) ) ) ) ( nelstructonforall P ( λ x : X, pr1 ( fs x ) ) ( pr2 sx ) ( λ x : X, pr2 ( fs x ) ) ) .

Definition finstructonweq { X : UU }  ( sx : finstruct X ) : finstruct ( X ≃ X ) := tpair _ ( factorial ( pr1 sx ) ) ( nelstructonweq ( pr2 sx ) ) .




(** *** The property of being finite *)

Definition isfinite  ( X : UU ) := ishinh ( finstruct X ) .

Definition FiniteSet := ∑ X:UU, isfinite X.

Definition isfinite_to_FiniteSet {X:UU} (f:isfinite X) : FiniteSet := X,,f.

Lemma isfinite_isdeceq X : isfinite X -> isdeceq X.
(* uses funextemptyAxiom *)
Proof. intros ? isfin.
       apply (isfin (hProppair _ (isapropisdeceq X))); intro f; clear isfin; simpl.
       apply (isdeceqweqf (pr2 f)).
       apply isdeceqstn.
Defined.

Lemma isfinite_isaset X : isfinite X -> isaset X.
Proof.
  intros ? isfin. apply (isfin (hProppair _ (isapropisaset X))); intro f; clear isfin; simpl.
  apply (isofhlevelweqf 2 (pr2 f)). apply isasetstn.
Defined.

Definition FiniteSet_to_hSet : FiniteSet -> hSet.
Proof. intro X. exact (hSetpair (pr1 X) (isfinite_isaset (pr1 X) (pr2 X))).
Defined.
Coercion FiniteSet_to_hSet : FiniteSet >-> hSet.

Definition fincard { X : UU } ( is : isfinite X ) : nat .
Proof.
  intros. apply (squash_pairs_to_set (λ n, stn n ≃ X) isasetnat).
  { intros n n' w w'. apply weqtoeqstn. exact (invweq w' ∘ w)%weq. }
  assumption.
Defined.

Definition cardinalityFiniteSet (X:FiniteSet) : nat := fincard (pr2 X).

Theorem ischoicebasefiniteset { X : UU } ( is : isfinite X ) : ischoicebase X .
Proof . intros . apply ( @hinhuniv ( finstruct X ) ( ischoicebase X ) ) .  intro nw . destruct nw as [ n w ] .   apply ( ischoicebaseweqf w ( ischoicebasestn n ) ) .  apply is .  Defined .

Definition isfinitestn ( n : nat ) : isfinite ( stn n ) := hinhpr ( finstructonstn n ) .

Definition standardFiniteSet n : FiniteSet := isfinite_to_FiniteSet (isfinitestn n).

Definition isfiniteweqf { X Y : UU } ( w : X ≃ Y ) ( sx : isfinite X ) : isfinite Y :=  hinhfun ( λ sx0 : _,  finstructweqf w sx0 ) sx .

Definition isfiniteweqb { X Y : UU } ( w : X ≃ Y ) ( sy : isfinite Y ) : isfinite X :=   hinhfun ( λ sy0 : _,  finstructweqb w sy0 ) sy .

Definition isfiniteempty : isfinite empty := hinhpr finstructonempty .

Definition isfiniteempty2 { X : UU } ( is : neg X ) : isfinite X :=  hinhpr ( finstructonempty2 is ) .

Definition isfiniteunit : isfinite unit := hinhpr finstructonunit .

Definition isfinitecontr { X : UU } ( is : iscontr X ) : isfinite X := hinhpr ( finstructoncontr is ) .

Definition isfinitebool : isfinite bool := hinhpr finstructonbool .

Definition isfinitecoprodwithunit { X : UU } ( sx : isfinite X ) : isfinite ( coprod X unit ) :=  hinhfun ( λ sx0 : _, finstructoncoprodwithunit sx0 ) sx .

Definition isfinitecompl { X : UU } ( x : X ) ( sx : isfinite X ) : isfinite ( compl X x ) := hinhfun ( λ sx0 : _, finstructoncompl x sx0 ) sx .

Definition isfinitecoprod { X  Y : UU } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( coprod X Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _, finstructoncoprod sx0 sy0 ) sx sy .

Definition isfinitetotal2 { X : UU } ( P : X -> UU ) ( sx : isfinite X ) ( fs : ∏ x : X , isfinite ( P x ) ) : isfinite ( total2 P ) .
Proof . intros . set ( fs' := ischoicebasefiniteset sx _ fs ) .  apply ( hinhfun2 ( fun fx0 : ∏ x : X , finstruct ( P x )  => λ sx0 : _, finstructontotal2 P sx0 fx0 ) fs' sx ) .  Defined .

Definition FiniteSetSum {I:FiniteSet} (X : I -> FiniteSet) : FiniteSet.
Proof.
  intros. exists (∑ i, X i).
  apply isfinitetotal2.
  - exact (pr2 I).
  - intros i. exact (pr2 (X i)).
Defined.

Delimit Scope finset with finset.

Notation "'∑' x .. y , P" := (FiniteSetSum (λ x,.. (FiniteSetSum (λ y, P))..))
  (at level 200, x binder, y binder, right associativity) : finset.
  (* type this in emacs in agda-input method with \sum *)

Definition isfinitedirprod { X Y : UU } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( dirprod X Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _, finstructondirprod sx0 sy0 ) sx sy .

Definition isfinitedecsubset { X : UU } ( f : X -> bool ) ( sx : isfinite X ) : isfinite ( hfiber f true ) := hinhfun ( λ sx0 : _,  finstructondecsubset f sx0 ) sx .

Definition isfinitefun { X Y : UU } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( X -> Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _, finstructonfun sx0 sy0 ) sx sy .

Definition isfiniteforall { X : UU } ( P : X -> UU ) ( sx : isfinite X ) ( fs : ∏ x : X , isfinite ( P x ) ) : isfinite ( ∏ x : X , P x ) .
Proof . intros . set ( fs' := ischoicebasefiniteset sx _ fs ) .  apply ( hinhfun2 ( fun fx0 : ∏ x : X , finstruct ( P x )  => λ sx0 : _, finstructonforall P sx0 fx0 ) fs' sx ) .  Defined .

Definition isfiniteweq { X : UU } ( sx : isfinite X ) : isfinite ( X ≃ X ) := hinhfun ( λ sx0 : _,  finstructonweq sx0 ) sx .









(*

(* The cardinality of finite sets using double negation and decidability of equality in nat. *)

Definition carddneg  ( X : UU ) (is: isfinite X): nat:= pr1 (isfiniteimplisfinite0 X is).

Definition preweq  ( X : UU ) (is: isfinite X): isofnel (carddneg X is) X.
Proof. intros X is X0.  set (c:= carddneg X is). set (dnw:= pr2 (isfiniteimplisfinite0 X is)). simpl in dnw. change (pr1 nat (λ n : nat, isofnel0 n X) (isfiniteimplisfinite0 X is)) with c in dnw.

assert (f: dirprod (finitestruct X) (dneg (weq (stn c) X)) -> weq (stn c) X). intro H. destruct H as [ t x ].  destruct t as [ t x0 ].
assert (dw: dneg ((stn t) ≃ (stn c))). set (ff:= fun ab:dirprod (weq (stn t) X)(weq (stn c) X) => weqcomp _ _ _ (pr1 ab) (invweq (pr2 ab))).  apply (dnegf _ _ ff (inhdnegand _ _ (todneg _ x0) x)).
assert (e:t = c). apply (stnsdnegweqtoeq _ _  dw). clear dnw. destruct e. assumption. unfold isofnel.
apply (hinhfun _ _ f (hinhand (finitestruct X) _ is (hinhpr dnw))). Defined.

*)

(* to be completed

Theorem carddnegweqf (X Y:UU)(f: X -> Y)(isw:isweq f)(isx: isfinite X): paths  (carddneg _ isx) (carddneg _ (isfiniteweqf _ _ _ isw isx)).
Proof. intros. *)

(* The cardinality of finite sets defined using the "impredicative" ishinh *)

Definition isfinite_to_DecidableEquality {X} : isfinite X -> DecidableRelation X.
  intros ? fin x y.
  exact (@isdecprop_to_DecidableProposition
                  (x=y)
                  (isdecpropif (x=y)
                               (isfinite_isaset X fin x y)
                               (isfinite_isdeceq X fin x y))).
Defined.

Lemma subsetFiniteness {X} (is : isfinite X) (P : DecidableSubtype X) :
  isfinite (decidableSubtypeCarrier P).
Proof.
  intros.
  assert (fin : isfinite (decidableSubtypeCarrier' P)).
  { now apply isfinitedecsubset. }
  refine (isfiniteweqf _ fin).
  apply decidableSubtypeCarrier_weq.
Defined.

Definition subsetFiniteSet {X:FiniteSet} (P:DecidableSubtype X) : FiniteSet.
Proof. intros X P. exact (isfinite_to_FiniteSet (subsetFiniteness (pr2 X) P)). Defined.

Definition fincard_subset {X} (is : isfinite X) (P : DecidableSubtype X) : nat.
Proof. intros ? fin ?. exact (fincard (subsetFiniteness fin P)). Defined.

Definition fincard_standardSubset {n} (P : DecidableSubtype (stn n)) : nat.
Proof. intros. exact (fincard (subsetFiniteness (isfinitestn n) P)). Defined.

Local Definition bound01 (P:DecidableProposition) : ((choice P 1 0) ≤ 1)%nat.
Proof.
  intros. unfold choice. choose P p q; reflexivity.
Defined.

Definition tallyStandardSubset {n} (P: DecidableSubtype (stn n)) : stn (S n).
Proof. intros. exists (stnsum (λ x, choice (P x) 1 0)). apply natlehtolthsn.
       apply (istransnatleh (m := stnsum(λ _ : stn n, 1))).
       { apply stnsum_le; intro i. apply bound01. }
       assert ( p : ∏ r s, r = s -> (r ≤ s)%nat). { intros ? ? e. destruct e. apply isreflnatleh. }
       apply p. apply stnsum_1.
Defined.

Definition tallyStandardSubsetSegment {n} (P: DecidableSubtype (stn n))
           (i:stn n) : stn n.
  (* count how many elements less than i satisfy P *)
  intros.
  assert (k := tallyStandardSubset
                 (λ j:stn i, P (stnmtostnn i n (natlthtoleh i n (pr2 i)) j))).
  apply (stnmtostnn (S i) n).
  { apply natlthtolehsn. exact (pr2 i). }
  exact k.
Defined.
