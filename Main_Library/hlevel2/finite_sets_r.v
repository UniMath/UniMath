(** * Addendum to Finite Sets.

In this file we introduce the type of finite sets as well as another definition of the cardinality function based on [ isapropishinh ] . *)



(** *** Preambule *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** *** Imports. *)


Require Export hProp_r hSet_r finite_sets.


(** *** Some Canonical Structures. *)

Definition isofnelinhProp ( n : nat )  ( X : UU0 ) := hProppair ( isofnel n X ) ( isapropishinh _ ). 
Canonical Structure isofnelinhProp.




(** *** The type of finite sets. *)


Definition hFSet := uu1.total2 UU0 ( fun X : UU0 => isfinite X ) .
Definition hFSetpair := uu1.tpair  UU0 ( fun X : UU0 => isfinite X ) .





Lemma cardaux1 ( X : UU0 ) ( n m : nat )  : isofnel n X -> isofnel m X -> paths _ n m .
Proof. intros X n m is1 is2. 
assert ( is : ishinh ( dirprod ( weq ( stn n ) X ) ( weq ( stn m ) X ) ) ) .   apply hinhand. assumption. assumption. 
apply ( hinhuniv  ( dirprod ( weq ( stn n ) X ) ( weq ( stn m ) X ) ) ( hProppair ( paths _ n m ) ( isasetnat n m ) )) . 
intro dp. destruct dp as [ wn wm ] . 
assert ( e : paths _ n m ) . apply stnsweqtoeq.  apply ( weqcomp _ _ _ wn ( weqinv _ _ wm ) ) .  assumption.  assumption.  Defined.


Lemma cardaux2 ( X : UU0 ) : isaprop ( total2 nat (fun n : nat => isofnel n X ) ) .
Proof. intro. apply ( isaprophsubtype nat_set ( fun n : nat => isofnelinhProp n X ) (cardaux1 X ) ) .   Defined. 


Definition card : hFSet -> nat .
Proof. intro. destruct X as [ X0 is ] . unfold isfinite in is.     
assert ( f  : finitestruct X0 -> total2 nat (fun n : nat => isofnel n X0 ) ) .  intro fs.  unfold finitestruct in fs.  split with ( pr21 _ _ fs ) .  apply hinhpr.  apply (pr22 _ _ fs ) . 
assert ( g: isfinite X0 -> total2 nat (fun n : nat => isofnel n X0) ). apply ( hinhuniv _ ( hProppair _ (cardaux2 X0) ) f ) .  apply ( pr21 _ _ ( g is ) ) . Defined. 





(** *** Test Computations. *)




Eval compute in card ( hFSetpair _  (isfinitedirprod _ _ (isfinitestn (S (S (S (S O)))))  (isfinitestn (S (S (S O)))))).

Eval compute in card ( hFSetpair  _ (isfiniteempty)).

Eval compute in card ( hFSetpair  _ (isfiniteunit)).

Eval lazy in card ( hFSetpair  _  (isfinitebool)).


Eval lazy in card ( hFSetpair  _ (isfinitecomplement _ true isfinitebool)).

Eval compute in card ( hFSetpair  _ (isfinitedirprod _ _ isfinitebool isfinitebool)).

Eval compute in card ( hFSetpair  _ (isfinitedirprod _ _ isfinitebool (isfinitedirprod _ _ isfinitebool isfinitebool))).

Eval compute in card ( hFSetpair  _ (isfinitecoprod _ _ (isfinitebool) (isfinitecomplement _ (ii1 _ _ (ii2 _ _ tt)) (isfinitestn (S (S (S O))))))).

Eval lazy in card ( hFSetpair  _ (isfinitecomplement _ (ii1 _ _ tt) (isfinitecoprod _ _ (isfiniteunit) (isfinitebool)))).

Eval lazy in  card ( hFSetpair  _ (isfinitecomplement _ (ii1 _ _ tt) (isfinitecoprod _ _ (isfiniteunit) (isfinitebool)))).

Eval lazy in card ( hFSetpair  _ (isfinitecomplement _ (dirprodpair _ _ tt tt) (isfinitedirprod _ _ isfiniteunit isfiniteunit))).


Eval lazy in (pr21 _ _ (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))).
 


Eval lazy in card ( hFSetpair  _ (isfinitecomplement _ (dirprodpair _ _ true (dirprodpair _ _ true false)) (isfinitedirprod _ _ (isfinitebool) (isfinitedirprod _ _ (isfinitebool) (isfinitebool))))).










(* End of the file finite_sets_r.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)