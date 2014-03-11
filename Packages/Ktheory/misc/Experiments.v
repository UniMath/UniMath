(* this file is just for experiments, and is not part of the development *)

(*
Goal forall (T:UU) (X : T -> T -> UU) (t t':T) (e:t==t') , X t t'.
  intros.
  destruct (!e).                (* doesn't work *)
  destruct e.                   (* replaces t' by t and eliminates e *)
  rewrite -> e.                 (* replaces t by t' *)
  rewrite    e.                 (* replaces t by t' *)
  rewrite <- e.                 (* replaces t' by t *)
*)

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel2.stnfsets.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.pathnotations. Import PathNotations.
Require Import RezkCompletion.precategories.

Require Import Ktheory.Utilities.
        Import Ktheory.Utilities.Notations.

Module A.

  Module Type TU.
    Variable T:UU. 
    Variable U:T->UU.
  End TU.

  Module Rec2 ( Import tu : TU ).
    Record F := newF { t:T; u:U t }.
    Lemma Feq (f f':F) (et : paths (t f) (t f')) (eu : paths (et # u f) (u f')) : paths f f'.
      destruct f as [a b].
      destruct f' as [a' b'].
      unfold t in et.
      unfold u in eu.
      destruct eu.
      destruct et.
      apply idpath.
    Defined.
    (* Check Feq. *)
  End Rec2.

  (* Print Module Rec2. *)

  Module nat_nat : TU.
    Definition T := nat.
    Definition U := (fun t:T => nat).
  End nat_nat.

  Module bool_bool : TU.
    Definition T := bool.
    Definition U := (fun t:T => bool).
  End bool_bool.

  Module prod_nat_nat := Rec2 nat_nat.
  Module prod_bool_bool := Rec2 bool_bool.

End A.

Module B.

  Require Import Foundations.Proof_of_Extensionality.funextfun.

  Add LoadPath "." as Ktheory.
  Require Import Ktheory.Utilities.

  Variable T:UU. 
  Variable U:T->UU.
  Variable i:isofhlevel 2 T.
  Variable j:forall t, isofhlevel 2 (U t).  

  Record F := newF { t:T; u:U t }.
  Definition G := total2 U.

  Lemma G2: isofhlevel 2 G.
    apply isofhleveltotal2.
    apply i. apply j. Defined.

  Lemma FG: G == F.
   apply univalenceaxiom.
   set (n := (fun g => newF (pr1 g) (pr2 g)) : G -> F).
   set (m := (fun f => tpair U (t f) (u f)) : F -> G).
   exists n.
   apply (gradth n m).
     intro. destruct x. apply idpath.
     intro. destruct y. apply idpath.
   Defined.

  Lemma F2: isofhlevel 2 F.
    destruct FG.  apply G2.
  Qed.

End B.
