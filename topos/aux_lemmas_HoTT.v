
Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.


(** lemmas taken from the HoTT library resp. the book *)


Definition transportD {A : UU} (B : A -> UU) (C : forall a:A, B a -> UU)
  {x1 x2 : A} (p : x1 == x2) (y : B x1) (z : C x1 y)
  : C x2 (transportf _ p y).
Proof.  destruct p. exact z.
Defined.


Definition transport_sigma {A : UU} {B : A -> UU} {C : forall a:A, B a -> UU}
  {x1 x2 : A} (p : x1 == x2) (yz : total2 (fun y : B x1 => C x1 y ))
  : transportf (fun x => total2 (fun y : B x => C x y)) p yz
    == tpair (fun y => C x2 y) (transportf _ p  (pr1 yz)) (transportD _ _ p (pr1 yz) (pr2 yz)).
Proof.
  destruct p. destruct yz. apply idpath.
Defined.

(*
Definition transport_sigma' {A : UU} {B : A -> UU} {C : total2 (fun a => B a) -> UU}
  {x1 x2 : A} (p : x1 == x2) 
  (yz : total2 (fun y : B x1 => C (tpair (fun a => B a) x1 y) ))

  : transportf (fun x => total2 (fun y : B x => C (tpair (fun a => B a) x y))) p yz
    == tpair (fun y => C (tpair _ x2 y)) (transportf _ p  (pr1 yz)) 
              (transportD _ _ p (pr1 yz) (pr2 yz)).
Proof.
  destruct p. destruct yz. apply idpath.
Defined.
*)