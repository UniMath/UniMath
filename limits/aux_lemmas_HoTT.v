
Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


Lemma eq_equalities_between_pairs (A : UU)(B : A -> UU)(x y : total2 (fun x => B x))
    (p q : x == y) (H : base_paths _ _ p == base_paths _ _ q) 
    (H2 : transportf (fun p : pr1 x == pr1 y =>  transportf _ p (pr2 x) == pr2 y )
         H (fiber_path p) == fiber_path q) :  p == q.
Proof.
  apply equal_equalities_between_pairs.
  set (H3 := total2_paths (B:=(fun p : pr1 x == pr1 y =>
          transportf (fun x : A => B x) p (pr2 x) == pr2 y))
          (s:=(total_paths_equiv B x y) p)
          (s':=(total_paths_equiv B x y) q) H).
   
  apply H3.
  assumption.
Defined.



Lemma transportf_idpath (X : UU) (P : X -> UU) (x : X)(z : P x) :
   transportf _ (idpath x) z == z.
Proof.
  unfold transportf.
  simpl.
  apply idpath.
Defined.


(** lemmas taken from the HoTT library resp. the book *)


Definition transportD {A : UU} (B : A -> UU) (C : forall a:A, B a -> UU)
  {x1 x2 : A} (p : x1 == x2) (y : B x1) (z : C x1 y)
  : C x2 (transportf _ p y).
Proof.  destruct p. exact z.
Defined.


Definition transportf_sigma {A : UU} {B : A -> UU} {C : forall a:A, B a -> UU}
  {x1 x2 : A} (p : x1 == x2) (yz : total2 (fun y : B x1 => C x1 y ))
  : transportf (fun x => total2 (fun y : B x => C x y)) p yz
    == tpair (fun y => C x2 y) (transportf _ p  (pr1 yz)) (transportD _ _ p (pr1 yz) (pr2 yz)).
Proof.
  destruct p. destruct yz. apply idpath.
Defined.

Definition transportf_dirprod (A : UU) (B B' : A -> UU) (x x' : total2 (fun a => dirprod (B a) (B' a)))
   (p : pr1 x == pr1 x') :
  transportf (fun a => dirprod (B a) (B' a)) p (pr2 x) == 
                            dirprodpair (transportf (fun a => B a) p (pr1 (pr2 x))) 
                                        (transportf (fun a => B' a) p (pr2 (pr2 x))) .
Proof.
  destruct x as [t tp].
  destruct x' as [t' tp'].
  simpl in *.
  destruct p.
  simpl.
  pathvia tp.
  rewrite transportf_idpath. apply idpath. 
  (* here apply transportf_idpath should work *)
  repeat rewrite transportf_idpath.
  apply tppr.
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