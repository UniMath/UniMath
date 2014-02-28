(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.algebra1b.
Require RezkCompletion.pathnotations Ktheory.Monoid.
Import pathnotations.PathNotations.
Local Notation Hom := monoidfun.
Local Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, only parsing).
Definition zero : gr.
  exists Monoid.zero. exists (pr2 Monoid.zero). exists (idfun unit).
  split. intro x. reflexivity. intro x. reflexivity. Defined.
Module Presentation.
  (** * groups by generators and relations *)
End Presentation.
Module Product.
  Definition make {I} (X:I->gr) : gr.
    intros. set (Y := Monoid.Product.make X). exists (pr1monoid Y). exists (pr2 Y).
    exists (fun y i => grinv (X i) (y i)). split.
    - intro y. apply funextsec; intro i. apply grlinvax.
    - intro y. apply funextsec; intro i. apply grrinvax. Defined.    
  Definition Proj {I} (X:I->gr) (i:I) : Hom (make X) (X i).
    intros. exact (Monoid.Product.Proj X i). Defined.
  Definition Fun {I} (X:I->gr) (T:gr) (g: forall i, Hom T (X i)) : Hom T (make X).
    intros. exact (Monoid.Product.Fun X T g). Defined.
  Definition Eqn {I} (X:I->gr) (T:gr) (g: forall i, Hom T (X i))
             : forall i, Proj X i ∘ Fun X T g == g i.
    intros. apply Monoid.funEquality. reflexivity. Qed.
End Product.

