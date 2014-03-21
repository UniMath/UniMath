(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.algebra1a
        Ktheory.Utilities.
Require Ktheory.Sets.
Import RezkCompletion.pathnotations.PathNotations Ktheory.Utilities.Notation.
Local Notation "x * y" := (op x y). 
Local Notation "g ∘ f" := (binopfuncomp f g) (at level 50, only parsing).
Local Notation Hom := binopfun.
Definition funEquality G H (p q : Hom G H)
           (v : pr1 p == pr1 q) : p == q.
  intros ? ? [p i] [q j] v. simpl in v. destruct v.
  destruct (pr1 (isapropisbinopfun p i j)). reflexivity. Qed.
Definition zero : setwithbinop.
  exists Sets.unit. exact (fun _ _ => tt). Defined.
Module Product.
  Lemma i1 {I} (X:I->setwithbinop) : isaset(sections X).
  Proof. intros. apply (impred 2); intros i. apply pr2. Qed.
  Definition make {I} (X:I->setwithbinop) : setwithbinop.
    intros.
    exists (sections X,,i1 X). exact (fun v w i => v i * w i). Defined.
  Definition Proj {I} (X:I->setwithbinop) : forall i:I, Hom (make X) (X i).
    intros. exists (fun y => y i). intros a b. reflexivity. Defined.
  Definition Fun {I} (X:I->setwithbinop) (T:setwithbinop)
             (g: forall i, Hom T (X i))
             : Hom T (make X).
    intros. exists (fun t i => g i t).
    intros t u. apply funextsec; intro i. apply (pr2 (g i)). Defined.
  Definition Eqn {I} (X:I->setwithbinop) (T:setwithbinop) (g: forall i, Hom T (X i))
             : forall i, Proj X i ∘ Fun X T g == g i.
    intros. apply funEquality. reflexivity. Qed.
End Product.
