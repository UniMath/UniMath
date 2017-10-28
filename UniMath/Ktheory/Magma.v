(* -*- coding: utf-8 -*- *)

Require Import UniMath.Algebra.BinaryOperations
        UniMath.Ktheory.Utilities.
Unset Automatic Introduction.
Local Notation "x * y" := (op x y).
Local Notation "g ∘ f" := (binopfuncomp f g) (at level 50, left associativity, only parsing).
Local Notation magma := setwithbinop.
Local Notation Hom := binopfun.
(** maps between magmas are equal if their underlying functions are equal *)
Definition funEquality G H (p q : Hom G H)
           (v : pr1 p = pr1 q) : p = q.
  intros ? ? [p i] [q j] v. simpl in v. destruct v.
  destruct (pr1 (isapropisbinopfun p i j)). reflexivity. Qed.
(** the trivial magma *)
Definition zero : magma.
  exists unitset. exact (λ _ _, tt). Defined.
(** product of magmas

    See Bourbaki Algebra, Chapter I, page 2 *)
Module Product.
  Lemma i1 {I} (X:I->magma) : isaset(∏ i, X i).
  Proof. intros. apply (impred 2); intros i. apply pr2. Qed.
  (** construction of the product *)
  Definition make {I} (X:I->magma) : magma.
    intros.
    exists ((∏ i, X i),,i1 X). exact (λ v w i, v i * w i). Defined.
  (** the projection maps *)
  Definition Proj {I} (X:I->setwithbinop) : ∏ i:I, Hom (make X) (X i).
    intros. exists (λ y, y i). intros a b. reflexivity. Defined.
  (** the universal map *)
  Definition Fun {I} (X:I->setwithbinop) (T:setwithbinop)
             (g: ∏ i, Hom T (X i))
             : Hom T (make X).
    intros. exists (λ t i, g i t).
    intros t u. apply funextsec; intro i. apply (pr2 (g i)). Defined.
  Definition Eqn {I} (X:I->setwithbinop) (T:setwithbinop) (g: ∏ i, Hom T (X i))
             : ∏ i, Proj X i ∘ Fun X T g = g i.
    intros. apply funEquality. reflexivity. Qed.
End Product.
