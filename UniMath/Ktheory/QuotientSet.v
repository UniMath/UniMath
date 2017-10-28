(* -*- coding: utf-8 -*- *)

Require Import
        UniMath.Foundations.Sets
        UniMath.Ktheory.Utilities.
Unset Automatic Introduction.
Definition iscomprelfun2 {X Y Z} (RX:hrel X) (RY:hrel Y)
           (f:X->Y->Z) : Type
  := (∏ x x', RX x x' -> ∏ y, f x y = f x' y) ×
     (∏ y y', RY y y' -> ∏ x, f x y = f x y').
Definition iscomprelrelfun2 {X Y Z} (RX:hrel X) (RY:hrel Y) (RZ:eqrel Z)
           (f:X->Y->Z) : Type
  := (∏ x x' y, RX x x' -> RZ (f x y) (f x' y)) ×
     (∏ x y y', RY y y' -> RZ (f x y) (f x y')).
Lemma setquotuniv_equal { X : UU } ( R : hrel X ) ( Y : hSet )
      ( f f' : X -> Y ) (p : f = f')
      ( is : iscomprelfun R f ) ( is' : iscomprelfun R f' )
: setquotuniv R Y f is = setquotuniv R Y f' is'.
Proof. intros. destruct p. apply funextsec; intro c.
       assert(ip : isaprop (iscomprelfun R f)). {
         apply impred; intro x; apply impred; intro x'.
         apply impred; intro p. apply setproperty. }
       assert( q : is = is' ). { apply ip. }
       destruct q. reflexivity. Qed.
Definition setquotuniv2 {X Y} (RX:hrel X) (RY:hrel Y)
           {Z:hSet} (f:X->Y->Z) (is:iscomprelfun2 RX RY f) :
  setquot RX -> setquot RY -> Z.
Proof. intros ? ? ? ? ? ? ? x''.
       simple refine (setquotuniv RX (funset (setquot RY) Z) _ _ _).
       { simpl. intro x. apply (setquotuniv RY Z (f x)).
         intros y y' e. unfold iscomprelfun2 in is.
         apply (pr2 is). assumption. }
       { intros x x' e.
         assert( p : f x = f x' ).
         { apply funextsec; intro y. apply (pr1 is). assumption. }
       apply setquotuniv_equal. assumption. } assumption. Defined.
Definition setquotfun2 {X Y Z} {RX:hrel X} {RY:hrel Y} {RZ:eqrel Z}
           (f:X->Y->Z) (is:iscomprelrelfun2 RX RY RZ f) :
  setquot RX -> setquot RY -> setquot RZ.
Proof. intros ? ? ? ? ? ? ? ?.
       set (f' := λ x y, setquotpr RZ (f x y) : setquotinset RZ).
       apply (setquotuniv2 RX RY f'). split.
       { intros ? ? p ?. apply iscompsetquotpr. exact (pr1 is x x' y p). }
       { intros ? ? p ?. apply iscompsetquotpr. exact (pr2 is x y y' p). }
Defined.
Lemma setquotfun2_equal {X Y Z} (RX:eqrel X) (RY:eqrel Y) (RZ:eqrel Z)
           (f:X->Y->Z) (is:iscomprelrelfun2 RX RY RZ f)
           (x:X) (y:Y) :
  setquotfun2 f is (setquotpr RX x) (setquotpr RY y) =
  setquotpr RZ (f x y).
Proof. reflexivity. (* it computes! *) Defined.
