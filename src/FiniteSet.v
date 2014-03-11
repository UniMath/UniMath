(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.finitesets
        Ktheory.Utilities.
Definition Data := total2 isfinite.
Definition ToType (X:Data) : Type := pr1 X.
Module Import Coercions.
  Coercion ToType : Data >-> Sortclass.
End Coercions.
Lemma Isdeceq (I:Data) : isdeceq I.
Proof. intros [I i]; simpl. apply @factor_through_squash with (X := finstruct I).
       { apply isapropisdeceq. }
       { intros [n [f j]]. apply @isdeceqweqf with (X := stn n).
         { exists f. assumption. }
         { apply isdeceqstn. } }
       { assumption. } Qed.
