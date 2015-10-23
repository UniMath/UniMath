(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.FiniteSets
        UniMath.Ktheory.Utilities.
Definition Data := totalSpace isfinite.
Definition ToType (X:Data) : Type := pr1 X.
Module Import Coercions.
  Coercion ToType : Data >-> Sortclass.
End Coercions.
Lemma Isdeceq (I:Data) : isdeceq I.
Proof. intros [I i]; simpl. apply isfinite_isdeceq. assumption. Qed.                            
