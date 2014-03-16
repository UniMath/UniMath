(* -*- coding: utf-8 -*- *)

(** *** terminal objects *)

Unset Automatic Introduction.
Require Import
        Ktheory.Utilities
        Ktheory.Precategories
        RezkCompletion.precategories
        RezkCompletion.auxiliary_lemmas_HoTT
        Foundations.hlevel2.hSet.
Import Precategories.Notation.
Module TerminalObject.
  Definition isTerminalObject (C:precategory) (a:ob C) := 
    forall x:ob C, iscontr (a ← x).
  Lemma theTerminalObjectIsomorphy (C:precategory) (a b:ob C) :
    isTerminalObject C a -> isTerminalObject C b -> @iso C a b.
  Proof. intros ? ? ? map_to_a_from_ map_to_b_from_. 
    exists (the (map_to_b_from_ a)).
    exists (the (map_to_a_from_ b)). 
    split. { intermediate_path (the (map_to_a_from_ a)). 
             apply uniqueness. apply uniqueness'. }
           { intermediate_path (the (map_to_b_from_ b)). 
             apply uniqueness. apply uniqueness'. } Defined.
  Lemma isaprop_isTerminalObject (C:precategory) (a:ob C) :
    isaprop(isTerminalObject C a).
  Proof. prop_logic. Qed.
  Definition isTerminalObjectProp (C:precategory) (a:ob C) := 
    hProppair (isTerminalObject C a) (isaprop_isTerminalObject C a) : hProp.
  Definition TerminalObject (C:precategory) := 
    total2 (fun a:ob C => isTerminalObject C a).
  Definition theTerminalObject {C:precategory} (z:TerminalObject C) := pr1 z.
  Definition theTerminalProperty {C:precategory} (z:TerminalObject C) := pr2 z.
  Lemma isaprop_TerminalObject (C:category) : isaprop (TerminalObject C).
  Proof. intros. apply invproofirrelevance. intros a b.
    apply (total2_paths 
             (isotoid _ (Precategories.theUnivalenceProperty C) 
                      (theTerminalObjectIsomorphy C _ _      
                         (theTerminalProperty a)
                         (theTerminalProperty b)))).
    apply isaprop_isTerminalObject. Qed.
  Definition squashTerminalObject (C:precategory) := squash (TerminalObject C).
  Definition squashTerminalObjectProp (C:precategory) := 
    hProppair (squashTerminalObject C) (isaprop_squash _).
End TerminalObject.

(** *** initial objects *)

Module InitialObject.
  Import RezkCompletion.pathnotations.PathNotations Ktheory.Utilities.Notation.
  Definition isInitialObject (C:precategory) (a:ob C) :=
    forall x:ob C, iscontr (x ← a).
  Lemma theInitialObjectIsomorphy (C:precategory) (a b:ob C) :
    isInitialObject C a -> isInitialObject C b -> @iso C a b.
  Proof. intros ? ? ? map_to_a_from_ map_to_b_from_. 
    exists (the (map_to_a_from_ b)). 
    exists (the (map_to_b_from_ a)).
    split. { intermediate_path (the (map_to_a_from_ a)). 
             apply uniqueness. apply uniqueness'. }
           { intermediate_path (the (map_to_b_from_ b)). 
             apply uniqueness. apply uniqueness'. } Defined.
  Lemma isaprop_isInitialObject (C:precategory) (a:ob C) :
    isaprop(isInitialObject C a).
  Proof. prop_logic. Qed.
  Definition isInitialObjectProp (C:precategory) (a:ob C) := 
    hProppair (isInitialObject C a) (isaprop_isInitialObject C a) : hProp.
  Record InitialObject (C:precategory) := make_InitialObject {
       theInitialObject : ob C ;
       theInitialProperty : isInitialObject C theInitialObject }.
  Definition InitialObject_total (C:precategory) := 
    total2 (fun a:ob C => isInitialObject C a).
  Definition unpack {C:precategory} : InitialObject_total C -> InitialObject C
    := fun X => make_InitialObject C (pr1 X) (pr2 X).
  Definition pack {C:precategory} : InitialObject C -> InitialObject_total C
    := fun Y => (theInitialObject _ Y,,theInitialProperty _ Y).
  Definition h {C:precategory} (X:InitialObject_total C) : pack (unpack X) == X
    := match X as t return (pack (unpack t) == t) 
       with X1,, X2 => idpath (X1,, X2) end.
  Definition k {C:precategory} (Y:InitialObject C) : unpack (pack Y) == Y
    := match Y as i return (unpack (pack i) == i) 
       with make_InitialObject _ Y1 Y2 => idpath _ end.
  Lemma unpack_weq (C:precategory) : weq (InitialObject_total C) (InitialObject C).
  Proof. intros. exists unpack. intros Y. exists (pack Y,,k Y). intros [X m].
         destruct m. set (H := h X). destruct H. reflexivity. Qed.
  Lemma isaprop_InitialObject' (C:category) : isaprop (InitialObject_total C).
  Proof. intros. apply invproofirrelevance. intros a b.
    apply (total2_paths (isotoid _ (Precategories.theUnivalenceProperty C) 
                          (theInitialObjectIsomorphy C _ _ (pr2 a) (pr2 b)))).
    apply isaprop_isInitialObject. Qed.
  Lemma isaprop_InitialObject (C:category) : isaprop (InitialObject C).
    intros. apply isofhlevelweqf with (X := InitialObject_total C).
    apply unpack_weq. apply isaprop_InitialObject'. Qed.
  Definition squashInitialObject (C:precategory) := squash (InitialObject C).
  Definition squashInitialObjectProp (C:precategory) := 
    hProppair (squashInitialObject C) (isaprop_squash _).
End InitialObject.
