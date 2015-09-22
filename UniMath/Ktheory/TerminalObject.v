(* -*- coding: utf-8 -*- *)

Require Import 
        UniMath.Foundations.hlevel2.hSet
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories 
        UniMath.Ktheory.Utilities.
Require UniMath.Ktheory.Precategories UniMath.Ktheory.Sets UniMath.Ktheory.Representation.
Import UniMath.Ktheory.Utilities.Notation UniMath.Ktheory.Precategories.Notation.
Definition unitFunctor_data (C:precategory) 
     : functor_data (Precategories.Precategory.obmor C) (Precategories.Precategory.obmor SET).
  intros. refine (tpair _ _ _).
  intros. exact Sets.unit. intros. exact (idfun _). Defined.
Definition unitFunctor (C:precategory) : C ==> SET.
  intros. exists (unitFunctor_data C).
  split. intros a . reflexivity. intros a b c f g . reflexivity. Defined.
Definition InitialObject (C:precategory) := Representation.Data (unitFunctor C).
Definition initialObject {C} (i:InitialObject C) : ob C.
  intros C i. exact (Representation.Object i). Defined.
Definition initialArrow {C} (i:InitialObject C) (c:ob C) : initialObject i → c.
  intros C [[i []] p] c. exact (pr1 (the (p (c,,tt)))). Defined.
Definition TerminalObject (C:precategory) 
  := Representation.Data (unitFunctor C^op).
Definition terminalObject {C} (t:InitialObject C) : ob C.
  intros C t. exact (Representation.Object t). Defined.
Definition terminalArrow {C} (t:TerminalObject C) (c:ob C) : c → terminalObject t.
  intros C [[i []] p] c. exact (pr1 (the (p (c,,tt)))). Defined.      
