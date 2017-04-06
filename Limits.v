(**
Limits
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations. 


Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Section Auxiliary.

Definition forms_cone {C : precategory} {g : graph} (d : diagram g C) (c : C) 
           (f : ∏ (v : vertex g), C⟦c, dob d v⟧) : UU
  :=  ∏ (u v : vertex g) (e : edge u v), f u · dmor d e  = f v.

Definition forms_cone_and_isLimCone {C : precategory} {g : graph} 
           (d : diagram g C) (c : C) 
           (f : ∏ (v : vertex g), C⟦c, dob d v⟧) : UU
  := ∑ H : forms_cone _ _ f,
           isLimCone _ _ (mk_cone _ H).

End Auxiliary.

Section limit.
Definition creates_limit_for
           {C : Precategory}
           (D : disp_precat C)
           {J : graph}
           (F : diagram J (total_precat D))
           {x : C}
           (L : cone (mapdiagram (pr1_precat D) F)  x)
           (isL : isLimCone _ x L) : UU
  := iscontr (
         ∑ (d : D x) (δ : ∏ j : vertex J, 
                                d -->[coneOut L j] (pr2 (dob F j))),
         forms_cone_and_isLimCone F (x,,d) (λ j, (coneOut L j,, δ j))
         ).

Definition creates_limits {C : Precategory} (D : disp_precat C) : UU
  := ∏  {J : graph}
        (F : diagram J (total_precat D))
        {x : C}
        (L : cone (mapdiagram (pr1_precat D) F)  x)
        (isL : isLimCone _ x L),
     creates_limit_for _ F L isL.


End limit.
           


(* *)