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

(* TODO: upstream into definition of cone in UniMath. *)
Definition forms_cone 
    {C : precategory} {g : graph} (d : diagram g C)
    (c : C) (f : ∏ (v : vertex g), C⟦c, dob d v⟧)
  : UU
:= ∏ (u v : vertex g) (e : edge u v),
     f u · dmor d e = f v.

Coercion coneOut : cone >-> Funclass.

End Auxiliary.

Section Creates_Limits.

(* TODO: consider implicitness of argument *)
Definition creates_limit
  {C : Precategory}
  (D : disp_precat C)
  {J : graph} (F : diagram J (total_precat D))
  {x : C} (L : cone (mapdiagram (pr1_precat D) F)  x)
  (isL : isLimCone _ x L) : UU
:= 
  ∑ (CC : iscontr 
      ( ∑ (d : D x)
          (δ : ∏ j : vertex J, d -->[L j] (pr2 (dob F j))),
          forms_cone F (x,,d)  (λ j, (L j ,, δ j))))
  , isLimCone _ _ (mk_cone _ (pr2 (pr2 (iscontrpr1 CC)))).
         
Definition creates_limits {C : Precategory} (D : disp_precat C) : UU
:= 
  ∏ {J : graph} (F : diagram J (total_precat D))
    {x : C} (L : cone (mapdiagram (pr1_precat D) F)  x)
    (isL : isLimCone _ x L),
  creates_limit _ _ _ isL.

End Creates_Limits.
           


(* *)