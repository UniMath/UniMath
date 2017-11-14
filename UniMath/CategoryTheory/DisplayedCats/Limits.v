(**
Limits
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

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
  {C : category}
  (D : disp_cat C)
  {J : graph} (F : diagram J (total_category D))
  {x : C} (L : cone (mapdiagram (pr1_category D) F)  x)
  (isL : isLimCone _ x L) : UU
:=
  ∑ (CC : iscontr
      ( ∑ (d : D x)
          (δ : ∏ j : vertex J, d -->[L j] (pr2 (dob F j))),
          forms_cone F (x,,d)  (λ j, (L j ,, δ j))))
  , isLimCone _ _ (mk_cone _ (pr2 (pr2 (iscontrpr1 CC)))).

Definition creates_limits {C : category} (D : disp_cat C) : UU
:=
  ∏ (J : graph) (F : diagram J (total_category D))
    {x : C} (L : cone (mapdiagram (pr1_category D) F)  x)
    (isL : isLimCone _ x L),
  creates_limit _ _ _ isL.

End Creates_Limits.

Section creates_preserves.

Context {C : category}
        (D : disp_cat C)
        (H : creates_limits D)
        (J : graph)
        (X : Lims_of_shape J C).

Notation π := (pr1_category D).

Definition total_limits : Lims_of_shape J (total_category D).
Proof.
  intro d.
  set (πd := mapdiagram π d).
  set (LL := X πd).
  set (L := pr1 LL).
  set (c := pr1 L).
  set (isL := pr2 LL). cbn in isL.
  set (XR := H _ d _ _ isL).
  unfold creates_limit in XR.
  cbn.
  use (mk_LimCone _ _ _ (pr2 XR)).
Defined.

Lemma pr1_preserves_limit (d : diagram J (total_category D))
  (x : total_category D) (CC : cone d x) : preserves_limit π _ x CC.
Proof.
  intro H1.
  set (XR := X (mapdiagram π d)).
  use is_iso_isLim.
  - apply homset_property.
  - apply X.
  - match goal with |[ |- is_iso ?foo ] => set (T:= foo) end.
    destruct X as [[a L] isL]. cbn in isL.
    clear XR.
    set (tL := H _ _ _ _ isL).
    unfold creates_limit in tL.
    set (RR := pr1 tL).
    set (RT1 := pr2 tL).
(*
    set (RX := isLim_is_iso _ (mk_LimCone _ _ CC H1) _ _ RT1).
    cbn in RX.
    set (XR := @functor_on_is_iso_is_iso _ _ π _ _ _ RX).
    cbn in XR.
    match goal with |[ H : is_iso ?f |- _ ] => set (T':= f) end.
*)

    set (RX := isLim_is_iso _ (mk_LimCone _ _ _ RT1) _ _ H1).
    set (XR := @functor_on_is_iso_is_iso _ _ π _ _ _ RX).
    match goal with |[ H : is_iso ?f |- _ ] => set (T':= f) end.

    assert (X0 : T' = T).
    {

      clear XR.
      clear RX.
      unfold T.
      unfold T'.
      apply (limArrowUnique (mk_LimCone _ _ _ isL)) .
      intro j.
      set (RRt := mk_LimCone _ _ _ RT1).
      set (RRtt := limArrowCommutes RRt x CC j).
      set (RH := maponpaths (#π)%Cat RRtt).
      cbn in RH.
      apply RH.
    }
    rewrite <- X0.
    apply XR.
Defined.

End creates_preserves.


(* *)