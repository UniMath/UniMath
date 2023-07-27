(**
Limits
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.equalizers.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Section Creates_Limits.

(* TODO: consider implicitness of argument *)
Definition creates_limit
  {C : category}
  (D : disp_cat C)
  {J : graph}
  (F : diagram J (total_category D))
  (L : LimCone (mapdiagram (pr1_category D) F)) : UU
:=
  ∑ (CC :
      ( ∃! (d : D (pr11 L))
          (δ : ∏ j : vertex J, d -->[limOut L j] (pr2 (dob F j))),
          forms_cone(c:=((pr11 L),,d)) F (λ j, (limOut L j ,, δ j))))
  , isLimCone _ _ (make_cone _ (pr2 (pr2 (pr1 CC)))).

Definition creates_limit_disp_struct
  {C : category}
  {P H Hprop Hid Hcomp}
  (D := disp_struct C P H Hprop Hid Hcomp)
  {J : graph}
  {F : diagram J (total_category D)}
  (L : LimCone (mapdiagram (pr1_category D) F))
  (d : D (pr11 L))
  (cone : ∏ j : vertex J, d -->[limOut L j] (pr2 (dob F j)))
  (d_is_unique : ∏ d', (∏ j : vertex J, d' -->[limOut L j] (pr2 (dob F j))) → d' = d)
  (is_limit : ∏ (d' : total_category D) (cone_out : ∏ u, d' --> (dob F u)) (is_cone : ∏ u v e, cone_out u · (dmor F e) = cone_out v), pr2 d' -->[limArrow L _ (make_cone (d := (mapdiagram (pr1_category D) F)) _ (λ u v e, (maponpaths pr1 (is_cone u v e))))] d)
  : creates_limit D F L.
Proof.
  use (((d ,, (cone ,, _)) ,, _) ,, (λ d' cone', (_ ,, _) ,, _)).
  - abstract (
      do 3 intro;
      apply (subtypePairEquality (λ _, Hprop _ _ _ _ _));
      apply (limOutCommutes L)
    ).
  - abstract (
      intro t;
      apply subtypePairEquality;
      [ intro;
        use (isaprop_total2 (_ ,, _) (λ _, _ ,, _));
          repeat (apply impred_isaprop; intro);
        [ apply Hprop
        | apply (homset_property (total_category _)) ]
      | apply d_is_unique;
        exact (pr12 t) ]
    ).
  - exact (_ ,, is_limit d' (pr1 cone') (pr2 cone')).
  - abstract (
      intro u;
      apply (subtypePairEquality (λ _, Hprop _ _ _ _ _));
      exact (limArrowCommutes L _ _ _)
    ).
  - abstract (
      intro t;
      repeat apply subtypePairEquality;
      [ intro;
        apply impred_isaprop;
        intro;
        apply (homset_property (total_category _))
      | simpl;
        intro;
        apply Hprop
      | apply (limArrowUnique L);
        intro;
        exact (maponpaths pr1 (pr2 t u)) ]
    ).
Defined.

Definition creates_limit_disp_full_sub
  {C : category}
  {P : C → UU}
  (D := disp_full_sub C P)
  (H : ∏ c, isaprop (P c))
  {J : graph}
  {F : diagram J (total_category D)}
  (L : LimCone (mapdiagram (pr1_category D) F))
  (d : P (pr11 L))
  : creates_limit D F L.
Proof.
  use (((d ,, (_ ,, _)) ,, _) ,, (λ d' cone', (_ ,, _) ,, _));
    simpl.
  - abstract exact (λ _, tt).
  - abstract (
      do 3 intro;
      apply subtypePairEquality';
      [ apply (limOutCommutes L)
      | apply isapropunit ]
    ).
  - abstract (
      intro;
      apply subtypePairEquality';
      [ apply H
      | use (isaprop_total2 (_ ,, _) (λ _, _ ,, _));
        [ apply impred_isaprop;
          intro;
          apply isapropunit
        | do 3 (apply impred_isaprop; intro);
          simpl;
          apply isaset_dirprod;
          [ apply homset_property
          | apply isasetunit] ] ]
    ).
  - use (_ ,, tt).
    apply limArrow.
    exact (mapcone (pr1_category D) F cone').
  - abstract (
      intro;
      apply subtypePairEquality';
      [ apply (limArrowCommutes L)
      | apply isapropunit ]
    ).
  - abstract (
      intro;
      repeat apply subtypePairEquality';
      [ apply limArrowUnique;
        intro;
        exact (maponpaths pr1 (pr2 t u))
      | abstract apply isapropunit
      | apply impred_isaprop;
        intro;
        apply (homset_property (total_category _)) ]
    ).
Defined.

Definition creates_limits {C : category} (D : disp_cat C) : UU := ∏
  (J : graph)
  (F : diagram J (total_category D))
  (L : LimCone (mapdiagram (pr1_category D) F) ),
  creates_limit _ _ L.

End Creates_Limits.

Definition total_limit
  {C : category}
  (D : disp_cat C)
  {J : graph}
  {F : diagram J (total_category D)}
  (L : LimCone (mapdiagram (pr1_category D) F))
  (H : creates_limit _ _ L)
  : LimCone F
  := make_LimCone _ _ _ (pr2 H).

Definition total_limits
  {C : category}
  (D : disp_cat C)
  (J : graph)
  (H : creates_limits D)
  (X : Lims_of_shape J C)
  : Lims_of_shape J (total_category D)
  := λ d, total_limit _ (X _) (H _ _ _).

Section creates_preserves.

Context {C : category}
        (D : disp_cat C)
        (J : graph)
        (H : creates_limits D)
        (X : Lims_of_shape J C).

Notation π := (pr1_category D).

Lemma pr1_preserves_limit (d : diagram J (total_category D))
  (x : total_category D) (CC : cone d x) : preserves_limit π _ x CC.
Proof.
  intro H1.
  set (XR := X (mapdiagram π d)).
  use is_z_iso_isLim.
  - apply X.
  - match goal with |[ |- is_z_isomorphism ?foo ] => set (T:= foo) end.
    destruct X as [[a L] isL]. cbn in isL.
    set (tL := H _ _ (make_LimCone _ _ _ isL)).
    clear XR.
    unfold creates_limit in tL.
    set (RR := pr1 tL).
    set (RT1 := pr2 tL).
(*
    set (RX := isLim_is_iso _ (make_LimCone _ _ CC H1) _ _ RT1).
    cbn in RX.
    set (XR := @functor_on_is_iso_is_iso _ _ π _ _ _ RX).
    cbn in XR.
    match goal with |[ H : is_iso ?f |- _ ] => set (T':= f) end.
*)

    set (RX := isLim_is_z_iso _ (make_LimCone _ _ _ RT1) _ _ H1).
    set (XR := @functor_on_is_z_isomorphism _ _ π _ _ _ RX).
    match goal with |[ H : is_z_isomorphism ?f |- _ ] => set (T':= f) end.

    assert (X0 : T' = T).
    {

      clear XR.
      clear RX.
      unfold T.
      unfold T'.
      apply (limArrowUnique (make_LimCone _ _ _ isL)) .
      intro j.
      set (RRt := make_LimCone _ _ _ RT1).
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
