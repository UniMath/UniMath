(**
Limits
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.
Local Open Scope mor_disp.

Section Creates_Limits.

(* TODO: consider implicitness of argument *)
Definition creates_limit
  {C : category}
  {D : disp_cat C}
  {J : graph}
  (F : diagram J (total_category D))
  (L : LimCone (mapdiagram (pr1_category D) F)) : UU
:=
  ∑ (CC :
      ( ∑ (d : D (lim L))
          (δ : ∏ j : vertex J, d -->[limOut L j] (pr2 (dob F j))),
          forms_cone (c := (lim L ,, d)) F (λ j, (limOut L j ,, δ j))))
  , isLimCone _ _ (make_cone _ (pr2 (pr2 CC))).

Definition make_creates_limit
  {C : category}
  {D : disp_cat C}
  {J : graph}
  {F : diagram J (total_category D)}
  {L : LimCone (mapdiagram (pr1_category D) F)}
  (d : D (lim L))
  (δ : ∏ j : vertex J, d -->[limOut L j] (pr2 (dob F j)))
  (Hcone : forms_cone (c := (lim L ,, d)) F (λ j, (limOut L j ,, δ j)))
  (Hlim : isLimCone _ _ (make_cone _ Hcone))
  : creates_limit F L
  := ((d ,, δ ,, Hcone) ,, Hlim).

Definition creates_limit_unique
  {C : category}
  {D : disp_cat C}
  {J : graph}
  (F : diagram J (total_category D))
  (L : LimCone (mapdiagram (pr1_category D) F)) : UU
:=
  ∑ (CC :
      ( ∃! (d : D (lim L))
          (δ : ∏ j : vertex J, d -->[limOut L j] (pr2 (dob F j))),
          forms_cone (c := (lim L ,, d)) F (λ j, (limOut L j ,, δ j))))
  , isLimCone _ _ (make_cone _ (pr2 (pr2 (pr1 CC)))).

Definition make_creates_limit_unique
  {C : category}
  {D : disp_cat C}
  {J : graph}
  {F : diagram J (total_category D)}
  {L : LimCone (mapdiagram (pr1_category D) F)}
  (CC : creates_limit F L)
  (Hunique : ∏ (d : D (lim L))
    (δ : ∏ j : vertex J, d -->[limOut L j] (pr2 (dob F j)))
    (H : forms_cone (c := (lim L ,, d)) F (λ j, (limOut L j ,, δ j))),
    (d ,, δ ,, H) = pr1 CC
  )
  : creates_limit_unique F L.
Proof.
  refine ((pr1 CC ,, _) ,, pr2 CC).
  exact (λ _, Hunique _ _ _).
Defined.

Definition creates_limit_unique_to_creates_limit
  {C : category}
  {D : disp_cat C}
  {J : graph}
  (F : diagram J (total_category D))
  (L : LimCone (mapdiagram (pr1_category D) F))
  : creates_limit_unique F L → creates_limit F L
  := λ CC, (pr11 CC ,, pr2 CC).

Definition creates_limit_disp_struct
  {C : category}
  {P H Hprop Hid Hcomp}
  (D := disp_struct C P H Hprop Hid Hcomp)
  {J : graph}
  {F : diagram J (total_category D)}
  (L : LimCone (mapdiagram (pr1_category D) F))
  (d : D (lim L))
  (cone : ∏ j : vertex J, d -->[limOut L j] (pr2 (dob F j)))
  (is_limit : ∏ (d' : total_category D)
    (cone_out : ∏ u, d' --> (dob F u))
    (is_cone : ∏ u v e, cone_out u · (dmor F e) = cone_out v)
    (L_lim_arrow := limArrow L _ (make_cone
      (d := (mapdiagram (pr1_category D) F)) _
      (λ u v e, maponpaths pr1 (is_cone u v e)))),
    pr2 d' -->[L_lim_arrow] d)
  : creates_limit F L.
Proof.
  use (make_creates_limit d cone _ (λ d' cone', (_ ,, _) ,, _)).
  - abstract (
      do 3 intro;
      apply (subtypePairEquality (λ _, Hprop _ _ _ _ _));
      apply (limOutCommutes L)
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

Definition creates_limit_unique_disp_struct
  {C : category}
  {P H Hprop Hid Hcomp}
  (D := disp_struct C P H Hprop Hid Hcomp)
  {J : graph}
  {F : diagram J (total_category D)}
  {L : LimCone (mapdiagram (pr1_category D) F)}
  (CC : creates_limit F L)
  (d_is_unique : ∏ d', (∏ j : vertex J, d' -->[limOut L j] (pr2 (dob F j))) → d' = pr11 CC)
  : creates_limit_unique F L.
Proof.
  use (make_creates_limit_unique CC).
  abstract (
    intros d δ H0;
    apply subtypePairEquality;
    [ intro;
      use (isaprop_total2 (_ ,, _) (λ _, _ ,, _));
        repeat (apply impred_isaprop; intro);
      [ apply Hprop
      | apply (homset_property (total_category _)) ]
    | exact (d_is_unique _ δ) ]
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
  (d : P (lim L))
  : creates_limit F L.
Proof.
  use (make_creates_limit (d : (D _)) _ _ (λ d' cone', (_ ,, _) ,, _)).
  - abstract exact (λ _, tt).
  - abstract (
      do 3 intro;
      apply subtypePairEquality';
      [ apply (limOutCommutes L)
      | apply isapropunit ]
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

Definition creates_limit_unique_disp_full_sub
  {C : category}
  {P : C → UU}
  (D := disp_full_sub C P)
  (H : ∏ c, isaprop (P c))
  {J : graph}
  {F : diagram J (total_category D)}
  (L : LimCone (mapdiagram (pr1_category D) F))
  (CC : creates_limit F L)
  : creates_limit_unique F L.
Proof.
  use (make_creates_limit_unique CC).
  abstract (
    do 3 intro;
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
Defined.

Definition creates_limits {C : category} (D : disp_cat C) : UU := ∏
  (J : graph)
  (F : diagram J (total_category D))
  (L : LimCone (mapdiagram (pr1_category D) F) ),
  creates_limit F L.

Definition creates_limits_unique {C : category} (D : disp_cat C) : UU := ∏
  (J : graph)
  (F : diagram J (total_category D))
  (L : LimCone (mapdiagram (pr1_category D) F) ),
  creates_limit_unique F L.

End Creates_Limits.

Definition total_limit
  {C : category}
  {D : disp_cat C}
  {J : graph}
  {F : diagram J (total_category D)}
  (L : LimCone (mapdiagram (pr1_category D) F))
  (H : creates_limit F L)
  : LimCone F
  := make_LimCone _ _ _ (pr2 H).

Definition total_limits
  {C : category}
  {D : disp_cat C}
  {J : graph}
  (H : creates_limits D)
  (X : Lims_of_shape J C)
  : Lims_of_shape J (total_category D)
  := λ d, total_limit (X _) (H _ _ _).

Section fiber.

  Context {C : category}.
  Context {D : disp_cat C}.
  Context (c : C).
  Context {J : graph}.

  Context {F : diagram J (fiber_category D c)}.
  Context (L : LimCone (constant_diagram J c)).
  Context (H : creates_limit _ ((L : LimCone
    (mapdiagram (fiber_to_total_functor D c ∙ pr1_category D) F)
  ) : LimCone (mapdiagram (pr1_category _) (mapdiagram _ F)))).

  Let Δ := limArrow L _ (constant_cone J c).
  Let L' := make_LimCone _ _ _ (pr2 H).

  Context (candidate : cartesian_lift (pr11 H) Δ).

  Definition fiber_lim
    : D[{c}]
    := pr1 candidate.

  Definition fiber_lim_out
    (u : vertex J)
    : D[{c}] ⟦ fiber_lim , dob F u ⟧
    := (transportf _ (limArrowCommutes _ _ _ _) (pr12 candidate ;; pr121 H u)).

  Lemma fiber_lim_out_commutes
    (u v : vertex J)
    (e : edge u v)
    : transportf _ (id_right _) (fiber_lim_out u ;; dmor F e) = fiber_lim_out v.
  Proof.
    unfold fiber_lim_out.
    rewrite mor_disp_transportf_postwhisker.
    apply transportf_transpose_right.
    refine (_ @ maponpaths _ (fiber_paths (pr221 H u v e))).
    rewrite mor_disp_transportf_prewhisker.
    simpl.
    rewrite assoc_disp.
    apply transportf_transpose_right.
    apply transportf_transpose_right.
    do 4 refine (transport_f_f _ _ _ _ @ _).
    apply transportf_set.
    apply homset_property.
  Qed.

  Section fiber_is_limit.

    Context (d': D[{c}]).
    Context (d'_cone: cone F d').

    Context (f := limArrow L' _ (mapcone (fiber_to_total_functor D c) _ d'_cone)).
    Context (fc := limArrowCommutes L' _ (mapcone (fiber_to_total_functor D c) _ d'_cone)).
    Context (fu := limArrowUnique L' _ (mapcone (fiber_to_total_functor D c) _ d'_cone)).

    Local Lemma f_over_delta : pr1 f = identity c · Δ.
    Proof.
      rewrite id_left.
      use limArrowUnique.
      intro u.
      exact (base_paths _ _ (fc u)).
    Qed.

    Context (g := pr22 candidate c (identity c) d' (transportf _ f_over_delta (pr2 f))).

    Definition fiber_limit_arrow
      : d' -->[identity c] fiber_lim
      := pr11 g.

    Lemma fiber_limit_arrow_commutes
      : is_cone_mor d'_cone (fiber_lim_out,, fiber_lim_out_commutes) fiber_limit_arrow.
    Proof.
      unfold fiber_limit_arrow, fiber_lim_out.
      intro u.
      refine (_ @ (fiber_paths (fc u))).
      apply transportf_transpose_right.
      cbn.
      refine (_ @ maponpaths (λ x, x ;; (pr121 H u)) (transportb_transpose_left (pr21 g))).
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      apply transportf_transpose_right.
      cbn.
      rewrite mor_disp_transportf_prewhisker.
      rewrite assoc_disp.
      do 4 refine (transport_f_f _ _ _ _ @ _).
      apply transportf_set.
      apply homset_property.
    Qed.

    Lemma fiber_limit_arrow_unique
      (h : d' -->[ identity c] fiber_lim)
      (h_commutes : is_cone_mor d'_cone (fiber_lim_out,, fiber_lim_out_commutes) h)
      : (h ,, h_commutes) = fiber_limit_arrow,, fiber_limit_arrow_commutes.
    Proof.
      use subtypePairEquality.
      - intro.
        apply impred_isaprop.
        intro.
        apply (homset_property (fiber_category _ _)).
      - refine (base_paths _ _ (pr2 g (_ ,, _))).
        use (!fiber_paths (!fu ((identity c · Δ) ,, (h ;; pr12 candidate)) _) @ _).
        + intro u.
          use total2_paths_f.
          * simpl.
            rewrite id_left.
            apply (limArrowCommutes L).
          * abstract (
              refine (_ @ (h_commutes u));
              cbn;
              apply transportf_transpose_right;
              refine (_ @ !mor_disp_transportf_prewhisker _ _ _);
              apply transportf_transpose_right;
              refine (_ @ !assoc_disp _ _ _);
              apply transportf_transpose_right;
              do 3 refine (transport_f_f _ _ _ _ @ _);
              apply transportf_set;
              apply homset_property
            ).
        + apply transportf_transpose_right.
          refine (transport_f_f _ _ _ _ @ _).
          apply transportf_set.
          apply homset_property.
    Qed.

  End fiber_is_limit.

  Definition fiber_limit
    : LimCone F.
  Proof.
    use tpair.
    - use (fiber_lim ,, (fiber_lim_out ,, fiber_lim_out_commutes)).
    - intros d' d'_cone.
      exact ((
        _ ,,
        fiber_limit_arrow_commutes d' d'_cone) ,,
        (λ h, fiber_limit_arrow_unique d' d'_cone (pr1 h) (pr2 h))
      ).
  Defined.

End fiber.

Check fiber_limit.

Definition fiber_limits
  {C : category}
  {D : disp_cat C}
  (c : C)
  {J : graph}
  (H : creates_limits D)
  (L : Lims_of_shape J C)
  (cl : cleaving D)
  : Lims_of_shape J (D[{c}])
  := λ F, fiber_limit c
    (L _)
    (H _ _ _)
    (cl _ _ _ _).

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
