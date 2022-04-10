(** * HomotopicalCategory *)
(** ** Contents

  - Definitions:
    - two_of_six
    - two_of_three
    - homotopical_category
    - homotopical_functor
    - is_minimal (minimal homotopical category)

  - Properties:
    - two_of_six_is_prop
    - two_of_three_is_prop
    - is_homotopical_is_prop
    - is_homotopical_functor_is_prop
    - is_minimal_is_prop

  - Results:
    - [two_of_six_implies_two_of_three]
    - [cats_minimal_homotopical] (any category is a minimal homotopical category)

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

Open Scope cat.

Definition morph_class (C : category) := ∏ (x y : C), hsubtype (x --> y).

Definition category_with_weq := ∑ C : category, morph_class C.

Definition category_with_weq_pr1 (C : category_with_weq) : category := pr1 C.

Coercion category_with_weq_pr1 : category_with_weq >-> category.

Definition two_of_six {C : category} (W : morph_class C) :=
  ∏ {x y z t : C}
    {f  : x --> y}
    {g  : y --> z}
    {h  : z --> t}
    (gf : W x z (f · g))
    (hg  : W y t (g · h)),
    (W x y f)
      × (W y z g)
      × (W z t h)
      × (W x t (f · g · h)).

Proposition two_of_six_is_prop {C : category} (W : morph_class C) : isaprop (two_of_six W).
Proof.
  unfold two_of_six.
  repeat (apply impred ; intro).
  apply isofhleveltotal2. apply (W _ _ _).
  intro. apply isofhleveltotal2. apply (W _ _ _).
  intro. apply isofhleveltotal2. apply (W _ _ _).
  intro. apply (W _ _ _).
Defined.

Definition is_homotopical (C : category_with_weq) : UU := two_of_six (pr2 C).

Proposition is_homotopical_is_prop (C : category_with_weq) : isaprop (is_homotopical C).
Proof.
  apply two_of_six_is_prop.
Defined.

Definition homotopical_category : UU := ∑ (C : category_with_weq), is_homotopical C.

Definition homotopical_category_pr1 (C : homotopical_category) : category_with_weq := pr1 C.

Coercion homotopical_category_pr1 : homotopical_category >-> category_with_weq.

Definition category_with_weq_pr2 (C : category_with_weq) : morph_class (pr1 C) := pr2 C.

Definition is_homotopical_functor {C C' : homotopical_category} (F : functor C C') : UU :=
  ∏ (x y : C) (f : category_with_weq_pr2 C x y), category_with_weq_pr2 C' _ _ (# F (pr1 f)).

Proposition is_homotopical_functor_is_prop {C C' : homotopical_category} (F : functor C C') : isaprop (is_homotopical_functor F).
Proof.
  repeat (apply impred ; intro).
  apply (pr21 C').
Defined.

Definition homotopical_functor (C C' : homotopical_category) : UU := ∑ f : functor C C', is_homotopical_functor f.

Definition two_of_three {C : category} (W : morph_class C) :=
  ∏ {x y z : C}
    (f  : x --> y)
    (g  : y --> z),
  (W _ _ f × W _ _ g ->  W _ _ (f · g)) ×
  (W _ _ f × W _ _ (f · g) ->  W _ _ g) ×
  (W _ _ g × W _ _ (f · g) ->  W _ _ f).

Proposition two_of_three_is_prop {C : category} (W : morph_class C) : isaprop (two_of_three W).
Proof.
  unfold two_of_three.
  repeat (apply impred ; intro).
  apply isofhleveltotal2.
  - apply impred. intros. apply (W _ _ _).
  - intros. apply isofhleveltotal2. apply impred. intros. apply (W _ _ _).
    intros. apply impred. intros. apply (W _ _ _).
Defined.

Lemma two_of_six_implies_two_of_three {C : category} {W : morph_class C} (p : two_of_six W) : two_of_three W.
Proof.
  unfold two_of_three.
  intros.
  split.
  - intros.
    rewrite <- (id_right f) in X.
    rewrite <- (id_left g) in X.
    pose (p _ _ _ _ _ _ _ (pr1 X) (pr2 X)).
    rewrite id_right in d.
    apply (pr222 d).
  - split.
    intros.
    destruct X as [ X1 X2 ].
    rewrite <- (id_left f) in X1.
    pose (p _ _ _ _ _ _ _ X1 X2).
    apply (pr122 d).
    intros.
    destruct X as [ X1 X2 ].
    rewrite <- (id_right g) in X1.
    pose (p _ _  _ _ _ _ _ X2 X1).
    apply (pr1 d).
Defined.

(* In the following we show categories are minimal homotopical categories. *)

Lemma left_inv_monic_is_right_inv {C : category} {x y : C} (f : x -->y) (f_is_monic : isMonic f) (g : y --> x) (is_left_inv : g · f = identity _) : f · g = identity _.
Proof.
  apply (maponpaths (fun k => f · k)) in is_left_inv.
  rewrite assoc in is_left_inv.
  rewrite id_right in is_left_inv.
  rewrite <- id_left in is_left_inv.
  apply f_is_monic in is_left_inv.
  apply is_left_inv.
Defined.

Lemma right_inv_epi_is_left_inv {C : category} {x y : C} (f : x --> y) (f_is_epic : isEpi f) (g : y --> x) (is_right_inv : f · g = identity _) : g · f = identity _.
Proof.
  apply (maponpaths (fun k => k · f)) in is_right_inv.
  rewrite id_left in is_right_inv.
  rewrite <- id_right in is_right_inv.
  rewrite <- assoc in is_right_inv.
  apply f_is_epic in is_right_inv.
  apply is_right_inv.
Defined.

Lemma iso_two_of_three_right {C : precategory} {x y z : C} {f : x --> y} {g : y --> z} (gf_is_iso : is_iso (f · g)) (f_is_iso : is_iso f) : is_iso g.
Proof.
  assert (g_right_inv : g · ((inv_from_iso (make_iso _ gf_is_iso)) · f)  = identity _).
  pose (iso_inv_after_iso (make_iso _ gf_is_iso)).
  apply (maponpaths (fun k => (inv_from_iso (make_iso _ f_is_iso)) · k · f)) in p.
  simpl in p.
  rewrite assoc in p.
  rewrite assoc in p.
  rewrite iso_after_iso_inv in p.
  rewrite id_left in p.
  rewrite id_right in p.
  rewrite iso_after_iso_inv in p.
  rewrite <- assoc in p.
  apply p.
  assert (g_left_inv : ((inv_from_iso (make_iso _ gf_is_iso)) · f) · g = identity _).
  rewrite <- assoc.
  apply (iso_after_iso_inv (make_iso _ gf_is_iso)).
  eapply (is_iso_qinv _ _).
  exists g_right_inv. apply g_left_inv.
Defined.

Lemma z_iso_two_of_three_right {C : category} {x y z : C} {f : x --> y} {g : y --> z} (gf_is_iso : is_z_isomorphism (f · g)) (f_is_iso : is_z_isomorphism f) : is_z_isomorphism g.
Proof.
  apply is_z_iso_from_is_iso.
  eapply iso_two_of_three_right.
  exact (is_iso_from_is_z_iso _ gf_is_iso).
  exact (is_iso_from_is_z_iso _ f_is_iso).
Defined.

Lemma iso_two_of_three_left {C : precategory} {x y z : C} {f : x --> y} {g : y --> z} (gf_is_iso : is_iso (f · g)) (g_is_iso : is_iso g) : is_iso f.
Proof.
  assert (f_right_inv : f · (g · (inv_from_iso (make_iso _ gf_is_iso)))  = identity _).
  rewrite assoc.
  apply (iso_inv_after_iso (make_iso _ gf_is_iso)).
  assert (f_left_inv : (g · (inv_from_iso (make_iso _ gf_is_iso))) · f = identity _).
  pose (iso_after_iso_inv (make_iso _ gf_is_iso)).
  apply (maponpaths (fun k => g · k · (inv_from_iso (make_iso _ g_is_iso)))) in p.
  simpl in p.
  rewrite <- assoc in p.
  rewrite <- assoc in p.
  rewrite <- assoc in p.
  rewrite id_right in p.
  pose (iso_inv_after_iso (make_iso _ g_is_iso)).
  simpl in p0.
  rewrite p0 in p.
  clear p0.
  rewrite id_right in p.
  rewrite  assoc in p.
  apply p.
  eapply (is_iso_qinv _ _).
  exists f_right_inv. apply f_left_inv.
Defined.

Lemma z_iso_two_of_three_left {C : category} {x y z : C} {f : x --> y} {g : y --> z} (gf_is_iso : is_z_isomorphism (f · g)) (g_is_iso : is_z_isomorphism g) : is_z_isomorphism f.
Proof.
  apply is_z_iso_from_is_iso.
  eapply iso_two_of_three_left.
  exact (is_iso_from_is_z_iso _ gf_is_iso).
  exact (is_iso_from_is_z_iso _ g_is_iso).
Defined.

Definition is_minimal (C : homotopical_category) : UU := ∏ {x y : C} (f : pr21 C x y), is_iso (pr1 f).

Proposition is_minimal_is_prop (C : homotopical_category) : isaprop (is_minimal C).
Proof.
  unfold is_minimal.
  apply impred ; intro.
  apply impred ; intro.
  apply impred ; intro.
  apply isaprop_is_iso.
Defined.

(* Any category is a minimal homotopical category taking the weak equivalences to be the isos *)
Lemma cats_minimal_homotopical (C : category) : homotopical_category.
Proof.
  unfold homotopical_category.
  pose (C_Weq := (C ,, (fun x y f => (is_z_isomorphism f ,, isaprop_is_z_isomorphism f))) : category_with_weq ).
  exists C_Weq.
  unfold is_homotopical.
  unfold two_of_six.
  intros.
  assert (g_is_iso : is_z_isomorphism g).
  {
    assert (g_is_monic : isMonic g).
    apply (isMonic_postcomp _ g h).
    simpl in hg.
    apply (is_iso_isMonic _ _ hg).
    assert (g_left_inv : ((is_z_isomorphism_mor gf) · f · g) = identity _).
    rewrite <- assoc.
    apply (z_iso_after_z_iso_inv (f · g ,, gf)).
    pose (g_right_inv := left_inv_monic_is_right_inv _ g_is_monic _ g_left_inv).
    eapply make_is_z_isomorphism.
    split.
    apply g_right_inv.
    apply g_left_inv.
  }
  pose (f_is_iso := z_iso_two_of_three_left gf g_is_iso).
  split. apply f_is_iso.
  split. apply g_is_iso.
  split. apply (z_iso_two_of_three_right hg g_is_iso).
  rewrite <- assoc.
  apply is_z_isomorphism_comp.
  apply f_is_iso.
  apply hg.
Defined.
