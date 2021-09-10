(**
  Definition of tensorial strengths between actions over monoidal categories.

  Based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore.

  To distinguish this from less general approaches, we will speak of action-based strength.

  Added by Ralph Matthes in 2021: relative strength of Ahrens and Matthes defined and shown to be an instance of action-based strength, another general definition in the spirit of Janelidze and Kelly
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Actions.

Local Open Scope cat.

Section A.

Context (Mon_V : monoidal_precat).

Local Definition I := monoidal_precat_unit Mon_V.
Local Definition tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).

Section ActionBasedStrengths_Definition.

Context {A A': precategory}.
Context (actn : action Mon_V A)(actn' : action Mon_V A').

Local Definition ϱ := act_ϱ actn.
Local Definition χ := act_χ actn.
Local Definition ϱ' := act_ϱ actn'.
Local Definition χ' := act_χ actn'.

Section ActionBasedStrengths_Natural_Transformation.

Context (F : A ⟶ A').

Notation "X ⊙ Y" := (act_odot actn (X , Y)) (at level 31).
Notation "f #⊙ g" := (#(act_odot actn) (f #, g)) (at level 31).
Notation "X ⊙' Y" := (act_odot actn' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#(act_odot actn') (f #, g)) (at level 31).

Definition actionbased_strength_dom : A ⊠ Mon_V ⟶ A' :=
  functor_composite (pair_functor F (functor_identity _)) (act_odot actn').

Lemma actionbased_strength_dom_ok: functor_on_objects actionbased_strength_dom = λ ax, F (ob1 ax) ⊙' (ob2 ax).
Proof.
  apply idpath.
Qed.

Definition actionbased_strength_codom : A ⊠ Mon_V ⟶ A' :=
  functor_composite (act_odot actn) F.

Lemma actionbased_strength_codom_ok: functor_on_objects actionbased_strength_codom = λ ax, F (ob1 ax ⊙ ob2 ax).
Proof.
  apply idpath.
Qed.

Definition actionbased_strength_nat : UU := nat_trans actionbased_strength_dom actionbased_strength_codom.

Definition actionbased_strength_nat_funclass (ϛ : actionbased_strength_nat):
  ∏ x : ob (A ⊠ Mon_V), actionbased_strength_dom x --> actionbased_strength_codom x
  := pr1 ϛ.
Coercion actionbased_strength_nat_funclass : actionbased_strength_nat >-> Funclass.

Definition actionbased_strength_triangle_eq (ϛ : actionbased_strength_nat) :=
  ∏ (a : A), (ϛ (a, I)) · (#F (ϱ a)) = ϱ' (F a).

Definition actionbased_strength_pentagon_eq (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (x y : Mon_V),
  (χ' ((F a, x), y)) · ϛ (a, x ⊗ y) =
  (ϛ (a, x)) #⊙' (id y) · (ϛ (a ⊙ x, y)) · (#F (χ ((a, x), y))).

(** the original notion in Fiore's LICS'08 paper *)
Definition actionbased_strength_pentagon_eq_variant1 (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (x y : Mon_V),
  ϛ (a, x ⊗ y) =
  (nat_z_iso_to_trans_inv χ' ((F a, x), y)) · (ϛ (a, x)) #⊙' (id y) · (ϛ (a ⊙ x, y)) · (#F (χ ((a, x), y))).

(** the notion that fits with the definition of relative strength in the TYPES'15 post-proceedings paper by Ahrens and Matthes *)
Definition actionbased_strength_pentagon_eq_variant2 (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (x y : Mon_V),
  ϛ (a, x ⊗ y) · (#F (nat_z_iso_to_trans_inv χ ((a, x), y))) =
  (nat_z_iso_to_trans_inv χ' ((F a, x), y)) · (ϛ (a, x)) #⊙' (id y) · (ϛ (a ⊙ x, y)).

(** as expected, the notions are logically equivalent *)
Lemma actionbased_strength_pentagon_eq_tovariant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq ϛ -> actionbased_strength_pentagon_eq_variant1 ϛ.
Proof.
  intros Heq a x y.
  red in Heq.
  apply pathsinv0.
  unfold nat_z_iso_to_trans_inv; cbn.
  unfold is_z_isomorphism_mor.
  do 2 rewrite <- assoc.
  apply (z_iso_inv_on_right _ _ _ (make_z_iso _ _ (pr2 χ' ((F a, x), y)))).
  apply pathsinv0.
  rewrite assoc.
  cbn.
  apply Heq.
Qed.

Lemma actionbased_strength_pentagon_eq_fromvariant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant1 ϛ -> actionbased_strength_pentagon_eq ϛ.
Proof.
  intros Heq a x y.
  red in Heq.
  unfold nat_z_iso_to_trans_inv in Heq; cbn in Heq.
  unfold is_z_isomorphism_mor in Heq.
  apply pathsinv0.
  apply (z_iso_inv_to_left _ _ _ (make_z_iso _ _ (pr2 χ' ((F a, x), y)))).
  cbn.
  apply pathsinv0.
  do 2 rewrite assoc.
  apply Heq.
Qed.

Lemma actionbased_strength_pentagon_eq_variant1variant2 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant1 ϛ -> actionbased_strength_pentagon_eq_variant2 ϛ.
Proof.
  intros Heq a x y.
  red in Heq.
  etrans.
  { unfold nat_z_iso_to_trans_inv.  cbn.
    apply maponpaths.
    apply pathsinv0.
    apply functor_on_inv_from_z_iso'.
  }
  apply pathsinv0.
  apply (z_iso_inv_on_left _ _ _ _ (make_z_iso (# F (χ ((a, x), y)))
         (is_z_isomorphism_mor (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))
         (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))).
  apply Heq.
Qed.

Lemma actionbased_strength_pentagon_eq_variant2variant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant2 ϛ -> actionbased_strength_pentagon_eq_variant1 ϛ.
Proof.
  intros Heq a x y.
  red in Heq.
  apply pathsinv0.
  apply (z_iso_inv_to_right _ _ _ _ (make_z_iso (# F (χ ((a, x), y)))
         (is_z_isomorphism_mor (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))
         (functor_on_is_z_isomorphism F (pr2 χ ((a, x), y))))).
  etrans.
  { apply pathsinv0.
    apply Heq. }
  clear Heq.
  apply maponpaths.
  apply pathsinv0.
  apply (functor_on_inv_from_z_iso' _ (pr2 χ ((a, x), y))).
Qed.

Lemma isaprop_actionbased_strength_triangle_eq (ϛ : actionbased_strength_nat) (hsA' : has_homsets A') : isaprop (actionbased_strength_triangle_eq ϛ).
Proof.
  apply impred; intros a.
  apply hsA'.
Qed.

Lemma isaprop_actionbased_strength_pentagon_eq (ϛ : actionbased_strength_nat) (hsA' : has_homsets A') : isaprop (actionbased_strength_pentagon_eq ϛ).
Proof.
  apply impred; intros a.
  apply impred; intros v.
  apply impred; intros w.
  apply hsA'.
Qed.

End ActionBasedStrengths_Natural_Transformation.

Definition actionbased_strength (F : A ⟶ A') : UU := ∑ (ϛ : actionbased_strength_nat F),
   (actionbased_strength_triangle_eq F ϛ) × (actionbased_strength_pentagon_eq F ϛ).

Lemma actionbased_strength_eq (hsA' : has_homsets A') {F : A ⟶ A'} (sη sη': actionbased_strength F) :
  pr1 sη = pr1 sη' -> sη = sη'.
Proof.
  intro Heq.
  apply subtypePath; trivial.
  intro ϛ. apply isapropdirprod.
  + apply isaprop_actionbased_strength_triangle_eq, hsA'.
  + apply isaprop_actionbased_strength_pentagon_eq, hsA'.
Qed.

Definition actionbased_strength_to_nat {F : A ⟶ A'} (FF : actionbased_strength F) :
  actionbased_strength_nat F
  := pr1 FF.
Coercion actionbased_strength_to_nat : actionbased_strength >-> actionbased_strength_nat.

(*
Definition actionbased_strength_to_nat_trans {F : A ⟶ A'} (FF : actionbased_strength F) :
  nat_trans (actionbased_strength_dom F) (actionbased_strength_codom F)
  := pr1 FF.
Coercion actionbased_strength_to_nat_trans : actionbased_strength >-> nat_trans.
 *)
Identity Coercion actionbased_strength_nat_to_nat_trans : actionbased_strength_nat >-> nat_trans.

Definition ab_strength_triangle {F : A ⟶ A'} (FF : actionbased_strength F) :
  actionbased_strength_triangle_eq F FF
  := pr1 (pr2 FF).

Definition ab_strength_pentagon {F : A ⟶ A'} (FF : actionbased_strength F) :
  actionbased_strength_pentagon_eq F FF
  := pr2 (pr2 FF).

End ActionBasedStrengths_Definition.

Definition actionbased_strong_functor {A A' : precategory} (actn : action Mon_V A)(actn' : action Mon_V A') : UU
  := ∑ (F : A ⟶ A'), actionbased_strength actn actn' F.

Definition actionbased_strong_functor_to_functor (A A' : precategory) (actn : action Mon_V A)(actn' : action Mon_V A') (FF : actionbased_strong_functor actn actn') : A ⟶ A' := pr1 FF.
Coercion actionbased_strong_functor_to_functor : actionbased_strong_functor >-> functor.

Definition ab_strong_functor_strength {A A' : precategory} (actn : action Mon_V A)(actn' : action Mon_V A')
           (FF : actionbased_strong_functor actn actn') : actionbased_strength_nat actn actn' FF
  := pr1 (pr2 FF).

(*
  The standard tensorial strength:
  F(A) ⊗ B --> F(A ⊗ B)
*)
Definition tensorial_strength : Mon_V ⟶ Mon_V → UU := actionbased_strength (tensorial_action Mon_V) (tensorial_action Mon_V).

Section Alternative_Definition.
(** we continue in the spirit of the definition of actions given by Janelidze and Kelly, however we are not aware
    of this definition in the literature *)

  Context {A A' : precategory} (hsA: has_homsets A) (hsA' : has_homsets A').

  Let Mon_EndA : monoidal_precat := monoidal_precat_of_endofunctors hsA.
  Let Mon_EndA' : monoidal_precat := monoidal_precat_of_endofunctors hsA'.

  Context (FA: strong_monoidal_functor Mon_V Mon_EndA).
  Context (FA': strong_monoidal_functor Mon_V Mon_EndA').

Section Param_Distr.

  Context (F : functor A A').

  (** a parameterized form of distributivity as strength *)
  Definition param_distributivity_dom : functor Mon_V [A, A', hsA'].
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro v. exact (functor_composite F (FA' v)).
      + intros v v' f.
        exact (pre_whisker F (# FA' f)).
    - split.
      + intro v.
        (* UniMath.MoreFoundations.Tactics.show_id_type. *)
        apply nat_trans_eq; try exact hsA'.
        intro a.
        cbn.
        assert (aux := functor_id FA' v).
        apply (maponpaths pr1) in aux.
        apply toforallpaths in aux.
        rewrite aux.
        apply idpath.
      + intros v1 v2 v3 f g.
        apply nat_trans_eq; try exact hsA'.
        intro a.
        cbn.
        assert (aux := functor_comp FA' f g).
        apply (maponpaths pr1) in aux.
        apply toforallpaths in aux.
        apply aux.
  Defined.

  Definition param_distributivity_codom : functor Mon_V [A, A', hsA'].
    Proof.
    use make_functor.
    - use make_functor_data.
      + intro v. exact (functor_composite (FA v) F).
      + intros v v' f.
        exact (post_whisker (# FA f) F).
    - split.
      + intro v.
        apply nat_trans_eq; try exact hsA'.
        intro a.
        cbn.
        assert (aux := functor_id FA v).
        apply (maponpaths pr1) in aux.
        apply toforallpaths in aux.
        rewrite aux.
        apply functor_id.
      + intros v1 v2 v3 f g.
        apply nat_trans_eq; try exact hsA'.
        intro a.
        cbn.
        assert (aux := functor_comp FA f g).
        apply (maponpaths pr1) in aux.
        apply toforallpaths in aux.
        rewrite aux.
        apply functor_comp.
    Defined.

    Definition parameterized_distributivity_nat : UU := param_distributivity_dom ⟹ param_distributivity_codom.

    Definition parameterized_distributivity_nat_funclass (δ : parameterized_distributivity_nat):
      ∏ x : ob (Mon_V), param_distributivity_dom x --> param_distributivity_codom x
      := pr1 δ.
    Coercion parameterized_distributivity_nat_funclass : parameterized_distributivity_nat >-> Funclass.

    Section The_Laws.

    Context (δ : parameterized_distributivity_nat).

    Definition param_distr_triangle_eq : UU :=
      nat_trans_comp _ _ _ (pre_whisker F (lax_monoidal_functor_ϵ FA')) (δ I) =
      post_whisker (lax_monoidal_functor_ϵ FA) F.

    Definition param_distr_triangle_eq_variant : UU :=
      nat_trans_comp _ _ _ (δ I) (post_whisker (strong_monoidal_functor_ϵ_inv FA) F)  =
      pre_whisker F (strong_monoidal_functor_ϵ_inv FA').


    Definition aux1_param_distr_triangle_eq_variant : z_iso (functor_compose hsA hsA' (FA I: functor A A) F)(functor_composite (MonoidalFunctors.I_D Mon_EndA) F).
    Proof.
      use tpair.
      - exact (post_whisker (strong_monoidal_functor_ϵ_inv FA) F).
      - cbn.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        apply post_whisker_z_iso_is_z_iso.
        apply (nat_trafo_pointwise_z_iso_if_z_iso _ _ _ _ _ (pr1 (strong_monoidal_functor_ϵ_is_z_iso FA))).
        apply is_z_isomorphism_inv.
    Defined.

    Definition aux2_param_distr_triangle_eq_variant : z_iso (functor_compose hsA' hsA' F (FA' (MonoidalFunctors.I_C Mon_V)))(functor_composite F (MonoidalFunctors.I_D Mon_EndA')).
    Proof.
      use tpair.
      - exact (pre_whisker F (strong_monoidal_functor_ϵ_inv FA')).
      - cbn.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        apply pre_whisker_on_nat_z_iso.
        apply (nat_trafo_pointwise_z_iso_if_z_iso _ _ _ _ _ (pr1 (strong_monoidal_functor_ϵ_is_z_iso FA'))).
        apply is_z_isomorphism_inv.
    Defined.

    Lemma param_distr_triangle_eq_variant_follows :
      param_distr_triangle_eq -> param_distr_triangle_eq_variant.
    Proof.
      intro Hyp.
      red.
      apply (z_iso_inv_to_right _ _ _ _ aux1_param_distr_triangle_eq_variant).
      apply (z_iso_inv_to_left _ _ _ aux2_param_distr_triangle_eq_variant).
      cbn.
      apply nat_trans_eq; try exact hsA'.
      intro a.
      cbn.
      red in Hyp.
      apply (maponpaths pr1) in Hyp.
      apply toforallpaths in Hyp.
      apply Hyp.
    Qed.

    Lemma param_distr_triangle_eq_variant_implies :
      param_distr_triangle_eq_variant -> param_distr_triangle_eq.
    Proof.
      intro Hyp.
      red in Hyp.
      apply pathsinv0 in Hyp.
      apply (z_iso_inv_on_left _ _ _ _ aux1_param_distr_triangle_eq_variant) in Hyp.
      apply (z_iso_inv_on_right _ _ _ aux2_param_distr_triangle_eq_variant) in Hyp.
      red.
      apply nat_trans_eq; try exact hsA'.
      intro a.
      cbn.
      apply (maponpaths pr1) in Hyp.
      apply toforallpaths in Hyp.
      apply Hyp.
    Qed.


    Definition param_distr_pentagon_eq_body (x y : Mon_V) : UU :=
      nat_trans_comp _ _ _ (pre_whisker F (lax_monoidal_functor_μ FA' (x,,y))) (δ (x ⊗ y)) =
      nat_trans_comp _ _ _ (nat_trans_comp _ _ _ (post_whisker (δ x) (FA' y))
                                           (pre_whisker (FA x: functor A A) (δ y)))
                     (post_whisker (lax_monoidal_functor_μ FA (x,,y)) F).

(*
      set (aux1 := pre_whisker F (lax_monoidal_functor_μ FA' (x,,y))).
      set (aux2 := δ (x ⊗ y)).
      set (auxl := nat_trans_comp _ _ _ aux1 aux2).
      set (aux3 := post_whisker (δ x) (FA' y)).
      set (aux4 := pre_whisker (FA x: functor A A) (δ y)).
      set (aux5 := post_whisker (lax_monoidal_functor_μ FA (x,,y)) F).
      set (auxr1 := nat_trans_comp _ _ _ aux3 aux4).
      set (auxr := nat_trans_comp _ _ _ auxr1 aux5).
*)

    Definition param_distr_pentagon_eq : UU := ∏ (x y : Mon_V), param_distr_pentagon_eq_body x y.

End The_Laws.
End Param_Distr.

   Definition parameterized_distributivity (F : A ⟶ A') : UU := ∑ (δ : parameterized_distributivity_nat F),
     (param_distr_triangle_eq F δ) × (param_distr_pentagon_eq F δ).



(* TODO: just continue *)


End Alternative_Definition.

End A.

Section B.
(** following the TYPES'15 post-proceedings paper by Ahrens and Matthes - will be identified as an instance of the previous *)

  Context {Mon_W Mon_V : monoidal_precat}.

  Local Definition timesV := monoidal_precat_tensor Mon_V.
  Local Definition lambda := monoidal_precat_left_unitor Mon_V.
  Local Definition alpha := monoidal_precat_associator Mon_V.

  Local Definition timesW := monoidal_precat_tensor Mon_W.

  Context (U : strong_monoidal_functor Mon_W Mon_V).

Section RelativeStrengths_Natural_Transformation.
  Context (F: Mon_V ⟶ Mon_V).

  Notation "X ⊗V Y" := (timesV (X , Y)) (at level 31).
  Notation "X •W Y" := (timesW (X , Y)) (at level 31).

  Notation "f #⊗V g" := (#timesV (f #, g)) (at level 31).
  Notation "f #•W g" := (#timesW (f #, g)) (at level 31).

  Definition rel_strength_dom : Mon_W ⊠ Mon_V ⟶ Mon_V :=
    functor_composite (pair_functor U F) timesV.

  Lemma rel_strength_dom_ok: functor_on_objects rel_strength_dom = λ ax, U (ob1 ax) ⊗V  F (ob2 ax).
  Proof.
    apply idpath.
  Qed.

  Definition rel_strength_codom : Mon_W ⊠ Mon_V ⟶ Mon_V :=
  functor_composite (functor_composite (pair_functor U (functor_identity _)) timesV) F.

  Lemma rel_strength_codom_ok: functor_on_objects rel_strength_codom = λ ax, F (U (ob1 ax) ⊗V ob2 ax).
  Proof.
    apply idpath.
  Qed.

  Definition rel_strength_nat : UU := nat_trans rel_strength_dom rel_strength_codom.

  Definition rel_strength_nat_funclass (ϛ : rel_strength_nat):
  ∏ x : ob (Mon_W ⊠ Mon_V), rel_strength_dom x --> rel_strength_codom x
  := pr1 ϛ.
  Coercion rel_strength_nat_funclass : rel_strength_nat >-> Funclass.

  (** the following looks like a pentagon but is of the nature of a triangle equation *)
  Definition rel_strength_pentagon_eq (ϛ : rel_strength_nat) :=
    ∏ (v : Mon_V), ϛ (monoidal_precat_unit Mon_W, v) · #F (strong_monoidal_functor_ϵ_inv U #⊗V identity v) · #F (lambda v)  =
               strong_monoidal_functor_ϵ_inv U #⊗V identity (F v) · lambda (F v).

  (** the following looks like a rectangle in the paper but is of the nature of a pentagon equation *)
  Definition rel_strength_rectangle_eq (ϛ : rel_strength_nat): UU := ∏ (w w' : Mon_W), ∏ (v : Mon_V),
  ϛ (w •W w', v) · #F (strong_monoidal_functor_μ_inv U (w, w') #⊗V identity v) · #F (alpha ((U w, U w'), v)) =
  strong_monoidal_functor_μ_inv U (w, w') #⊗V identity (F v) · alpha ((U w, U w'), F v) ·
                                        identity (U w) #⊗V ϛ (w', v) · ϛ (w, U w' ⊗V v).

End RelativeStrengths_Natural_Transformation.

Definition rel_strength (F : Mon_V ⟶ Mon_V): UU :=
  ∑ (ϛ : rel_strength_nat F), (rel_strength_pentagon_eq F ϛ) × (rel_strength_rectangle_eq F ϛ).


Definition rel_strength_to_rel_strength_nat {F : Mon_V ⟶ Mon_V} (str : rel_strength F) :
  rel_strength_nat F
  := pr1 str.
Coercion rel_strength_to_rel_strength_nat : rel_strength >-> rel_strength_nat.

(* Definition rel_strength_to_nat_trans {F : Mon_V ⟶ Mon_V} (str : rel_strength F) :
  nat_trans (rel_strength_dom F) (rel_strength_codom F)
  := pr1 str.
Coercion rel_strength_to_nat_trans : rel_strength >-> nat_trans. *)

Identity Coercion rel_strength_nat_to_nat_trans : rel_strength_nat >-> nat_trans.

Definition rel_strength_pentagon {F : Mon_V ⟶ Mon_V} (str : rel_strength F) :
  rel_strength_pentagon_eq F str
  := pr1 (pr2 str).

Definition rel_strength_rectangle {F : Mon_V ⟶ Mon_V} (str : rel_strength F) :
  rel_strength_rectangle_eq F str
  := pr2 (pr2 str).

Section RelativeStrength_Is_An_ActionBasedStrength.

  Context (F: Mon_V ⟶ Mon_V) (str: rel_strength F).

  Local Definition pentagon := rel_strength_pentagon str.
  Local Definition rectangle := rel_strength_rectangle str.

  Local Definition Mon_W' := swapping_of_monoidal_precat Mon_W.
  Local Definition timesW' := monoidal_precat_tensor Mon_W'.
  Local Definition Mon_V' := swapping_of_monoidal_precat Mon_V.
  Local Definition timesV' := monoidal_precat_tensor Mon_V'.

  Local Definition U' := swapping_of_strong_monoidal_functor U: strong_monoidal_functor Mon_W' Mon_V'.
  Local Definition phiinv' := pre_whisker binswap_pair_functor (strong_monoidal_functor_μ_inv U).

  Local Definition UAct := U_action Mon_W' U': action Mon_W' Mon_V'.

  Local Definition ϛ' := pre_whisker binswap_pair_functor str.

Definition actionbased_strength_from_relative_strength: actionbased_strength Mon_W' UAct UAct F.
Proof.
  exists ϛ'.
  split.
  - red.
    cbn.
    intro v.
    change (str (monoidal_precat_unit Mon_W, v) · # F (# timesV (strong_monoidal_functor_ϵ_inv U #, id v) · lambda v) =
            # timesV (strong_monoidal_functor_ϵ_inv U #, id F v) · lambda (F v)).
    rewrite <- pentagon.
    rewrite assoc'. rewrite functor_comp.
    apply idpath.
  - cbn.
    apply actionbased_strength_pentagon_eq_fromvariant1.
    apply actionbased_strength_pentagon_eq_variant2variant1.
    red.
    intros v w' w.
    unfold ϛ', Mon_W', Mon_V', U'.
    cbn.
    unfold is_z_isomorphism_mor, pre_whisker_on_nat_z_iso.
    cbn.
    assert (Hyp := rectangle w w' v).
    fold timesV.
    fold timesW.
    fold alpha.
    change (str (timesW (w, w'), v)
  · # F (# timesV (strong_monoidal_functor_μ_inv U (w, w') #, id v) · alpha ((U w, U w'), v)) =
  # timesV (strong_monoidal_functor_μ_inv U (w, w') #, id F v) · alpha ((U w, U w'), F v)
  · # timesV (# U (id w) #, str (w', v)) · str (w, timesV (U w', v))).
    rewrite functor_id.
    rewrite functor_comp.
    rewrite assoc.
    exact Hyp.
Defined.

End RelativeStrength_Is_An_ActionBasedStrength.

Section ActionBasedStrength_Instantiates_To_RelativeStrength.

  Context (F: Mon_V ⟶ Mon_V) (ab_str: actionbased_strength Mon_W' UAct UAct F).

  Local Definition θ' : rel_strength_nat F := pre_whisker binswap_pair_functor ab_str.

  Lemma relative_strength_from_actionbased_strength_laws : rel_strength_pentagon_eq F θ' × rel_strength_rectangle_eq F θ'.
  Proof.
    split.
    - red.
      cbn.
      intro v.
      assert (Hyp := ab_strength_triangle _ _ _ ab_str v).
      cbn in Hyp. fold timesV in Hyp.
      etrans.
      2: exact Hyp.
      clear Hyp.
      rewrite <- assoc.
      apply maponpaths.
      apply pathsinv0.
      apply functor_comp.
    - red. cbn. intros w w' v.
      assert (Hyp := actionbased_strength_pentagon_eq_variant1variant2 _ _ _ _ ab_str
                     (actionbased_strength_pentagon_eq_tovariant1 _ _ _ _ ab_str
                                              (ab_strength_pentagon _ _ _ ab_str)) v w' w).
      cbn in Hyp.
      unfold is_z_isomorphism_mor, pre_whisker_on_nat_z_iso in Hyp.
      cbn in Hyp.
      unfold is_z_isomorphism_mor.
      rewrite functor_id in Hyp.
      rewrite functor_comp in Hyp.
      rewrite assoc in Hyp.
      exact Hyp.
  Qed.

  Definition relative_strength_from_actionbased_strength: rel_strength F.
  Proof.
    exists θ'.
    exact relative_strength_from_actionbased_strength_laws.
  Defined.

End ActionBasedStrength_Instantiates_To_RelativeStrength.

End B.

Arguments ab_strength_triangle {_ _ _ _ _} _.
Arguments ab_strength_pentagon {_ _ _ _ _} _.
Arguments ab_strong_functor_strength {_ _ _ _} _.
