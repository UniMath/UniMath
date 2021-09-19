(**
  Definition of tensorial strength between actions over monoidal categories, as introduced
  under the name C-categories and C-functors (for C a monoidal category) by Bodo Pareigis (1977).

  The concrete definition is close to the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore (2008). Notably, the strength itself is not required to be an isomorphism.

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
Require Import UniMath.CategoryTheory.HorizontalComposition.
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

Definition actionbased_strength_pentagon_eq (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (v w : Mon_V),
  (χ' ((F a, v), w)) · ϛ (a, v ⊗ w) =
  (ϛ (a, v)) #⊙' (id w) · (ϛ (a ⊙ v, w)) · (#F (χ ((a, v), w))).

(** the original notion in Fiore's LICS'08 paper *)
Definition actionbased_strength_pentagon_eq_variant1 (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (v w : Mon_V),
  ϛ (a, v ⊗ w) =
  (nat_z_iso_to_trans_inv χ' ((F a, v), w)) · (ϛ (a, v)) #⊙' (id w) · (ϛ (a ⊙ v, w)) · (#F (χ ((a, v), w))).

(** the notion that fits with the definition of relative strength in the TYPES'15 post-proceedings paper by Ahrens and Matthes *)
Definition actionbased_strength_pentagon_eq_variant2 (ϛ : actionbased_strength_nat): UU := ∏ (a : A), ∏ (v w : Mon_V),
  ϛ (a, v ⊗ w) · (#F (nat_z_iso_to_trans_inv χ ((a, v), w))) =
  (nat_z_iso_to_trans_inv χ' ((F a, v), w)) · (ϛ (a, v)) #⊙' (id w) · (ϛ (a ⊙ v, w)).

(** as expected, the notions are logically equivalent *)
Lemma actionbased_strength_pentagon_eq_tovariant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq ϛ -> actionbased_strength_pentagon_eq_variant1 ϛ.
Proof.
  intros Heq a v w.
  red in Heq.
  apply pathsinv0.
  unfold nat_z_iso_to_trans_inv; cbn.
  unfold is_z_isomorphism_mor.
  do 2 rewrite <- assoc.
  apply (z_iso_inv_on_right _ _ _ (make_z_iso _ _ (pr2 χ' ((F a, v), w)))).
  apply pathsinv0.
  rewrite assoc.
  cbn.
  apply Heq.
Qed.

Lemma actionbased_strength_pentagon_eq_fromvariant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant1 ϛ -> actionbased_strength_pentagon_eq ϛ.
Proof.
  intros Heq a v w.
  red in Heq.
  unfold nat_z_iso_to_trans_inv in Heq; cbn in Heq.
  unfold is_z_isomorphism_mor in Heq.
  apply pathsinv0.
  apply (z_iso_inv_to_left _ _ _ (make_z_iso _ _ (pr2 χ' ((F a, v), w)))).
  cbn.
  apply pathsinv0.
  do 2 rewrite assoc.
  apply Heq.
Qed.

Lemma actionbased_strength_pentagon_eq_variant1variant2 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant1 ϛ -> actionbased_strength_pentagon_eq_variant2 ϛ.
Proof.
  intros Heq a v w.
  red in Heq.
  etrans.
  { unfold nat_z_iso_to_trans_inv.  cbn.
    apply maponpaths.
    apply pathsinv0.
    apply functor_on_inv_from_z_iso'.
  }
  apply pathsinv0.
  apply (z_iso_inv_on_left _ _ _ _ (make_z_iso (# F (χ ((a, v), w)))
         (is_z_isomorphism_mor (functor_on_is_z_isomorphism F (pr2 χ ((a, v), w))))
         (functor_on_is_z_isomorphism F (pr2 χ ((a, v), w))))).
  apply Heq.
Qed.

Lemma actionbased_strength_pentagon_eq_variant2variant1 (ϛ : actionbased_strength_nat): actionbased_strength_pentagon_eq_variant2 ϛ -> actionbased_strength_pentagon_eq_variant1 ϛ.
Proof.
  intros Heq a v w.
  red in Heq.
  apply pathsinv0.
  apply (z_iso_inv_to_right _ _ _ _ (make_z_iso (# F (χ ((a, v), w)))
         (is_z_isomorphism_mor (functor_on_is_z_isomorphism F (pr2 χ ((a, v), w))))
         (functor_on_is_z_isomorphism F (pr2 χ ((a, v), w))))).
  etrans.
  { apply pathsinv0.
    apply Heq. }
  clear Heq.
  apply maponpaths.
  apply pathsinv0.
  apply (functor_on_inv_from_z_iso' _ (pr2 χ ((a, v), w))).
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

Definition ab_strength_identity_functor {A : precategory} (actn : action Mon_V A) :
  actionbased_strength actn actn (functor_identity A).
Proof.
  use tpair.
  - use make_nat_trans.
    + intro av. apply identity.
    + intros av av' fg.
      cbn. rewrite id_left. apply id_right.
  - split.
    + intro a. cbn. apply id_left.
    + intros a v w. cbn. rewrite binprod_id. do 2 rewrite id_right.
      etrans.
      2: {apply cancel_postcomposition. apply pathsinv0, functor_id. }
      apply pathsinv0, id_left.
Defined.

Definition ab_strength_composition {A1 A2 A3 : precategory}
           {actn1 : action Mon_V A1} {actn2 : action Mon_V A2} {actn3 : action Mon_V A3}
           {F : A1 ⟶ A2} {F' : A2 ⟶ A3} :
  actionbased_strength actn1 actn2 F -> actionbased_strength actn2 actn3 F' ->
  actionbased_strength actn1 actn3 (F ∙ F').
Proof.
  intros ζ ζ'.
  use tpair.
  - use make_nat_trans.
    + intro av. induction av as [a v].
      exact (ζ' (F a,, v) · # F' (ζ (a,, v))).
    + intros av av' fg. induction av as [a v]. induction av' as [a' v']. induction fg as [f g].
      cbn.
      assert (ζisnatinst := nat_trans_ax ζ (a,, v) (a',, v') (f,, g)).
      assert (ζ'isnatinst := nat_trans_ax ζ' (F a,, v) (F a',, v') (# F f,, g)).
      rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        apply ζ'isnatinst. }
      do 2 rewrite <- assoc.
      apply maponpaths.
      cbn.
      do 2 rewrite <- functor_comp.
      apply maponpaths.
      apply ζisnatinst.
  - split.
    + intro a. cbn.
      assert (ζtriangleeqinst := ab_strength_triangle _ _ ζ a).
      assert (ζ'triangleeqinst := ab_strength_triangle _ _ ζ' (F a)).
      rewrite <- assoc.
      rewrite <- functor_comp.
      etrans.
      { do 2 apply maponpaths. exact ζtriangleeqinst. }
      exact ζ'triangleeqinst.
    + intros a v w. cbn.
      assert (ζpentagoneqinst := ab_strength_pentagon _ _ ζ a v w).
      assert (ζ'pentagoneqinst := ab_strength_pentagon _ _ ζ' (F a) v w).
      etrans.
      { rewrite assoc. apply cancel_postcomposition. exact ζ'pentagoneqinst. }
      clear ζ'pentagoneqinst.
      etrans.
      2: { rewrite <- (id_right (id w)).
           rewrite binprod_comp.
           do 2 apply cancel_postcomposition.
           apply pathsinv0, functor_comp. }
      repeat rewrite <- assoc.
      apply maponpaths.
      etrans.
      { apply maponpaths.
        apply pathsinv0.
        apply (functor_comp F' (χ actn2 ((F a, v), w)) (ζ (a,, v ⊗ w))).
      }
      etrans.
      { do 2 apply maponpaths. apply ζpentagoneqinst. }
      clear ζpentagoneqinst.
      etrans.
      { do 2 rewrite functor_comp. repeat rewrite assoc. apply idpath. }
      repeat rewrite assoc.
      do 2 apply cancel_postcomposition.
      assert (ζ'natinst := nat_trans_ax ζ' (act_odot actn2 (F a, v),, w)
                                        (F(act_odot actn1 (a, v)),, w)
                                        (ζ (a,, v),, id w)).
      cbn in ζ'natinst.
      etrans.
      2 : { apply pathsinv0, ζ'natinst. }
      apply idpath.
Defined.

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
  Let hsMon_EndA : has_homsets Mon_EndA := functor_category_has_homsets _ _ hsA.
  Let hsMon_EndA' : has_homsets Mon_EndA' := functor_category_has_homsets _ _ hsA'.

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
      ∏ v : ob (Mon_V), param_distributivity_dom v --> param_distributivity_codom v
      := pr1 δ.
    Coercion parameterized_distributivity_nat_funclass : parameterized_distributivity_nat >-> Funclass.

Section The_Laws.

    Context (δ : parameterized_distributivity_nat).

    Definition param_distr_triangle_eq : UU :=
      nat_trans_comp _ _ _ (pre_whisker F (lax_monoidal_functor_ϵ FA')) (δ I) =
      post_whisker (lax_monoidal_functor_ϵ FA) F.

    (** the type of the following def. is the same as that of [δ I], as seen from the definition that comes
        directly afterwards *)
    Definition param_distr_triangle_eq_variant0_RHS :=
      nat_trans_comp _ _ _ (pre_whisker F (strong_monoidal_functor_ϵ_inv FA'))
                                 (post_whisker (lax_monoidal_functor_ϵ FA) F).

    Definition param_distr_triangle_eq_variant0 : UU := δ I = param_distr_triangle_eq_variant0_RHS.

    Definition param_distr_triangle_eq_variant : UU :=
      nat_trans_comp _ _ _ (δ I) (post_whisker (strong_monoidal_functor_ϵ_inv FA) F)  =
      pre_whisker F (strong_monoidal_functor_ϵ_inv FA').

    Definition postwhisker_with_ϵ_z_iso : z_iso (functor_compose hsA hsA' (MonoidalFunctors.I_D Mon_EndA) F) (functor_compose hsA hsA' (FA I: functor A A) F).
    Proof.
      use tpair.
      - exact (post_whisker (lax_monoidal_functor_ϵ FA) F).
      - cbn.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        apply post_whisker_z_iso_is_z_iso.
        apply (nat_trafo_pointwise_z_iso_if_z_iso _ (lax_monoidal_functor_ϵ FA)).
        exact (strong_monoidal_functor_ϵ_is_z_iso FA).
    Defined.

    Definition postwhisker_with_ϵ_inv_z_iso : z_iso (functor_compose hsA hsA' (FA I: functor A A) F) (functor_composite (MonoidalFunctors.I_D Mon_EndA) F).
    Proof.
      use tpair.
      - exact (post_whisker (strong_monoidal_functor_ϵ_inv FA) F).
      - cbn.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        apply post_whisker_z_iso_is_z_iso.
        apply (nat_trafo_pointwise_z_iso_if_z_iso _ (pr1 (strong_monoidal_functor_ϵ_is_z_iso FA))).
        apply is_z_isomorphism_inv.
    Defined.

    Definition prewhisker_with_ϵ_inv_z_iso : z_iso (functor_compose hsA' hsA' F (FA' (MonoidalFunctors.I_C Mon_V))) (functor_composite F (MonoidalFunctors.I_D Mon_EndA')).
    Proof.
      use tpair.
      - exact (pre_whisker F (strong_monoidal_functor_ϵ_inv FA')).
      - cbn.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        apply pre_whisker_on_nat_z_iso.
        apply (nat_trafo_pointwise_z_iso_if_z_iso _ (pr1 (strong_monoidal_functor_ϵ_is_z_iso FA'))).
        apply is_z_isomorphism_inv.
    Defined.

    Lemma param_distr_triangle_eq_variant0_follows :
      param_distr_triangle_eq -> param_distr_triangle_eq_variant0.
    Proof.
      intro Hyp.
      red.
      change (δ I = prewhisker_with_ϵ_inv_z_iso · postwhisker_with_ϵ_z_iso).
      apply pathsinv0 in Hyp.
      apply (z_iso_inv_to_left _ _ _ prewhisker_with_ϵ_inv_z_iso).
      apply pathsinv0.
      cbn.
      apply nat_trans_eq; try exact hsA'.
      intro a.
      cbn.
      apply (maponpaths pr1) in Hyp.
      apply toforallpaths in Hyp.
      apply Hyp.
    Qed.

    Lemma param_distr_triangle_eq_variant0_implies :
      param_distr_triangle_eq_variant0 -> param_distr_triangle_eq.
    Proof.
      intro Hyp.
      red in Hyp.
      change (δ I = prewhisker_with_ϵ_inv_z_iso · postwhisker_with_ϵ_z_iso) in Hyp.
      apply (z_iso_inv_on_right _ _ _ prewhisker_with_ϵ_inv_z_iso) in Hyp.
      red.
      apply nat_trans_eq; try exact hsA'.
      intro a.
      cbn.
      apply (maponpaths pr1) in Hyp.
      apply toforallpaths in Hyp.
      apply Hyp.
    Qed.

    Lemma param_distr_triangle_eq_variant_follows :
      param_distr_triangle_eq -> param_distr_triangle_eq_variant.
    Proof.
      intro Hyp.
      red.
      apply (z_iso_inv_to_right _ _ _ _ postwhisker_with_ϵ_inv_z_iso).
      apply (z_iso_inv_to_left _ _ _ prewhisker_with_ϵ_inv_z_iso).
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
      apply (z_iso_inv_on_left _ _ _ _ postwhisker_with_ϵ_inv_z_iso) in Hyp.
      apply (z_iso_inv_on_right _ _ _ prewhisker_with_ϵ_inv_z_iso) in Hyp.
      red.
      apply nat_trans_eq; try exact hsA'.
      intro a.
      cbn.
      apply (maponpaths pr1) in Hyp.
      apply toforallpaths in Hyp.
      apply Hyp.
    Qed.


    Definition param_distr_pentagon_eq_body (v w : Mon_V) : UU :=
      nat_trans_comp _ _ _ (pre_whisker F (lax_monoidal_functor_μ FA' (v,,w))) (δ (v ⊗ w)) =
      nat_trans_comp _ _ _ (nat_trans_comp _ _ _ (post_whisker (δ v) (FA' w))
                                           (pre_whisker (FA v: functor A A) (δ w)))
                     (post_whisker (lax_monoidal_functor_μ FA (v,,w)) F).

    (** we also abstract over the constituent distributivities *)
    Definition param_distr_pentagon_eq_body_RHS_in_steps (v w : Mon_V)
               (dv: [A, A', hsA'] ⟦ param_distributivity_dom v, param_distributivity_codom v ⟧)
               (dw: [A, A', hsA'] ⟦ param_distributivity_dom w, param_distributivity_codom w ⟧) :
      [A, A', hsA']
        ⟦ functor_compose hsA' hsA' F (monoidal_functor_map_dom Mon_V Mon_EndA' FA' (v,, w)),
          functor_compose hsA hsA' (monoidal_functor_map_codom Mon_V Mon_EndA FA (v,, w)) F ⟧.
    Proof.
      set (aux1 := post_whisker dv (FA' w):
              [A, A', hsA']⟦functor_compose hsA' hsA' (param_distributivity_dom v) (FA' w),
                            functor_compose hsA' hsA' (param_distributivity_codom v) (FA' w)⟧).
      set (aux2 := pre_whisker (FA v: functor A A) dw:
          [A, A', hsA']⟦functor_compose hsA hsA' (FA v : A ⟶ A) (param_distributivity_dom w),
                        functor_compose hsA hsA' (FA v : A ⟶ A) (param_distributivity_codom w)⟧).
      set (aux3 := post_whisker (lax_monoidal_functor_μ FA (v,,w)) F:
      [A, A', hsA']⟦functor_compose hsA hsA' (monoidal_functor_map_dom Mon_V Mon_EndA FA (v,, w)) F,
                    functor_compose hsA hsA' (monoidal_functor_map_codom Mon_V Mon_EndA FA (v,, w)) F⟧).
      set (auxr := aux1 · aux2).
      exact (auxr · aux3).
    Defined.

    Definition param_distr_pentagon_eq_body_in_steps (v w : Mon_V) : UU.
    Proof.
      set (aux1 := pre_whisker F (lax_monoidal_functor_μ FA' (v,,w)):
           [A, A', hsA']⟦functor_compose hsA' hsA' F (monoidal_functor_map_dom Mon_V Mon_EndA' FA' (v,, w)),
                         functor_compose hsA' hsA' F (monoidal_functor_map_codom Mon_V Mon_EndA' FA' (v,, w))⟧).
      set (aux2 := δ (v ⊗ w)).
      exact (aux1 · aux2 = param_distr_pentagon_eq_body_RHS_in_steps v w (δ v) (δ w)).
    Defined.

    Goal param_distr_pentagon_eq_body = param_distr_pentagon_eq_body_in_steps.
    Proof.
       apply idpath.
    Qed.

    Definition param_distr_pentagon_eq : UU := ∏ (v w : Mon_V), param_distr_pentagon_eq_body v w.


    Definition param_distr_pentagon_eq_body_variant_RHS (v w : Mon_V)
               (dv: [A, A', hsA'] ⟦ param_distributivity_dom v, param_distributivity_codom v ⟧)
               (dw: [A, A', hsA'] ⟦ param_distributivity_dom w, param_distributivity_codom w ⟧) :
      [A, A', hsA'] ⟦ param_distributivity_dom (v ⊗ w), param_distributivity_codom (v ⊗ w) ⟧ :=
      nat_trans_comp _ _ _ (pre_whisker F (strong_monoidal_functor_μ_inv FA' (v,,w)))
                           (nat_trans_comp _ _ _ (nat_trans_comp _ _ _ (post_whisker dv (FA' w))
                                   (pre_whisker (FA v: functor A A) dw))
                                           (post_whisker (lax_monoidal_functor_μ FA (v,,w)) F)).

    Definition param_distr_pentagon_eq_body_variant_RHS_in_steps (v w : Mon_V)
               (dv: [A, A', hsA'] ⟦ param_distributivity_dom v, param_distributivity_codom v ⟧)
               (dw: [A, A', hsA'] ⟦ param_distributivity_dom w, param_distributivity_codom w ⟧) :
      [A, A', hsA'] ⟦ param_distributivity_dom (v ⊗ w), param_distributivity_codom (v ⊗ w) ⟧.
    Proof.
      set (aux1inv := pre_whisker F (strong_monoidal_functor_μ_inv FA' (v,,w)):
           [A, A', hsA']⟦functor_compose hsA' hsA' F (monoidal_functor_map_codom Mon_V Mon_EndA' FA' (v,, w)),
                         functor_compose hsA' hsA' F (monoidal_functor_map_dom Mon_V Mon_EndA' FA' (v,, w))⟧).
      exact (aux1inv · (param_distr_pentagon_eq_body_RHS_in_steps v w dv dw)).
    Defined.

    Goal param_distr_pentagon_eq_body_variant_RHS = param_distr_pentagon_eq_body_variant_RHS_in_steps.
    Proof.
      apply idpath.
    Qed.

    Definition param_distr_pentagon_eq_body_variant (v w : Mon_V): UU :=
      δ (v ⊗ w) = param_distr_pentagon_eq_body_variant_RHS v w (δ v) (δ w).

    Definition prewhisker_with_μ_inv_z_iso (v w : Mon_V):
      z_iso (functor_compose hsA' hsA' F (monoidal_functor_map_codom Mon_V Mon_EndA' FA' (v,, w)))
            (functor_compose hsA' hsA' F (monoidal_functor_map_dom Mon_V Mon_EndA' FA' (v,, w))).
    Proof.
      use tpair.
      - exact (pre_whisker F (strong_monoidal_functor_μ_inv FA' (v,,w))).
      - cbn.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        apply pre_whisker_on_nat_z_iso.
        apply (nat_trafo_pointwise_z_iso_if_z_iso _ (pr1 (strong_monoidal_functor_μ_is_nat_z_iso FA' (v,,w)))).
        apply is_z_isomorphism_inv.
    Defined.

    Lemma param_distr_pentagon_eq_body_variant_follows (v w : Mon_V):
      param_distr_pentagon_eq_body v w -> param_distr_pentagon_eq_body_variant v w.
    Proof.
      intro Hyp.
      red.
      change param_distr_pentagon_eq_body_variant_RHS with param_distr_pentagon_eq_body_variant_RHS_in_steps.
      unfold param_distr_pentagon_eq_body_variant_RHS_in_steps.
      apply (z_iso_inv_to_left _ _ _ (prewhisker_with_μ_inv_z_iso v w)).
      red in Hyp.
      apply nat_trans_eq; try exact hsA'.
      intro a.
      cbn.
      apply (maponpaths pr1) in Hyp.
      apply toforallpaths in Hyp.
      apply Hyp.
    Qed.

    Lemma param_distr_pentagon_eq_body_variant_implies (v w : Mon_V):
      param_distr_pentagon_eq_body_variant v w -> param_distr_pentagon_eq_body v w.
    Proof.
      intro Hyp.
      red in Hyp.
      change param_distr_pentagon_eq_body_variant_RHS with param_distr_pentagon_eq_body_variant_RHS_in_steps in Hyp.
      unfold param_distr_pentagon_eq_body_variant_RHS_in_steps in Hyp.
      apply (z_iso_inv_on_right _ _ _ (prewhisker_with_μ_inv_z_iso v w)) in Hyp.
      red.
      apply nat_trans_eq; try exact hsA'.
      intro a.
      cbn.
      apply (maponpaths pr1) in Hyp.
      apply toforallpaths in Hyp.
      apply Hyp.
    Qed.


    Lemma isaprop_param_distr_triangle_eq : isaprop param_distr_triangle_eq.
    Proof.
      apply (functor_category_has_homsets _ _ hsA').
    Qed.

    Lemma isaprop_param_distr_pentagon_eq : isaprop param_distr_pentagon_eq.
    Proof.
      red.
      apply impred; intros v.
      apply impred; intros w.
      apply isaset_nat_trans; exact hsA'.
    Qed.

End The_Laws.

   Definition parameterized_distributivity : UU := ∑ (δ : parameterized_distributivity_nat),
     (param_distr_triangle_eq δ) × (param_distr_pentagon_eq δ).

   Lemma parameterized_distributivity_eq (sδ sδ': parameterized_distributivity) :
     pr1 sδ = pr1 sδ' -> sδ = sδ'.
   Proof.
     intro Heq.
     apply subtypePath; trivial.
     intro δ. apply isapropdirprod.
     - apply isaprop_param_distr_triangle_eq.
     - apply isaprop_param_distr_pentagon_eq.
   Qed.

Definition parameterized_distributivity_to_nat (sδ : parameterized_distributivity) :
  parameterized_distributivity_nat
  := pr1 sδ.
Coercion parameterized_distributivity_to_nat : parameterized_distributivity >-> parameterized_distributivity_nat.

Identity Coercion parameterized_distributivity_nat_to_nat_trans : parameterized_distributivity_nat >-> nat_trans.


   Context (sδ : parameterized_distributivity).

   Let δ_triangle_eq := pr1 (pr2 sδ).
   Let δ_pentagon_eq := pr2 (pr2 sδ).
   Let actionA := action_from_alt Mon_V A hsA FA.
   Let actionA' := action_from_alt Mon_V A' hsA' FA'.

   Definition strength_nat_from_alt_aux_dom :
     actionbased_strength_dom actionA' F ⟹ uncurry_functor hsA' param_distributivity_dom.
   Proof.
     use make_nat_trans.
     - intro av.
       apply identity.
     - intros av av' fg.
       cbn.
       rewrite id_left, id_right.
       apply idpath.
   Defined.

   Definition strength_nat_from_alt_aux_codom :
     uncurry_functor hsA' param_distributivity_codom ⟹ actionbased_strength_codom actionA F.
   Proof.
     use make_nat_trans.
     - intro av.
       apply identity.
     - intros av av' fg.
       cbn.
       rewrite id_left, id_right.
       apply pathsinv0.
       apply functor_comp.
   Defined.

   Definition strength_nat_from_alt : actionbased_strength_nat actionA actionA' F.
   Proof.
     red.
     refine (nat_trans_comp _ _ _ strength_nat_from_alt_aux_dom _).
     refine (nat_trans_comp _ _ _ _ strength_nat_from_alt_aux_codom).
     exact (uncurry_nattrans hsA' sδ).
   Defined.

   Lemma triangle_eq_from_alt : actionbased_strength_triangle_eq actionA actionA' F strength_nat_from_alt.
   Proof.
     red.
     intro a.
     apply param_distr_triangle_eq_variant_follows in δ_triangle_eq.
     red in δ_triangle_eq.
     apply (maponpaths pr1) in δ_triangle_eq.
     apply toforallpaths in δ_triangle_eq.
     assert (δ_triangle_eq_inst := δ_triangle_eq a).
     clear δ_triangle_eq δ_pentagon_eq.
     cbn in δ_triangle_eq_inst.
     unfold strength_nat_from_alt, actionA, actionA'.
     cbn.
     do 3 rewrite id_left.
     rewrite id_right.
     exact δ_triangle_eq_inst.
   Qed.

   Lemma pentagon_eq_from_alt : actionbased_strength_pentagon_eq actionA actionA' F strength_nat_from_alt.
   Proof.
     red.
     intros a v w.
     clear δ_triangle_eq.
     assert (Hyp := δ_pentagon_eq v w).
     red in Hyp.
     apply (maponpaths pr1) in Hyp.
     apply toforallpaths in Hyp.
     assert (Hypinst := Hyp a).
     clear Hyp.
     cbn in Hypinst.
     unfold strength_nat_from_alt, actionA, actionA'.
     cbn.
     do 5 rewrite id_left.
     do 5 rewrite id_right.
     assert (aux := functor_id FA' w).
     apply (maponpaths pr1) in aux.
     apply toforallpaths in aux.
     rewrite aux.
     rewrite id_right.
     exact Hypinst.
   Qed.

   Definition actionbased_strong_functor_from_alt : actionbased_strong_functor actionA actionA'.
   Proof.
     exists F. exists strength_nat_from_alt.
     split.
     - exact triangle_eq_from_alt.
     - exact pentagon_eq_from_alt.
   Defined.

End Param_Distr.

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
