
(** **********************************************************

Anders Mörtberg, 2016

************************************************************)


(** **********************************************************

Contents:

- Definition of the functors given by binary product with
  a fixed object
- Definition of exponentials

Section [ExponentialsCarriedThroughAdjointEquivalence] added by Ralph Matthes in 2023

************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.binproducts.

(* for Section [ExponentialsCarriedThroughAdjointEquivalence] *)
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryEquality.
Require Import UniMath.CategoryTheory.Core.Univalence.

Local Open Scope cat.

Section exponentials.

Context {C : category} (PC : BinProducts C).

(* The functor "a * _" and "_ * a" *)
Definition constprod_functor1 (a : C) : functor C C :=
  BinProduct_of_functors C C PC (constant_functor C C a) (functor_identity C).

Definition constprod_functor2 (a : C) : functor C C :=
  BinProduct_of_functors C C PC (functor_identity C) (constant_functor C C a).

Definition is_exponentiable (a : C) : UU := is_left_adjoint (constprod_functor1 a).

Definition Exponentials : UU := ∏ (a : C), is_exponentiable a.
Definition hasExponentials : UU := ∏ (a : C), ∥ is_exponentiable a ∥.

Definition nat_trans_constprod_functor1 (a : C) :
  nat_trans (constprod_functor1 a) (constprod_functor2 a).
Proof.
use tpair.
- intro x; simpl; unfold BinProduct_of_functors_ob; simpl.
  apply BinProductArrow; [ apply BinProductPr2 | apply BinProductPr1 ].
- abstract (intros x y f; simpl; unfold BinProduct_of_functors_mor; simpl;
  eapply pathscomp0; [apply precompWithBinProductArrow|];
  apply pathsinv0; eapply pathscomp0; [apply postcompWithBinProductArrow|];
  now rewrite (BinProductOfArrowsPr2 C _ (PC a x)), (BinProductOfArrowsPr1 C _ (PC a x))).
Defined.

Definition nat_trans_constprod_functor2 (a : C) :
  nat_trans (constprod_functor2 a) (constprod_functor1 a).
Proof.
use tpair.
- intro x; simpl; unfold BinProduct_of_functors_ob; simpl.
  apply BinProductArrow; [ apply BinProductPr2 | apply BinProductPr1 ].
- abstract (intros x y f; simpl; unfold BinProduct_of_functors_mor; simpl;
  eapply pathscomp0; [apply precompWithBinProductArrow|];
  apply pathsinv0; eapply pathscomp0; [apply postcompWithBinProductArrow|];
  now rewrite (BinProductOfArrowsPr2 C _ (PC x a)), (BinProductOfArrowsPr1 C _ (PC x a))).
Defined.

Lemma is_z_iso_constprod_functor1 a :
  @is_z_isomorphism [C,C] _ _ (nat_trans_constprod_functor1 a).
Proof.
  exists (nat_trans_constprod_functor2 a).
  split.
  + abstract (
    apply (nat_trans_eq C); intro x; simpl; unfold BinProduct_of_functors_ob; simpl;
    eapply pathscomp0; [apply precompWithBinProductArrow|];
    now rewrite BinProductPr1Commutes, BinProductPr2Commutes, BinProductArrowEta, !id_left).
  + abstract (
    apply (nat_trans_eq C); intro x; simpl; unfold BinProduct_of_functors_ob; simpl;
    eapply pathscomp0; [apply precompWithBinProductArrow|];
    now rewrite BinProductPr1Commutes, BinProductPr2Commutes, BinProductArrowEta, !id_left).
Defined.

(* This is not used *)
Lemma is_z_iso_constprod_functor2 a :
  @is_z_isomorphism [C,C] _ _ (nat_trans_constprod_functor2 a).
Proof.
  exists (nat_trans_constprod_functor1 a).
  split.
  + abstract (
        apply (nat_trans_eq C); intro x; simpl; unfold BinProduct_of_functors_ob; simpl;
        eapply pathscomp0; [apply precompWithBinProductArrow|];
        now rewrite BinProductPr1Commutes, BinProductPr2Commutes, BinProductArrowEta, !id_left).
  + abstract (
        apply (nat_trans_eq C); intro x; simpl; unfold BinProduct_of_functors_ob; simpl;
        eapply pathscomp0; [apply precompWithBinProductArrow|];
        now rewrite BinProductPr1Commutes, BinProductPr2Commutes, BinProductArrowEta, !id_left).
Defined.

Definition flip_z_iso a : @z_iso [C,C] (constprod_functor1 a) (constprod_functor2 a) :=
  tpair _ _ (is_z_iso_constprod_functor1 a).

Variable (a : C).
Variable (HF : is_left_adjoint (constprod_functor1 a)).

Local Notation F := (constprod_functor1 a).
Local Notation F' := (constprod_functor2 a).
Let G := right_adjoint HF.
Let H := pr2 HF : are_adjoints F G.
Let eta : [C,C]⟦functor_identity C,functor_composite F G⟧ := unit_from_left_adjoint H.
Let eps : [C,C]⟦functor_composite G F,functor_identity C⟧ := counit_from_left_adjoint H.
Let H1 := triangle_id_left_ad H.
Let H2 := triangle_id_right_ad H.

Arguments constprod_functor1 : simpl never.
Arguments constprod_functor2 : simpl never.
Arguments flip_z_iso : simpl never.

Local Definition eta' : [C,C]⟦functor_identity C,functor_composite F' G⟧ :=
  let G' := (post_composition_functor C C C G)
  in eta · (# G' (flip_z_iso a)).

Local Definition eps' : [C,C]⟦functor_composite G F',functor_identity C⟧ :=
  let G' := (pre_composition_functor C C C G)
  in # G' (inv_from_z_iso (flip_z_iso a)) · eps.

Local Lemma form_adjunction_eta'_eps' : form_adjunction F' G eta' eps'.
Proof.
fold eta in H1; fold eps in H1; fold eta in H2; fold eps in H2; fold G in H2.
use tpair.
+ intro x; unfold eta', eps'; cbn.
  rewrite assoc.
  eapply pathscomp0.
  - eapply cancel_postcomposition.
    exact (nat_trans_ax (inv_from_z_iso (flip_z_iso _)) _ _ _).
  - rewrite functor_comp, assoc.
    eapply pathscomp0; [rewrite <- assoc; apply maponpaths, (nat_trans_ax eps)|].
    rewrite <- assoc.
    eapply pathscomp0; [apply maponpaths; rewrite assoc; apply cancel_postcomposition, H1|].
    rewrite id_left.
    apply (nat_trans_eq_pointwise (z_iso_after_z_iso_inv (flip_z_iso a)) x).
+ intro x; cbn.
  rewrite <- (H2 x), <- assoc, <- (functor_comp G).
  apply maponpaths, maponpaths.
  rewrite assoc.
  apply remove_id_left; try apply idpath.
  apply (nat_trans_eq_pointwise (z_iso_inv_after_z_iso (flip_z_iso a))).
Qed.

Lemma is_left_adjoint_constprod_functor2 : is_left_adjoint F'.
Proof.
apply (tpair _ G).
apply (tpair _ (make_dirprod eta' eps')).
apply form_adjunction_eta'_eps'.
Defined.

End exponentials.

Section ExponentialsCarriedThroughAdjointEquivalence.

  Context {C : category} (PC : BinProducts C) {D : category} (PD : BinProducts D)
    (ExpC : Exponentials PC) (adjeq : adj_equiv C D).

  Let F : functor C D := adjeq.
  Let G : functor D C := adj_equivalence_inv adjeq.
  Let η_z_iso : ∏ (c : C), z_iso c (G (F c)) := unit_pointwise_z_iso_from_adj_equivalence adjeq.
  Let ε_z_iso : ∏ (d : D), z_iso (F (G d)) d := counit_pointwise_z_iso_from_adj_equivalence adjeq.
  Let η_nat_z_iso : nat_z_iso (functor_identity C) (functor_composite F G) :=
        unit_nat_z_iso_from_adj_equivalence_of_cats adjeq.
  Let ε_nat_z_iso : nat_z_iso  (functor_composite G F) (functor_identity D) :=
        counit_nat_z_iso_from_adj_equivalence_of_cats adjeq.

  Let FC (c : C) : functor C C := constprod_functor1 PC c.
  Let GC (c : C) : functor C C := right_adjoint (ExpC c).
  Let ηC (c : C) : functor_identity C ⟹ (FC c) ∙ (GC c) := unit_from_left_adjoint (ExpC c).
  Let εC (c : C) : functor_composite (GC c) (FC c) ⟹ functor_identity C := counit_from_left_adjoint (ExpC c).

Section FixAnObject.

  Context (d0 : D).

  Let Fd0 : functor D D := constprod_functor1 PD d0.
  Let Gd0 : functor D D := functor_composite (functor_composite G (GC (G d0))) F.

Local Definition inherited_BP_on_C (d : D) : BinProduct C (G d0) (G d).
Proof.
  use tpair.
  - exists (G (pr1 (pr1 (PD d0 d)))).
    exact (# G (pr1 (pr2 (pr1 (PD d0 d)))),,# G (pr2 (pr2 (pr1 (PD d0 d))))).
  - set (Hpres := right_adjoint_preserves_binproduct adjeq adjeq : preserves_binproduct G).
    exact (Hpres _ _ _ _ _ (pr2 (PD d0 d))).
Defined.

Local Definition μ_nat_trans_data : nat_trans_data (G ∙ FC (G d0)) (Fd0 ∙ G).
Proof.
  intro d.
  exact (BinProductOfArrows _ (inherited_BP_on_C d) (PC (G d0) (G d)) (identity _) (identity _)).
Defined.

Local Lemma μ_nat_trans_law : is_nat_trans _ _ μ_nat_trans_data.
Proof.
  intros d' d f.
  apply (BinProductArrowsEq _ _ _ (inherited_BP_on_C d)).
  - etrans.
    { rewrite assoc'.
      apply maponpaths.
      apply (BinProductOfArrowsPr1 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
    rewrite id_right.
    etrans.
    2: { cbn.
         rewrite assoc'.
         etrans.
         2: { apply maponpaths.
              apply functor_comp. }
         unfold BinProduct_of_functors_mor.
         cbn.
         etrans.
         2: { do 2 apply maponpaths.
              apply pathsinv0, BinProductOfArrowsPr1. }
         rewrite id_right.
         unfold BinProductPr1.
         apply pathsinv0, (BinProductOfArrowsPr1 _ (inherited_BP_on_C d') (PC (G d0) (G d'))).
    }
    rewrite id_right.
    cbn.
    unfold BinProduct_of_functors_mor, constant_functor, functor_identity.
    cbn.
    etrans.
    { apply (BinProductOfArrowsPr1 _ (PC (G d0) (G d)) (PC (G d0) (G d'))). }
    apply id_right.
  - etrans.
    { rewrite assoc'.
      apply maponpaths.
      apply (BinProductOfArrowsPr2 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
    rewrite id_right.
    etrans.
    2: { cbn.
         rewrite assoc'.
         etrans.
         2: { apply maponpaths.
              apply functor_comp. }
         unfold BinProduct_of_functors_mor.
         cbn.
         etrans.
         2: { do 2 apply maponpaths.
              apply pathsinv0, BinProductOfArrowsPr2. }
         rewrite functor_comp.
         rewrite assoc.
         apply cancel_postcomposition.
         unfold BinProductPr2.
         apply pathsinv0, (BinProductOfArrowsPr2 _ (inherited_BP_on_C d') (PC (G d0) (G d'))).
    }
    rewrite id_right.
    cbn.
    unfold BinProduct_of_functors_mor, constant_functor, functor_identity.
    cbn.
    etrans.
    { apply (BinProductOfArrowsPr2 _ (PC (G d0) (G d)) (PC (G d0) (G d'))). }
    apply idpath.
Qed.

Local Definition μ_nat_trans : nat_trans (G ∙ FC (G d0)) (Fd0 ∙ G) := _,,μ_nat_trans_law.

Local Definition μ_nat_trans_inv_pointwise (d : D) : C ⟦ (Fd0 ∙ G) d, (G ∙ FC (G d0)) d ⟧.
Proof.
  exact (BinProductOfArrows _ (PC (G d0) (G d)) (inherited_BP_on_C d) (identity _) (identity _)).
Defined.

Local Lemma μ_nat_trans_is_inverse (d : D): is_inverse_in_precat (μ_nat_trans d) (μ_nat_trans_inv_pointwise d).
Proof.
  split; cbn.
  - apply pathsinv0, BinProduct_endo_is_identity.
    + rewrite assoc'.
      etrans.
      { apply maponpaths.
        cbn.
        apply (BinProductOfArrowsPr1 _ (PC (G d0) (G d)) (inherited_BP_on_C d)). }
      rewrite id_right.
      etrans.
      { cbn.
        apply (BinProductOfArrowsPr1 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
      apply id_right.
    + rewrite assoc'.
      etrans.
      { apply maponpaths.
        cbn.
        apply (BinProductOfArrowsPr2 _ (PC (G d0) (G d)) (inherited_BP_on_C d)). }
      rewrite id_right.
      etrans.
      { cbn.
        apply (BinProductOfArrowsPr2 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
      apply id_right.
  - unfold BinProduct_of_functors_ob, constant_functor, functor_identity.
    cbn.
    apply pathsinv0. apply (BinProduct_endo_is_identity _ _ _ (inherited_BP_on_C d)).
    + rewrite assoc'.
      etrans.
      { apply maponpaths.
        apply (BinProductOfArrowsPr1 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
      rewrite id_right.
      etrans.
      { apply (BinProductOfArrowsPr1 _ (PC (G d0) (G d)) (inherited_BP_on_C d)). }
      apply id_right.
    + rewrite assoc'.
      etrans.
      { apply maponpaths.
        apply (BinProductOfArrowsPr2 _ (inherited_BP_on_C d) (PC (G d0) (G d))). }
      rewrite id_right.
      etrans.
      { apply (BinProductOfArrowsPr2 _ (PC (G d0) (G d)) (inherited_BP_on_C d)). }
      apply id_right.
Qed.

Local Definition μ : nat_z_iso (functor_composite G (FC (G d0))) (functor_composite Fd0 G).
Proof.
  use make_nat_z_iso.
  - exact μ_nat_trans.
  - intro d.
    use tpair.
    + exact (μ_nat_trans_inv_pointwise d).
    + exact (μ_nat_trans_is_inverse d).
Defined.

Local Definition ηDd0 : functor_identity D ⟹ Fd0 ∙ Gd0.
Proof.
  simple refine (nat_trans_comp _ _ _ (nat_z_iso_to_trans_inv ε_nat_z_iso) _).
  unfold Gd0.
  change ((functor_composite G (functor_identity C)) ∙ F ⟹ (Fd0 ∙ (G ∙ GC (G d0))) ∙ F).
  apply post_whisker.
  refine (nat_trans_comp _ _ _ _ _).
  - apply (pre_whisker G (ηC (G d0))).
  - change (functor_composite (functor_composite G (FC (G d0))) (GC (G d0)) ⟹
              functor_composite (Fd0 ∙ G) (GC (G d0))).
    apply post_whisker.
    apply μ.
Defined.

Local Definition εDd0 : Gd0 ∙ Fd0 ⟹ functor_identity D.
Proof.
  simple refine (nat_trans_comp _ _ _ _ ε_nat_z_iso).
  change (functor_composite (functor_composite Gd0 Fd0) (functor_identity D) ⟹ G ∙ F).
  refine (nat_trans_comp _ _ _ _ _).
  - apply (pre_whisker _ (nat_z_iso_to_trans_inv ε_nat_z_iso)).
  - change ((functor_composite (Gd0 ∙ Fd0) G) ∙ F ⟹ G ∙ F).
    apply post_whisker.
    unfold Gd0.
    change (((G ∙ GC (G d0)) ∙ F) ∙ (Fd0 ∙ G) ⟹ G).
    refine (nat_trans_comp _ _ _ _ _).
    + apply (pre_whisker _ (nat_z_iso_to_trans_inv μ)).
    + change ((((G ∙ GC (G d0)) ∙ F) ∙ G) ∙ FC (G d0) ⟹ G).
      refine (nat_trans_comp _ _ _ _ _).
      * use (post_whisker _ (FC (G d0))).
        -- exact (G ∙ GC (G d0)).
        -- change (functor_composite (G ∙ GC (G d0)) (functor_composite F G) ⟹
                     functor_composite (G ∙ GC (G d0)) (functor_identity C)).
           apply (pre_whisker _ (nat_z_iso_to_trans_inv η_nat_z_iso)).
      * change (functor_composite G (functor_composite (GC (G d0)) (FC (G d0))) ⟹ G).
        apply (pre_whisker _ (εC (G d0))).
Defined.

Definition is_expDd0_adjunction_data : adjunction_data D D.
Proof.
  use make_adjunction_data.
  - exact Fd0.
  - exact Gd0.
  - exact ηDd0.
  - exact εDd0.
Defined.

Lemma is_expDd0_adjunction_laws : form_adjunction' is_expDd0_adjunction_data.
Proof.
  split.
  - intro d.
    change (# Fd0 (ηDd0 d) · εDd0 (Fd0 d) = identity (Fd0 d)).
    unfold ηDd0.
    etrans.
    { apply cancel_postcomposition.
      etrans.
      { apply functor_comp. }
      do 2 apply maponpaths.
      assert (Hpost := post_whisker_composition _ _ _ F _ _ _ (pre_whisker G (ηC (G d0))) (post_whisker (pr1 μ) (GC (G d0)))).
      refine (toforallpaths _ _ _ (maponpaths pr1 Hpost) d).
    }
    etrans.
    { apply cancel_postcomposition.
      apply maponpaths.
      apply functor_comp. }
    unfold εDd0.
(* so it is in principle possible to work with this definition, but every step takes an effort,
   requiring a perfect proof on paper before

    rewrite functor_comp.
    use BinProductArrowsEq.
    + rewrite id_left.


      cbn. unfold BinProduct_of_functors_mor.
      rewrite id_left.
      unfold BinProduct_of_functors_ob, constant_functor, functor_identity.
      cbn.
      etrans.
      { apply cancel_postcomposition.
        apply
      admit.
    + cbn. unfold BinProduct_of_functors_mor.
      rewrite id_left.
      unfold BinProduct_of_functors_ob, constant_functor, functor_identity.
      cbn.
      (* is this supposed to be analogous? *)
      admit.
  - intro d. show_id_type. (* F-images in source and target of the morphisms *)
    cbn.
    admit.
*)
Abort.

(*
Definition is_expDd0_adjunction : adjunction D D := _,,is_expDd0_adjunction_laws.

Local Definition is_expDd0 : is_exponentiable PD d0.
Proof.
  exists Gd0.
  exact is_expDd0_adjunction.
Defined.
 *)

(* an experiment towards using univalence for this proof
Lemma is_expDd0_adjunction_laws_equal_cats (Heq : C = D) (*(PCeq : transportf _ Heq PC = PD)*) :
  form_adjunction' is_expDd0_adjunction_data.
Proof.
  induction Heq.
*)

End FixAnObject.
(*
Definition exponentials_through_adj_equivalence : Exponentials PD.
Proof.
  intro d0. exact (is_expDd0 d0).
Defined.
 *)



End ExponentialsCarriedThroughAdjointEquivalence.

Section AlternativeWithUnivalence.

  Context {C : category} (PC : BinProducts C) {D : category} (PD : BinProducts D)
    (ExpC : Exponentials PC) (adjeq : adj_equiv C D) (Cuniv : is_univalent C) (Duniv : is_univalent D).

  Local Lemma CDeq : C = D.
  Proof.
    assert (aux : category_to_precategory C = category_to_precategory D).
    { apply (invmap (catiso_is_path_precat C D D)).
      apply (adj_equivalence_of_cats_to_cat_iso adjeq); assumption. }
    apply subtypePath. intro. apply isaprop_has_homsets.
    exact aux.
  Qed.

  Definition exponentials_through_adj_equivalence_univalent_cats : Exponentials PD.
  Proof.
    induction CDeq.
    clear adjeq.
    assert (aux : PC = PD).
    2: { rewrite <- aux. exact ExpC. }
    apply funextsec.
    intro c1.
    apply funextsec.
    intro c2.
    apply isaprop_BinProduct; exact Cuniv.
  Defined.

End AlternativeWithUnivalence.

(**
 Accessors for exponentials
 *)
Section AccessorsExponentials.
  Context {C : category}
          {prodC : BinProducts C}
          (expC : Exponentials prodC).

  Definition exp
             (x y : C)
    : C
    := pr1 (expC x) y.

  Definition exp_eval
             (x y : C)
    : prodC x (exp x y) --> y
    := counit_from_are_adjoints (pr2 (expC x)) y.

  Definition exp_eval_alt
             (x y : C)
    : prodC (exp x y) x --> y
    := prod_swap prodC _ _ · exp_eval x y.

  Definition exp_lam
             {x y z : C}
             (f : prodC y x --> z)
    : x --> exp y z
    := unit_from_are_adjoints (pr2 (expC y)) x · # (pr1 (expC y)) f.

  Definition exp_lam_alt
             {x y z : C}
             (f : prodC z x --> y)
    : z --> exp x y
    := exp_lam (prod_swap prodC _ _ · f).

  Proposition exp_beta
              {x y z : C}
              (f : prodC y x --> z)
    : BinProductOfArrows _ _ _ (identity _) (exp_lam f)
      · exp_eval _ _
      =
      f.
  Proof.
    unfold exp_lam.
    rewrite <- BinProductOfArrows_idxcomp.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (nat_trans_ax
              (counit_from_are_adjoints (pr2 (expC y)))
              _
              _
              f).
    }
    cbn.
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply (triangle_id_left_ad (pr2 (expC y))).
  Qed.

  Proposition exp_beta_alt
              {x y z : C}
              (f : prodC z x --> y)
    : BinProductOfArrows _ _ _ (exp_lam_alt f) (identity x)
      · exp_eval_alt x y
      =
      f.
  Proof.
    unfold exp_eval_alt.
    rewrite !assoc.
    rewrite BinProductOfArrows_swap.
    unfold exp_lam_alt.
    rewrite !assoc'.
    rewrite exp_beta.
    rewrite !assoc.
    rewrite prod_swap_swap.
    apply id_left.
  Qed.

  Proposition exp_eta
              {x y z : C}
              (f : z --> exp x y)
    : f
      =
      exp_lam (BinProductOfArrows C _ _ (identity x) f · exp_eval x y).
  Proof.
    unfold exp_lam.
    rewrite functor_comp.
    rewrite !assoc.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!(nat_trans_ax
                 (unit_from_are_adjoints (pr2 (expC x)))
                 _
                 _
                 f)).
    }
    refine (_ @ id_right _).
    rewrite !assoc'.
    apply maponpaths.
    exact (triangle_id_right_ad (pr2 (expC x)) _).
  Qed.

  Proposition exp_eta_alt
              {x y z : C}
              (f : z --> exp x y)
    : f
      =
      exp_lam_alt (BinProductOfArrows C _ _ f (identity x) · exp_eval_alt x y).
  Proof.
    refine (exp_eta _ @ _).
    unfold exp_lam_alt.
    apply maponpaths.
    unfold exp_eval_alt.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite BinProductOfArrows_swap.
    rewrite !assoc.
    rewrite prod_swap_swap.
    rewrite id_left.
    apply idpath.
  Qed.

  Proposition exp_funext
              {x y z : C}
              {f g : z --> exp x y}
              (p : ∏ (a : C)
                     (h : a --> x),
                   BinProductOfArrows C _ (prodC a z) h f · exp_eval x y
                   =
                   BinProductOfArrows C _ (prodC a z) h g · exp_eval x y)
    : f = g.
  Proof.
    refine (exp_eta f @ _ @ !(exp_eta g)).
    apply maponpaths.
    apply p.
  Qed.

  Proposition exp_lam_natural
              {w x y z : C}
              (f : prodC y x --> z)
              (s : w --> x)
    : s · exp_lam f
      =
      exp_lam (BinProductOfArrows _ _ _ (identity _ ) s · f).
  Proof.
    use exp_funext.
    intros a h.
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (!(id_right _)).
    }
    rewrite <- BinProductOfArrows_comp.
    rewrite !assoc'.
    rewrite exp_beta.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (!(id_right _)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      exact (!(id_left _)).
    }
    rewrite <- BinProductOfArrows_comp.
    rewrite !assoc'.
    rewrite exp_beta.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite BinProductOfArrows_comp.
    rewrite id_left, id_right.
    apply idpath.
  Qed.
End AccessorsExponentials.
