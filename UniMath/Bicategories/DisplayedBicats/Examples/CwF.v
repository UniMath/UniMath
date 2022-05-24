(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

(* ============================================================================================= *)
(* Categories with Families (CwF).                                                               *)
(*                                                                                               *)
(* The bicategory of CwF implemented as iterated displayed bicategories on Cat (the              *)
(* bicategory of categories).                                                                    *)
(* ============================================================================================= *)

(* Foundations. *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(* Categories. *)
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.whiskering.
Require Export UniMath.CategoryTheory.yoneda.
Require Export UniMath.CategoryTheory.limits.pullbacks.

(* Displayed categories. *)
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

(* (Displayed) Bicategories. *)
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ContravariantFunctor.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Cofunctormap.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Local Notation "'SET'" := HSET_univalent_category.
Local Notation "'PreShv' C" := [C^op,SET] (at level 4) : cat.
Local Notation "'Yo'" := (yoneda _ : functor _ (PreShv _)).

Section Yoneda.

  Context {C : category} {hsC : has_homsets C}.

  Definition yy {F : PreShv C} {c : C}
    : ((F : C^op ⟶ SET) c : hSet) ≃
      [C^op, HSET, has_homsets_HSET] ⟦ yoneda C c, F⟧.
  Proof.
    apply invweq. apply yoneda_weq.
  Defined.

  Lemma yy_natural (F : PreShv C) (c : C)
        (A : (F : C^op ⟶ SET) c : hSet)
        c' (f : C⟦c', c⟧)
    : yy (functor_on_morphisms (F : C^op ⟶ SET) f A) =
      functor_on_morphisms (yoneda C) f · yy A.
  Proof.
    assert (XTT := is_natural_yoneda_iso_inv _ F _ _ f).
    apply (toforallpaths _ _ _ XTT).
  Qed.

  Lemma yy_comp_nat_trans
        (F F' : PreShv C) (p : _ ⟦F, F'⟧)
        A (v : (F : C^op ⟶ SET) A : hSet)
    : yy v · p = yy ((p : nat_trans _ _ )  _ v).
  Proof.
    apply nat_trans_eq.
    - apply has_homsets_HSET.
    - intro c. simpl.
      apply funextsec. intro f. cbn.
      assert (XR := toforallpaths _ _ _ (nat_trans_ax p _ _ f) v ).
      cbn in XR.
      apply XR.
  Qed.

End Yoneda.

(* Adapted from
   TypeTheory/TypeTheory/Auxiliary/Auxiliary.v
   TypeTheory/ALV1/CwF_def.v *)
(*
Section Representation.

  Context {C : category}
          {Ty Tm : opp_precat_data C ⟶ SET}
          (pp : Tm ⟹ Ty).

  Definition map_into (Γ : C) : UU := ∑ (ΓA : C), C ⟦ΓA, Γ⟧.

  Definition cwf_tm_of_ty {Γ : C} (A : Ty Γ : hSet) : UU
    := ∑ (t : (Tm Γ : hSet)),
       (pp : nat_trans _ _) _ t = A.

  Lemma cwf_square_comm {Γ} {A}
        {ΓA : C} {π : ΓA --> Γ}
        {t : Tm ΓA : hSet} (e : (pp : nat_trans _ _) _ t = functor_on_morphisms Ty π A)
    : functor_on_morphisms Yo π · yy A = yy t · pp.
  Proof.
    apply pathsinv0.
    etrans. 2: apply yy_natural.
    etrans. apply yy_comp_nat_trans.
    apply maponpaths, e.
  Qed.

  Definition cwf_fiber_representation {Γ : C} (A : Ty Γ : hSet) : UU
    := ∑ (ΓAπ : map_into Γ) (te : cwf_tm_of_ty (functor_on_morphisms Ty (pr2 ΓAπ) A)),
       isPullback _ _ _ _ (cwf_square_comm (pr2 te)).

  Definition cwf_representation : UU
    := ∏ Γ (A : Ty Γ : hSet), cwf_fiber_representation A.
End Representation.
*)

Lemma transportf_yy
      {C : category}
      (F : opp_precat_data C ⟶ SET) (c c' : C) (A : (F : functor _ _ ) c : hSet)
      (e : c = c')
(* TODO: see #1470 *)
  : paths
    (pr1weq
       (@yy C F c')
       (@transportf _ (fun d => pr1hSet (functor_on_objects F d : hSet)) _ _ e A))
    (@transportf _ (fun d => nat_trans _ F) _ _ e (pr1weq (@yy C F c) A)).
Proof.
  induction e.
  apply idpath.
Defined.

Lemma forall_isotid (A : category) (a_is : is_univalent A)
      (a a' : A) (P : z_iso a a' -> UU)
  : (∏ e, P (idtoiso e)) → ∏ i, P i.
Proof.
  intros H i.
  rewrite <- (idtoiso_isotoid _ a_is).
  apply H.
Defined.

Lemma transportf_isotoid_functor
      (A X : category) (H : is_univalent A)
      (K : functor A X)
      (a a' : A) (p : z_iso a a') (b : X) (f : K a --> b)
  : transportf (fun a0 => K a0 --> b) (isotoid _ H p) f = (#K)%cat (inv_from_z_iso p) · f.
Proof.
  rewrite functor_on_inv_from_z_iso. simpl. cbn.
  generalize p.
  apply forall_isotid.
  - apply H.
  - intro e. induction e.
    cbn.
    rewrite functor_id.
    rewrite id_left.
    rewrite isotoid_identity_iso.
    apply idpath.
Defined.

Lemma inv_from_z_iso_iso_from_fully_faithful_reflection {C D : precategory}
      (F : functor C D) (HF : fully_faithful F) (a b : C) (i : z_iso (F a) (F b))
  : inv_from_z_iso
      (iso_from_fully_faithful_reflection HF i) =
    iso_from_fully_faithful_reflection HF (z_iso_inv_from_z_iso i).
Proof.
  apply idpath.
Defined.

Section CwFRepresentation.
  Context {C : category}
          {Ty Tm : opp_precat_data C ⟶ SET}
          (pp : Tm ⟹ Ty)
          (HC : is_univalent C).

  Definition cwf_fiber_rep_data {Γ:C} (A : Ty Γ : hSet) : UU
    := ∑ (ΓA : C), C ⟦ΓA, Γ⟧ × (Tm ΓA : hSet).

  Lemma cwf_square_comm {Γ} {A}
        {ΓA : C} {π : ΓA --> Γ}
        {t : Tm ΓA : hSet} (e : (pp : nat_trans _ _) _ t = functor_on_morphisms Ty π A)
(* TODO: see #1470 *)
    : @paths _
    (@compose _ _
       (@functor_on_objects _ (functor_category _ HSET_univalent_category) _ Γ)
       Ty (functor_on_morphisms _ π)
       (pr1weq (@yy C Ty Γ) A))
    (@compose _
       (@functor_on_objects _ (functor_category _ hset_category) _ ΓA)
       Tm Ty
       (pr1weq (@yy C Tm ΓA) t) pp).
  Proof.
    apply pathsinv0.
    etrans. 2: apply yy_natural.
    etrans. apply yy_comp_nat_trans.
    apply maponpaths, e.
  Qed.

  Definition cwf_fiber_rep_ax
             {Γ:C} {A : Ty Γ : hSet}
             (ΓAπt : cwf_fiber_rep_data A) : UU
    := ∑ (H : pp _ (pr2 (pr2 ΓAπt)) = (#Ty)%cat (pr1 (pr2 ΓAπt)) A),
       isPullback (cwf_square_comm H).

  Definition cwf_fiber_representation {Γ:C} (A : Ty Γ : hSet) : UU
    := ∑ ΓAπt : cwf_fiber_rep_data A, cwf_fiber_rep_ax ΓAπt.

  Lemma isaprop_cwf_fiber_representation {Γ:C} (A : Ty Γ : hSet)
    : is_univalent C -> isaprop (cwf_fiber_representation A).
  Proof.
    intro isC.
    apply invproofirrelevance.
    intros x x'. apply subtypePath.
    { intro.
      apply isofhleveltotal2.
      - apply setproperty.
      - intro. apply isaprop_isPullback.
    }
    destruct x as [x H].
    destruct x' as [x' H']. cbn.
    destruct x as [ΓA m].
    destruct x' as [ΓA' m']. cbn in *.
    destruct H as [H isP].
    destruct H' as [H' isP'].
    use (total2_paths_f).
    - set (T1 := make_Pullback _ isP).
      set (T2 := make_Pullback _ isP').
      set (i := z_iso_from_Pullback_to_Pullback T1 T2). cbn in i.
      set (i' := invmap (weq_ff_functor_on_z_iso (yoneda_fully_faithful _) _ _ ) i ).
      set (TT := isotoid _ isC i').
      apply TT.
    - cbn.
      set (XT := transportf_dirprod _ (fun a' => C⟦a', Γ⟧) (fun a' => Tm a' : hSet)).
      cbn in XT.
      set (XT' := XT (tpair _ ΓA m : ∑ R : C, C ⟦ R, Γ ⟧ × (Tm R : hSet) )
                     (tpair _ ΓA' m' : ∑ R : C, C ⟦ R, Γ ⟧ × (Tm R : hSet) )).
      cbn in *.
      match goal with | [ |- transportf _ ?e _ = _ ] => set (TT := e) end.
      rewrite XT'. clear XT' XT.
      destruct m as [π te].
      destruct m' as [π' te'].
      cbn.
      apply pathsdirprod.
      + unfold TT; clear TT.
        rewrite transportf_isotoid.
        cbn.
        unfold from_Pullback_to_Pullback.
        cbn in *.
        pose (XR' := nat_trans_eq_pointwise
                       (PullbackArrow_PullbackPr1
                          (make_Pullback _ isP)
                          (yoneda_objects C ΓA')
                          (yoneda_morphisms C ΓA' Γ π')
                          (yoneda_map_2 C ΓA' Tm te')
                          (PullbackSqrCommutes
                             (make_Pullback _ isP')))
                       ΓA').
        cbn in XR'.
        assert (XR'':= toforallpaths _ _  _ XR').
        cbn in XR''.
        etrans. apply XR''.
        apply id_left.
      + unfold TT; clear TT.
        match goal with |[|- transportf ?r  _ _ = _ ] => set (P:=r) end.
        match goal with |[|- transportf _ (_ _ _ (_ _ ?ii)) _ = _ ] => set (i:=ii) end.
        simpl in i.
        apply (invmaponpathsweq (@yy _ Tm ΓA')).
        etrans.
        {
          apply transportf_yy.
        }
        etrans.
        {
          apply (transportf_isotoid_functor C (functor_category _ SET)).
        }
        rewrite inv_from_z_iso_iso_from_fully_faithful_reflection.
        assert (XX:=homotweqinvweq (weq_from_fully_faithful
                                      (yoneda_fully_faithful _) ΓA' ΓA )).
        etrans. apply maponpaths_2. apply XX.
        clear XX.
        etrans. apply maponpaths_2. unfold from_Pullback_to_Pullback. apply idpath.
        pose (XR' := PullbackArrow_PullbackPr2
                       (make_Pullback _ isP)
                       (yoneda_objects C ΓA')
                       (yoneda_morphisms C ΓA' Γ π')
                       (yoneda_map_2 C ΓA' Tm te')
                       (PullbackSqrCommutes
                          (make_Pullback _ isP'))).
        apply XR'.
  Qed.

  Definition cwf_representation : UU
    := ∏ Γ (A : Ty Γ : hSet), cwf_fiber_representation A.

  Definition isaprop_cwf_representation
    : isaprop cwf_representation.
  Proof.
    do 2 (apply impred ; intro).
    apply isaprop_cwf_fiber_representation.
    exact HC.
  Defined.
End CwFRepresentation.

Section Projections.

  Context {C : category}
          {Ty Tm : opp_precat_data C ⟶ SET}
          {pp : Tm ⟹ Ty}.

  Variable (R : cwf_representation pp).
  Variable (Γ : C) (A : Ty Γ : hSet).

  Definition ext : C := pr1 (pr1 (R Γ A)).

  Definition π : C⟦ext,Γ⟧ := pr121 (R Γ A).

  Definition var : (Tm ext:hSet) := pr221 (R Γ A).

  Definition comm
    : pp ext var = functor_on_morphisms Ty π A
    := pr12 (R Γ A).

  Definition pullback
    : isPullback (cwf_square_comm pp comm)
    := pr2 (pr2 (R Γ A)).
End Projections.

Arguments iso _ _ _ : clear implicits.

Section CwF.
  Definition disp_cwf' : disp_bicat (morphisms_of_presheaves SET).
  Proof.
    refine (disp_fullsubbicat (morphisms_of_presheaves SET) _).
    intros (C, ((Ty, Tm), pp)).
    cbn in *.
    exact (@cwf_representation C _ _ pp).
  Defined.

  Definition disp_cwf : disp_bicat bicat_of_univ_cats
    := sigma_bicat _ _ disp_cwf'.

  Definition disp_2cells_isaprop_disp_cwf
    : disp_2cells_isaprop disp_cwf.
  Proof.
    apply disp_2cells_isaprop_sigma.
    - apply disp_2cells_isaprop_morphisms_of_presheaves_display.
    - apply disp_2cells_isaprop_fullsubbicat.
  Qed.

  Definition disp_locally_groupoid_disp_cwf
    : disp_locally_groupoid disp_cwf.
  Proof.
    apply disp_locally_groupoid_sigma.
    - exact univalent_cat_is_univalent_2.
    - apply disp_2cells_isaprop_morphisms_of_presheaves_display.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_locally_groupoid_morphisms_of_presheaves_display.
    - apply disp_locally_groupoid_fullsubbicat.
  Qed.

  Definition cwf : bicat
    := total_bicat disp_cwf.

  Lemma disp_univalent_2_1_morphisms_of_presheaf_display
    : disp_univalent_2_1 (morphisms_of_presheaves_display SET).
  Proof.
    apply sigma_disp_univalent_2_1_with_props.
    - apply disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_presheaf.
    - apply disp_2cells_isaprop_cofunctormaps.
    - apply disp_two_presheaves_is_univalent_2_1.
    - apply disp_cofunctormaps_bicat_univalent_2_1.
  Qed.

  Lemma disp_univalent_2_0_morphisms_of_presheaf_display
    : disp_univalent_2_0 (morphisms_of_presheaves_display SET).
  Proof.
    apply sigma_disp_univalent_2_0_with_props.
    - exact univalent_cat_is_univalent_2.
    - apply disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_presheaf.
    - apply disp_2cells_isaprop_cofunctormaps.
    - apply disp_two_presheaves_is_univalent_2_1.
    - apply disp_cofunctormaps_bicat_univalent_2_1.
    - apply disp_locally_groupoid_prod ; apply disp_locally_groupoid_presheaf.
    - apply disp_locally_groupoid_cofunctormaps.
    - apply disp_two_presheaves_is_univalent_2_0.
    - apply disp_cofunctormaps_bicat_univalent_2_0.
  Qed.

  Definition cwf_is_univalent_2_1
    : is_univalent_2_1 cwf.
  Proof.
    apply sigma_is_univalent_2_1.
    - exact univalent_cat_is_univalent_2_1.
    - exact disp_univalent_2_1_morphisms_of_presheaf_display.
    - apply disp_fullsubbicat_univalent_2_1.
  Qed.

  Definition cwf_is_univalent_2_0
    : is_univalent_2_0 cwf.
  Proof.
    apply sigma_is_univalent_2_0.
    - exact univalent_cat_is_univalent_2.
    - split.
      + exact disp_univalent_2_0_morphisms_of_presheaf_display.
      + exact disp_univalent_2_1_morphisms_of_presheaf_display.
    - split.
      + apply disp_univalent_2_0_fullsubbicat.
        * apply morphisms_of_presheaves_univalent_2.
        * intros C.
          apply isaprop_cwf_representation.
          apply (pr1 C).
      + apply disp_fullsubbicat_univalent_2_1.
  Qed.

  Definition cwf_is_univalent_2
    : is_univalent_2 cwf.
  Proof.
    split.
    - exact cwf_is_univalent_2_0.
    - exact cwf_is_univalent_2_1.
  Defined.
End CwF.
