(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

(* ============================================================================================= *)
(* Categories with Familise (CwF).                                                               *)
(*                                                                                               *)
(* The bicategory of CwF implemented as iterated displayed bicategories on Cat (the              *)
(* bicategory of categories).                                                                    *)
(* ============================================================================================= *)

(* Foundations. *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(* Categories. *)
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.whiskering.
Require Export UniMath.CategoryTheory.yoneda.
Require Export UniMath.CategoryTheory.limits.pullbacks.

(* Displayed categories. *)
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

(* (Displayed) Bicategories. *)
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.ContravariantFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Sigma.
Require Import UniMath.CategoryTheory.Bicategories.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Cofunctormap.

Open Scope cat.
Open Scope mor_disp_scope.

Local Notation "'SET'" := hset_category.
Local Notation "'PreShv' C" := [C^op,SET] (at level 4) : cat.
Local Notation "'Yo'" := (yoneda _ (homset_property _) : functor _ (PreShv _)).

Section Yoneda.

  Context {C : precategory} {hsC : has_homsets C}.

  Definition yy {F : PreShv C} {c : C}
    : ((F : C^op ⟶ SET) c : hSet) ≃
      [C^op, HSET, has_homsets_HSET] ⟦ yoneda C hsC c, F⟧.
  Proof.
    apply invweq. apply yoneda_weq.
  Defined.

  Lemma yy_natural (F : PreShv C) (c : C)
        (A : (F : C^op ⟶ SET) c : hSet)
        c' (f : C⟦c', c⟧)
    : yy (functor_on_morphisms (F : C^op ⟶ SET) f A) =
      functor_on_morphisms (yoneda C hsC) f · yy A.
  Proof.
    assert (XTT := is_natural_yoneda_iso_inv _ hsC F _ _ f).
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

Section Projections.

  Context {C : category}
          {Ty Tm : opp_precat_data C ⟶ SET}
          {pp : Tm ⟹ Ty}.

  Variable (R : cwf_representation pp).
  Variable (Γ : C) (A : Ty Γ : hSet).

  Definition ext : C := pr1 (pr1 (R Γ A)).

  Definition π : C⟦ext,Γ⟧ := pr2 (pr1 (R Γ A)).

  Definition var : (Tm ext:hSet) := pr1 (pr1 (pr2 (R Γ A))).

  Definition comm
    : pp ext var = functor_on_morphisms Ty π A
    := pr2 (pr1 (pr2 (R Γ A))).

  Definition pullback
    : isPullback (yy A) pp
                 (functor_on_morphisms (yoneda C (homset_property C)) π)
                 (yy var) (cwf_square_comm pp comm)
    := pr2 (pr2 (R Γ A)).

End Projections.

Arguments iso _ _ _ : clear implicits.

Section Representation_Morphisms.

  Context {C : category}
          {Ty Tm : opp_precat_data C ⟶ SET}
          {pp : Tm ⟹ Ty}
          (R : cwf_representation pp).

  Context {C' : category}
          {Ty' Tm' : opp_precat_data C' ⟶ SET}
          {pp' : Tm' ⟹ Ty'}
          (R' : cwf_representation pp').

  Context {f : functor C C'}
          (fty : Ty ⟹ functor_composite (functor_opp f) Ty')
          (ftm : Tm ⟹ functor_composite (functor_opp f) Tm').

  Definition isoext_type (Γ : C) (A : (Ty Γ : hSet)) : UU
    := iso C' (f (ext R Γ A)) (ext R' (f Γ) (fty Γ A)).

  Definition π_compatibility_type (Γ : C) (A : (Ty Γ : hSet))
             (i : isoext_type Γ A)
    : UU
    := functor_on_morphisms f (π R Γ A) =
       (i:iso _ _ _) · π R' (f Γ) (fty Γ A).

  Definition var_compatibility_type (Γ : C) (A : (Ty Γ : hSet))
             (i : iso C' (f (ext R Γ A)) (ext R' (f Γ) (fty Γ A)))
    : UU
    := functor_on_morphisms Tm' (opp_iso i) (var R' (f Γ) (fty Γ A)) =
       ftm _ (var R Γ A).

End Representation_Morphisms.

Section CwF.

  Definition disp_cwf_cat_ob_mor
    : disp_cat_ob_mor (total_bicat (morphisms_of_preshaves SET)).
  Proof.
    use tpair; cbn.
    - intros (C, ((Ty, Tm), pp)).
      exact (cwf_representation pp).
    - intros (C, ((Ty, Tm), pp)).
      intros (C', ((Ty', Tm'), pp')).
      intros R R'. cbn in *.
      intros (f, ((fty, ftm), eq)).
      exact (∏ (Γ : C) (A : (Ty Γ:hSet)),
             ∑ (φ : isoext_type R R' fty Γ A),
             π_compatibility_type R R' fty Γ A φ ×
             var_compatibility_type R R' fty ftm Γ A φ).
  Defined.

  Lemma disp_cwf_cat_id_comp_internal
        {C1 : category}
        {Ty1 Tm1 : opp_precat C1 ⟶ hset_precategory}
        (pp1 : Tm1 ⟹ Ty1)
        {C2 : category}
        {Ty2 Tm2 : opp_precat C2 ⟶ hset_precategory}
        (pp2 : Tm2 ⟹ Ty2)
        {C3 : category}
        {Ty3 Tm3 : opp_precat C3 ⟶ hset_precategory}
        {pp3 : Tm3 ⟹ Ty3}
        (f : C1 ⟶ C2)
        (fty : Ty1 ⟹ functor_composite (functor_opp f) Ty2)
        (ftm : Tm1 ⟹ functor_composite (functor_opp f) Tm2)
        (feq : nat_trans_comp pp1 fty=
               nat_trans_comp ftm (pre_whisker (functor_opp f) pp2))
        (g : C2 ⟶ C3)
        (gty : Ty2 ⟹ functor_composite (functor_opp g) Ty3)
        (gtm : Tm2 ⟹ functor_composite (functor_opp g) Tm3)
        (geq : nat_trans_comp pp2 gty =
               nat_trans_comp gtm (pre_whisker (functor_opp g) pp3))
        (r1 : cwf_representation pp1)
        (r2 : cwf_representation pp2)
        (r3 : cwf_representation pp3)
        (fcomp : ∏ (Γ : C1) (A : (Ty1 Γ : hSet)),
                 ∑ (φ : isoext_type r1 r2 fty Γ A),
                 π_compatibility_type r1 r2 fty Γ A φ ×
                 var_compatibility_type r1 r2 fty ftm Γ A φ)
        (gcomp : ∏ (Γ : C2) (A : (Ty2 Γ : hSet)),
                 ∑ (φ : isoext_type r2 r3 gty Γ A),
                 π_compatibility_type r2 r3 gty Γ A φ ×
                 var_compatibility_type r2 r3 gty gtm Γ A φ)
        (Γ : C1) (A : (Ty1 Γ : hSet))
    : π_compatibility_type
        r1 r3
        (@nat_trans_comp _ SET _ _ ((functor_opp (f ∙ g)) ∙ Ty3)
                         fty (pre_whisker (functor_opp f) gty)) Γ A
        (iso_comp (functor_on_iso g (pr1 (fcomp Γ A))) (pr1 (gcomp (f Γ) (fty Γ A)))) ×
      var_compatibility_type
        r1 r3
        (@nat_trans_comp _ SET _ _ (functor_opp (f ∙ g) ∙ Ty3)
                         fty (pre_whisker (functor_opp f) gty))
        (nat_trans_comp ftm (pre_whisker (functor_opp f) gtm)) Γ A
        (iso_comp (functor_on_iso g (pr1 (fcomp Γ A))) (pr1 (gcomp (f Γ) (fty Γ A)))).
  Proof.
    cbn in *. apply tpair.
    - unfold π_compatibility_type. cbn.
      set (fcomp' := fcomp Γ A).
      destruct fcomp' as (fφ, (π_fcomp, var_fcomp)).
      set (gcomp' := gcomp (f Γ) (fty _ A)).
      destruct gcomp' as (gφ, (π_gcomp, var_gcomp)).
      unfold π_compatibility_type in π_fcomp, π_gcomp.
      etrans. { apply maponpaths. apply π_fcomp. }
      rewrite functor_comp.
      rewrite <- assoc. apply maponpaths.
      apply π_gcomp.
    - unfold var_compatibility_type. cbn.
      set (fcomp' := fcomp Γ A).
      destruct fcomp' as (fφ, (π_fcomp, var_fcomp)).
      set (gcomp' := gcomp (f Γ) (fty _ A)).
      destruct gcomp' as (gφ, (π_gcomp, var_gcomp)).
      unfold var_compatibility_type in var_fcomp, var_gcomp.
      cbn in *.
      rewrite <- var_fcomp.
      etrans.
      apply (toforallpaths _ _ _ (functor_comp Tm3 _ _)).
      cbn.
      pose (gtmeq := (pr2 gtm) (ext r2 (f Γ) (fty _ A))
                               (f (ext r1 Γ A))
                               (pr1 fφ)).
      apply toforallpaths in gtmeq.
      cbn in gtmeq.
      rewrite gtmeq.
      apply maponpaths.
      exact var_gcomp.
  Qed.

  Definition disp_cwf_cat_id_comp
    : disp_cat_id_comp _ disp_cwf_cat_ob_mor.
  Proof.
    apply tpair. cbn.
    - intros (C, ((Ty, Tm), p)).
      intros r Γ A.
      unfold isoext_type.
      cbn.
      use tpair.
      + exact (identity_iso _).
      + cbn. split.
        * unfold π_compatibility_type.
          cbn. apply pathsinv0. apply id_left.
        * unfold var_compatibility_type. cbn.
          pose (pp := functor_id Tm (ext r Γ A)).
          apply (toforallpaths _ _ _ pp).
    - intros (C1, ((Ty1, Tm1), pp1)).
      intros (C2, ((Ty2, Tm2), pp2)).
      intros (C3, ((Ty3, Tm3), pp3)).
      cbn in *.
      intros (f, ((fty, ftm), feq)).
      cbn in *.
      intros (g, ((gty, gtm), geq)).
      cbn in *.
      intros r1 r2 r3.
      intros fcomp gcomp Γ A.
      use tpair.
      + unfold isoext_type. cbn.
        specialize (fcomp Γ A).
        destruct fcomp as (fφ, (π_fcomp, var_fcomp)).
        unfold isoext_type in fφ.
        specialize (gcomp (f Γ) (fty _ A)).
        destruct gcomp as (gφ, (π_gcomp, var_gcomp)).
        unfold isoext_type in gφ.
        exact (iso_comp (functor_on_iso g fφ) gφ).
      + pose (rmk := @disp_cwf_cat_id_comp_internal). cbn in rmk.
        apply rmk; [exact feq | exact geq].
  Defined.

  Definition disp_cwf_cat_data
    : disp_cat_data (total_bicat (morphisms_of_preshaves SET))
    := (_ ,, disp_cwf_cat_id_comp).

  Definition disp_cwf : disp_prebicat _
    := disp_cell_unit_prebicat disp_cwf_cat_data.

(*
  Definition disp_cwf_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells (total_bicat (morphisms_of_preshaves SET)).
  Proof.
    exists disp_cwf_cat_data. red. cbn.
    intros.
      (*
    intros (C, ((Ty, Tm), pp)).
    intros (C', ((Ty', Tm'), pp')).
    cbn in *.
    intros (f, ((fty, ftm), feq)).
    intros (g, ((gty, gtm), geq)).
    cbn in *.
    intros (x, ((xty, xtm), _)).
    intros r r' Γ A.
    cbn in *.
    unfold cwf_representation in r.
    unfold cwf_fiber_representation in r.
    cbn in r.
       *)
    exact unit.
  Defined.
*)

End CwF.
