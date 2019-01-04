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
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.whiskering.
Require Export UniMath.CategoryTheory.yoneda.
Require Export UniMath.CategoryTheory.limits.pullbacks.

(* Displayed categories. *)
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

(* (Displayed) Bicategories. *)
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.ContravariantFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Cofunctormap.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Local Notation "'SET'" := HSET_univalent_category.
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

  Definition isaprop_cwf_fiber_representation {Γ : C} (A : Ty Γ : hSet)
    : isaprop (cwf_fiber_representation A).
  Admitted.

  Definition cwf_representation : UU
    := ∏ Γ (A : Ty Γ : hSet), cwf_fiber_representation A.

  Definition isaprop_cwf_representation
    : isaprop cwf_representation.
  Proof.
    do 2 (apply impred ; intro).
    apply isaprop_cwf_fiber_representation.
  Defined.
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

Section CwF.
  Definition cwf : bicat.
  Proof.
    refine (fullsubbicat (morphisms_of_presheaves SET) _).
    intros (C, ((Ty, Tm), pp)).
    cbn in *.
    exact (@cwf_representation C _ _ pp).
  Defined.

  Definition cwf_is_univalent_2_1
    : is_univalent_2_1 cwf.
  Proof.
    apply is_univalent_2_1_fullsubbicat.
    apply morphisms_of_presheaves_univalent_2_1.
  Defined.

  Definition cwf_is_univalent_2_0
    : is_univalent_2_0 cwf.
  Proof.
    apply is_univalent_2_0_fullsubbicat.
    - apply morphisms_of_presheaves_univalent_2_0.
    - apply morphisms_of_presheaves_univalent_2_1.
    - intros.
      apply isaprop_cwf_representation.
  Defined.
End CwF.
