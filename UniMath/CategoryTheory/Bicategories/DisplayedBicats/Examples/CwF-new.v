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

  Definition cwf_representation : UU
    := ∏ Γ (A : Ty Γ : hSet), cwf_fiber_representation A.
End Representation.

Lemma transportf_yy
      {C : precategory} {hsC : has_homsets C}
      (F : opp_precat_data C ⟶ SET) (c c' : C) (A : (F : functor _ _ ) c : hSet)
      (e : c = c')
  : yy (transportf (fun d => (F : functor _ _ ) d : hSet) e A) =
    transportf (fun d => nat_trans (yoneda _ hsC d : functor _ _) F) e (yy A).
Proof.
  induction e.
  apply idpath.
Defined.

Lemma forall_isotid (A : precategory) (a_is : is_univalent A)
      (a a' : A) (P : iso a a' -> UU)
  : (∏ e, P (idtoiso e)) → ∏ i, P i.
Proof.
  intros H i.
  rewrite <- (idtoiso_isotoid _ a_is).
  apply H.
Defined.

Lemma transportf_isotoid_functor
      (A X : precategory) (H : is_univalent A)
      (K : functor A X)
      (a a' : A) (p : iso a a') (b : X) (f : K a --> b)
  : transportf (fun a0 => K a0 --> b) (isotoid _ H p) f = (#K)%cat (inv_from_iso p) · f.
Proof.
  rewrite functor_on_inv_from_iso. simpl. cbn.
  unfold precomp_with. rewrite id_right.
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

Lemma inv_from_iso_iso_from_fully_faithful_reflection {C D : precategory}
      (F : functor C D) (HF : fully_faithful F) (a b : C) (i : iso (F a) (F b))
  : inv_from_iso
      (iso_from_fully_faithful_reflection HF i) =
    iso_from_fully_faithful_reflection HF (iso_inv_from_iso i).
Proof.
  cbn.
  unfold precomp_with.
  apply id_right.
Defined.

Section CwFIsAProp.
  Context {C : category}
          {Ty Tm : opp_precat_data C ⟶ SET}
          (pp : Tm ⟹ Ty)
          (HC : is_univalent C).

  Definition cwf_fiber_rep_data {Γ:C} (A : Ty Γ : hSet) : UU
    := ∑ (ΓA : C), C ⟦ΓA, Γ⟧ × (Tm ΓA : hSet).

  Definition cwf_fiber_rep_ax
             {Γ:C} {A : Ty Γ : hSet}
             (ΓAπt : cwf_fiber_rep_data A) : UU
    := ∑ (H : pp _ (pr2 (pr2 ΓAπt)) = (#Ty)%cat (pr1 (pr2 ΓAπt)) A),
       isPullback _ _ _ _ (cwf_square_comm pp H).

  Definition cwf_fiber_representation' {Γ:C} (A : Ty Γ : hSet) : UU
    := ∑ ΓAπt : cwf_fiber_rep_data A, cwf_fiber_rep_ax ΓAπt.

  Lemma isaprop_cwf_fiber_representation' {Γ:C} (A : Ty Γ : hSet)
    : is_univalent C -> isaprop (cwf_fiber_representation' A).
  Proof.
    intro isC.
    apply invproofirrelevance.
    intros x x'. apply subtypeEquality.
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
    - set (T1 := mk_Pullback _ _ _ _ _ _ isP).
      set (T2 := mk_Pullback _ _ _ _ _ _ isP').
      set (i := iso_from_Pullback_to_Pullback T1 T2). cbn in i.
      set (i' := invmap (weq_ff_functor_on_iso (yoneda_fully_faithful _ _ ) _ _ ) i ).
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
        cbn. unfold precomp_with.
        rewrite id_right.
        unfold from_Pullback_to_Pullback.
        cbn in *.
        match goal with |[|- (_  ( _ ?PP _ _ _  _ ) )  _ _ · _ = _ ] =>
                         set (P:=PP) end.
        match goal with |[|- ( _ (PullbackArrow _ ?PP ?E2 ?E3 _ )) _ _ · _ = _ ]
                         => set (E1 := PP);
                              set (e1 := E1);
                              set (e2 := E2);
                              set (e3 := E3) end.
        match goal with |[|- ( _ (PullbackArrow _ _ _ _ ?E4 )) _ _ · _ = _ ]
                         => set (e4 := E4) end.
        assert (XR := PullbackArrow_PullbackPr1 P e1 e2 e3 e4).
        assert (XR':= nat_trans_eq_pointwise XR ΓA').
        cbn in XR'.
        assert (XR'':= toforallpaths _ _  _ XR').
        cbn in XR''.
        etrans. apply XR''.
        apply id_left.
      + unfold TT; clear TT.
        match goal with |[|- transportf ?r  _ _ = _ ] => set (P:=r) end.
        match goal with |[|- transportf _ (_ _ _ (_ _ ?ii)) _ = _ ] => set (i:=ii) end.
        simpl in i.
        apply (invmaponpathsweq (@yy _ (homset_property _ ) Tm ΓA')).
        etrans. apply transportf_yy.
        etrans. apply transportf_isotoid_functor.
        rewrite inv_from_iso_iso_from_fully_faithful_reflection.
        assert (XX:=homotweqinvweq (weq_from_fully_faithful
                                      (yoneda_fully_faithful _ (homset_property C)) ΓA' ΓA )).
        etrans. apply maponpaths_2. apply XX.
        clear XX.
        etrans. apply maponpaths_2. apply id_right.
        etrans. apply maponpaths_2. unfold from_Pullback_to_Pullback. apply idpath.
        match goal with |[|- ( _ ?PP _ _ _  _ ) · _ = _ ] =>
                         set (PT:=PP) end.
        match goal with |[|- PullbackArrow _ ?PP ?E2 ?E3 _ · _ = _ ]
                         => set (E1 := PP);
                              set (e1 := E1);
                              set (e2 := E2);
                              set (e3 := E3) end.
        match goal with |[|- PullbackArrow _ _ _ _ ?E4 · _ = _ ]
                         => set (e4 := E4) end.
        apply (PullbackArrow_PullbackPr2 PT e1 e2 e3 e4).
  Qed.

  Definition isaprop_cwf_fiber_representation {Γ : C} (A : Ty Γ : hSet)
    : isaprop (cwf_fiber_representation pp A).
  Proof.
    simple refine (isofhlevelweqb _ _ _).
    - exact (cwf_fiber_representation' A).
    - unfold cwf_fiber_representation, cwf_fiber_representation'.
      admit.
    - apply isaprop_cwf_fiber_representation'.
      exact HC.
  Admitted.

  Definition isaprop_cwf_representation
    : isaprop cwf_representation.
  Proof.
    do 2 (apply impred ; intro).
    apply isaprop_cwf_fiber_representation.
  Defined.




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
