(**

Reference : "Initial Semantics for Strengthened Signatures" (André Hirschowitz , Marco Maggesi)

Let (H, θ) be a strengthened signature, M an endo-functor.
If M has a structure of (left) module over a monad T, then it can be lifted to endow
H(M) with a structure of module over T.

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.


Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.CategoryTheory.LModules.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.HorizontalComposition.

(* Require Import UniMath.CategoryTheory.PrecategoryBinProduct. *)
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

(** A monad is a pointed endofunctor *)
Definition ptd_from_mon {C:precategory} hsC (T:Monad C) : precategory_Ptd C hsC :=
  ((T:functor C C),, η T).

(** Let (Z, e : 1 -> Z) be a pointed endofunctor.
Then e is a morphism (actually the initial morphism) in the category of pointed endofunctors *)
Lemma is_ptd_mor_pt {C:precategory} hs (F:ptd_obj C) : is_ptd_mor _ (F:=id_Ptd C hs) (ptd_pt _ F).
Proof.
  intro c; apply id_left.
Qed.

Definition ptd_mor_pt {C:precategory} hs (F:ptd_obj C) : ptd_mor _ (id_Ptd C hs) F :=
  (ptd_pt _ F ,, is_ptd_mor_pt hs F).

Local Notation σ := (lm_mult _).

Section SignatureLiftModule.
  Variables (C:precategory) (hsC : has_homsets C)
            (D:precategory) (hsD : has_homsets D)
           (H : Signature C hsC D hsD).

  (** The forgetful functor from pointed endofunctors to endofunctors *)
  Local Notation "'U'" := (functor_ptd_forget C hsC).
  (** The precategory of pointed endofunctors on [C] *)
  Local Notation "'Ptd'" := (precategory_Ptd C hsC).
  (** The category of endofunctors on [C] *)
  Local Notation "'EndC'":= ([C, C, hsC]) .
  Variables (T:Monad C) (M: LModule T C).

  Local Notation Mf := (M : functor _ _).
  Local Notation "'p' T" := (ptd_from_mon hsC T) (at level 3).

  (** The pointed functor TT *)
  Let  T2 := (ptd_composite _ hsC (p T) (p T)) .

  (** The multiplication of a monad is a morphism of pointed endofunctors *)
  Lemma is_ptd_mor_μ : is_ptd_mor _ (F:= T2) (G:=p T)  (μ T).
  Proof.
    intro c.
    cbn.
    rewrite <- assoc.
    etrans; [|apply id_right].
    apply cancel_precomposition.
    apply Monad_law2.
  Qed.

  Definition ptd_mor_from_μ : ptd_mor _ T2 (p T) := (_ ,, is_ptd_mor_μ).


  Let strength_law1_pw M x   :=
    nat_trans_eq_pointwise
      (θ_Strength1_int_implies_θ_Strength1 _ _ _ _ _ _ (Sig_strength_law1 _ _ _ _ H ) M) x.

  (** A pointwise version of the second strength law with only one identity instead
of two α_functor *)
  Lemma strength_law2_pw :
    ∏ (X : EndC) (Z Z' : Ptd) x,
    ((theta H) (X ⊗ (Z p• Z')) : nat_trans _ _) x =
    ((theta H) (X ⊗ Z') •• (U Z):nat_trans _ _) x
      · ((theta H) ((functor_compose hsC hsC (U Z') X) ⊗ Z):nat_trans _ _) x
      · (# H (identity (functor_compose hsC hsC (U Z ∙ U Z') X)
          :
          [C, C, hsC] ⟦ functor_compose hsC hsC (U Z) (U Z' ∙ X : [C, C, hsC]),
          functor_compose hsC hsC (U Z ∙ U Z') X ⟧) : nat_trans _ _) x.
  Proof.
    intros X Z Z' x.
    etrans; revgoals.
    apply ( nat_trans_eq_pointwise (θ_Strength2_int_implies_θ_Strength2 _ _ _ _ _ _
                                           (Sig_strength_law2 _ _ _ _ H) X Z Z' _
           (identity _) ) x) .
    etrans;[eapply pathsinv0;apply id_right|].
    apply cancel_precomposition.
    eapply pathsinv0.
    etrans. eapply nat_trans_eq_pointwise.
    eapply (functor_id H).
    apply idpath.
  Qed.

  Local Notation θ_nat_2_pw := (θ_nat_2_pointwise _ _ _ _ H (theta H)).
  Local Notation θ_nat_1_pw := (θ_nat_1_pointwise _ _ _ _ H (theta H) ).


  (** The module multiplication is given by

         Θ_M,T        H(σ)
H(M) T ------> H(MT) ------> H(M)

   *)
  Local Definition lift_lm_mult : [C,D, hsD] ⟦  T ∙ H Mf, H Mf⟧ :=
    nat_trans_comp ((theta H) ((M : C ⟶ C),, ptd_from_mon hsC T)) (# H (σ M)).

  Local Definition lift_LModule_data : LModule_data T D :=
    tpair (fun x=> [C,D, hsD] ⟦  T ∙ x, x⟧) (H Mf) lift_lm_mult.

  Local Lemma lift_lm_mult_laws : LModule_laws _ lift_LModule_data.
  Proof.
    split.
    - intro c.
      etrans.
      apply assoc.
      etrans.
      apply cancel_postcomposition.
      eapply ( θ_nat_2_pw Mf (id_Ptd C hsC) (p T) (ptd_mor_pt hsC _) c).
      etrans.
      eapply cancel_postcomposition.
      rewrite (horcomp_pre_post _ _ (category_pair _ hsC )).
      rewrite (functor_comp H).
      etrans; [apply assoc|].
      apply cancel_postcomposition.
      apply strength_law1_pw.
      etrans;[|apply id_right].
      rewrite <- assoc.
      eapply cancel_precomposition.
      etrans.
      apply functor_comp_pw.
      etrans; [|apply (nat_trans_eq_pointwise (functor_id H Mf))].
      apply functor_cancel_pw.
      apply (nat_trans_eq hsC).
      eapply (LModule_law1).
    - intro c.
      cbn.
      etrans.
      rewrite assoc.
      apply cancel_postcomposition.
      etrans.
      apply (θ_nat_2_pw Mf _ _ (ptd_mor_from_μ)  c).
      apply cancel_postcomposition.
      apply (strength_law2_pw Mf (p T) (p T)).
      etrans; revgoals.
      rewrite <- assoc.
      apply cancel_precomposition.
      rewrite assoc;      apply cancel_postcomposition.
      eapply pathsinv0.
      apply (θ_nat_1_pw _ _ (σ M) (p T) c).
      cbn.
      repeat rewrite <- assoc.
      apply cancel_precomposition.
      apply cancel_precomposition.
      etrans; revgoals.
      eapply pathsinv0.
      apply (functor_comp_pw hsC hsD H).
      etrans.
      apply cancel_precomposition.
      apply (functor_comp_pw hsC hsD H).
      etrans.
      apply (functor_comp_pw hsC hsD H).
      apply functor_cancel_pw.
      apply (nat_trans_eq hsC).
      intro x.
      cbn.
      repeat rewrite id_left.
      rewrite functor_id,id_right.
      apply LModule_law2.
  Qed.

  Local Definition lift_lmodule : LModule T D := (lift_LModule_data,, lift_lm_mult_laws).
End SignatureLiftModule.


Section InitialRep.
  (** ** Some variables and assumptions *)

  (** Assume having a precategory [C] whose hom-types are sets *)
  Variable C : precategory.
  Variable hs : has_homsets C.

  Variable CP : BinCoproducts C.

  Local Notation "'EndC'":= ([C, C, hs]) .
  Let hsEndC : has_homsets EndC := functor_category_has_homsets C C hs.
  Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CP hs.

  Variable H : Signature C hs C hs.

  Let θ := theta H.

  Let θ_strength1_int := Sig_strength_law1 _ _ _ _ H.
  Let θ_strength2_int := Sig_strength_law2 _ _ _ _ H.

  Let Id_H
    : functor EndC EndC
    := BinCoproduct_of_functors _ _ CPEndC
                                (constant_functor _ _ (functor_identity _ : EndC))
                                H.

  Let Alg : precategory := FunctorAlg Id_H hsEndC.

  (** The precategory of pointed endofunctors on [C] *)
  Local Notation "'Ptd'" := (precategory_Ptd C hs).
  (** The category of endofunctors on [C] *)
  Local Notation "'EndC'":= ([C, C, hs]) .
  (** The product of two precategories *)

  Local Notation "'p' T" := (ptd_from_alg T) (at level 3).
  Local Notation "f ⊕ g" := (BinCoproductOfArrows _ (CPEndC _ _ ) (CPEndC _ _ ) f g) (at level 40).
  Local Notation η := @eta_from_alg.
  Require Import UniMath.CategoryTheory.limits.initial.

  Variable T : hss CP H.
  Local Notation T_mon := (Monad_from_hss _ _ _ _ T).
  Local Notation T_mod := (tautological_LModule T_mon).
  Local Notation HT_mod := (lift_lmodule _ _ _ _ H _ T_mod).
  Section TauModuleMorphism.

    Lemma τ_lmodule_laws : LModule_Mor_laws T_mon (T:=HT_mod) (T' := T_mod) (τ T).
    Admitted.

    Definition τ_lmodule_mor :  LModule_Mor  _ _ _ :=
      tpair (fun x => LModule_Mor_laws _ x) _ τ_lmodule_laws.
  End TauModuleMorphism.

  Section InitialRep.

    Variable initT : isInitial Alg (alg_from_hss _ _ _  _ T).
    Let T_init : Initial Alg := tpair (fun x => isInitial _ x) _ initT.

    Variable (M:Monad C).
    Local Notation M_mod := (tautological_LModule M).
    Local Notation HM_mod := (lift_lmodule _ _ _ _ H _ M_mod).
    Variable (τ_M: LModule_Mor M HM_mod M_mod).

    Let M_alg : Alg.
      eapply (tpair (fun x => EndC ⟦ Id_H x, x ⟧) (M:functor _ _)).
      (* Comment faire ??  *)
    Admitted.
  End InitialRep.


End TauModuleMorphism.