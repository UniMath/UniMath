(** **********************************************************

Contents:

- Construction of a substitution system from an initial algebra Proof that the substitution system
- Constructed from an initial algebra is an initial substitution system

This file differs from LiftingInitial.v in the hypotheses. Here we use omega cocontinuity instead of
Kan extensions.

Written by: Anders Mörtberg, 2016 (adapted from LiftingInitial.v)

************************************************************)

Set Kernel Term Sharing.

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration_alt.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.Notation.

Local Open Scope cat.

Local Coercion alg_carrier : algebra_ob >-> ob.

Section category_Algebra.

Variables (C : precategory) (hsC : has_homsets C) (CP : BinCoproducts C).
Variables (IC : Initial C) (CC : Colims_of_shape nat_graph C).
Variables (H : Signature C hsC C hsC) (HH : is_omega_cocont H).

Local Notation "'EndC'":= ([C, C, hsC]) .
Local Notation "'Ptd'" := (precategory_Ptd C hsC).

Let hsEndC : has_homsets EndC := functor_category_has_homsets C C hsC.
Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CP hsC.
Let EndEndC := [EndC, EndC, hsEndC].
Let CPEndEndC:= BinCoproducts_functor_precat _ _ CPEndC hsEndC: BinCoproducts EndEndC.
Let θ := theta H.

Definition Const_plus_H (X : EndC) : functor EndC EndC
  := BinCoproduct_of_functors _ _ CPEndC (constant_functor _ _ X) H.

Definition Id_H :  functor [C, C, hsC] [C, C, hsC]
 := Const_plus_H (functor_identity _ : EndC).

Let Alg : precategory := FunctorAlg Id_H hsEndC.

Let InitialEndC : Initial EndC.
Proof.
apply Initial_functor_precat, IC.
Defined.

Let Colims_of_shape_nat_graph_EndC : Colims_of_shape nat_graph EndC.
Proof.
apply ColimsFunctorCategory_of_shape, CC.
Defined.

Lemma is_omega_cocont_Id_H : is_omega_cocont Id_H.
Proof.
apply is_omega_cocont_BinCoproduct_of_functors; try apply functor_category_has_homsets.
- apply is_omega_cocont_constant_functor, functor_category_has_homsets.
- apply HH.
Defined.

Definition InitAlg : Alg :=
  InitialObject (colimAlgInitial hsEndC InitialEndC is_omega_cocont_Id_H (Colims_of_shape_nat_graph_EndC _)).

Lemma isInitial_pre_comp (Z : Ptd) : isInitial [C, C, hsC] (ℓ (U Z) InitialEndC).
Proof.
use mk_isInitial; intros F.
mkpair.
- mkpair.
  + intros c; simpl; apply InitialArrow.
  + abstract (intros x y f; cbn; apply InitialArrowEq).
- abstract (intros G; apply subtypeEquality;
    [ intros x; apply isaprop_is_nat_trans,hsC
    | apply funextsec; intro c; apply InitialArrowUnique]).
Defined.

Local Lemma HU (Z : Ptd) : is_omega_cocont (pre_composition_functor C C C hsC hsC (U Z)).
Proof.
apply is_omega_cocont_pre_composition_functor, CC.
Defined.

Definition SpecializedGMIt (Z : Ptd) (X : EndC) :
  ∏ (G : functor [C, C, hsC] [C, C, hsC]) (ρ : [C, C, hsC] ⟦ G X, X ⟧)
    (θ : functor_composite Id_H (ℓ (U Z)) ⟹ functor_composite (ℓ (U Z)) G),
  ∃! h : [C, C, hsC] ⟦ ℓ (U Z) (alg_carrier _ InitAlg), X ⟧,
    # (ℓ (U Z)) (alg_map Id_H InitAlg) · h =
    θ (alg_carrier _ InitAlg) · # G h · ρ
  := SpecialGenMendlerIteration hsEndC InitialEndC Colims_of_shape_nat_graph_EndC
                                Id_H is_omega_cocont_Id_H hsEndC X (ℓ (U Z)) (isInitial_pre_comp Z) (HU Z).

Definition θ_in_first_arg (Z: Ptd)
  : functor_fix_snd_arg [C, C,hsC] Ptd [C, C, hsC] (θ_source H) Z
    ⟹
    functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_target H) Z
  := nat_trans_fix_snd_arg _ _ _ _ _ θ Z.


Local Lemma aux_iso_1_is_nat_trans (Z : Ptd) :
   is_nat_trans
     (functor_composite Id_H (ℓ (U Z)))
     (pr1 (BinCoproductObject EndEndC
        (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
           (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_source H) Z))))
     (λ X : [C, C, hsC],
      BinCoproductOfArrows [C, C, hsC]
        (CPEndC (functor_composite (U Z) (functor_identity C))
           ((θ_source H) (X ⊗ Z))) (CPEndC (U Z) ((θ_source H) (X ⊗ Z)))
        (ρ_functor (U Z)) (nat_trans_id ((θ_source H) (X ⊗ Z):functor C C))).
Proof.
intros X X' α.
apply (nat_trans_eq hsC); intro c; simpl.
eapply pathscomp0; [apply BinCoproductOfArrows_comp |].
eapply pathscomp0; [|eapply pathsinv0, BinCoproductOfArrows_comp]; simpl.
now rewrite functor_id, !id_left, !id_right.
Qed.

Definition aux_iso_1 (Z : Ptd)
  : EndEndC
    ⟦ functor_composite Id_H (ℓ (U Z)),
      BinCoproductObject EndEndC
           (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
              (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_source H) Z))⟧.
Proof.
mkpair.
- intro X.
  exact (BinCoproductOfArrows EndC (CPEndC _ _) (CPEndC _ _) (ρ_functor (U Z))
           (nat_trans_id (θ_source H (X⊗Z):functor C C))).
- exact (aux_iso_1_is_nat_trans Z).
Defined.

Local Lemma aux_iso_1_inv_is_nat_trans (Z : Ptd) :
   is_nat_trans
     (pr1 (BinCoproductObject EndEndC
        (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
           (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_source H) Z))) )
     (functor_composite Id_H (ℓ (U Z)))
     (λ X : [C, C, hsC],
      BinCoproductOfArrows [C, C, hsC]
        (CPEndC (functor_composite (functor_identity C) (U Z))
           ((θ_source H) (X ⊗ Z))) (CPEndC (U Z) ((θ_source H) (X ⊗ Z)))
        (λ_functor (U Z)) (nat_trans_id ((θ_source H) (X ⊗ Z):functor C C))).
Proof.
intros X X' α.
apply (nat_trans_eq hsC); intro c; simpl.
eapply pathscomp0;[apply BinCoproductOfArrows_comp|].
eapply pathscomp0;[|eapply pathsinv0, BinCoproductOfArrows_comp]; simpl.
now rewrite functor_id, !id_left, !id_right.
Qed.

Local Definition aux_iso_1_inv (Z: Ptd)
  : EndEndC
    ⟦ BinCoproductObject EndEndC
           (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
              (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_source H) Z)),
      functor_composite Id_H (ℓ (U Z)) ⟧.
Proof.
mkpair.
- intro X.
  exact (BinCoproductOfArrows EndC (CPEndC _ _) (CPEndC _ _) (λ_functor (U Z))
         (nat_trans_id (θ_source H (X⊗Z):functor C C))).
- exact (aux_iso_1_inv_is_nat_trans Z).
Defined.

Local Lemma aux_iso_2_inv_is_nat_trans (Z : Ptd) :
   is_nat_trans
     (pr1 (BinCoproductObject EndEndC
        (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
           (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC](θ_target H) Z))) )
     (functor_composite (ℓ (U Z))
        (Const_plus_H (U Z)))
     (λ X : [C, C, hsC],
      nat_trans_id
        (BinCoproductObject [C, C, hsC] (CPEndC (U Z) ((θ_target H) (X ⊗ Z)))
         :functor C C)).
Proof.
intros X X' α.
rewrite id_left, id_right.
apply (nat_trans_eq hsC); intro c; simpl.
unfold coproduct_nat_trans_data; simpl.
unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
apply BinCoproductOfArrows_eq; trivial.
unfold functor_fix_snd_arg_mor; simpl.
unfold θ_target_mor; simpl.
revert c; apply nat_trans_eq_pointwise, maponpaths.
apply (nat_trans_eq hsC); intro c; simpl.
now rewrite <- (nat_trans_ax α), functor_id, id_left.
Qed.

Local Definition aux_iso_2_inv (Z : Ptd)
  : EndEndC
    ⟦ BinCoproductObject EndEndC
         (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
                    (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_target H) Z)),
      functor_composite (ℓ (U Z) )   (Const_plus_H (U Z)) ⟧.
Proof.
mkpair.
- intro X.
  exact (nat_trans_id ((@BinCoproductObject EndC (U Z) (θ_target H (X⊗Z)) (CPEndC _ _) )
           : functor C C)).
- exact (aux_iso_2_inv_is_nat_trans Z).
Defined.

Definition θ'_Thm15 (Z: Ptd)
  : EndEndC
    ⟦ BinCoproductObject EndEndC
        (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
           (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_source H) Z)),
      BinCoproductObject EndEndC
        (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
            (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_target H) Z)) ⟧
  := BinCoproductOfArrows
   EndEndC (CPEndEndC _ _) (CPEndEndC _ _)
   (identity (constant_functor EndC _ (U Z): functor_precategory EndC EndC hsEndC))
   (θ_in_first_arg Z).

Definition ρ_Thm15 (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧)
  : [C, C, hsC] ⟦ BinCoproductObject [C, C, hsC] (CPEndC (U Z) (H `InitAlg)), `InitAlg ⟧
  := @BinCoproductArrow
   EndC _ _  (CPEndC (U Z)
   (H (alg_carrier _ InitAlg))) (alg_carrier _ InitAlg) (#U f)
   (BinCoproductIn2 _ (CPEndC _ _) · (alg_map _ InitAlg)).


Definition SpecializedGMIt_Thm15 (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧)
  : ∃! h : [C, C, hsC]
              ⟦ ℓ (U Z) (pr1 InitAlg),
              pr1 InitAlg ⟧,
       # (ℓ (U Z)) (alg_map Id_H InitAlg) · h =
       pr1 (aux_iso_1 Z · θ'_Thm15 Z · aux_iso_2_inv Z)
         (pr1 InitAlg) ·
       # (Const_plus_H (U Z)) h · ρ_Thm15 Z f :=
   (SpecializedGMIt Z (pr1 InitAlg) (Const_plus_H (U Z))
     (ρ_Thm15 Z f) (aux_iso_1 Z · θ'_Thm15 Z · aux_iso_2_inv Z)).

Definition bracket_Thm15 (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧)
  : [C, C, hsC]
       ⟦ ℓ (U Z) (pr1 InitAlg), pr1 InitAlg ⟧
  := pr1 (pr1 (SpecializedGMIt_Thm15 Z f)).

Notation "⦃ f ⦄" := (bracket_Thm15 _ f) (at level 0).

(* we prove the individual components for ease of compilation *)
Lemma bracket_Thm15_ok_part1 (Z : Ptd) (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
 # U f = # (pr1 (ℓ (U Z))) (η InitAlg) · ⦃f⦄.
Proof.
apply (nat_trans_eq hsC); intro c.
assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 Z f))).
assert (h_eq' := maponpaths (λ m,
               (((aux_iso_1_inv Z):(_⟹_)) _)· m) h_eq); clear h_eq.
assert (h_eq1' := maponpaths (λ m,
               (BinCoproductIn1 EndC (CPEndC _ _))· m) h_eq'); clear h_eq'.
assert (h_eq1'_inst := nat_trans_eq_pointwise h_eq1' c); clear h_eq1'.
eapply pathscomp0, pathscomp0; [|apply (!h_eq1'_inst)|]; clear h_eq1'_inst.
- apply BinCoproductIn1Commutes_right_in_ctx_dir; simpl.
  rewrite id_left, <- !assoc.
  apply BinCoproductIn1Commutes_right_in_ctx_dir; simpl.
  rewrite !id_left, !(@id_left EndC).
  now apply BinCoproductIn1Commutes_right_in_ctx_dir,
            BinCoproductIn1Commutes_right_in_ctx_dir,
            BinCoproductIn1Commutes_right_dir.
- apply BinCoproductIn1Commutes_left_in_ctx_dir; simpl.
  now rewrite id_left, assoc.
Qed.

(* produce some output to keep TRAVIS running *)
Check bracket_Thm15_ok_part1.

Lemma bracket_Thm15_ok_part2 (Z : Ptd) (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
  (theta H) ((alg_carrier _ InitAlg) ⊗ Z) ·  # H ⦃f⦄ · τ InitAlg =
  # (pr1 (ℓ (U Z))) (τ InitAlg) · ⦃f⦄.
Proof.
apply (nat_trans_eq hsC); intro c.
assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 Z f))).
assert (h_eq' := maponpaths (λ m,
                (((aux_iso_1_inv Z):(_⟹_)) _)· m) h_eq); clear h_eq.
(* until here same as in previous lemma *)
assert (h_eq2' := maponpaths (λ m,
                (BinCoproductIn2 EndC (CPEndC _ _))· m) h_eq');  clear h_eq'.
assert (h_eq2'_inst := nat_trans_eq_pointwise h_eq2' c); clear h_eq2'.
eapply pathscomp0, pathscomp0; [|apply (!h_eq2'_inst)|]; clear h_eq2'_inst.
- apply BinCoproductIn2Commutes_right_in_ctx_dir; simpl.
  rewrite id_right, id_left, <- !assoc.
  apply BinCoproductIn2Commutes_right_in_ctx_dir; simpl.
  rewrite id_left.
  apply BinCoproductIn2Commutes_right_in_ctx_dir.
  apply BinCoproductIn2Commutes_right_in_double_ctx_dir.
  rewrite <- assoc; apply maponpaths.
  apply pathsinv0; simpl.
  rewrite <- assoc; apply maponpaths.
  now apply BinCoproductIn2Commutes.
- apply BinCoproductIn2Commutes_left_in_ctx_dir.
  now rewrite id_left; apply assoc.
Qed.

(* produce some output to keep TRAVIS running *)
Check bracket_Thm15_ok_part2.

Lemma bracket_Thm15_ok (Z : Ptd) (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
  bracket_property_parts f ⦃f⦄.
Proof.
split.
+ exact (bracket_Thm15_ok_part1 Z f).
+ exact (bracket_Thm15_ok_part2 Z f).
Qed.

Lemma bracket_Thm15_ok_cor (Z : Ptd) (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
 bracket_property f (bracket_Thm15 Z f).
Proof.
now apply whole_from_parts, bracket_Thm15_ok.
Qed.

Local Lemma bracket_unique (Z : Ptd) (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
 ∏ t : ∑ h : [C, C, hsC] ⟦ functor_composite (U Z) (pr1  InitAlg),
                            pr1 InitAlg ⟧, bracket_property f h,
   t = tpair _ ⦃f⦄ (bracket_Thm15_ok_cor Z f).
Proof.
intros [h' h'_eq]; apply subtypeEquality; [intro; apply (isaset_nat_trans hsC)|].
simpl; apply parts_from_whole in h'_eq.
apply path_to_ctr, (nat_trans_eq hsC); intro c.
simpl; rewrite !(@id_left EndC), id_right, <- !assoc.
eapply pathscomp0; [| eapply pathsinv0, postcompWithBinCoproductArrow].
apply BinCoproductArrowUnique.
+ destruct h'_eq as [h'_eq1 _]; simpl.
  rewrite id_left, assoc.
  eapply pathscomp0; [eapply pathsinv0, (nat_trans_eq_pointwise h'_eq1 c)|].
  now apply BinCoproductIn1Commutes_right_in_ctx_dir,
            BinCoproductIn1Commutes_right_in_ctx_dir,
            BinCoproductIn1Commutes_right_dir.
+ destruct h'_eq as [_ h'_eq2].
  rewrite assoc.
  eapply pathscomp0; [eapply pathsinv0, (nat_trans_eq_pointwise h'_eq2 c)|].
  apply BinCoproductIn2Commutes_right_in_ctx_dir.
  apply BinCoproductIn2Commutes_right_in_double_ctx_dir.
  simpl; rewrite <- !assoc.
  now apply maponpaths, maponpaths, pathsinv0, BinCoproductIn2Commutes.
Qed.

Definition bracket_for_InitAlg : bracket InitAlg.
Proof.
intros Z f.
mkpair.
- mkpair.
  + exact (bracket_Thm15 Z f).
  + exact (bracket_Thm15_ok_cor Z f).
    (* B: better to prove the whole outside, and apply it here *)
    (* when the first components were not opaque, the following proof
       became extremely slow *)
- apply bracket_unique.
Defined.

(* produce some output to keep TRAVIS running *)
Check bracket_for_InitAlg.

Definition InitHSS : hss_precategory CP H.
Proof.
 (*
  red. (* FORBIDDEN, otherwise universe problem when checking the definition *)
  unfold hss_precategory; simpl.
*)
exists InitAlg.
exact bracket_for_InitAlg.
Defined.

Local Definition Ghat : EndEndC := Const_plus_H (pr1 InitAlg).

Definition constant_nat_trans (C' D : precategory)
   (hsD : has_homsets D) (d d' : D) (m : D⟦d,d'⟧)
    : [C', D, hsD] ⟦constant_functor C' D d, constant_functor C' D d'⟧.
Proof.
exists (λ _, m).
abstract (intros ? ? ?; pathvia m; [ apply id_left | apply pathsinv0, id_right]).
Defined.

Definition thetahat_0 (Z : Ptd) (f : Z --> ptd_from_alg InitAlg) :
  EndEndC
  ⟦ BinCoproductObject EndEndC
      (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (U Z))
         (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_source H) Z)),
    BinCoproductObject EndEndC
      (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (pr1 InitAlg))
                 (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_target H) Z)) ⟧.
Proof.
exact (BinCoproductOfArrows EndEndC (CPEndEndC _ _) (CPEndEndC _ _)
                           (constant_nat_trans _ _ hsEndC _ _ (#U f))
                           (θ_in_first_arg Z)).
Defined.

Local Definition iso1' (Z : Ptd) : EndEndC ⟦ functor_composite Id_H (ℓ (U Z)),
 BinCoproductObject _
    (CPEndEndC (constant_functor _ _  (U Z)) (functor_fix_snd_arg _ _ _ (θ_source H) Z)) ⟧.
Proof.
exact (aux_iso_1 Z).
Defined.

Local Lemma is_nat_trans_iso2' (Z : Ptd) :
   is_nat_trans
     (pr1 (BinCoproductObject EndEndC
        (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (pr1 InitAlg))
           (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_target H) Z))))
     (functor_composite (ℓ (U Z)) Ghat)
     (λ X : [C, C, hsC],
      nat_trans_id
        (BinCoproductObject [C, C, hsC]
           (CPEndC
              ((constant_functor [C, C, hsC] [C, C, hsC] (pr1 InitAlg)) X)
              ((θ_target H) (X ⊗ Z)))
         :functor C C)).
Proof.
intros X X' α.
rewrite id_left, id_right.
apply (nat_trans_eq hsC); intro c; simpl.
unfold coproduct_nat_trans_data; simpl.
unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
apply BinCoproductOfArrows_eq; trivial.
unfold functor_fix_snd_arg_mor; simpl.
unfold θ_target_mor; simpl.
revert c; apply nat_trans_eq_pointwise, maponpaths.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite <- (nat_trans_ax α), functor_id.
now apply id_left.
Qed.

Local Definition iso2' (Z : Ptd) : EndEndC ⟦
  BinCoproductObject EndEndC
  (CPEndEndC (constant_functor [C, C, hsC] [C, C, hsC] (pr1 InitAlg))
             (functor_fix_snd_arg [C, C, hsC] Ptd [C, C, hsC] (θ_target H) Z)),
  functor_composite (ℓ (U Z)) Ghat ⟧.
Proof.
mkpair.
- intro X.
  exact (nat_trans_id ((@BinCoproductObject EndC _ (θ_target H (X⊗Z)) (CPEndC _ _) )
            : functor C C)).
- exact (is_nat_trans_iso2' Z).
Defined.

Definition thetahat (Z : Ptd) (f : Z --> ptd_from_alg InitAlg)
           : EndEndC ⟦ functor_composite Id_H (ℓ (U Z)),
                       functor_composite (ℓ (U Z)) (Ghat) ⟧.
Proof.
exact (iso1' Z · thetahat_0 Z f · iso2' Z).
Defined.


Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Let Yon (X : EndC) : functor EndC^op HSET := yoneda_objects EndC hsEndC X.

Definition Phi_fusion (Z : Ptd) (X : EndC) (b : pr1 InitAlg --> X) :
  functor_composite (functor_opp (ℓ (U Z))) (Yon (pr1 InitAlg))
   ⟹
  functor_composite (functor_opp (ℓ (U Z))) (Yon X) .
Proof.
mkpair.
- intros Y a.
  exact (a · b).
- abstract (intros ? ? ?; simpl; apply funextsec; intro;
            unfold yoneda_objects_ob; simpl; unfold compose; simpl;
            apply (nat_trans_eq hsC); simpl; intros ?;
            apply pathsinv0, assoc).
Defined.

Let IA := colimAlgInitial hsEndC InitialEndC is_omega_cocont_Id_H (Colims_of_shape_nat_graph_EndC _).

Lemma ishssMor_InitAlg (T' : hss CP H) :
  @ishssMor C hsC CP H InitHSS T'
           (InitialArrow IA (pr1 T') : @algebra_mor EndC Id_H InitAlg T' ).
Proof.
intros Z f.
set (β0 := InitialArrow IA (pr1 T')).
match goal with | [|- _ · ?b = _ ] => set (β := b) end.
set (rhohat := BinCoproductArrow EndC  (CPEndC _ _ )  β (tau_from_alg T')
                :  pr1 Ghat T' --> T').
set (X:= SpecializedGMIt Z _ Ghat rhohat (thetahat Z f)).
pathvia (pr1 (pr1 X)).
- set (TT := @fusion_law EndC hsEndC InitialEndC Colims_of_shape_nat_graph_EndC
                         Id_H is_omega_cocont_Id_H _ hsEndC (pr1 (InitAlg)) T').
  set (Psi := ψ_from_comps (Id_H) hsEndC _ (ℓ (U Z)) (Const_plus_H (U Z)) (ρ_Thm15 Z f)
                             (aux_iso_1 Z · θ'_Thm15 Z · aux_iso_2_inv Z) ).
  set (T2 := TT _ (HU Z) (isInitial_pre_comp Z) Psi).
  set (T3 := T2 (ℓ (U Z)) (HU Z)).
  set (Psi' := ψ_from_comps (Id_H) hsEndC _ (ℓ (U Z)) (Ghat) (rhohat)
                           (iso1' Z · thetahat_0 Z f · iso2' Z) ).
  set (T4 := T3 (isInitial_pre_comp Z) Psi').
  set (Φ := (Phi_fusion Z T' β)).
  set (T5 := T4 Φ).
  pathvia (Φ _ (fbracket InitHSS f)); trivial.
  eapply pathscomp0; [|apply T5]; clear TT T2 T3 T4 T5 X.
  * now apply cancel_postcomposition.
  * (* hypothesis of fusion law *)
    apply funextsec; intro t.
    apply (nat_trans_eq hsC); intro c; simpl.
    rewrite !id_right.
    (* should be decomposed into two diagrams *)
    apply BinCoproductArrow_eq_cor.
    + (* first diagram *)
      rewrite <- !assoc.
      apply BinCoproductIn1Commutes_left_in_ctx_dir, BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl; rewrite id_left.
      apply BinCoproductIn1Commutes_left_in_ctx_dir, BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl; rewrite id_left.
      apply BinCoproductIn1Commutes_left_in_ctx_dir.
      simpl; rewrite id_left.
      apply BinCoproductIn1Commutes_left_in_ctx_dir.
      rewrite <- assoc.
      apply maponpaths, BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl; rewrite id_left.
      now apply BinCoproductIn1Commutes_right_dir.
    + (* second diagram *)
      rewrite <- !assoc.
      apply BinCoproductIn2Commutes_left_in_ctx_dir, BinCoproductIn2Commutes_right_in_ctx_dir.
      simpl; rewrite id_left.
      apply BinCoproductIn2Commutes_left_in_ctx_dir, BinCoproductIn2Commutes_right_in_ctx_dir.
      simpl; rewrite <- !assoc.
      apply maponpaths, BinCoproductIn2Commutes_left_in_ctx_dir, BinCoproductIn2Commutes_right_in_ctx_dir.
      simpl.
      rewrite <- !assoc.
      eapply pathscomp0;
        [| eapply pathsinv0, cancel_postcomposition,
           (nat_trans_eq_pointwise (functor_comp H t β) c)].
      simpl; rewrite <- assoc.
      apply maponpaths, BinCoproductIn2Commutes_left_in_ctx_dir.
      assert (Hyp_c := nat_trans_eq_pointwise (τ_part_of_alg_mor _ hsC CP _ _ _ (InitialArrow IA (pr1 T'))) c).
      simpl in Hyp_c.
      eapply pathscomp0; [eapply pathsinv0, Hyp_c|].
      now apply maponpaths, pathsinv0, BinCoproductIn2Commutes.
  - apply pathsinv0, path_to_ctr.
    (* now a lot of serious verification work to be done *)
    apply (nat_trans_eq hsC); intro c.
    simpl; rewrite id_right.
    (* look at type: *)
    (*  match goal with | [ |- ?l = _ ] => let ty:= (type of l) in idtac ty end. *)
    apply BinCoproductArrow_eq_cor.
    + rewrite <- !assoc.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl; rewrite id_left.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl; rewrite <- assoc.
      eapply pathscomp0;
        [| apply maponpaths, BinCoproductIn1Commutes_right_in_ctx_dir; simpl;
           rewrite id_left; apply BinCoproductIn1Commutes_right_dir, idpath].
      rewrite !assoc.
      assert (fbracket_η_inst_c := nat_trans_eq_pointwise (fbracket_η T' (f· ptd_from_alg_mor _ hsC CP H β0)) c).
      eapply pathscomp0; [| apply (!fbracket_η_inst_c)].
      apply cancel_postcomposition, (ptd_mor_commutes _ (ptd_from_alg_mor _ hsC CP H β0) ((pr1 Z) c)).
    + (* now the difficult case *)
      repeat rewrite <- assoc.
      apply BinCoproductIn2Commutes_right_in_ctx_dir.
      simpl.
      unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data, coproduct_nat_trans_data.
      rewrite id_left.
      apply BinCoproductIn2Commutes_right_in_ctx_dir.
      unfold nat_trans_fix_snd_arg_data.
      simpl.
      unfold coproduct_nat_trans_in2_data.
      repeat rewrite <- assoc.
      eapply pathscomp0. Focus 2.
        apply maponpaths.
        apply BinCoproductIn2Commutes_right_in_ctx_dir.
        rewrite <- assoc.
        apply maponpaths.
        apply BinCoproductIn2Commutes_right_dir.
        apply idpath.
      do 2 rewrite assoc.
      eapply pathscomp0.
        apply cancel_postcomposition.
        eapply pathsinv0.
        assert (τ_part_of_alg_mor_inst := τ_part_of_alg_mor _ hsC CP H _ _ β0).
        assert (τ_part_of_alg_mor_inst_Zc :=
                  nat_trans_eq_pointwise τ_part_of_alg_mor_inst ((pr1 Z) c));
          clear τ_part_of_alg_mor_inst.
        apply τ_part_of_alg_mor_inst_Zc.
      simpl.
      unfold coproduct_nat_trans_in2_data.
      repeat rewrite <- assoc.
      eapply pathscomp0.
        apply maponpaths.
        rewrite assoc.
        eapply pathsinv0.
        assert (fbracket_τ_inst := fbracket_τ T' (f· ptd_from_alg_mor _ hsC CP H β0)).
        assert (fbracket_τ_inst_c := nat_trans_eq_pointwise fbracket_τ_inst c); clear fbracket_τ_inst.
        apply fbracket_τ_inst_c.
      simpl.
      unfold coproduct_nat_trans_in2_data.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      assert (Hyp:
                 ((# (pr1 (ℓ(U Z))) (# H β))·
                 (theta H) ((alg_carrier _  T') ⊗ Z)·
                 # H (fbracket T' (f· ptd_from_alg_mor C hsC CP H β0))
                 =
                 θ (tpair (λ _ : functor C C, ptd_obj C) (alg_carrier _ (InitialObject IA)) Z) ·
                 # H (# (pr1 (ℓ(U Z))) β ·
                 fbracket T' (f· ptd_from_alg_mor C hsC CP H β0)))).
      Focus 2.
      assert (Hyp_c := nat_trans_eq_pointwise Hyp c); clear Hyp.
      exact Hyp_c.
      clear c. clear X. clear rhohat.
      rewrite (functor_comp H).
      rewrite assoc.
      apply cancel_postcomposition.
      apply (nat_trans_eq hsC); intro c.
      assert (θ_nat_1_pointwise_inst := θ_nat_1_pointwise _ hsC _ hsC H θ _ _ β Z c).
      eapply pathscomp0 ; [exact θ_nat_1_pointwise_inst | ].
      clear θ_nat_1_pointwise_inst.
      simpl.
      apply maponpaths.
      assert (Hyp: # H (β ∙∙ nat_trans_id (pr1 Z)) = # H (# (pr1 (ℓ(U Z))) β)).
      { apply maponpaths, (nat_trans_eq hsC); intro c'; simpl.
        now rewrite functor_id, id_right. }
      now apply (nat_trans_eq_pointwise Hyp c).
Qed.

Definition hss_InitMor : ∏ T' : hss CP H, hssMor InitHSS T'.
Proof.
intro T'.
exists (InitialArrow IA (pr1 T')).
apply ishssMor_InitAlg.
Defined.

Lemma hss_InitMor_unique (T' : hss_precategory CP H):
  ∏ t : hss_precategory CP H ⟦ InitHSS, T' ⟧, t = hss_InitMor T'.
Proof.
intro t.
apply (invmap (hssMor_eq1 _ _ _ _ _ _ _ _ )).
apply (@InitialArrowUnique _ IA (pr1 T') (pr1 t)).
Qed.

Lemma isInitial_InitHSS : isInitial (hss_precategory CP H) InitHSS.
Proof.
use mk_isInitial; intro T.
exists (hss_InitMor T).
apply hss_InitMor_unique.
Defined.


Lemma InitialHSS : Initial (hss_precategory CP H).
Proof.
apply (mk_Initial InitHSS), isInitial_InitHSS.
Defined.

End category_Algebra.
