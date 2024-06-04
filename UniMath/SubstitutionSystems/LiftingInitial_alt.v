(** **********************************************************

Contents:

- Construction of a substitution system from an initial algebra
- Proof that the substitution system constructed from an initial algebra is an initial substitution system

This file differs from LiftingInitial.v in the hypotheses. Here we use omega cocontinuity instead of
Kan extensions.

Written by: Anders Mörtberg, 2016 (adapted from LiftingInitial.v)

************************************************************)

Set Kernel Term Sharing.

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration_alt.
Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.

Local Open Scope cat.

Local Coercion alg_carrier : algebra_ob >-> ob.

Section category_Algebra.

Context (C : category) (CP : BinCoproducts C)
        (IC : Initial C) (CC : Colims_of_shape nat_graph C).

Local Notation "'EndC'":= ([C, C]) .
Local Notation "'Ptd'" := (category_Ptd C).

Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CP.
Let EndEndC := [EndC, EndC].
Let CPEndEndC:= BinCoproducts_functor_precat _ _ CPEndC: BinCoproducts EndEndC.

Let InitialEndC : Initial EndC.
Proof.
apply Initial_functor_precat, IC.
Defined.

Let Colims_of_shape_nat_graph_EndC : Colims_of_shape nat_graph EndC.
Proof.
apply ColimsFunctorCategory_of_shape, CC.
Defined.

Section fix_an_H.

  Context (H : functor [C, C] [C, C]) (HH : is_omega_cocont H).

  Let Const_plus_H (X : EndC) : functor EndC EndC := Const_plus_H C CP H X.

  Let Id_H : functor [C, C] [C, C] := Id_H C CP H.

  Let Alg : precategory := FunctorAlg Id_H.

Lemma is_omega_cocont_Const_plus_H (X : EndC) : is_omega_cocont (Const_plus_H X).
Proof.
  apply is_omega_cocont_BinCoproduct_of_functors; try apply functor_category_has_homsets.
  - apply is_omega_cocont_constant_functor.
  - apply HH.
Defined.

Definition is_omega_cocont_Id_H : is_omega_cocont Id_H := is_omega_cocont_Const_plus_H (functor_identity C).

Definition InitAlg : Alg :=
  InitialObject (colimAlgInitial InitialEndC is_omega_cocont_Id_H (Colims_of_shape_nat_graph_EndC _)).

Definition ptdInitAlg : Ptd := ptd_from_alg InitAlg.

Section fix_a_Z.

  Context (Z : Ptd).

Lemma isInitial_pre_comp : isInitial [C, C] (ℓ (U Z) InitialEndC).
Proof.
use make_isInitial; intros F.
use tpair.
- use tpair.
  + intros c; simpl; apply InitialArrow.
  + abstract (intros x y f; cbn; apply InitialArrowEq).
- abstract (intros G; apply subtypePath;
    [ intros x; apply isaprop_is_nat_trans, homset_property
    | apply funextsec; intro c; apply InitialArrowUnique]).
Defined.

Local Lemma HU : is_omega_cocont (pre_composition_functor C C C (U Z)).
Proof.
apply is_omega_cocont_pre_composition_functor, CC.
Defined.

Definition SpecializedGMIt (X : EndC) :
  ∏ (G : functor [C, C] [C, C]) (ρ : [C, C] ⟦ G X, X ⟧)
    (θ : functor_composite Id_H (ℓ (U Z)) ⟹ functor_composite (ℓ (U Z)) G),
  ∃! h : [C, C] ⟦ ℓ (U Z) (alg_carrier _ InitAlg), X ⟧,
    # (ℓ (U Z)) (alg_map Id_H InitAlg) · h =
    θ (alg_carrier _ InitAlg) · # G h · ρ
  := SpecialGenMendlerIteration InitialEndC Colims_of_shape_nat_graph_EndC
                                Id_H is_omega_cocont_Id_H X (ℓ (U Z)) isInitial_pre_comp HU.

Context (prestrength_in_first_arg : PrestrengthForSignatureAtPoint _ _ _ H Z).

Local Lemma aux_iso_1_is_nat_trans :
   is_nat_trans
     (functor_composite Id_H (ℓ (U Z)))
     (pr1 (BinCoproductObject
        (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
           (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z))))
     (λ X : [C, C],
      BinCoproductOfArrows [C, C]
        (CPEndC (functor_composite (U Z) (functor_identity C))
           ((θ_source H) (X ⊗ Z))) (CPEndC (U Z) ((θ_source H) (X ⊗ Z)))
        (runitor_CAT (U Z)) (nat_trans_id ((θ_source H) (X ⊗ Z):functor C C))).
Proof.
  intros X X' α.
  apply nat_trans_eq_alt; intro c; simpl.
  etrans; [ apply BinCoproductOfArrows_comp |].
  etrans; [| eapply pathsinv0, BinCoproductOfArrows_comp ]; simpl.
  repeat rewrite id_right.
  rewrite (functor_id (H X)).
  do 2 rewrite id_left.
  apply idpath.
Qed.

Definition aux_iso_1
  : EndEndC
    ⟦ functor_composite Id_H (ℓ (U Z)),
      BinCoproductObject
           (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
              (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z))⟧.
Proof.
use tpair.
- intro X.
  exact (BinCoproductOfArrows EndC (CPEndC _ _) (CPEndC _ _) (runitor_CAT (U Z))
           (nat_trans_id (θ_source H (X⊗Z):functor C C))).
- exact aux_iso_1_is_nat_trans.
Defined.

Local Lemma aux_iso_1_inv_is_nat_trans :
   is_nat_trans
     (pr1 (BinCoproductObject
        (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
           (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z))) )
     (functor_composite Id_H (ℓ (U Z)))
     (λ X : [C, C],
      BinCoproductOfArrows [C, C]
        (CPEndC (functor_composite (functor_identity C) (U Z))
           ((θ_source H) (X ⊗ Z))) (CPEndC (U Z) ((θ_source H) (X ⊗ Z)))
        (lunitor_CAT (U Z)) (nat_trans_id ((θ_source H) (X ⊗ Z):functor C C))).
Proof.
  intros X X' α.
  apply nat_trans_eq_alt; intro c; simpl.
  etrans; [ apply BinCoproductOfArrows_comp |].
  etrans; [| eapply pathsinv0, BinCoproductOfArrows_comp ]; simpl.
  repeat rewrite id_right.
  rewrite (functor_id (H X)).
  repeat rewrite id_left.
  apply idpath.
Qed.

Local Definition aux_iso_1_inv
  : EndEndC
    ⟦ BinCoproductObject
           (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
              (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z)),
      functor_composite Id_H (ℓ (U Z)) ⟧.
Proof.
use tpair.
- intro X.
  exact (BinCoproductOfArrows EndC (CPEndC _ _) (CPEndC _ _) (lunitor_CAT (U Z))
         (nat_trans_id (θ_source H (X⊗Z):functor C C))).
- exact aux_iso_1_inv_is_nat_trans.
Defined.

Local Lemma aux_iso_2_inv_is_nat_trans :
   is_nat_trans
     (pr1 (BinCoproductObject
        (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
           (functor_fix_snd_arg [C, C] Ptd [C, C](θ_target H) Z))) )
     (functor_composite (ℓ (U Z))
        (Const_plus_H (U Z)))
     (λ X : [C, C],
      nat_trans_id
        (BinCoproductObject (CPEndC (U Z) ((θ_target H) (X ⊗ Z)))
         :functor C C)).
Proof.
intros X X' α.
rewrite id_left, id_right.
apply nat_trans_eq_alt; intro c; simpl.
unfold coproduct_nat_trans_data; simpl.
unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
apply (maponpaths_12 (BinCoproductOfArrows _ _ _)); try apply idpath.
unfold functor_fix_snd_arg_mor; simpl.
revert c; apply nat_trans_eq_pointwise, maponpaths.
apply nat_trans_eq_alt; intro c; simpl.
rewrite (functor_id X).
apply id_left.
Qed.

Local Definition aux_iso_2_inv
  : EndEndC
    ⟦ BinCoproductObject
         (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
                    (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_target H) Z)),
      functor_composite (ℓ (U Z) )   (Const_plus_H (U Z)) ⟧.
Proof.
use tpair.
- intro X.
  exact (nat_trans_id ((@BinCoproductObject EndC (U Z) (θ_target H (X⊗Z)) (CPEndC _ _) )
           : functor C C)).
- exact aux_iso_2_inv_is_nat_trans.
Defined.

Definition θ'_Thm15
  : EndEndC
    ⟦ BinCoproductObject
        (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
           (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z)),
      BinCoproductObject
        (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
            (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_target H) Z)) ⟧
  := BinCoproductOfArrows
   EndEndC (CPEndEndC _ _) (CPEndEndC _ _)
   (identity (constant_functor EndC _ (U Z): functor_category EndC EndC))
   prestrength_in_first_arg.

Definition ρ_Thm15 (f : Ptd ⟦ Z, ptdInitAlg ⟧)
  : [C, C] ⟦ BinCoproductObject (CPEndC (U Z) (H `InitAlg)), `InitAlg ⟧
  := @BinCoproductArrow
   EndC _ _  (CPEndC (U Z)
   (H (alg_carrier _ InitAlg))) (alg_carrier _ InitAlg) (#U f)
   (BinCoproductIn2 (CPEndC _ _) · (alg_map _ InitAlg)).


Definition SpecializedGMIt_Thm15 (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧)
  : ∃! h : [C, C]
              ⟦ ℓ (U Z) (pr1 InitAlg),
              pr1 InitAlg ⟧,
       # (ℓ (U Z)) (alg_map Id_H InitAlg) · h =
       pr1 (aux_iso_1 · θ'_Thm15 · aux_iso_2_inv)
         (pr1 InitAlg) ·
       # (Const_plus_H (U Z)) h · ρ_Thm15 f :=
   (SpecializedGMIt (pr1 InitAlg) (Const_plus_H (U Z))
     (ρ_Thm15 f) (aux_iso_1 · θ'_Thm15 · aux_iso_2_inv)).

Definition bracket_Thm15 (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧)
  : [C, C]⟦ ℓ (U Z) (pr1 InitAlg), pr1 InitAlg ⟧
  := pr1 (pr1 (SpecializedGMIt_Thm15 f)).

Notation "⦃ f ⦄" := (bracket_Thm15 f) (at level 0).

(* we prove the individual components for ease of compilation *)
Lemma bracket_Thm15_ok_part1 (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
 # U f = # (pr1 (ℓ (U Z))) (η InitAlg) · ⦃f⦄.
Proof.
apply nat_trans_eq_alt; intro c.
assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 f))).
assert (h_eq' := maponpaths (λ m,
               ((aux_iso_1_inv:(_⟹_)) _)· m) h_eq); clear h_eq.
assert (h_eq1' := maponpaths (λ m,
               (BinCoproductIn1 (CPEndC _ _))· m) h_eq'); clear h_eq'.
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

Lemma bracket_Thm15_ok_part2 (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
  prestrength_in_first_arg (alg_carrier _ InitAlg) ·  # H ⦃f⦄ · τ InitAlg =
  # (pr1 (ℓ (U Z))) (τ InitAlg) · ⦃f⦄.
Proof.
apply nat_trans_eq_alt; intro c.
assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 f))).
assert (h_eq' := maponpaths (λ m,
                ((aux_iso_1_inv:(_⟹_)) _)· m) h_eq); clear h_eq.
(* until here same as in previous lemma *)
assert (h_eq2' := maponpaths (λ m,
                (BinCoproductIn2 (CPEndC _ _))· m) h_eq');  clear h_eq'.
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

Lemma bracket_Thm15_ok (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
  bracket_property_parts prestrength_in_first_arg InitAlg f ⦃f⦄.
Proof.
split.
+ exact (bracket_Thm15_ok_part1 f).
+ exact (bracket_Thm15_ok_part2 f).
Qed.

Lemma bracket_Thm15_ok_cor (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
 bracket_property prestrength_in_first_arg InitAlg f (bracket_Thm15 f).
Proof.
now apply whole_from_parts, bracket_Thm15_ok.
Qed.

Local Lemma bracket_unique (f : Ptd ⟦ Z, ptd_from_alg InitAlg ⟧) :
 ∏ t : ∑ h : [C, C] ⟦ functor_composite (U Z) (pr1  InitAlg),
                            pr1 InitAlg ⟧, bracket_property prestrength_in_first_arg InitAlg f h,
   t = tpair _ ⦃f⦄ (bracket_Thm15_ok_cor f).
Proof.
intros [h' h'_eq]; apply subtypePath; [intro; apply (isaset_nat_trans (homset_property C))|].
simpl; apply parts_from_whole in h'_eq.
apply path_to_ctr, nat_trans_eq_alt; intro c.
simpl; rewrite !(@id_left EndC), id_right, <- !assoc.
etrans; [| eapply pathsinv0, postcompWithBinCoproductArrow ].
apply BinCoproductArrowUnique.
+ destruct h'_eq as [h'_eq1 _]; simpl.
  rewrite id_left, assoc.
  etrans; [ eapply pathsinv0, (nat_trans_eq_pointwise h'_eq1 c) |].
  now apply BinCoproductIn1Commutes_right_in_ctx_dir,
            BinCoproductIn1Commutes_right_in_ctx_dir,
            BinCoproductIn1Commutes_right_dir.
+ destruct h'_eq as [_ h'_eq2].
  rewrite assoc.
  etrans; [ eapply pathsinv0, (nat_trans_eq_pointwise h'_eq2 c) |].
  apply BinCoproductIn2Commutes_right_in_ctx_dir.
  apply BinCoproductIn2Commutes_right_in_double_ctx_dir.
  simpl; rewrite <- !assoc.
  now apply maponpaths, maponpaths, pathsinv0, BinCoproductIn2Commutes.
Qed.

End fix_a_Z.

End fix_an_H.

Context (H :  @Presignature C C C) (HH : is_omega_cocont H).
Let Id_H := Id_H C CP H.
Let θ := theta H.
Let InitAlg := InitAlg H HH.
Let ptdInitAlg := ptdInitAlg H HH.

Definition bracket_for_InitAlg : bracket θ InitAlg.
Proof.
intros Z f.
use tpair.
- use tpair.
  + exact (bracket_Thm15 H HH Z (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) f).
  + exact (bracket_Thm15_ok_cor H HH Z (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) f).
    (* B: better to prove the whole outside, and apply it here *)
    (* when the first components were not opaque, the following proof
       became extremely slow *)
- cbn. apply bracket_unique.
Defined.

Definition InitHSS : hss_category CP H.
Proof.
 (*
  red. (* FORBIDDEN, otherwise universe problem when checking the definition *)
  unfold hss_precategory; simpl.
*)
exists InitAlg.
exact bracket_for_InitAlg.
Defined.

Local Definition Ghat : EndEndC := Const_plus_H C CP H (pr1 InitAlg).

Definition constant_nat_trans (C' D : category) (d d' : D) (m : D⟦d,d'⟧)
    : [C', D] ⟦constant_functor C' D d, constant_functor C' D d'⟧.
Proof.
exists (λ _, m).
abstract (intros ? ? ?; intermediate_path m; [ apply id_left | apply pathsinv0, id_right]).
Defined.

Definition thetahat_0 (Z : Ptd) (f : Z --> ptdInitAlg) :
  EndEndC
  ⟦ BinCoproductObject
      (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
         (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z)),
    BinCoproductObject
      (CPEndEndC (constant_functor [C, C] [C, C] (pr1 InitAlg))
                 (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_target H) Z)) ⟧.
Proof.
exact (BinCoproductOfArrows EndEndC (CPEndEndC _ _) (CPEndEndC _ _)
                           (constant_nat_trans _ _ _ _ (#U f))
                           (nat_trans_fix_snd_arg _ _ _ _ _ θ Z)).
Defined.

Local Definition iso1' (Z : Ptd) : EndEndC ⟦ functor_composite Id_H (ℓ (U Z)),
 BinCoproductObject
    (CPEndEndC (constant_functor _ _  (U Z)) (functor_fix_snd_arg _ _ _ (θ_source H) Z)) ⟧.
Proof.
exact (aux_iso_1 H Z).
Defined.

Local Lemma is_nat_trans_iso2' (Z : Ptd) :
   is_nat_trans
     (pr1 (BinCoproductObject
        (CPEndEndC (constant_functor [C, C] [C, C] (pr1 InitAlg))
           (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_target H) Z))))
     (functor_composite (ℓ (U Z)) Ghat)
     (λ X : [C, C],
      nat_trans_id
        (BinCoproductObject
           (CPEndC
              ((constant_functor [C, C] [C, C] (pr1 InitAlg)) X)
              ((θ_target H) (X ⊗ Z)))
         :functor C C)).
Proof.
intros X X' α.
rewrite id_left, id_right.
apply nat_trans_eq_alt; intro c; simpl.
unfold coproduct_nat_trans_data; simpl.
unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
apply (maponpaths_12 (BinCoproductOfArrows _ _ _)); try apply idpath.
unfold functor_fix_snd_arg_mor; simpl.
revert c; apply nat_trans_eq_pointwise, maponpaths.
apply nat_trans_eq_alt; intro c; simpl.
rewrite (functor_id X).
apply id_left.
Qed.

Local Definition iso2' (Z : Ptd) : EndEndC ⟦
  BinCoproductObject
  (CPEndEndC (constant_functor [C, C] [C, C] (pr1 InitAlg))
             (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_target H) Z)),
  functor_composite (ℓ (U Z)) Ghat ⟧.
Proof.
use tpair.
- intro X.
  exact (nat_trans_id ((@BinCoproductObject EndC _ (θ_target H (X⊗Z)) (CPEndC _ _) )
            : functor C C)).
- exact (is_nat_trans_iso2' Z).
Defined.

Definition thetahat (Z : Ptd) (f : Z --> ptdInitAlg)
           : EndEndC ⟦ functor_composite Id_H (ℓ (U Z)),
                       functor_composite (ℓ (U Z)) (Ghat) ⟧.
Proof.
exact (iso1' Z · thetahat_0 Z f · iso2' Z).
Defined.


Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Let Yon (X : EndC) : functor EndC^op HSET := yoneda_objects EndC X.

Definition Phi_fusion (Z : Ptd) (X : EndC) (b : pr1 InitAlg --> X) :
  functor_composite (functor_opp (ℓ (U Z))) (Yon (pr1 InitAlg))
   ⟹
  functor_composite (functor_opp (ℓ (U Z))) (Yon X) .
Proof.
use tpair.
- intros Y a.
  exact (a · b).
- abstract (intros ? ? ?; simpl; apply funextsec; intro;
            unfold yoneda_objects_ob; simpl; unfold compose; simpl;
            apply nat_trans_eq; [apply homset_property |]; simpl; intro;
            apply assoc').
Defined.

Let IA := colimAlgInitial InitialEndC (is_omega_cocont_Id_H H HH) (Colims_of_shape_nat_graph_EndC _).

Lemma ishssMor_InitAlg (T' : hss CP H) :
  @ishssMor C CP H InitHSS T'
           (InitialArrow IA (pr1 T') : @algebra_mor EndC Id_H InitAlg T' ).
Proof.
intros Z f.
set (β0 := InitialArrow IA (pr1 T')).
match goal with | [|- _ · ?b = _ ] => set (β := b) end.
set (rhohat := BinCoproductArrow (CPEndC _ _ )  β (tau_from_alg T')
                :  pr1 Ghat T' --> T').
set (X:= SpecializedGMIt H HH Z _ Ghat rhohat (thetahat Z f)).
intermediate_path (pr1 (pr1 X)).
- set (TT := @fusion_law EndC InitialEndC Colims_of_shape_nat_graph_EndC
                         Id_H (is_omega_cocont_Id_H H HH) _ (pr1 (InitAlg)) T').
  set (Psi := ψ_from_comps (Id_H) _ (ℓ (U Z)) (Const_plus_H C CP H (U Z)) (ρ_Thm15 H HH Z f)
                             (aux_iso_1 H Z · θ'_Thm15 H Z (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) · aux_iso_2_inv H Z) ).
  set (T2 := TT _ (HU Z) (isInitial_pre_comp Z) Psi).
  set (T3 := T2 (ℓ (U Z)) (HU Z)).
  set (Psi' := ψ_from_comps (Id_H) _ (ℓ (U Z)) (Ghat) (rhohat)
                           (iso1' Z · thetahat_0 Z f · iso2' Z) ).
  set (T4 := T3 (isInitial_pre_comp Z) Psi').
  set (Φ := (Phi_fusion Z T' β)).
  set (T5 := T4 Φ).
  intermediate_path (Φ _ (fbracket InitHSS f)); try apply idpath.
  etrans; [| apply T5 ]; clear TT T2 T3 T4 T5 X.
  * now apply cancel_postcomposition.
  * (* hypothesis of fusion law *)
    apply funextsec; intro t.
    apply nat_trans_eq_alt; intro c; simpl.
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
      etrans;
        [| eapply pathsinv0, cancel_postcomposition,
           (nat_trans_eq_pointwise (functor_comp H t β) c) ].
      simpl; rewrite <- assoc.
      apply maponpaths, BinCoproductIn2Commutes_left_in_ctx_dir.
      assert (Hyp_c := nat_trans_eq_pointwise (τ_part_of_alg_mor _ CP _ _ _ (InitialArrow IA (pr1 T'))) c).
      simpl in Hyp_c.
      etrans; [ eapply pathsinv0, Hyp_c |].
      now apply maponpaths, pathsinv0, BinCoproductIn2Commutes.
  - apply pathsinv0, path_to_ctr.
    (* now a lot of serious verification work to be done *)
    apply nat_trans_eq_alt; intro c.
    simpl; rewrite id_right.
    (* look at type: *)
    (*  match goal with | [ |- ?l = _ ] => let ty:= (type of l) in idtac ty end. *)
    apply BinCoproductArrow_eq_cor.
    + rewrite <- !assoc.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl; rewrite id_left.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl; rewrite <- assoc.
      etrans;
        [| apply maponpaths, BinCoproductIn1Commutes_right_in_ctx_dir; simpl;
           rewrite id_left; apply BinCoproductIn1Commutes_right_dir, idpath ].
      rewrite !assoc.
      assert (fbracket_η_inst_c := nat_trans_eq_pointwise (fbracket_η T' (f · ptd_from_alg_mor _ CP H β0)) c).
      etrans; [| apply (!fbracket_η_inst_c) ].
      apply cancel_postcomposition, (ptd_mor_commutes _ (ptd_from_alg_mor _ CP H β0) ((pr1 Z) c)).
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
      etrans.
      2: { apply maponpaths.
           apply BinCoproductIn2Commutes_right_in_ctx_dir.
           rewrite <- assoc.
           apply maponpaths.
           apply BinCoproductIn2Commutes_right_dir.
           apply idpath.
      }
      do 2 rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        eapply pathsinv0.
        assert (τ_part_of_alg_mor_inst := τ_part_of_alg_mor _ CP H _ _ β0).
        assert (τ_part_of_alg_mor_inst_Zc :=
                  nat_trans_eq_pointwise τ_part_of_alg_mor_inst ((pr1 Z) c));
          clear τ_part_of_alg_mor_inst.
        apply τ_part_of_alg_mor_inst_Zc.
      }
      simpl.
      unfold coproduct_nat_trans_in2_data.
      repeat rewrite <- assoc.
      etrans.
      { apply maponpaths.
        rewrite assoc.
        eapply pathsinv0.
        assert (fbracket_τ_inst := fbracket_τ T' (f · ptd_from_alg_mor _ CP H β0)).
        assert (fbracket_τ_inst_c := nat_trans_eq_pointwise fbracket_τ_inst c); clear fbracket_τ_inst.
        apply fbracket_τ_inst_c.
      }
      simpl.
      unfold coproduct_nat_trans_in2_data.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      assert (Hyp:
                 ((# (pr1 (ℓ(U Z))) (# H β))·
                 θ ((alg_carrier _  T') ⊗ Z)·
                 # H (fbracket T' (f · ptd_from_alg_mor C CP H β0))
                 =
                 θ (tpair (λ _ : functor C C, ptd_obj C) (alg_carrier _ (InitialObject IA)) Z) ·
                 # H (# (pr1 (ℓ(U Z))) β ·
                 fbracket T' (f · ptd_from_alg_mor C CP H β0)))).
      2: { assert (Hyp_c := nat_trans_eq_pointwise Hyp c); clear Hyp.
           exact Hyp_c. }
      clear c. clear X. clear rhohat.
      rewrite (functor_comp H).
      rewrite assoc.
      apply cancel_postcomposition.
      apply nat_trans_eq_alt; intro c.
      assert (θ_nat_1_pointwise_inst := θ_nat_1_pointwise _ _ _ H θ _ _ β Z c).
      etrans; [ exact θ_nat_1_pointwise_inst |].
      clear θ_nat_1_pointwise_inst.
      simpl.
      apply maponpaths.
      rewrite horcomp_id_prewhisker.
      apply idpath.
Qed.

Definition hss_InitMor : ∏ T' : hss CP H, hssMor InitHSS T'.
Proof.
intro T'.
exists (InitialArrow IA (pr1 T')).
apply ishssMor_InitAlg.
Defined.

Lemma hss_InitMor_unique (T' : hss_category CP H):
  ∏ t : hss_category CP H ⟦ InitHSS, T' ⟧, t = hss_InitMor T'.
Proof.
intro t.
apply (invmap (hssMor_eq1 _ _ _ _ _ _ _)).
apply (@InitialArrowUnique _ IA (pr1 T') (pr1 t)).
Qed.

Lemma isInitial_InitHSS : isInitial (hss_category CP H) InitHSS.
Proof.
use make_isInitial; intro T.
exists (hss_InitMor T).
apply hss_InitMor_unique.
Defined.


Lemma InitialHSS : Initial (hss_category CP H).
Proof.
apply (make_Initial InitHSS), isInitial_InitHSS.
Defined.

End category_Algebra.
