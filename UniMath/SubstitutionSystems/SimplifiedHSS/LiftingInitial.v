
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Construction of a substitution system from an initial algebra
- Proof that the substitution system constructed from an
  initial algebra is an initial substitution system


version for simplified notion of HSS by Ralph Matthes (2022, 2023)
the file is very close to the homonymous file in the parent directory
basically, the changes in SimplifiedHSS.SubstitutionSystems are propagated


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
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SimplifiedHSS.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration.
Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.

Local Open Scope cat.

Local Coercion alg_carrier : algebra_ob >-> ob.

Section category_Algebra.

Context  (C : category) (CP : BinCoproducts C).

Local Notation "'EndC'":= ([C, C]) .
Local Notation "'Ptd'" := (category_Ptd C).

Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CP.
Let EndEndC := [EndC, EndC].
Let CPEndEndC:= BinCoproducts_functor_precat _ _ CPEndC: BinCoproducts EndEndC.


Context (KanExt : ∏ Z : Ptd, GlobalRightKanExtensionExists _ _ (U Z) C).

Context (H : Presignature C C C).
Let θ := theta H.

Let Const_plus_H (X : EndC) : functor EndC EndC := Const_plus_H C CP H X.

Let Id_H :  functor [C, C] [C, C] := Id_H C CP H.

Let Alg : category := FunctorAlg Id_H.


Context (IA : Initial Alg).

Definition SpecializedGMIt (Z : Ptd) (X : EndC)
  :  ∏ (G : functor [C, C] [C, C])
       (ρ : [C, C] ⟦ G X, X ⟧)
       (θ : functor_composite Id_H (ℓ (U Z)) ⟹ functor_composite (ℓ (U Z)) G),
     ∃! h : [C, C] ⟦ ℓ (U Z) (` (InitialObject IA)), X ⟧,
            # (ℓ (U Z)) (alg_map Id_H (InitialObject IA)) · h
            =
            θ (` (InitialObject IA)) · # G h · ρ
   :=
  SpecialGenMendlerIteration _ _ IA EndC X _ (KanExt Z) .


Definition θ_in_first_arg (Z: Ptd)
  : functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z
    ⟹
    functor_fix_snd_arg [C, C] Ptd [C, C] (θ_target H) Z
  := nat_trans_fix_snd_arg _ _ _ _ _ θ Z.

Definition InitAlg : Alg := InitialObject IA.

Definition ptdInitAlg : Ptd := ptd_from_alg InitAlg.

Local Lemma aux_iso_1_is_nat_trans (Z : Ptd) :
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
  apply nat_trans_eq_alt.
  intro c.
  simpl.
  unfold coproduct_nat_trans_data, coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
  etrans; [apply BinCoproductOfArrows_comp |].
  etrans.
  2: { eapply pathsinv0. apply BinCoproductOfArrows_comp. }
  apply maponpaths_12.
  - etrans; [ apply id_left |].
    apply pathsinv0.
    apply id_right.
  - rewrite id_right.
    rewrite id_left.
    rewrite (functor_id (H X)).
    apply pathsinv0, id_left.
Qed.

Definition aux_iso_1 (Z : Ptd)
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
  - exact (aux_iso_1_is_nat_trans Z).
Defined.

Local Lemma aux_iso_1_inv_is_nat_trans (Z : Ptd) :
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
  apply nat_trans_eq_alt.
  intro c; simpl.
  unfold coproduct_nat_trans_data, coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
  etrans; [apply BinCoproductOfArrows_comp |].
  etrans.
  2: { eapply pathsinv0. apply BinCoproductOfArrows_comp. }
  apply maponpaths_12.
  - rewrite id_right.
    apply pathsinv0.
    apply id_right.
  - rewrite (functor_id (H X)).
    do 2 rewrite id_left.
    apply id_right.
Qed.

Local Definition aux_iso_1_inv (Z: Ptd)
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
  - exact (aux_iso_1_inv_is_nat_trans Z).
Defined.

(*
Definition G_Thm15 (X : EndC) := coproduct_functor _ _ CPEndC
                       (constant_functor _ _ X)
                       H.
 *)

Local Lemma aux_iso_2_inv_is_nat_trans (Z : Ptd) :
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
  rewrite (@id_left EndC).
  rewrite (@id_right EndC).
  apply nat_trans_eq_alt.
  intro c; simpl.
  unfold coproduct_nat_trans_data, coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
  apply (maponpaths_12 (BinCoproductOfArrows _ _ _)).
  + apply idpath.
  + unfold functor_fix_snd_arg_mor; simpl.
    revert c.
    apply nat_trans_eq_pointwise.
    apply maponpaths.
    apply nat_trans_eq_alt.
    intro c.
    simpl.
    rewrite (functor_id X).
    apply id_left.
Qed.

Local Definition aux_iso_2_inv (Z : Ptd)
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
  - exact (aux_iso_2_inv_is_nat_trans Z).
Defined.

Definition θ'_Thm15 (Z: Ptd)
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
   (θ_in_first_arg Z).

Definition ρ_Thm15 (Z: Ptd)(f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧)
  : [C, C] ⟦ BinCoproductObject (CPEndC (U Z) (H `InitAlg)), `InitAlg ⟧
  := @BinCoproductArrow
   EndC _ _  (CPEndC (U Z)
   (H (alg_carrier _ InitAlg))) (alg_carrier _ InitAlg) f
   (BinCoproductIn2 (CPEndC _ _) · (alg_map _ InitAlg)).

Definition SpecializedGMIt_Thm15 (Z: Ptd)(f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧)
  : ∃! h : [C, C] ⟦ ℓ (U Z) (` (InitialObject IA)), pr1 InitAlg ⟧,
           # (ℓ (U Z)) (alg_map Id_H (InitialObject IA)) · h
           =
           pr1 ((aux_iso_1 Z · θ'_Thm15 Z · aux_iso_2_inv Z)) (` (InitialObject IA)) ·
           # (Const_plus_H (U Z)) h · ρ_Thm15 Z f
  := SpecializedGMIt Z (pr1 InitAlg) (Const_plus_H (U Z))
     (ρ_Thm15 Z f) (aux_iso_1 Z · θ'_Thm15 Z · aux_iso_2_inv Z).

Definition bracket_Thm15 (Z: Ptd)(f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧)
  : [C, C] ⟦ ℓ (U Z) (` (InitialObject IA)), `InitAlg ⟧
  := pr1 (pr1 (SpecializedGMIt_Thm15 Z f)).

Notation "⦃ f ⦄" := (bracket_Thm15 _ f) (at level 0).

(* we prove the individual components for ease of compilation *)
Lemma bracket_Thm15_ok_part1 (Z: Ptd)(f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧):
 f = # (pr1 (ℓ (U Z))) (η InitAlg) · ⦃f⦄.
Proof.
  apply nat_trans_eq_alt.
  intro c.
  assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 Z f))).
  assert (h_eq' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ =>
               (((aux_iso_1_inv Z):(_ ⟹ _)) _)· m) h_eq);
  clear h_eq.
  simpl in h_eq'.
  assert (h_eq1' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ =>
               (BinCoproductIn1 (CPEndC _ _))· m) h_eq');
  clear h_eq'.
  assert (h_eq1'_inst := nat_trans_eq_pointwise h_eq1' c);
  clear h_eq1'.
(* match goal right in the beginning in contrast with earlier approach - suggestion by Benedikt *)
  match goal with |[ H1 : _  = ?f |- _ = _   ] =>
         intermediate_path f end.

  - clear h_eq1'_inst.
    unfold coproduct_nat_trans_data; simpl.
    unfold coproduct_nat_trans_in1_data ; simpl.
    repeat rewrite <- assoc .
    apply BinCoproductIn1Commutes_right_in_ctx_dir.
    simpl.
    rewrite id_left.
    apply BinCoproductIn1Commutes_right_in_ctx_dir.
    simpl.
    rewrite id_left.
    apply BinCoproductIn1Commutes_right_in_ctx_dir.
    rewrite (@id_left EndC).
    rewrite id_left.
    apply BinCoproductIn1Commutes_right_in_ctx_dir.
    rewrite (@id_left EndC).
    apply BinCoproductIn1Commutes_right_dir.
    apply idpath.
  - rewrite <- h_eq1'_inst.
    clear h_eq1'_inst.
    apply BinCoproductIn1Commutes_left_in_ctx_dir.
    unfold nat_trans_id; simpl.
    rewrite id_left.
    repeat rewrite (id_left EndEndC).
    repeat rewrite (id_left EndC).
    unfold functor_fix_snd_arg_ob.
    repeat rewrite assoc.
(*    apply maponpaths. *)
    apply idpath.
Qed.

Lemma bracket_Thm15_ok_part2 (Z: Ptd)(f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧):
 (theta H) ((alg_carrier _  InitAlg) ⊗ Z) ·  # H ⦃f⦄ · τ InitAlg
  =
   # (pr1 (ℓ (U Z))) (τ InitAlg) · ⦃f⦄.
Proof.
  apply nat_trans_eq_alt.
  intro c.
  assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 Z f))).
  assert (h_eq' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ =>
                  (((aux_iso_1_inv Z):(_⟹_)) _)· m) h_eq);
  clear h_eq.
 (*        simpl in h_eq'. (* until here same as in previous lemma *) *)

  assert (h_eq2' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ =>
                (BinCoproductIn2 (CPEndC _ _))· m) h_eq').
  clear h_eq'.
  assert (h_eq2'_inst := nat_trans_eq_pointwise h_eq2' c).
  clear h_eq2'.
  match goal with |[ H1 : _  = ?f |- _ = _   ] =>
                   intermediate_path f end.
  - clear h_eq2'_inst.
    apply BinCoproductIn2Commutes_right_in_ctx_dir.
    unfold aux_iso_1; simpl.
    rewrite id_right.
    rewrite id_left.
    do 3 rewrite <- assoc.
    apply BinCoproductIn2Commutes_right_in_ctx_dir.
    unfold nat_trans_id; simpl. rewrite id_left.
    apply BinCoproductIn2Commutes_right_in_ctx_dir.
    unfold nat_trans_fix_snd_arg_data.
    apply BinCoproductIn2Commutes_right_in_double_ctx_dir.
    rewrite <- assoc.
    apply maponpaths.
    eapply pathscomp0. 2: apply assoc.
    apply maponpaths.
    apply pathsinv0.
    apply BinCoproductIn2Commutes.

(* alternative with slightly less precise control: *)
(*            do 4 rewrite <- assoc. *)
(*            apply BinCoproductIn2Commutes_right_in_ctx_dir. *)
(*            rewrite id_left. *)
(*            apply BinCoproductIn2Commutes_right_in_ctx_dir. *)
(*            apply BinCoproductIn2Commutes_right_in_ctx_dir. *)
(*            unfold nat_trans_fix_snd_arg_data. *)
(*            rewrite id_left. *)
(*            apply BinCoproductIn2Commutes_right_in_double_ctx_dir. *)
(*            do 2 rewrite <- assoc. *)
(*            apply maponpaths. *)
(*            apply maponpaths. *)
(*            apply pathsinv0. *)
(*            apply BinCoproductIn2Commutes. *)
(* *)

  - rewrite <- h_eq2'_inst. clear h_eq2'_inst.
    apply BinCoproductIn2Commutes_left_in_ctx_dir.
    repeat rewrite id_left.
    apply assoc.
Qed.

Lemma bracket_Thm15_ok (Z: Ptd)(f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧):
 bracket_property_parts (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) _ f ⦃f⦄.
Proof.
  split.
  + exact (bracket_Thm15_ok_part1 Z f).
  + exact (bracket_Thm15_ok_part2 Z f).
Qed.

Lemma bracket_Thm15_ok_cor (Z: Ptd)(f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧):
 bracket_property (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) _ f (bracket_Thm15 Z f).
Proof.
  apply whole_from_parts.
  apply bracket_Thm15_ok.
Qed.

Local Lemma foo' (Z : Ptd) (f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧) :
 ∏ t : ∑ h : [C, C] ⟦ functor_composite (U Z) (pr1  InitAlg),
                         pr1 InitAlg ⟧,
       bracket_property (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) _ f h,
   t
   =
   tpair
     (λ h : [C, C]
            ⟦ functor_composite (U Z) (pr1 InitAlg),
              pr1 InitAlg ⟧,
       bracket_property (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) _ f h)
      ⦃f⦄ (bracket_Thm15_ok_cor Z f).
Proof.
  intros [h' h'_eq].
  apply subtypePath.
  - intro.
    unfold bracket_property.
    apply (isaset_nat_trans (homset_property C)).
  - simpl.
    apply parts_from_whole in h'_eq.
(*    destruct h'_eq as [h'_eq1 h'_eq2]. *)
    unfold bracket_Thm15.
    apply path_to_ctr.
    apply nat_trans_eq_alt.
    intro c; simpl.
    unfold coproduct_nat_trans_data.
    repeat rewrite (@id_left EndC).
    rewrite id_right.
    repeat rewrite <- @assoc.
    etrans.
    2: { eapply pathsinv0. apply postcompWithBinCoproductArrow. }
    apply BinCoproductArrowUnique.
    + destruct h'_eq as [h'_eq1 _ ]. (*clear h'_eq2.*)
      simpl.
      rewrite id_left.
      assert (h'_eq1_inst := nat_trans_eq_pointwise h'_eq1 c);
        clear h'_eq1.
      simpl in h'_eq1_inst.
      unfold coproduct_nat_trans_in1_data in h'_eq1_inst; simpl in h'_eq1_inst.
      rewrite <- @assoc in h'_eq1_inst.
      etrans.
      { eapply pathsinv0; exact h'_eq1_inst. }
      clear h'_eq1_inst.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      apply BinCoproductIn1Commutes_right_dir.
      apply idpath.
    + destruct h'_eq as [_ h'_eq2]. (*clear h'_eq2.*)
      assert (h'_eq2_inst := nat_trans_eq_pointwise h'_eq2 c);
        clear h'_eq2.
      simpl in h'_eq2_inst.
      unfold coproduct_nat_trans_in2_data in h'_eq2_inst; simpl in h'_eq2_inst.
      apply pathsinv0 in h'_eq2_inst.
      rewrite <- assoc in h'_eq2_inst.
      etrans; [ exact h'_eq2_inst |]. clear h'_eq2_inst.
      apply BinCoproductIn2Commutes_right_in_ctx_dir.
      apply BinCoproductIn2Commutes_right_in_double_ctx_dir.
      unfold nat_trans_fix_snd_arg_data; simpl.
      do 2 rewrite <- assoc.
      apply maponpaths.
      rewrite <- assoc.
      apply maponpaths.
      apply pathsinv0.
      apply BinCoproductIn2Commutes.
Qed.

Definition bracket_for_InitAlg : bracket θ InitAlg.
Proof.
  intros Z f.
  use tpair.
  - use tpair.
    + exact (bracket_Thm15 Z f).
    + exact (bracket_Thm15_ok_cor Z f).
       (* B: better to prove the whole outside, and apply it here *)
     (* when the first components were not opaque, the following proof
        became extremely slow *)
  - simpl; apply foo'.
Defined.

Definition InitHSS : hss_category CP H.
Proof.
 (*
  red. (* FORBIDDEN, otherwise universe problem when checking the definition *)
  unfold hss_precategory; simpl.
*)
  exists (InitAlg).
  exact bracket_for_InitAlg.
Defined.


Local Definition Ghat : EndEndC := Const_plus_H (pr1 InitAlg).

Definition constant_nat_trans (C' D : category)
   (d d' : D)
   (m : d --> d')
    : [C', D] ⟦constant_functor C' D d, constant_functor C' D d'⟧.
Proof.
  exists (λ _, m).
  abstract (
    intros ? ? ? ;
    intermediate_path m ;
    [
    apply id_left |
    apply pathsinv0 ;
  apply id_right] ).
Defined.

Definition thetahat_0 (Z : Ptd) (f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧):
EndEndC
⟦ BinCoproductObject
    (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
       (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z)),
BinCoproductObject
  (CPEndEndC (constant_functor [C, C] [C, C] (pr1 InitAlg))
             (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_target H) Z)) ⟧ .
Proof.
  exact (BinCoproductOfArrows EndEndC (CPEndEndC _ _) (CPEndEndC _ _)
                           (constant_nat_trans _ _ _ _ f)
                           (θ_in_first_arg Z)).
Defined.

Local Definition iso1' (Z : Ptd) :  EndEndC ⟦ functor_composite Id_H
                                        (ℓ (U Z)),
 BinCoproductObject
    (CPEndEndC (constant_functor [C, C] [C, C] (U Z))
               (functor_fix_snd_arg [C, C] Ptd [C, C] (θ_source H) Z)) ⟧.
Proof.
  exact (aux_iso_1 Z).
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
         : functor C C)).
Proof.
  intros X X' α.
  rewrite (@id_left EndC).
  rewrite (@id_right EndC).
  apply nat_trans_eq_alt.
  intro c; simpl.
  unfold coproduct_nat_trans_data, coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
  apply (maponpaths_12 (BinCoproductOfArrows _ _ _)).
  - apply idpath.
  - unfold functor_fix_snd_arg_mor; simpl.
    revert c.
    apply nat_trans_eq_pointwise.
    apply maponpaths.
    apply nat_trans_eq_alt.
    intro c.
    simpl.
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

Definition thetahat (Z : Ptd)  (f : [C, C] ⟦ U Z, U (ptd_from_alg InitAlg) ⟧)
           : EndEndC ⟦ functor_composite Id_H
                                        (ℓ (U Z)),
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
  - intro Y.
    intro a.
    exact (a · b).
  - abstract (
    intros ? ? ?; simpl;
    apply funextsec;
    intro;
    unfold yoneda_objects_ob; simpl;
    unfold compose;
    simpl;
    apply nat_trans_eq; [ apply homset_property |];
    simpl; intro; apply assoc').
Defined.

Lemma ishssMor_InitAlg (T' : hss CP H) :
  @ishssMor C CP H
        InitHSS T'
           (InitialArrow IA (pr1 T') : @algebra_mor EndC Id_H InitAlg T' ).
Proof.
  unfold ishssMor.
  unfold isbracketMor.
  intros Z f.
  set (β0 := InitialArrow IA (pr1 T')).
  match goal with | [|- _ · ?b = _ ] => set (β := b) end.
  set ( rhohat := BinCoproductArrow (CPEndC _ _ )  β (tau_from_alg T')
                  :  pr1 Ghat T' --> T').
  set (X:= SpecializedGMIt Z _ Ghat rhohat (thetahat Z f)).
  intermediate_path (pr1 (pr1 X)).
  - set (TT:= fusion_law _ _ IA _ (pr1 InitAlg) T' _ (KanExt Z)).
    set (Psi := ψ_from_comps _ (Id_H) _ _ (ℓ (U Z)) (Const_plus_H (U Z)) (ρ_Thm15 Z f)
                             (aux_iso_1 Z · θ'_Thm15 Z · aux_iso_2_inv Z) ).
    set (T2 := TT Psi).
    set (T3 := T2 (ℓ (U Z)) (KanExt Z)).
    set (Psi' := ψ_from_comps _ (Id_H) _ _ (ℓ (U Z)) (Ghat) (rhohat)
                             (iso1' Z · thetahat_0 Z f · iso2' Z) ).
    set (T4 := T3 Psi').
    set (Φ := (Phi_fusion Z T' β)).
    set (T5 := T4 Φ).
    intermediate_path (Φ _ (fbracket InitHSS Z f)).
    + apply idpath.
    + eapply pathscomp0.
      2: { apply T5.
      (* hypothesis of fusion law *)
      apply funextsec. intro t.
      simpl.
      unfold compose. simpl.
      apply nat_trans_eq_alt.
      simpl.
      intro c.
      rewrite id_right.
      rewrite id_right.
      (* should be decomposed into two diagrams *)
      apply BinCoproductArrow_eq_cor.
      * (* first diagram *)
        clear TT T2 T3 T4 T5.
        do 5 rewrite <- assoc.
        apply BinCoproductIn1Commutes_left_in_ctx_dir.
        apply BinCoproductIn1Commutes_right_in_ctx_dir.
        simpl.
        rewrite id_left.
        apply BinCoproductIn1Commutes_left_in_ctx_dir.
        apply BinCoproductIn1Commutes_right_in_ctx_dir.
        simpl.
        rewrite id_left.
        apply BinCoproductIn1Commutes_left_in_ctx_dir.
        simpl.
        rewrite id_left.
        apply BinCoproductIn1Commutes_left_in_ctx_dir.
        rewrite <- assoc.
        apply maponpaths.
        apply BinCoproductIn1Commutes_right_in_ctx_dir.
        simpl.
        rewrite id_left.
        apply BinCoproductIn1Commutes_right_dir.
        apply idpath.

      * (* second diagram *)
        clear TT T2 T3 T4 T5.
        do 5 rewrite <- assoc.
        apply BinCoproductIn2Commutes_left_in_ctx_dir.
        apply BinCoproductIn2Commutes_right_in_ctx_dir.
        rewrite (@id_left EndC).
        apply BinCoproductIn2Commutes_left_in_ctx_dir.
        apply BinCoproductIn2Commutes_right_in_ctx_dir.
        simpl.
        unfold nat_trans_fix_snd_arg_data.
        repeat rewrite <- assoc.
        apply maponpaths.
        apply BinCoproductIn2Commutes_left_in_ctx_dir.
        apply BinCoproductIn2Commutes_right_in_ctx_dir.
        simpl.
        assert (H_nat_inst := functor_comp H t β).
        assert (H_nat_inst_c := nat_trans_eq_pointwise H_nat_inst c); clear H_nat_inst.
        {
          match goal with |[ H1 : _  = ?f |- _ = _· ?g · ?h  ] =>
             intermediate_path (f·g·h) end.
          + clear H_nat_inst_c.
            simpl.
            repeat rewrite <- assoc.
            apply maponpaths.
            apply BinCoproductIn2Commutes_left_in_ctx_dir.
            simpl.
            unfold coproduct_nat_trans_in2_data, coproduct_nat_trans_data.
            assert (Hyp := τ_part_of_alg_mor _ CP _ _ _ (InitialArrow IA (pr1 T'))).
            assert (Hyp_c := nat_trans_eq_pointwise Hyp c); clear Hyp.
            simpl in Hyp_c.
            etrans; [ eapply pathsinv0; exact Hyp_c |].
            clear Hyp_c.
            apply maponpaths.
            apply pathsinv0.
            apply BinCoproductIn2Commutes.
          + rewrite <- H_nat_inst_c.
            apply idpath.
        }
      }
      apply cancel_postcomposition.
      apply idpath.
  - apply pathsinv0.
    apply path_to_ctr.
    (* now a lot of serious verification work to be done *)
    apply nat_trans_eq_alt.
    intro c.
    simpl.
    rewrite id_right.
    (* look at type: *)
(*        match goal with | [ |- ?l = _ ] => let ty:= (type of l) in idtac ty end. *)
    apply BinCoproductArrow_eq_cor.
    + repeat rewrite <- assoc.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl.
      unfold coproduct_nat_trans_in1_data,
             coproduct_nat_trans_in2_data,
             coproduct_nat_trans_data.
      rewrite id_left.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      simpl.
      repeat rewrite <- assoc.
      etrans.
      2: { apply maponpaths. apply BinCoproductIn1Commutes_right_in_ctx_dir.
           rewrite id_left. apply BinCoproductIn1Commutes_right_dir.
           apply idpath. }
      do 2 rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        assert (ptd_mor_commutes_inst := ptd_mor_commutes _ (ptd_from_alg_mor _ CP H β0) ((pr1 Z) c)).
        apply ptd_mor_commutes_inst. }
      assert (fbracket_η_inst := fbracket_η T' (f · #U (ptd_from_alg_mor _ CP H β0))).
      assert (fbracket_η_inst_c := nat_trans_eq_pointwise fbracket_η_inst c); clear fbracket_η_inst.
      apply (!fbracket_η_inst_c).
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
        assert (fbracket_τ_inst := fbracket_τ T' (f · #U (ptd_from_alg_mor _  CP H β0))).
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
                 (theta H) ((alg_carrier _  T') ⊗ Z)·
                 # H (fbracket T' _ (f · #U(ptd_from_alg_mor C CP H β0)))
                 =
                 θ (tpair (λ _ : functor C C, ptd_obj C) (alg_carrier _ (InitialObject IA)) Z) ·
                 # H (# (pr1 (ℓ(U Z))) β ·
                 fbracket T' _ (f · #U(ptd_from_alg_mor C CP H β0))))).
      2: { assert (Hyp_c := nat_trans_eq_pointwise Hyp c); clear Hyp.
           exact Hyp_c. }
      clear c. clear X. clear rhohat.
      rewrite (functor_comp H).
      rewrite assoc.
      apply cancel_postcomposition.
      fold θ.
      apply nat_trans_eq_alt.
      intro c.
      assert (θ_nat_1_pointwise_inst := θ_nat_1_pointwise _ _ _ H θ _ _ β Z c).
      etrans ; [exact θ_nat_1_pointwise_inst | ].
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
  ∏ t : hss_precategory CP H ⟦ InitHSS, T' ⟧, t = hss_InitMor T'.
Proof.
  intro t.
  apply (invmap (hssMor_eq1 _ _ _ _ _ _ _)).
  apply (@InitialArrowUnique _ IA (pr1 T') (pr1 t)).
Qed.

Lemma isInitial_InitHSS : isInitial (hss_category CP H) InitHSS.
Proof.
  use make_isInitial.
  intro T.
  exists (hss_InitMor T).
  apply hss_InitMor_unique.
Defined.


Lemma InitialHSS : Initial (hss_category CP H).
Proof.
  use (make_Initial InitHSS).
  apply isInitial_InitHSS.
Defined.


End category_Algebra.
