
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of signatures
-    Proof that two forms of strength laws are equivalent
-    (Part on relation with relative strength moved into separate file in 2023)

************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.SubstitutionSystems.Notation.

Local Open Scope subsys.

(** Goal: define signatures as pairs of a rank-2 functor and a "strength" *)

(** * Definition of signatures *)

Section fix_a_category.

  Context (C : category).

(** The category of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (category_Ptd C).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C]).

(** in the original definition, this second category was the same as the first one *)
Context (D : category).

(** we do not yet have a use of this third category being different from the very first one *)
Context (D' : category).

Section about_signatures.

(** [H] is a rank-2 functor: a functor between functor categories *)
Context (H : functor [C, D'] [C, D]).


(** ** Source and target of the natural transformation [θ] *)


(** Source is given by [(X,Z) => H(X)∙U(Z)] *)
Definition θ_source: ([C, D'] ⊠ Ptd) ⟶ [C, D].
Proof.
  apply (functor_composite (pair_functor H U)).
  apply (functor_composite binswap_pair_functor).
  apply functorial_composition.
Defined.

Lemma θ_source_ok: functor_on_objects θ_source =  λ FX : [C, D'] ⊠ Ptd, H (pr1 FX) • U (pr2 FX).
Proof.
  apply idpath.
Qed.

(** Target is given by [(X,Z) => H(X∙U(Z))] *)
Definition θ_target : ([C, D'] ⊠ Ptd) ⟶ [C, D].
Proof.
  apply (functor_composite (pair_functor (functor_identity _) U)).
  apply (functor_composite binswap_pair_functor).
  use (functor_composite _ H).
  apply functorial_composition.
Defined.

Lemma θ_target_ok: functor_on_objects θ_target =  λ FX : [C, D'] ⊠ Ptd, H (pr1 FX • U (pr2 FX)).
Proof.
  apply idpath.
Qed.

Section fix_a_θ.

(** * Two alternative versions of the strength laws are defined and seen as equivalent *)


(** We assume a suitable (bi)natural transformation [θ] *)
Hypothesis θ : θ_source ⟹ θ_target.

(** [θ] is supposed to satisfy two strength laws *)

Definition θ_Strength1 : UU := ∏ X : [C, D'],
  (θ (X ⊗ (id_Ptd C))) · # H (identity X : functor_composite (functor_identity C) X ⟹ pr1 X)
          = nat_trans_id _ .

Section Strength_law_1_intensional.

(** needs the heterogeneous formulation of the monoidal operation to type-check *)
Definition θ_Strength1_int : UU
  := ∏ X : [C, D'],
           θ (X ⊗ (id_Ptd C)) · # H (lunitor_CAT _) = lunitor_CAT _.

(** the following naturally-looking definition is often not suitable to work with *)
Definition θ_Strength1_int_nicer : UU
  := ∏ X : [C, D'],
           θ (X ⊗ (id_Ptd C)) = nat_trans_id ((H X): functor C D).

(*
Section Test.
Context (X : [C, D']).
Check (nat_trans_id ((H X): functor C D) : (θ_source (X ⊗ (id_Ptd C)): functor C D) ⟹ (θ_target (X ⊗ (id_Ptd C)): functor C D)).
End Test.
*)

Lemma θ_Strength1_int_nicer_implies_θ_Strength1_int : θ_Strength1_int_nicer → θ_Strength1_int.
Proof.
  intros T X.
  rewrite T.
  etrans.
  { apply maponpaths.
    apply (functor_id H X). }
  apply id_right.
Qed.

Lemma θ_Strength1_int_implies_θ_Strength1_int_nicer : θ_Strength1_int → θ_Strength1_int_nicer.
Proof.
  intros T X.
  etrans; [| apply T].
  etrans.
  2: { apply pathsinv0.
       apply maponpaths.
       apply (functor_id H X). }
  apply pathsinv0.
  apply id_right.
Qed.


Lemma isaprop_θ_Strength1_int: isaprop θ_Strength1_int.
Proof.
  apply impred; intros X x x'.
  apply isaset_nat_trans, homset_property.
Qed.

Lemma θ_Strength1_int_implies_θ_Strength1 : θ_Strength1_int → θ_Strength1.
Proof.
  unfold θ_Strength1_int, θ_Strength1.
  intros T X.
  assert (TX := T X).
  apply nat_trans_eq_alt.
  intro c; cbn.
  assert (T2 := nat_trans_eq_pointwise TX c).
  cbn in *.
  exact T2.
Qed.

(* practically the same proof works in the opposite direction *)
Lemma θ_Strength1_implies_θ_Strength1_int : θ_Strength1 → θ_Strength1_int.
Proof.
  unfold θ_Strength1_int, θ_Strength1.
  intros T X.
  assert (TX := T X).
  apply nat_trans_eq_alt.
  intro c; cbn.
  assert (T2 := nat_trans_eq_pointwise TX c).
  cbn in *.
  exact T2.
Qed.

End Strength_law_1_intensional.

(** we are using [Z p• Z'] for compatibility with legacy code - instead of [ptd_compose] *)
Definition θ_Strength2 : UU := ∏ (X : [C, D']) (Z Z' : Ptd) (Y : [C, D'])
           (α : functor_compose (functor_composite (U Z) (U Z')) X --> Y),
    θ (X ⊗ (Z p• Z' : Ptd)) · # H α =
    θ (X ⊗ Z') •• (U Z) · θ ((functor_compose (U Z') X) ⊗ Z) ·
       # H (α : functor_compose (U Z) (X • (U Z')) --> Y).


Section Strength_law_2_intensional.

Definition θ_Strength2_int : UU
  := ∏ (X : [C, D']) (Z Z' : Ptd),
      θ (X ⊗ (Z p• Z')) · #H (rassociator_CAT (U Z) (U Z') X )  =
        (lassociator_CAT (U Z) (U Z') (H X) :
          [C, D] ⟦ functor_compose (functor_composite (U Z) (U Z')) (H X),
                        functor_composite (U Z) (functor_composite (U Z') (H X)) ⟧
      ) ·
      θ (X ⊗ Z') •• (U Z) · θ ((functor_compose (U Z') X) ⊗ Z) .

Lemma isaprop_θ_Strength2_int: isaprop θ_Strength2_int.
Proof.
  apply impred; intros X.
  apply impred; intros Z.
  apply impred; intros Z'.
  apply isaset_nat_trans, homset_property.
Qed.

Lemma θ_Strength2_int_implies_θ_Strength2 : θ_Strength2_int → θ_Strength2.
Proof.
  unfold θ_Strength2_int, θ_Strength2.
  intros T X Z Z' Y a.
  apply nat_trans_eq_alt.
  intro c.
  assert (TXZZ' := T X Z Z').
  assert (TXZZ'c := nat_trans_eq_pointwise TXZZ' c).
  cbn in TXZZ'c.
  clear T TXZZ'.
  rewrite id_left in TXZZ'c.
  cbn. rewrite <- TXZZ'c; clear TXZZ'c.
  rewrite <- assoc.
  apply maponpaths.
  assert (functor_comp_H := functor_comp H (rassociator_CAT (pr1 Z) (pr1 Z') X)
           (a : functor_compose (U Z) (functor_composite (U Z') X) --> Y)).
  assert (functor_comp_H_c := nat_trans_eq_pointwise functor_comp_H c).
  cbn in functor_comp_H_c.
  etrans; [| apply functor_comp_H_c ].
  clear functor_comp_H functor_comp_H_c.
  revert c.
  apply nat_trans_eq_pointwise.
  apply maponpaths.
  apply nat_trans_eq_alt.
  intro c; apply pathsinv0, id_left.
Qed.

(* for curiosity also the other direction *)
Lemma θ_Strength2_implies_θ_Strength2_int : θ_Strength2 → θ_Strength2_int.
Proof.
  unfold θ_Strength2_int, θ_Strength2.
  intros T X Z Z'.
  assert (TXZZ'_inst := T X Z Z' (functor_compose (U Z)
          (functor_composite (U Z') X)) (lassociator_CAT (pr1 Z) (pr1 Z') X)).
  eapply pathscomp0.
  { apply TXZZ'_inst. }
  clear T TXZZ'_inst.
  apply nat_trans_eq_alt.
  intro c.
  cbn.
  rewrite id_left.
  rewrite <- assoc.
  apply maponpaths.
  etrans; [| apply id_right].
  apply maponpaths.
  assert (functor_id_H := functor_id H (functor_compose (pr1 Z) (functor_composite (pr1 Z') X))).
  assert (functor_id_H_c := nat_trans_eq_pointwise functor_id_H c).
  etrans; [| apply functor_id_H_c].
  clear functor_id_H functor_id_H_c.
  revert c.
  apply nat_trans_eq_pointwise.
  apply maponpaths.
  apply nat_trans_eq_alt.
  intro c; apply idpath.
Qed.

Definition θ_Strength2_int_nicer : UU := ∏ (X : [C, D']) (Z Z' : Ptd),
      θ (X ⊗ (Z p• Z'))  =
        (lassociator_CAT (U Z) (U Z') (H X) :
          [C, D] ⟦ functor_compose (functor_composite (U Z) (U Z')) (H X),
                        functor_composite (U Z) (functor_composite (U Z') (H X)) ⟧) ·
             θ (X ⊗ Z') •• (U Z) · θ ((functor_compose (U Z') X) ⊗ Z) ·
             #H (lassociator_CAT (U Z) (U Z') X ).


Lemma θ_Strength2_int_implies_θ_Strength2_int_nicer: θ_Strength2_int -> θ_Strength2_int_nicer.
Proof.
  intro Hyp.
  intros X Z Z'.
  assert (HypX := Hyp X Z Z').
  set (auxiso := functor_on_z_iso H (z_iso_inv (_,,(lassociator_CAT_pointwise_is_z_iso (U Z) (U Z') X)))).
  apply pathsinv0 in HypX. apply (z_iso_inv_on_left _ _ _ _ auxiso) in HypX.
  assumption.
Qed.

Lemma θ_Strength2_int_nicer_implies_θ_Strength2_int: θ_Strength2_int_nicer -> θ_Strength2_int.
  intro Hyp.
  intros X Z Z'.
  assert (HypX := Hyp X Z Z').
  set (auxiso := functor_on_z_iso H (z_iso_inv (_,,(lassociator_CAT_pointwise_is_z_iso (U Z) (U Z') X)))).
  apply (z_iso_inv_to_right _ _ _ _ auxiso).
  assumption.
Qed.

Definition θ_Strength2_int_nicest : UU := ∏ (X : [C, D']) (Z Z' : Ptd),
      θ (X ⊗ (Z p• Z'))  =
      θ (X ⊗ Z') •• (U Z) ·
        θ ((functor_compose (U Z') X) ⊗ Z) ·
        #H (lassociator_CAT (U Z) (U Z') X ).

Lemma θ_Strength2_int_nicest_implies_θ_Strength2_int_nicer: θ_Strength2_int_nicest -> θ_Strength2_int_nicer.
Proof.
  intro Hyp.
  intros X Z Z'.
  assert (HypX := Hyp X Z Z').
  do 2 rewrite <- assoc.
  etrans.
  2: { apply maponpaths.
       rewrite assoc.
       exact HypX. }
  apply pathsinv0.
  apply (id_left(a:=functor_compose (U Z ∙ U Z') (H X))).
Qed.

Lemma θ_Strength2_int_nicer_implies_θ_Strength2_int_nicest: θ_Strength2_int_nicer -> θ_Strength2_int_nicest.
Proof.
  intro Hyp.
  intros X Z Z'.
  assert (HypX := Hyp X Z Z').
  etrans. { exact HypX. }
  etrans.
  { do 2 apply cancel_postcomposition.
    apply (id_left(a:=functor_compose (U Z ∙ U Z') (H X))). }
  apply idpath.
Qed.

End Strength_law_2_intensional.

(** Not having a general theory of binatural transformations, we isolate
    naturality in each component here *)

(** an experiment *)
Lemma θ_nat_1_pointfree (X X' : [C, D']) (α : X --> X') (Z : Ptd)
  : compose (C := [C, D])
            (# (functorial_composition _ _ _) ((nat_trans_id (pr1 (U Z)),,# H α):
                                                 [C, C] ⊠ [C, D] ⟦(U Z,, H X), (U Z,, H X') ⟧))
            (θ (X' ⊗ Z)) =
      θ (X ⊗ Z) · # H (
          # (functorial_composition _ _ _) ((nat_trans_id (pr1 (U Z)),, α):
                                               [C, C] ⊠ [C, D'] ⟦(U Z,, X), (U Z,, X') ⟧)
        ).
Proof.
  set (t := nat_trans_ax θ).
  set (t' := t (X ⊗ Z) (X' ⊗ Z)).
  set (t'' := t' (catbinprodmor α (identity _ ))).
  cbn in t''.
  exact t''.
Qed.

Lemma θ_nat_1 (X X' : [C, D']) (α : X --> X') (Z : Ptd)
  : compose (C := [C, D]) (# H α ⋆ nat_trans_id (pr1 (U Z))) (θ (X' ⊗ Z)) =
        θ (X ⊗ Z) · # H (α ⋆ nat_trans_id (pr1 (U Z))).
Proof.
  set (t := nat_trans_ax θ).
  set (t' := t (X ⊗ Z) (X' ⊗ Z)).
  set (t'' := t' (catbinprodmor α (identity _ ))).
  rewrite (@horcomp_post_pre _ _ D).
  rewrite (@horcomp_post_pre _ _ D').
  cbn in t''.
  exact t''.
Qed.

Lemma θ_nat_1_pointwise (X X' : [C, D']) (α : X --> X') (Z : Ptd) (c : C)
  :  pr1 (# H α) ((pr1 Z) c) · pr1 (θ (X' ⊗ Z)) c =
       pr1 (θ (X ⊗ Z)) c · pr1 (# H (α ⋆ nat_trans_id (pr1 Z))) c.
Proof.
  assert (t := θ_nat_1 _ _ α Z).
  assert (t' := nat_trans_eq_weq (homset_property D) _ _ t c).
  clear t.
  cbn in t'. unfold horcomp_data in t'.
  etrans; [| exact t' ].
  clear t'.
  apply pathsinv0.
  etrans.
  { apply cancel_postcomposition.
    apply maponpaths.
    apply functor_id. }
  rewrite <- assoc.
  rewrite id_left.
  apply idpath.
Qed.

Lemma θ_nat_2 (X : [C, D']) (Z Z' : Ptd) (f : Z --> Z')
  : compose (C := [C, D]) (identity (H X) ⋆ pr1 f) (θ (X ⊗ Z')) =
       θ (X ⊗ Z) · # H (identity X ⋆ pr1 f).
Proof.
  set (t := nat_trans_ax θ).
  set (t' := t (X ⊗ Z) (X ⊗ Z') (catbinprodmor (identity _ ) f)).
  rewrite (@horcomp_post_pre _ _ D).
  rewrite (@horcomp_post_pre _ _ D').
  cbn in t'.
  unfold catbinprodmor in t'.
  cbn in t'.
  set (T := functor_id H X).
  cbn in *.
  rewrite T in t'. clear T.
  exact t'.
Qed.

Lemma θ_nat_2_pointwise (X : [C, D']) (Z Z' : Ptd) (f : Z --> Z') (c : C)
  :  # (pr1 (H X)) ((pr1 f) c) · pr1 (θ (X ⊗ Z')) c =
       pr1 (θ (X ⊗ Z)) c · pr1 (# H (identity X ⋆ pr1 f)) c .
Proof.
  set (t := θ_nat_2 X _ _ f).
  set (t' := nat_trans_eq_weq (homset_property D) _ _ t c).
  clearbody t'; clear t.
  cbn in t'. unfold horcomp_data in t'.
  rewrite id_left in t'.
  exact t'.
Qed.

End fix_a_θ.

(** * Definition of encapsulations of strength (locally/globally, with/without laws *)

Definition PrestrengthForSignatureAtPoint (Z: Ptd) : UU :=
  functor_fix_snd_arg [C, D'] Ptd [C, D] θ_source Z ⟹
  functor_fix_snd_arg [C, D'] Ptd [C, D] θ_target Z.

Definition PrestrengthForSignature : UU := θ_source ⟹ θ_target.


Definition nat_trans_data_from_PrestrengthForSignature_funclass (θ: PrestrengthForSignature) :
  ∏ x, θ_source x --> θ_target x := pr1 θ.
Coercion nat_trans_data_from_PrestrengthForSignature_funclass: PrestrengthForSignature >-> Funclass.

Definition nat_trans_data_from_PrestrengthForSignatureAtPoint_funclass (Z: Ptd)(θ: PrestrengthForSignatureAtPoint Z) :
  ∏ x, functor_fix_snd_arg [C, D'] Ptd [C, D] θ_source Z x -->
       functor_fix_snd_arg [C, D'] Ptd [C, D] θ_target Z x := pr1 θ.
Coercion nat_trans_data_from_PrestrengthForSignatureAtPoint_funclass: PrestrengthForSignatureAtPoint >-> Funclass.


Definition StrengthForSignature : UU :=
  ∑ θ : PrestrengthForSignature, θ_Strength1_int θ × θ_Strength2_int θ.

Coercion Strength_Prestrength (θwithlaws: StrengthForSignature) : PrestrengthForSignature := pr1 θwithlaws.


End about_signatures.

Definition Presignature : UU
  := ∑ H : [C, D'] ⟶ [C, D] , PrestrengthForSignature H.

Definition Signature : UU
  := ∑ H : [C, D'] ⟶ [C, D] , StrengthForSignature H.

Coercion Presignature_Functor (S : Presignature) : functor _ _ := pr1 S.
Coercion Signature_Functor (S : Signature) : functor _ _ := pr1 S.
Coercion Presignature_Signature (S : Signature) : Presignature := Signature_Functor S ,, Strength_Prestrength _ (pr2 S).

Definition theta (H : Presignature) : PrestrengthForSignature H := pr2 H.

Definition Sig_strength_law1 (H : Signature) : θ_Strength1_int _ _ := pr1 (pr2 (pr2 H)).

Definition Sig_strength_law2 (H : Signature) : θ_Strength2_int _ _ := pr2 (pr2 (pr2 H)).

Lemma StrengthForSignature_eq (H : [C, D'] ⟶ [C, D] ) (sθ1 sθ2 : StrengthForSignature H) :
  pr1 sθ1 = pr1 sθ2 -> sθ1 = sθ2.
Proof.
  intro Heq.
  apply subtypePath; trivial.
  intro θ. apply isapropdirprod.
  + apply isaprop_θ_Strength1_int.
  + apply isaprop_θ_Strength2_int.
Qed.

End fix_a_category.

Arguments PrestrengthForSignature {_ _ _} _ .
Arguments StrengthForSignature {_ _ _} _ .
Arguments Presignature_Signature {_ _ _} _ .
Arguments theta {_ _ _} _ .
Arguments θ_source {_ _ _ } _ .
Arguments θ_target {_ _ _ } _ .
Arguments θ_Strength1 {_ _ _ _ } _ .
Arguments θ_Strength2 {_ _ _ _ } _ .
Arguments θ_Strength1_int {_ _ _ _} _ .
Arguments θ_Strength2_int {_ _ _ _} _ .
Arguments Sig_strength_law1 {_ _ _} _.
Arguments Sig_strength_law2 {_ _ _} _.
Arguments Signature_Functor {_ _ _} _.
Arguments θ_Strength1_int_implies_θ_Strength1 {_ _ _ _} _ _.
Arguments θ_Strength2_int_implies_θ_Strength2 {_ _ _ _} _ _.
Arguments θ_Strength2_int_implies_θ_Strength2_int_nicer {_ _ _ _} _ _.
