(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Definition of the arities of the constructors of lambda calculus
- Definition of the signatures of lambda calculus and lambda calculus with explicit flattening




************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.CategoryTheory.Monoidal.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.SubstitutionSystems.BinSumOfSignatures.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.


Section Preparations.

Variable C : precategory.
Variable hs : has_homsets C.
Variable CP : BinProducts C.
Variable CC : BinCoproducts C.

Definition square_functor := BinProduct_of_functors C C CP (functor_identity C) (functor_identity C).

End Preparations.

Section Lambda.

Variable C : precategory.
Variable hs : has_homsets C.

(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]) .

Variable terminal : Terminal C.

Variable CC : BinCoproducts C.
Variable CP : BinProducts C.

Let one : C :=  @TerminalObject C terminal.

(**
   [App_H (X) (A) :=  X(A) × X(A)]
*)
Definition App_H : functor EndC EndC.
Proof.
  apply square_functor.
  apply BinProducts_functor_precat.
  exact CP.
Defined.

Lemma is_omega_cocont_App_H
  (hE : ∏ x, is_omega_cocont (constprod_functor1 (BinProducts_functor_precat C C CP hs) x)) :
  is_omega_cocont App_H.
Proof.
  unfold App_H, square_functor.
  apply is_omega_cocont_BinProduct_of_functors; try assumption.
  - apply (BinProducts_functor_precat _ _ CP).
  - apply functor_category_has_homsets.
  - apply functor_category_has_homsets.
  - apply (is_omega_cocont_functor_identity (functor_category_has_homsets _ _ hs)).
  - apply (is_omega_cocont_functor_identity (functor_category_has_homsets _ _ hs)).
Defined.

(**
   [Abs_H (X) := X o option]
*)

(* Definition Abs_H_ob (X: EndC): functor C C := functor_composite (option_functor _ CC terminal) X. *)

(* (* works only with -type-in-type: *)
(* Definition Abs_H_mor_nat_trans_data (X X': EndC)(α: X --> X'): ∏ c, Abs_H_ob X c --> Abs_H_ob X' c. *)
(* Proof. *)
(*   intro. *)
(*   unfold Abs_H_ob. *)
(*   red. simpl. apply α. *)
(* Defined. *)
(* *) *)

(* Definition Abs_H_mor_nat_trans_data (X X': functor C C)(α: nat_trans X X'): ∏ c, Abs_H_ob X c --> Abs_H_ob X' c. *)
(* Proof. *)
(*   intro. *)
(*   apply α. *)
(* Defined. *)

(* Lemma is_nat_trans_Abs_H_mor_nat_trans_data  (X X': EndC)(α: X --> X'): is_nat_trans _ _ (Abs_H_mor_nat_trans_data X X' α). *)
(* Proof. *)
(*   red. *)
(*   intros c c' f. *)
(*   destruct α as [α α_nat_trans]. *)
(*   unfold Abs_H_mor_nat_trans_data, Abs_H_ob. *)
(*   simpl. *)
(*   apply α_nat_trans. *)
(*  Qed. *)

(* Definition Abs_H_mor (X X': EndC)(α: X --> X'): (Abs_H_ob X: ob EndC) --> Abs_H_ob X'. *)
(* Proof. *)
(*   exists (Abs_H_mor_nat_trans_data X X' α). *)
(*   exact (is_nat_trans_Abs_H_mor_nat_trans_data X X' α). *)
(* Defined. *)

(* Definition Abs_H_functor_data: functor_data EndC EndC. *)
(* Proof. *)
(*   exists Abs_H_ob. *)
(*   exact Abs_H_mor. *)
(* Defined. *)

(* Lemma is_functor_Abs_H_data: is_functor Abs_H_functor_data. *)
(* Proof. *)
(*   red. *)
(*   split; red. *)
(*   + intros X. *)
(*     unfold Abs_H_functor_data. *)
(*     simpl. *)
(*     apply nat_trans_eq; try assumption. *)
(*     intro c. *)
(*     unfold Abs_H_mor. *)
(*     simpl. *)
(*     apply idpath. *)
(*   + intros X X' X'' α β. *)
(*     unfold Abs_H_functor_data. *)
(*     simpl. *)
(*     apply nat_trans_eq; try assumption. *)
(*     intro c. *)
(*     unfold Abs_H_mor. *)
(*     simpl. *)
(*     apply idpath. *)
(* Qed. *)

Definition Abs_H : functor [C, C, hs] [C, C, hs] :=
 (* tpair _ _ is_functor_Abs_H_data. *)
  pre_composition_functor _ _ _ hs _ (option_functor CC terminal).

Lemma is_omega_cocont_Abs_H (CLC : Colims_of_shape nat_graph C) : is_omega_cocont Abs_H.
Proof.
  unfold Abs_H.
  apply (is_omega_cocont_pre_composition_functor _ _ _ CLC).
Defined.


(**
   [Flat_H (X) := X o X]

 free in two arguments, then precomposed with diagonal

*)

Definition Flat_H : functor [C, C, hs] [C, C, hs] := functor_composite (bindelta_functor [C, C, hs]) (functorial_composition hs hs).

(** here definition of suitable θ's together with their strength laws  *)


Definition App_θ_data: ∏ XZ, (θ_source(hs := hs) App_H) XZ --> (θ_target App_H) XZ.
Proof.
  intro XZ.
  apply nat_trans_id.
Defined.

Lemma is_nat_trans_App_θ_data: is_nat_trans _ _ App_θ_data.
Proof.
  red.
  unfold App_θ_data.
  intros XZ XZ' αβ.
(* the following only for better readability: *)
  (* destruct XZ as [X Z]; *)
  (* destruct XZ' as [X' Z']; *)
  (* destruct αβ as [α β]; *)
  (* simpl in *. *)
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  rewrite id_left.
  rewrite id_right.
  unfold binproduct_nat_trans_data, BinProduct_of_functors_mor.
  unfold BinProductOfArrows.
  etrans; [ apply precompWithBinProductArrow |].
  simpl.
  unfold binproduct_nat_trans_pr1_data. unfold binproduct_nat_trans_pr2_data.
  simpl.
  apply BinProductArrowUnique.
  + rewrite BinProductPr1Commutes.
    repeat rewrite assoc.
    etrans.
    { apply cancel_postcomposition.
      apply BinProductPr1Commutes. }
    apply idpath.
  + rewrite BinProductPr2Commutes.
    repeat rewrite assoc.
    etrans.
    { apply cancel_postcomposition.
      apply BinProductPr2Commutes. }
    apply idpath.
Qed.

Definition App_θ: PrestrengthForSignature App_H :=
  tpair _ _ is_nat_trans_App_θ_data.

Lemma App_θ_strength1_int: θ_Strength1_int App_θ.
Proof.
  red.
  intro.
  unfold App_θ, App_H.
  simpl.
  unfold App_θ_data.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  rewrite id_left.
  unfold binproduct_nat_trans_data.
  apply pathsinv0.
  apply BinProductArrowUnique.
  + rewrite id_left.
    unfold UnitorsAndAssociatorsForEndofunctors.λ_functors.
    simpl.
    rewrite id_right.
    apply idpath.
  + rewrite id_left.
    unfold UnitorsAndAssociatorsForEndofunctors.λ_functors.
    simpl.
    rewrite id_right.
    apply idpath.
Qed.


Lemma App_θ_strength2_int: θ_Strength2_int App_θ.
Proof.
  red.
  intros.
  unfold App_θ, App_H.
  simpl.
  unfold App_θ_data.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  do 3 rewrite id_left.
  unfold binproduct_nat_trans_data.
  apply pathsinv0.
  apply BinProductArrowUnique.
  + rewrite id_left.
    unfold UnitorsAndAssociatorsForEndofunctors.α_functors.
    simpl.
    rewrite id_right.
    apply idpath.
  + rewrite id_left.
    unfold UnitorsAndAssociatorsForEndofunctors.α_functors.
    simpl.
    rewrite id_right.
    apply idpath.
Qed.


Definition Abs_θ_data_data: ∏ XZ c, pr1 (θ_source(hs := hs) Abs_H XZ) c --> pr1 (θ_target Abs_H XZ) c.
Proof.
  intros XZ c.
(*
  destruct XZ as [X Z].
*)
  simpl.
  apply (functor_on_morphisms (functor_data_from_functor _ _ (pr1 XZ))).
  unfold BinCoproduct_of_functors_ob.
  unfold constant_functor.
(*
  destruct Z as [Z e].
*)
  simpl.
  apply BinCoproductArrow.
  + exact (BinCoproductIn1 _ _ ·
           nat_trans_data_from_nat_trans (pr2 (pr2 XZ)) (BinCoproductObject C (CC (TerminalObject terminal) c))).
  + exact (# (pr1 (pr2 XZ)) (BinCoproductIn2 _ (CC (TerminalObject terminal) c))).
Defined.

Lemma is_nat_trans_Abs_θ_data_data (XZ: [C, C, hs] ⊠ precategory_Ptd C hs): is_nat_trans _ _ (Abs_θ_data_data XZ).
Proof.
  intros c c' f.
  unfold Abs_θ_data_data.
  simpl.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  apply maponpaths.
  unfold BinCoproduct_of_functors_mor.
  etrans.
  { apply precompWithBinCoproductArrow. }
  etrans; [| apply (!(postcompWithBinCoproductArrow _ _ _ _ _)) ].
  simpl.
  rewrite id_left.
  rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  apply maponpaths_12.
  + assert (NN :=  nat_trans_ax (pr2 (pr2 XZ)) _ _ (BinCoproductOfArrows C (CC (TerminalObject terminal) c) (CC (TerminalObject terminal) c')
         (identity (TerminalObject terminal)) f)).
    match goal with |[ H1: _ = ?f·?g |- _ = ?h · _ ] =>
         intermediate_path (h·(f·g)) end.
    * rewrite <- NN.
      clear NN.
      unfold functor_identity.
      simpl.
      rewrite assoc.
      rewrite BinCoproductOfArrowsIn1.
      rewrite id_left.
      apply idpath.
    * apply idpath.
  + apply maponpaths.
    etrans; [| apply (!(BinCoproductOfArrowsIn2 _ _ _ _ _ )) ].
    apply idpath.


(*
  intros [X [Z e]].
  red.
  intros c c' f.
  simpl.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  apply maponpaths.
  unfold coproduct_functor_mor.
  eapply pathscomp0.
  apply precompWithBinCoproductArrow.
  eapply pathscomp0.
Focus 2.
  apply (!(postcompWithBinCoproductArrow _ _ _ _ _)).
  simpl.
  rewrite id_left.
  rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  simpl.
  apply maponpaths_12.
  + assert (NN :=  nat_trans_ax e _ _ (BinCoproductOfArrows C (CC (TerminalObject terminal) c) (CC (TerminalObject terminal) c')
         (identity (TerminalObject terminal)) f)).
    match goal with |[ H1: _ = ?f·?g |- _ = ?h · _ ] =>
         intermediate_path (h·(f·g)) end.
    * rewrite <- NN.
      clear NN.
      unfold functor_identity.
      simpl.
      rewrite assoc.
      rewrite BinCoproductOfArrowsIn1.
      rewrite id_left.
      apply idpath.
    * apply idpath.
  + apply maponpaths.
    eapply pathscomp0.
Focus 2.
    apply (!(BinCoproductOfArrowsIn2 _ _ _ _ _ )).
    apply idpath.
*)
Qed.


Definition Abs_θ_data (XZ: [C, C, hs] ⊠ precategory_Ptd C hs): (θ_source(hs := hs) Abs_H) XZ --> (θ_target Abs_H) XZ.
Proof.
  exact (tpair _ _ (is_nat_trans_Abs_θ_data_data XZ)).
Defined.

Lemma is_nat_trans_Abs_θ_data: is_nat_trans _ _ Abs_θ_data.
Proof.
  red.
  intros XZ XZ' αβ.
  destruct XZ as [X [Z e]].
  destruct XZ' as [X' [Z' e']].
  destruct αβ as [α β].
  simpl in *.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  unfold constant_functor.
  unfold BinCoproduct_of_functors_ob.
  simpl.
  rewrite assoc.
  unfold Abs_θ_data_data. simpl.
  rewrite (nat_trans_ax α).
  etrans.
  2: { apply cancel_postcomposition.
       apply functor_comp. }
  rewrite (nat_trans_ax α).
  unfold BinCoproduct_of_functors_ob.
  rewrite <- assoc.
  apply maponpaths.
  etrans.
  { apply pathsinv0, functor_comp. }
  apply maponpaths.
  unfold BinCoproduct_of_functors_mor, constant_functor_data.
  simpl.
  etrans; [ apply precompWithBinCoproductArrow |].
  rewrite id_left.
  etrans.
  2: { eapply pathsinv0.
       apply postcompWithBinCoproductArrow. }
  apply BinCoproductArrowUnique.
  -  rewrite BinCoproductIn1Commutes.
     rewrite <- assoc.
     apply maponpaths.
     apply pathsinv0, (ptd_mor_commutes _ β).
  - rewrite BinCoproductIn2Commutes.
    apply pathsinv0, (nat_trans_ax β).
Qed.

Definition Abs_θ: PrestrengthForSignature Abs_H :=
  tpair _ _ is_nat_trans_Abs_θ_data.

Lemma Abs_θ_strength1_int: θ_Strength1_int Abs_θ.
Proof.
  intro X.
  unfold Abs_θ, Abs_H, Abs_θ_data.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  rewrite id_right.
  apply functor_id_id.
  apply pathsinv0.
  apply BinCoproductArrowUnique.
  + apply idpath.
  + apply id_right.
Qed.

Lemma Abs_θ_strength2_int: θ_Strength2_int Abs_θ.
Proof.
  intros X Z Z'.
  unfold Abs_θ, Abs_H, Abs_θ_data.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  rewrite id_left.
  rewrite id_right.
  unfold Abs_θ_data_data. simpl. unfold horcomp_data; simpl.
  rewrite <- functor_comp.
  apply maponpaths.
  clear X.
  destruct Z as [Z e]; destruct Z' as [Z' e']; etrans.
  2: { eapply pathsinv0.
       apply postcompWithBinCoproductArrow. }
  simpl.
  apply maponpaths_12.
  + rewrite <- assoc.
    assert (NN := nat_trans_ax e' _ _ (e (BinCoproductObject C (CC (TerminalObject terminal) c)))).
    simpl in NN. (* is important for success of the trick *)
    match goal with |[ H1: _ = ?f·?g |- ?h · _ = _ ] =>
         intermediate_path (h·(f·g)) end.
    * apply maponpaths, NN.
    * assert (NNN := nat_trans_ax e' _ _ (BinCoproductArrow C (CC (TerminalObject terminal) (Z c))
         (BinCoproductIn1 C (CC (TerminalObject terminal) c)·
          e (BinCoproductObject C (CC (TerminalObject terminal) c)))
         (# Z (BinCoproductIn2 C (CC (TerminalObject terminal) c))))).
      simpl in NNN.
      match goal with |[ H1: _ = ?f·?g |- _ = ?h · _] =>
         intermediate_path (h·(f·g)) end.
      - simpl. rewrite <- NNN.
        clear NNN.
        do 2 rewrite assoc.
        rewrite BinCoproductIn1Commutes.
        do 2 rewrite <- assoc.
        apply maponpaths, pathsinv0, NN.
      - apply idpath.
  + rewrite <- functor_comp.
    apply maponpaths.
    etrans.
    2: { eapply pathsinv0.
         apply BinCoproductIn2Commutes. }
    apply idpath.
Qed.


Definition Flat_θ_data (XZ: [C, C, hs] ⊠ precategory_Ptd C hs): [C, C, hs] ⟦θ_source(hs := hs) Flat_H XZ, θ_target Flat_H XZ⟧.
Proof.
(*  destruct XZ as [X [Z e]].
  simpl.
*)
  set (h:= nat_trans_comp (λ_functors_inv (pr1 XZ)) ((nat_trans_id _) ⋆ (pr2 (pr2 XZ)))).
  set (F1' := pr1 (pr2 (left_unit_as_nat_z_iso hs hs) (pr1 XZ))).
  set (F2' := # (post_composition_functor _ _ _ hs hs (pr1 XZ)) (pr2 (pr2 XZ))).
  set (h' :=  F1' · F2').
  set (obsolete := nat_trans_comp (α_functors_inv (pr1 (pr2 XZ)) (pr1 XZ) (pr1 XZ)) (h ⋆ (nat_trans_id (functor_composite (pr1 (pr2 XZ)) (pr1 XZ))))).
  set (F3' := pr1 (pr2 (associator_of_endofunctors hs) ((pr1 (pr2 XZ),, pr1 XZ),, pr1 XZ))).
  unfold MonoidalCategories.assoc_right, MonoidalCategories.assoc_left in F3'.
  unfold precategory_binproduct_unassoc, pair_functor, functorial_composition in F3'.
  set (F4' := # (pre_composition_functor _ _ _ hs hs (functor_compose hs hs (pr1 (pr2 XZ)) (pr1 XZ))) h').
  exact (F3' · F4').
Defined.

Lemma is_nat_trans_Flat_θ_data: is_nat_trans _ _ Flat_θ_data.
Proof.
  intros XZ XZ' αβ.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  destruct XZ as [X [Z e]];
  destruct XZ' as [X' [Z' e']];
  destruct αβ as [α β];
  simpl in *.
  repeat rewrite id_left.
  rewrite (functor_comp Z).
  rewrite (functor_comp X).
  repeat rewrite assoc.
  do 4 rewrite <- functor_comp.
  rewrite (nat_trans_ax α).
  repeat rewrite <- assoc.
  rewrite <- functor_comp.
  do 2 rewrite (nat_trans_ax α).
  do 2 apply maponpaths.
  repeat rewrite assoc.
  etrans.
  2: { do 2 apply cancel_postcomposition.
       apply (nat_trans_ax e). }
  cbn.
  assert (β_is_pointed := ptd_mor_commutes _ β).
  simpl in β_is_pointed.
  rewrite <- (nat_trans_ax α).
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  etrans.
  2: { apply cancel_postcomposition.
       apply (nat_trans_ax e). }
  cbn.
  rewrite <- assoc.
  rewrite β_is_pointed.
  apply idpath.
Qed.

Definition Flat_θ: PrestrengthForSignature Flat_H :=
  tpair _ _ is_nat_trans_Flat_θ_data.

Lemma Flat_θ_strength1_int: θ_Strength1_int Flat_θ.
Proof.
  intro.
  unfold Flat_θ, Flat_H.
  apply (nat_trans_eq hs).
  intro c.
  simpl.
  do 2 rewrite id_left.
  rewrite functor_id.
  rewrite id_left.
  rewrite id_right.
  apply functor_id.
Qed.

Lemma Flat_θ_strength2_int: θ_Strength2_int Flat_θ.
Proof.
  intros ? ? ?.
  apply (nat_trans_eq hs).
  intro c.
  cbn.
  repeat rewrite id_left.
  rewrite id_right.
  repeat rewrite <- functor_comp.
  apply maponpaths.
  repeat rewrite functor_id.
  rewrite id_right.
  set (c' := pr1 X (pr1 Z' (pr1 Z c))).
  change (pr1 (ptd_pt C Z) c' · pr1 (ptd_pt C Z') (pr1 (pr1 (pr1 Z)) c') =
            pr1 (pr2 Z') c' · # (pr1 Z') (pr1 (pr2 Z) c')).
  etrans.
  2: { apply (nat_trans_ax (pr2 Z')). }
  apply idpath.
Qed.

(** finally, constitute the 3 signatures *)

Definition App_Sig: Signature C hs C hs C hs.
Proof.
  exists App_H.
  exists App_θ.
  split.
  + exact App_θ_strength1_int.
  + exact App_θ_strength2_int.
Defined.

Definition Abs_Sig: Signature C hs C hs C hs.
Proof.
  exists Abs_H.
  exists Abs_θ.
  split.
  + exact Abs_θ_strength1_int.
  + exact Abs_θ_strength2_int.
Defined.

Definition Flat_Sig: Signature C hs C hs C hs.
Proof.
  exists Flat_H.
  exists Flat_θ.
  split.
  + exact Flat_θ_strength1_int.
  + exact Flat_θ_strength2_int.
Defined.

Definition Lam_Sig: Signature C hs C hs C hs :=
  BinSum_of_Signatures C hs C hs C hs CC App_Sig Abs_Sig.

Lemma is_omega_cocont_Lam
  (hE : ∏ x, is_omega_cocont (constprod_functor1 (BinProducts_functor_precat C C CP hs) x))
  (LC : Colims_of_shape nat_graph C) : is_omega_cocont (Signature_Functor Lam_Sig).
Proof.
  apply is_omega_cocont_BinCoproduct_of_functors.
  - apply functor_category_has_homsets.
  - apply (is_omega_cocont_App_H hE).
  - apply (is_omega_cocont_Abs_H LC).
Defined.

Definition LamE_Sig: Signature C hs C hs C hs :=
  BinSum_of_Signatures C hs C hs C hs CC Lam_Sig Flat_Sig.

End Lambda.
