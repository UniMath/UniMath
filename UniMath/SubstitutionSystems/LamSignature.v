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

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.BinSumOfSignatures.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.CategoryTheory.CocontFunctors.
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

   ingredients:
     - functor_composite in CategoryTheory.functor_categories
     - map given by horizontal composition in Substsystems.HorizontalComposition

 Alternatively : free in two arguments, then precomposed with diagonal

*)
Definition Flat_H_ob (X: EndC): functor C C := functor_composite X X.
Definition Flat_H_mor (X X': EndC)(α: X --> X'): (Flat_H_ob X: EndC) --> Flat_H_ob X' := α ∙∙ α.
Definition Flat_H_functor_data: functor_data EndC EndC.
Proof.
  exists Flat_H_ob.
  exact Flat_H_mor.
Defined.

Lemma is_functor_Flat_H_data: is_functor Flat_H_functor_data.
Proof.
  red.
  split; red.
  + intros X.
    unfold Flat_H_functor_data.
    simpl.
    unfold Flat_H_mor.
    apply nat_trans_eq; try assumption.
    intro c.
    simpl.
    rewrite id_left.
    apply functor_id.
  + intros X X' X'' α β.
    unfold Flat_H_functor_data.
    simpl.
    unfold Flat_H_mor.
    apply nat_trans_eq; try assumption.
    intro c.
    simpl.
    rewrite functor_comp.
    repeat rewrite <- assoc.
    apply maponpaths.
    repeat rewrite assoc.
    rewrite (nat_trans_ax β).
    apply idpath.
Qed.

Definition Flat_H : functor [C, C, hs] [C, C, hs] := tpair _ _ is_functor_Flat_H_data.



(** here definition of suitable θ's together with their strength laws  *)


Definition App_θ_data: ∏ XZ, (θ_source App_H)XZ --> (θ_target App_H)XZ.
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
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_left.
  rewrite id_right.
  unfold binproduct_nat_trans_data, BinProduct_of_functors_mor.
  unfold BinProductOfArrows.
  eapply pathscomp0.
  apply precompWithBinProductArrow.
  simpl.
  unfold binproduct_nat_trans_pr1_data. unfold binproduct_nat_trans_pr2_data.
  simpl.
  apply BinProductArrowUnique.
  + rewrite BinProductPr1Commutes.
    repeat rewrite assoc.
    rewrite BinProductPr1Commutes.
    apply idpath.
  + rewrite BinProductPr2Commutes.
    repeat rewrite assoc.
    rewrite BinProductPr2Commutes.
    apply idpath.
Qed.

Definition App_θ: nat_trans (θ_source App_H) (θ_target App_H) :=
  tpair _ _ is_nat_trans_App_θ_data.

Lemma App_θ_strength1_int: θ_Strength1_int App_θ.
Proof.
  red.
  intro.
  unfold App_θ, App_H.
  simpl.
  unfold App_θ_data.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_left.
  unfold binproduct_nat_trans_data.
  apply pathsinv0.
  apply BinProductArrowUnique.
  + rewrite id_left.
    unfold EndofunctorsMonoidal.λ_functor.
    unfold EndofunctorsMonoidal.ρ_functor.
    simpl.
    rewrite id_right.
    apply idpath.
  + rewrite id_left.
    unfold EndofunctorsMonoidal.λ_functor.
    unfold EndofunctorsMonoidal.ρ_functor.
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
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  do 3 rewrite id_left.
  unfold binproduct_nat_trans_data.
  apply pathsinv0.
  apply BinProductArrowUnique.
  + rewrite id_left.
    unfold EndofunctorsMonoidal.α_functor.
    simpl.
    rewrite id_right.
    apply idpath.
  + rewrite id_left.
    unfold EndofunctorsMonoidal.α_functor.
    simpl.
    rewrite id_right.
    apply idpath.
Qed.


Definition Abs_θ_data_data: ∏ XZ A, ((θ_source Abs_H)XZ: functor C C) A --> ((θ_target Abs_H)XZ: functor C C) A.
Proof.
  intro XZ.
(*
  destruct XZ as [X Z].
*)
  simpl.
  intro A.
  apply (functor_on_morphisms (functor_data_from_functor _ _ (pr1 XZ))).
  unfold BinCoproduct_of_functors_ob.
  unfold constant_functor.
  simpl.
(*
  destruct Z as [Z e].
*)
  simpl.
  apply BinCoproductArrow.
  + exact (BinCoproductIn1 _ _ ·
           nat_trans_data (pr2 (pr2 XZ)) (BinCoproductObject C (CC (TerminalObject terminal) A))).
  + exact (# (pr1 (pr2 XZ)) (BinCoproductIn2 _ (CC (TerminalObject terminal) A))).
Defined.

Lemma is_nat_trans_Abs_θ_data_data: ∏ XZ, is_nat_trans _ _ (Abs_θ_data_data XZ).
Proof.

  intro XZ.
  intros c c' f.
  unfold Abs_θ_data_data.
  simpl.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  apply maponpaths.
  unfold BinCoproduct_of_functors_mor.
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
  apply BinCoproductArrow_eq.
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
    eapply pathscomp0.
Focus 2.
    apply (!(BinCoproductOfArrowsIn2 _ _ _ _ _ )).
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
  apply BinCoproductArrow_eq.
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


Definition Abs_θ_data: ∏ XZ, (θ_source Abs_H)XZ --> (θ_target Abs_H)XZ.
Proof.
  intro XZ.
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
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  simpl in *.
  unfold constant_functor.
  unfold BinCoproduct_of_functors_ob.
  simpl.
  rewrite assoc.
  unfold Abs_θ_data_data. simpl.
  rewrite (nat_trans_ax α).
  do 2 rewrite <- assoc.
  apply maponpaths.
  do 2 rewrite <- functor_comp.
  apply maponpaths.
  unfold BinCoproduct_of_functors_mor, constant_functor_data.
  simpl.
  eapply pathscomp0. apply precompWithBinCoproductArrow.
(*  rewrite precompWithBinCoproductArrow. *)
  eapply pathscomp0. Focus 2. eapply pathsinv0.
  apply postcompWithBinCoproductArrow.
(*
  eapply cancel_postcomposition. apply postcompWithBinCoproductArrow.
*)
(*  rewrite postcompWithBinCoproductArrow. *)
  apply BinCoproductArrow_eq.
  + rewrite id_left.
    rewrite <- assoc.
    rewrite <- (ptd_mor_commutes _ β).
    apply idpath.
  + simpl in *.
    apply pathsinv0.
    apply (nat_trans_ax β).
Qed.

Definition Abs_θ: nat_trans (θ_source Abs_H) (θ_target Abs_H) :=
  tpair _ _ is_nat_trans_Abs_θ_data.

Lemma Abs_θ_strength1_int: θ_Strength1_int Abs_θ.
Proof.
  red.
  intro.
  unfold Abs_θ, Abs_H.
  simpl.
  unfold Abs_θ_data.
  apply nat_trans_eq; try assumption.
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
  red.
  intros.
  unfold Abs_θ, Abs_H.
  simpl.
  unfold Abs_θ_data.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_left.
  rewrite id_right.
  unfold Abs_θ_data_data. simpl.
  rewrite <- functor_comp.
  apply maponpaths.
  clear X.
  destruct Z as [Z e];
  destruct Z' as [Z' e'];
  simpl.
  eapply pathscomp0.
Focus 2.
  eapply pathsinv0.
  apply postcompWithBinCoproductArrow.
  simpl in *.
  apply BinCoproductArrow_eq.
  + rewrite <- assoc.
    assert (NN := nat_trans_ax e' _ _ (e (BinCoproductObject C (CC (TerminalObject terminal) c)))).
    simpl in NN. (* is important for success of the trick *)
    match goal with |[ H1: _ = ?f·?g |- ?h · _ = _ ] =>
         intermediate_path (h·(f·g)) end.
    * apply idpath.
    * simpl. rewrite <- NN.
      clear NN.
      assert (NNN := nat_trans_ax e' _ _ (BinCoproductArrow C (CC (TerminalObject terminal) (Z c))
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
        apply idpath.
      - apply idpath.
  + rewrite <- functor_comp.
    apply maponpaths.
    eapply pathscomp0.
Focus 2.
    eapply pathsinv0.
    apply BinCoproductIn2Commutes.
    apply idpath.
Qed.


Definition Flat_θ_data: ∏ XZ, (θ_source Flat_H)XZ --> (θ_target Flat_H)XZ.
Proof.
  intro XZ.
(*  destruct XZ as [X [Z e]].
  simpl.
*)
  set (h:= nat_trans_comp (λ_functor_inv (pr1 XZ)) ((nat_trans_id _) ∙∙ (pr2 (pr2 XZ)))).
  exact (nat_trans_comp (α_functor_inv (pr1 (pr2 XZ)) (pr1 XZ) (pr1 XZ)) (h ∙∙ (nat_trans_id (functor_composite (pr1 (pr2 XZ)) (pr1 XZ))))).
Defined.

Lemma is_nat_trans_Flat_θ_data: is_nat_trans _ _ Flat_θ_data.
Proof.
  red.
  intros XZ XZ' αβ.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  destruct XZ as [X [Z e]];
  destruct XZ' as [X' [Z' e']];
  destruct αβ as [α β];
  simpl in *.
  repeat rewrite id_left.
  do 4 rewrite functor_id.
  do 2 rewrite id_right.
  repeat rewrite <- assoc.
  do 3 rewrite <- functor_comp.
  repeat rewrite assoc.
  rewrite (nat_trans_ax α).
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite <- functor_comp.
  apply maponpaths.
  repeat rewrite assoc.
  assert (β_is_pointed := ptd_mor_commutes _ β).
  simpl in β_is_pointed.
  rewrite β_is_pointed.
  simpl.
  eapply pathscomp0.
Focus 2.
  apply (nat_trans_ax e').
  apply idpath.
Qed.

Definition Flat_θ: nat_trans (θ_source Flat_H) (θ_target Flat_H) :=
  tpair _ _ is_nat_trans_Flat_θ_data.

Lemma Flat_θ_strength1_int: θ_Strength1_int Flat_θ.
Proof.
  red.
  intro.
  unfold Flat_θ, Flat_H.
  simpl.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  repeat rewrite id_left.
  repeat rewrite functor_id.
  repeat rewrite id_left.
  apply idpath.
Qed.

Lemma Flat_θ_strength2_int: θ_Strength2_int Flat_θ.
Proof.
  red.
  intros.
  destruct Z as [Z e];
  destruct Z' as [Z' e'];
  simpl.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  repeat rewrite id_left.
  repeat rewrite <- functor_comp.
  apply maponpaths.
  repeat rewrite functor_id.
  repeat rewrite id_right.
  apply idpath.
Qed.

(** finally, constitute the 3 signatures *)

Definition App_Sig: Signature C hs C hs.
Proof.
  exists App_H.
  exists App_θ.
  split.
  + exact App_θ_strength1_int.
  + exact App_θ_strength2_int.
Defined.

Definition Abs_Sig: Signature C hs C hs.
Proof.
  exists Abs_H.
  exists Abs_θ.
  split.
  + exact Abs_θ_strength1_int.
  + exact Abs_θ_strength2_int.
Defined.

Definition Flat_Sig: Signature C hs C hs.
Proof.
  exists Flat_H.
  exists Flat_θ.
  split.
  + exact Flat_θ_strength1_int.
  + exact Flat_θ_strength2_int.
Defined.

Definition Lam_Sig: Signature C hs C hs :=
  BinSum_of_Signatures C hs C hs CC App_Sig Abs_Sig.

Lemma is_omega_cocont_Lam
  (hE : ∏ x, is_omega_cocont (constprod_functor1 (BinProducts_functor_precat C C CP hs) x))
  (LC : Colims_of_shape nat_graph C) : is_omega_cocont (Signature_Functor _ _ _ _ Lam_Sig).
Proof.
apply is_omega_cocont_BinCoproduct_of_functors.
- apply functor_category_has_homsets.
- apply (is_omega_cocont_App_H hE).
- apply (is_omega_cocont_Abs_H LC).
Defined.

Definition LamE_Sig: Signature C hs C hs :=
  BinSum_of_Signatures C hs C hs CC Lam_Sig Flat_Sig.

End Lambda.
