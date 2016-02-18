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


Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.Notation.


Arguments θ_source {_ _} _ .
Arguments θ_target {_ _} _ .
Arguments θ_Strength1 {_ _ _} _ .
Arguments θ_Strength2 {_ _ _} _ .

Section Preparations.

Variable C : precategory.
Variable hs : has_homsets C.
Variable CP : Products C.
Variable CC : Coproducts C.
Variable terminal : Terminal C.
Let one : C :=  @TerminalObject C terminal.

Definition square_functor := product_functor C C CP (functor_identity C) (functor_identity C).

Definition option_functor: functor C C := coproduct_functor _ _ CC (constant_functor _ _  one) (functor_identity C).

End Preparations.


Section Lambda.

Variable C : precategory.
Variable hs : has_homsets C.

(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]) .

Variable terminal : Terminal C.

Variable CC : Coproducts C.
Variable CP : Products C.

Let one : C :=  @TerminalObject C terminal.

(**
   [App_H (X) (A) :=  X(A) × X(A)]
*)
Definition App_H : functor EndC EndC.
Proof.
  apply square_functor.
  apply Products_functor_precat.
  exact CP.
Defined.

(**
   [Abs_H (X) := X o option]
*)

Definition Abs_H_ob (X: EndC): functor C C := functor_composite (option_functor _ CC terminal) X.

(* works only with -type-in-type:
Definition Abs_H_mor_nat_trans_data (X X': EndC)(α: X ⇒ X'): ∀ c, Abs_H_ob X c ⇒ Abs_H_ob X' c.
Proof.
  intro.
  unfold Abs_H_ob.
  red. simpl. apply α.
Defined.
*)

Definition Abs_H_mor_nat_trans_data (X X': functor C C)(α: nat_trans X X'): ∀ c, Abs_H_ob X c ⇒ Abs_H_ob X' c.
Proof.
  intro.
  apply α.
Defined.

Lemma is_nat_trans_Abs_H_mor_nat_trans_data  (X X': EndC)(α: X ⇒ X'): is_nat_trans _ _ (Abs_H_mor_nat_trans_data X X' α).
Proof.
  red.
  intros c c' f.
  destruct α as [α α_nat_trans].
  unfold Abs_H_mor_nat_trans_data, Abs_H_ob.
  simpl.
  apply α_nat_trans.
 Qed.

Definition Abs_H_mor (X X': EndC)(α: X ⇒ X'): (Abs_H_ob X: ob EndC) ⇒ Abs_H_ob X'.
Proof.
  exists (Abs_H_mor_nat_trans_data X X' α).
  exact (is_nat_trans_Abs_H_mor_nat_trans_data X X' α).
Defined.

Definition Abs_H_functor_data: functor_data EndC EndC.
Proof.
  exists Abs_H_ob.
  exact Abs_H_mor.
Defined.

Lemma is_functor_Abs_H_data: is_functor Abs_H_functor_data.
Proof.
  red.
  split; red.
  + intros X.
    unfold Abs_H_functor_data.
    simpl.
    apply nat_trans_eq; try assumption.
    intro c.
    unfold Abs_H_mor.
    simpl.
    apply idpath.
  + intros X X' X'' α β.
    unfold Abs_H_functor_data.
    simpl.
    apply nat_trans_eq; try assumption.
    intro c.
    unfold Abs_H_mor.
    simpl.
    apply idpath.
Qed.

Definition Abs_H : functor [C, C, hs] [C, C, hs] := tpair _ _ is_functor_Abs_H_data.


(**
   [Flat_H (X) := X o X]

   ingredients:
     - functor_composite in CategoryTheory.functor_categories
     - map given by horizontal composition in Substsystems.HorizontalComposition

 Alternatively : free in two arguments, then precomposed with diagonal

*)
Definition Flat_H_ob (X: EndC): functor C C := functor_composite X X.
Definition Flat_H_mor (X X': EndC)(α: X ⇒ X'): (Flat_H_ob X: EndC) ⇒ Flat_H_ob X' := α ∙∙ α.
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


Definition App_θ_data: ∀ XZ, (θ_source App_H)XZ ⇒ (θ_target App_H)XZ.
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
  destruct XZ as [X Z];
  destruct XZ' as [X' Z'];
  destruct αβ as [α β];
  simpl in *.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_left.
  rewrite id_right.
  unfold product_nat_trans_data, product_functor_mor.
  unfold ProductOfArrows.
  eapply pathscomp0.
  apply precompWithProductArrow.
  simpl.
  unfold product_nat_trans_pr1_data. unfold product_nat_trans_pr2_data.
  simpl.
  apply ProductArrowUnique.
  + rewrite ProductPr1Commutes.
    repeat rewrite assoc.
    rewrite ProductPr1Commutes.
    apply idpath.
  + rewrite ProductPr2Commutes.
    repeat rewrite assoc.
    rewrite ProductPr2Commutes.
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
  unfold product_nat_trans_data.
  apply pathsinv0.
  apply ProductArrowUnique.
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
  unfold product_nat_trans_data.
  apply pathsinv0.
  apply ProductArrowUnique.
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


Definition Abs_θ_data_data: ∀ XZ A, ((θ_source Abs_H)XZ: functor C C) A ⇒ ((θ_target Abs_H)XZ: functor C C) A.
Proof.
  intro XZ.
(*
  destruct XZ as [X Z].
*)
  simpl.
  intro A.
  apply (functor_on_morphisms (functor_data_from_functor _ _ (pr1 XZ))).
  unfold coproduct_functor_ob.
  unfold constant_functor.
  simpl.
(*
  destruct Z as [Z e].
*)
  simpl.
  apply CoproductArrow.
  + exact (CoproductIn1 _ _ ;;
           nat_trans_data (pr2 (pr2 XZ)) (CoproductObject C (CC (TerminalObject terminal) A))).
  + exact (# (pr1 (pr2 XZ)) (CoproductIn2 _ (CC (TerminalObject terminal) A))).
Defined.

Lemma is_nat_trans_Abs_θ_data_data: ∀ XZ, is_nat_trans _ _ (Abs_θ_data_data XZ).
Proof.

  intro XZ.
  intros c c' f.
  unfold Abs_θ_data_data.
  simpl.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  apply maponpaths.
  unfold coproduct_functor_mor.
  eapply pathscomp0.
  apply precompWithCoproductArrow.
  eapply pathscomp0.
Focus 2.
  apply (!(postcompWithCoproductArrow _ _ _ _ _)).
  simpl.
  rewrite id_left.
  rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  simpl.
  apply CoproductArrow_eq.
  + assert (NN :=  nat_trans_ax (pr2 (pr2 XZ)) _ _ (CoproductOfArrows C (CC (TerminalObject terminal) c) (CC (TerminalObject terminal) c')
         (identity (TerminalObject terminal)) f)).
    match goal with |[ H1: _ = ?f;;?g |- _ = ?h ;; _ ] =>
         pathvia (h;;(f;;g)) end.
    * rewrite <- NN.
      clear NN.
      unfold functor_identity.
      simpl.
      rewrite assoc.
      rewrite CoproductOfArrowsIn1.
      rewrite id_left.
      apply idpath.
    * apply idpath.
  + apply maponpaths.
    eapply pathscomp0.
Focus 2.
    apply (!(CoproductOfArrowsIn2 _ _ _ _ _ )).
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
  apply precompWithCoproductArrow.
  eapply pathscomp0.
Focus 2.
  apply (!(postcompWithCoproductArrow _ _ _ _ _)).
  simpl.
  rewrite id_left.
  rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  simpl.
  apply CoproductArrow_eq.
  + assert (NN :=  nat_trans_ax e _ _ (CoproductOfArrows C (CC (TerminalObject terminal) c) (CC (TerminalObject terminal) c')
         (identity (TerminalObject terminal)) f)).
    match goal with |[ H1: _ = ?f;;?g |- _ = ?h ;; _ ] =>
         pathvia (h;;(f;;g)) end.
    * rewrite <- NN.
      clear NN.
      unfold functor_identity.
      simpl.
      rewrite assoc.
      rewrite CoproductOfArrowsIn1.
      rewrite id_left.
      apply idpath.
    * apply idpath.
  + apply maponpaths.
    eapply pathscomp0.
Focus 2.
    apply (!(CoproductOfArrowsIn2 _ _ _ _ _ )).
    apply idpath.
*)
Qed.


Definition Abs_θ_data: ∀ XZ, (θ_source Abs_H)XZ ⇒ (θ_target Abs_H)XZ.
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
  unfold coproduct_functor_ob.
  simpl.
  rewrite assoc.
  unfold Abs_θ_data_data. simpl.
  rewrite (nat_trans_ax α).
  do 2 rewrite <- assoc.
  apply maponpaths.
  do 2 rewrite <- functor_comp.
  apply maponpaths.
  unfold coproduct_functor_mor, constant_functor_data.
  simpl.
  eapply pathscomp0. apply precompWithCoproductArrow.
(*  rewrite precompWithCoproductArrow. *)
  eapply pathscomp0. Focus 2. eapply pathsinv0.
  apply postcompWithCoproductArrow.
(*
  eapply cancel_postcomposition. apply postcompWithCoproductArrow.
*)
(*  rewrite postcompWithCoproductArrow. *)
  apply CoproductArrow_eq.
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
  apply CoproductArrowUnique.
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
  apply postcompWithCoproductArrow.
  simpl in *.
  apply CoproductArrow_eq.
  + rewrite <- assoc.
    assert (NN := nat_trans_ax e' _ _ (e (CoproductObject C (CC (TerminalObject terminal) c)))).
    simpl in NN. (* is important for success of the trick *)
    match goal with |[ H1: _ = ?f;;?g |- ?h ;; _ = _ ] =>
         pathvia (h;;(f;;g)) end.
    * apply idpath.
    * simpl. rewrite <- NN.
      clear NN.
      assert (NNN := nat_trans_ax e' _ _ (CoproductArrow C (CC (TerminalObject terminal) (Z c))
         (CoproductIn1 C (CC (TerminalObject terminal) c);;
          e (CoproductObject C (CC (TerminalObject terminal) c)))
         (# Z (CoproductIn2 C (CC (TerminalObject terminal) c))))).
      simpl in NNN.
      match goal with |[ H1: _ = ?f;;?g |- _ = ?h ;; _] =>
         pathvia (h;;(f;;g)) end.
      - simpl. rewrite <- NNN.
        clear NNN.
        do 2 rewrite assoc.
        rewrite CoproductIn1Commutes.
        apply idpath.
      - apply idpath.
  + rewrite <- functor_comp.
    apply maponpaths.
    eapply pathscomp0.
Focus 2.
    eapply pathsinv0.
    apply CoproductIn2Commutes.
    apply idpath.
Qed.


Definition Flat_θ_data: ∀ XZ, (θ_source Flat_H)XZ ⇒ (θ_target Flat_H)XZ.
Proof.
  intro XZ.
(*  destruct XZ as [X [Z e]].
  simpl.
*)
  set (h:= nat_trans_comp (λ_functor_inv _ (pr1 XZ)) ((nat_trans_id _) ∙∙ (pr2 (pr2 XZ)))).
  exact (nat_trans_comp (α_functor_inv _ (pr1 (pr2 XZ)) (pr1 XZ) (pr1 XZ)) (h ∙∙ (nat_trans_id (functor_composite (pr1 (pr2 XZ)) (pr1 XZ))))).
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

Definition App_Sig: Signature C hs.
Proof.
  exists App_H.
  exists App_θ.
  split.
  + exact App_θ_strength1_int.
  + exact App_θ_strength2_int.
Defined.

Definition Abs_Sig: Signature C hs.
Proof.
  exists Abs_H.
  exists Abs_θ.
  split.
  + exact Abs_θ_strength1_int.
  + exact Abs_θ_strength2_int.
Defined.

Definition Flat_Sig: Signature C hs.
Proof.
  exists Flat_H.
  exists Flat_θ.
  split.
  + exact Flat_θ_strength1_int.
  + exact Flat_θ_strength2_int.
Defined.


Definition Lam_Sig: Signature C hs :=
  Sum_of_Signatures C hs CC App_Sig Abs_Sig.

Definition LamE_Sig: Signature C hs :=
  Sum_of_Signatures C hs CC Lam_Sig Flat_Sig.


End Lambda.
