(** **********************************************************

Contents:

- Derivation of Generalized Iteration in Mendler-style
  Instantiation to a special case, Specialized
- Mendler Iteration Proof of a fusion law à la Bird-Paterson
  (Generalised folds for nested datatypes, theorem 1) for
  Generalized Iteration in Mendler-style

This file differs from GenMendlerIteration.v in the hypotheses.
Here we use omega cocontinuity instead of Kan extensions.

Written by: Anders Mörtberg, 2016.
Based on a note by Ralph Matthes.

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "↓ f" := (mor_from_algebra_mor _ _ _ f) (at level 3, format "↓ f").
Local Notation "'chain'" := (diagram nat_graph).

(** Goal: derive Generalized Iteration in Mendler-style and a fusion law *)

(** * Generalized Iteration in Mendler-style *)
Section GenMenIt.

Context {C : precategory} (hsC : has_homsets C) (IC : Initial C)
        (CC : Colims_of_shape nat_graph C) (F : functor C C)
        (HF : is_omega_cocont F).

Local Notation "0" := (InitialObject IC).

Let AF := FunctorAlg F hsC.
Let chnF := initChain IC F.
Let μF_Initial : Initial AF := colimAlgInitial hsC IC HF (CC chnF).
Let μF : C := alg_carrier _ (InitialObject μF_Initial).
Let inF : C⟦F μF,μF⟧ := alg_map _ (InitialObject μF_Initial).
Let e : ∏ (n : nat), C⟦iter_functor F n IC,μF⟧ := colimIn (CC chnF).
Let cocone_μF : cocone chnF μF := colimCocone (CC chnF).

Local Lemma e_comm (n : nat) : e (S n) = # F (e n) · inF.
Proof.
apply pathsinv0,
      (colimArrowCommutes (mk_ColimCocone _ _ _ (HF _ _ _
                          (isColimCocone_from_ColimCocone (CC chnF))))).
Qed.

Context {D : precategory} (hsD : has_homsets D).

Section the_iteration_principle.

Variables (X : D) (L : functor C D) (IL : isInitial D (L 0)) (HL : is_omega_cocont L).

Let ILD : Initial D := tpair _ _ IL.
Local Notation "'L0'" := (InitialObject ILD).

Let Yon : functor D^op HSET := yoneda_objects D hsD X.

Definition ψ_source : functor C^op HSET := functor_composite (functor_opp L) Yon.
Definition ψ_target : functor C^op HSET := functor_composite (functor_opp F) ψ_source.

Section general_case.

Variable (ψ : ψ_source ⟹ ψ_target).

Let LchnF : chain D := mapchain L chnF.
Let z : D⟦L0,X⟧ := InitialArrow ILD X.

Local Definition Pow_source : functor C^op HSET := ψ_source.
Local Definition Pow_target (n : nat) : functor C^op HSET :=
  functor_composite (functor_opp (iter_functor F n)) ψ_source.

Local Definition Pow (n : nat) : Pow_source ⟹ Pow_target n.
Proof.
induction n as [|n Pown].
- apply nat_trans_id.
- apply (nat_trans_comp Pown (pre_whisker (functor_opp (iter_functor F n)) ψ)).
Defined.

Local Lemma Pow_cocone_subproof n :
  dmor LchnF (idpath (S n)) · pr1 (Pow (S n)) IC z = pr1 (Pow n) IC z.
Proof.
induction n as [|n IHn].
+ cbn.
  apply (InitialArrowUnique ILD).
+ change (pr1 (Pow (S (S n))) _ z) with (ψ (iter_functor F (S n) 0) (Pow (S n) _ z)).
  assert (H : dmor LchnF (idpath (S (S n))) · ψ ((iter_functor F (S n)) IC) ((Pow (S n)) IC z) =
              ψ (iter_functor F n 0) (dmor LchnF (idpath (S n)) · pr1 (Pow (S n)) _ z)).
    apply pathsinv0, (toforallpaths _ _ _ (nat_trans_ax ψ _ _ (dmor chnF (idpath (S n))))).
  now rewrite H, IHn.
Qed.

Local Definition Pow_cocone : cocone LchnF X.
Proof.
use mk_cocone.
- intro n.
  apply (pr1 (Pow n) _ z).
- abstract (intros n m []; clear m; apply Pow_cocone_subproof).
Defined.

Local Definition CC_LchnF : ColimCocone LchnF.
Proof.
use mk_ColimCocone.
- apply (L μF).
- apply (mapcocone L _ cocone_μF).
- apply HL, (isColimCocone_from_ColimCocone (CC chnF)).
Defined.

Definition preIt : D⟦L μF,X⟧ := colimArrow CC_LchnF X Pow_cocone.

Local Lemma eqSS n : # L (e n) · preIt = Pow n IC z.
Proof.
apply (colimArrowCommutes CC_LchnF).
Qed.

Local Lemma is_iso_inF : is_iso inF.
Proof.
(* Use Lambek's lemma, this could be extracted from the concrete proof as well *)
apply (initialAlg_is_iso _ hsC), pr2.
Defined.

Let inF_iso : iso (F μF) μF := isopair _ is_iso_inF.
Let inF_inv : C⟦μF,F μF⟧ := inv_from_iso inF_iso.

(* The direction * -> ** *)
Lemma S_imp_SS h n : # L inF · h = ψ μF h → # L (e n) · h = Pow n IC z.
Proof.
intros Hh.
induction n.
- cbn.
  apply (InitialArrowUnique ILD).
- rewrite e_comm, functor_comp, <- assoc, Hh.
  assert (H : # L (# F (e n)) · ψ μF h = ψ (iter_functor F n 0) (# L (e n) · h)).
    apply pathsinv0, (toforallpaths _ _ _ (nat_trans_ax ψ _ _ (e n))).
  now rewrite H, IHn.
Qed.

(* The direction ** -> * *)
Local Lemma SS_imp_S (H : ∏ n, # L (e n) · preIt = Pow n IC z) : # L inF · preIt = ψ μF preIt.
Proof.
assert (H'' : # L inF · # L inF_inv = identity _).
{ rewrite <- functor_comp,  <- functor_id.
   apply maponpaths, (iso_inv_after_iso inF_iso). }
assert (H' : ∏ n, # L (e (S n)) · # L inF_inv · ψ μF preIt = pr1 (Pow (S n)) _ z).
{ intro n.
  rewrite e_comm, functor_comp.
  eapply pathscomp0;
   [apply cancel_postcomposition; rewrite <-assoc;  apply maponpaths, H''|].
  rewrite id_right.
  assert (H1 : # L (# F (e n)) · ψ μF preIt = ψ (iter_functor F n 0) (# L (e n) · preIt)).
  { apply pathsinv0, (toforallpaths _ _ _ (nat_trans_ax ψ _ _ (e n))). }
  eapply pathscomp0; [ apply H1|].
  now rewrite H.
}
assert (HH : preIt = # L inF_inv · ψ μF preIt).
{ apply pathsinv0, (colimArrowUnique CC_LchnF); simpl; intro n.
  destruct n.
  - apply (InitialArrowUnique ILD).
  - simpl; eapply pathscomp0; [| apply H'].
    now apply assoc.
}
eapply pathscomp0; [ apply maponpaths, HH|].
now rewrite assoc, H'', id_left.
Qed.

Lemma preIt_ok : # L inF · preIt = ψ μF preIt.
Proof.
now apply SS_imp_S; intro n; apply eqSS.
Qed.

Lemma preIt_uniq (t : ∑ h, # L inF · h = ψ μF h) : t = (preIt,,preIt_ok).
Proof.
apply subtypeEquality; [intros f; apply hsD|]; simpl.
destruct t as [f Hf]; simpl.
apply (colimArrowUnique CC_LchnF); intro n.
now apply S_imp_SS, Hf.
Qed.

Theorem GenMendlerIteration : ∃! (h : L μF --> X), #L inF · h = ψ μF h.
Proof.
use tpair.
- apply (preIt,,preIt_ok).
- exact preIt_uniq.
Defined.

Definition It : L μF --> X := pr1 (pr1 GenMendlerIteration).

Lemma It_is_preIt : It = preIt.
Proof.
apply idpath.
Qed.

End general_case.

(** * Specialized Mendler Iteration *)
Section special_case.

Variables (G : functor D D) (ρ : G X --> X).
Variables (θ : functor_composite F L ⟹ functor_composite L G).

Lemma is_nat_trans_ψ_from_comps :
        is_nat_trans ψ_source ψ_target
          (λ A (f : yoneda_objects_ob D X (L A)), θ A · # G f · ρ).
Proof.
intros A B h; apply funextfun; intro f; cbn.
rewrite functor_comp, !assoc.
assert (θ_nat_trans_ax := nat_trans_ax θ); simpl in θ_nat_trans_ax.
now rewrite <- θ_nat_trans_ax.
Qed.

Definition ψ_from_comps : ψ_source ⟹ ψ_target.
Proof.
use tpair.
- intros A f.
  exact (θ A · #G f · ρ).
- apply is_nat_trans_ψ_from_comps.
Defined.

Definition SpecialGenMendlerIteration :
  ∃! (h : L μF --> X), # L inF · h = θ μF · #G h · ρ
    := GenMendlerIteration ψ_from_comps.

End special_case.
End the_iteration_principle.

(** * Fusion law for Generalized Iteration in Mendler-style *)
Section fusion_law.

Variables (X X' : D).

Let Yon : functor D^op HSET := yoneda_objects D hsD X.
Let Yon' : functor D^op HSET := yoneda_objects D hsD X'.

Variables (L : functor C D) (HL : is_omega_cocont L) (IL : isInitial D (L 0)).
Variables (ψ : ψ_source X L ⟹ ψ_target X L).

Variables (L' : functor C D) (HL' : is_omega_cocont L') (IL' : isInitial D (L' 0)).
Variables (ψ' : ψ_source X' L' ⟹ ψ_target X' L').

Variables (Φ : functor_composite (functor_opp L) Yon ⟹ functor_composite (functor_opp L') Yon').

Variables (H : ψ μF · Φ (F μF) = Φ μF · ψ' μF).

Theorem fusion_law : Φ μF (It X L IL HL ψ) = It X' L' IL' HL' ψ'.
Proof.
apply path_to_ctr.
assert (Φ_is_nat := nat_trans_ax Φ).
assert (Φ_is_nat_inst1 := Φ_is_nat _ _ inF).
assert (Φ_is_nat_inst2 := toforallpaths _ _ _ Φ_is_nat_inst1 (It X L IL HL ψ)).
unfold compose in Φ_is_nat_inst2; simpl in Φ_is_nat_inst2.
simpl.
rewrite <- Φ_is_nat_inst2.
assert (H_inst :=  toforallpaths _ _ _ H (It X L IL HL ψ)).
unfold compose in H_inst; simpl in H_inst.
rewrite <- H_inst.
apply maponpaths.
rewrite It_is_preIt.
apply preIt_ok.
Qed.

End fusion_law.
End GenMenIt.
