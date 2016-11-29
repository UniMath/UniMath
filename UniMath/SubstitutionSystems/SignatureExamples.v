(**

Definitions of various signatures.

Written by: Anders Mörtberg, 2016
Based on a note by Ralph Matthes

*)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.Lam.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.

(** Construct θ in a Signature in the case when the functor is
    precomposition with a functor G by constructing a family of simpler
    distributive laws δ *)
Section θ_from_δ.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable G : functor C C.

(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hsC).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hsC]) .

Definition δ_source_ob (Ze : Ptd) : EndC := G • pr1 Ze.
Definition δ_source_mor {Ze Ze' : Ptd} (α : Ze --> Ze') :
  δ_source_ob Ze --> δ_source_ob Ze' := horcomp (pr1 α) (nat_trans_id G).

Definition δ_source_functor_data : functor_data Ptd EndC.
Proof.
exists δ_source_ob.
exact (@δ_source_mor).
Defined.

Lemma is_functor_δ_source : is_functor δ_source_functor_data.
Proof.
split; simpl.
- intro Ze.
  apply (nat_trans_eq hsC).
  now intro c; simpl; rewrite functor_id, id_right.
- intros [Z e] [Z' e'] [Z'' e''] [α a] [β b].
  apply (nat_trans_eq hsC); intro c; simpl in *.
  now rewrite !id_left, functor_comp.
Qed.

Definition δ_source : functor Ptd EndC := tpair _ _ is_functor_δ_source.

Definition δ_target_ob (Ze : Ptd) : EndC := pr1 Ze • G.
Definition δ_target_mor {Ze Ze' : Ptd} (α : Ze --> Ze') :
  δ_target_ob Ze --> δ_target_ob Ze' := horcomp (nat_trans_id G) (pr1 α).

Definition δ_target_functor_data : functor_data Ptd EndC.
Proof.
exists δ_target_ob.
exact (@δ_target_mor).
Defined.

Lemma is_functor_δ_target : is_functor δ_target_functor_data.
Proof.
split; simpl.
- intro Ze.
  apply (nat_trans_eq hsC).
  now intro c; simpl; rewrite functor_id, id_right.
- intros [Z e] [Z' e'] [Z'' e''] [α a] [β b].
  apply (nat_trans_eq hsC); intro c; simpl in *.
  now rewrite !functor_id, !id_right.
Qed.

Definition δ_target : functor Ptd EndC := tpair _ _ is_functor_δ_target.

Hypothesis δ : δ_source ⟶ δ_target.

Let precompG := (pre_composition_functor _ _ _ hsC hsC G).

Definition θ_from_δ_mor (XZe : [C, C, hsC] XX Ptd) :
  [C, C, hsC] ⟦ θ_source precompG XZe, θ_target precompG XZe ⟧.
Proof.
set (X := pr1 XZe); set (Z := pr1 (pr2 XZe)).
set (F1 := α_functor _ G Z X).
set (F2 := post_whisker (δ (pr2 XZe)) X).
set (F3 := α_functor_inv _ Z G X).
apply (nat_trans_comp F3 (nat_trans_comp F2 F1)).
Defined.

Lemma is_nat_trans_θ_from_δ_mor :
   is_nat_trans (θ_source precompG) (θ_target precompG) θ_from_δ_mor.
Proof.
intros [F1 X1] [F2 X2] [α X]; simpl in *.
apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_right, !id_left.
generalize (nat_trans_eq_pointwise (nat_trans_ax δ X1 X2 X) c); simpl.
rewrite id_left, functor_id, id_right.
intros H.
rewrite <- assoc.
eapply pathscomp0.
  eapply maponpaths, pathsinv0, functor_comp.
eapply pathscomp0.
  eapply maponpaths, maponpaths, H.
rewrite assoc; apply pathsinv0.
eapply pathscomp0.
  eapply cancel_postcomposition, nat_trans_ax.
now rewrite <- assoc, <- functor_comp.
Qed.

Definition θ_from_δ : θ_source precompG ⟶ θ_target precompG :=
  tpair _ _ is_nat_trans_θ_from_δ_mor.

(* Should be ρ_G^-1 ∘ λ_G ? *)
Definition δ_law1 : UU := δ (id_Ptd C hsC) = nat_trans_id G.
Hypothesis (H1 : δ_law1).

Lemma θ_Strength1_int_from_δ : θ_Strength1_int θ_from_δ.
Proof.
intro F.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite id_left, !id_right.
eapply pathscomp0;
  [eapply maponpaths, (nat_trans_eq_pointwise H1 c)|].
apply functor_id.
Qed.

Let D' Ze Ze' :=
  nat_trans_comp (α_functor _ (pr1 Ze) (pr1 Ze') G)
 (nat_trans_comp (pre_whisker (pr1 Ze) (δ Ze'))
 (nat_trans_comp (α_functor_inv _ (pr1 Ze) G (pr1 Ze'))
 (nat_trans_comp (post_whisker (δ Ze) (pr1 Ze'))
                 (α_functor _ G (pr1 Ze) (pr1 Ze'))))).

Definition δ_law2 : UU := Π Ze Ze', δ (Ze p• Ze') = D' Ze Ze'.
Hypothesis H2 : δ_law2.

Lemma θ_Strength2_int_from_δ : θ_Strength2_int θ_from_δ.
Proof.
intros F Ze Ze'; simpl.
set (Z := pr1 Ze); set (Z' := pr1 Ze').
apply (nat_trans_eq hsC); intro c; simpl.
generalize (nat_trans_eq_pointwise (H2 Ze Ze') c); simpl.
rewrite !id_left, !id_right; intro H.
eapply pathscomp0;
  [eapply maponpaths, H|].
apply functor_comp.
Qed.

Definition θ_precompG : Σ θ : θ_source precompG ⟶ θ_target precompG,
                              θ_Strength1_int θ × θ_Strength2_int θ :=
  tpair _ θ_from_δ (θ_Strength1_int_from_δ,,θ_Strength2_int_from_δ).

Definition θ_from_δ_Signature : Signature C hsC :=
  tpair _ precompG θ_precompG.

End θ_from_δ.

(* Composition of δ's *)
Section δ_mul.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable G1 G2 : functor C C.

Variable δ1 : δ_source C hsC G1 ⟶ δ_target C hsC G1.
Variable δ2 : δ_source C hsC G2 ⟶ δ_target C hsC G2.
Hypothesis (δ1_law1 : δ_law1 C hsC G1 δ1) (δ1_law2 : δ_law2 C hsC G1 δ1).
Hypothesis (δ2_law1 : δ_law1 C hsC G2 δ2) (δ2_law2 : δ_law2 C hsC G2 δ2).

Definition δ_comp_mor (Ze : ptd_obj C) :
       functor_composite_data (pr1 Ze) (functor_composite_data G1 G2)
   ⟶ functor_composite_data (functor_composite_data G1 G2) (pr1 Ze).
Proof.
set (Z := pr1 Ze).
set (F1 := α_functor_inv _ Z G1 G2).
set (F2 := post_whisker (δ1 Ze) G2).
set (F3 := α_functor _ G1 Z G2).
set (F4 := pre_whisker G1 (δ2 Ze)).
set (F5 := α_functor_inv _ G1 G2 Z).
exact (nat_trans_comp F1 (nat_trans_comp F2 (nat_trans_comp F3 (nat_trans_comp F4 F5)))).
Defined.

Lemma is_nat_trans_δ_comp_mor : is_nat_trans (δ_source _ _ (G2 • G1 : [C,C,hsC]))
                                             (δ_target _ hsC (G2 • G1 : [C,C,hsC])) δ_comp_mor.
Proof.
intros [Z e] [Z' e'] [α X]; simpl in *.
apply (nat_trans_eq hsC); intro c; simpl; rewrite functor_id, !id_right, !id_left.
eapply pathscomp0.
  rewrite assoc.
  eapply cancel_postcomposition, pathsinv0, functor_comp.
eapply pathscomp0.
  eapply cancel_postcomposition, maponpaths.
  generalize (nat_trans_eq_pointwise (nat_trans_ax δ1 (Z,,e) (Z',, e') (α,,X)) c).
  simpl; rewrite id_left, functor_id, id_right; intro H1.
  apply H1.
rewrite functor_comp, <- assoc.
eapply pathscomp0.
  eapply maponpaths.
  generalize (nat_trans_eq_pointwise (nat_trans_ax δ2 (Z,,e) (Z',, e') (α,,X)) (G1 c)).
  simpl; rewrite id_left, functor_id, id_right; intro H2.
  apply H2.
now rewrite assoc.
Qed.

Definition δ_comp : δ_source C hsC (G2 • G1 : [C,C,hsC]) ⟶ δ_target C hsC (G2 • G1 : [C,C,hsC]) :=
  tpair _ δ_comp_mor is_nat_trans_δ_comp_mor.

Lemma δ_comp_law1 : δ_law1 C hsC (G2 • G1 : [C,C,hsC]) δ_comp.
Proof.
apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_left, id_right.
eapply pathscomp0.
  eapply maponpaths, (nat_trans_eq_pointwise δ2_law1 (G1 c)).
eapply pathscomp0.
  eapply cancel_postcomposition, maponpaths, (nat_trans_eq_pointwise δ1_law1 c).
now rewrite id_right; apply functor_id.
Qed.

Lemma δ_comp_law2 : δ_law2 C hsC (G2 • G1 : [C,C,hsC]) δ_comp.
Proof.
intros Ze Ze'.
apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_left, !id_right.
eapply pathscomp0.
  eapply cancel_postcomposition, maponpaths, (nat_trans_eq_pointwise (δ1_law2 Ze Ze') c).
eapply pathscomp0.
  eapply maponpaths, (nat_trans_eq_pointwise (δ2_law2 Ze Ze') (G1 c)).
simpl; rewrite !id_left, !id_right.
eapply pathscomp0.
  eapply cancel_postcomposition, functor_comp.
rewrite <- !assoc.
apply maponpaths.
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition, (nat_trans_ax (δ2 Ze') _ _ (pr1 (δ1 Ze) c)).
simpl; rewrite <- !assoc.
now apply maponpaths, pathsinv0, functor_comp.
Qed.

End δ_mul.

(* Construct the δ when G = option *)
Section option_sig.

Variables (C : precategory) (hsC : has_homsets C) (TC : Terminal C) (CC : BinCoproducts C).

Local Notation "'Ptd'" := (precategory_Ptd C hsC).

Let opt := option_functor CC TC.

Definition δ_option_mor (Ze : Ptd) (c : C) :  C ⟦ BinCoproductObject C (CC TC (pr1 Ze c)),
                                                  pr1 Ze (BinCoproductObject C (CC TC c)) ⟧.
Proof.
apply (@BinCoproductArrow _ _ _ (CC TC (pr1 Ze c)) (pr1 Ze (BinCoproductObject C (CC TC c)))).
- apply (BinCoproductIn1 _ (CC TC c) ;; pr2 Ze (BinCoproductObject _ (CC TC c))).
- apply (# (pr1 Ze) (BinCoproductIn2 _ (CC TC c))).
Defined.

Lemma is_nat_trans_δ_option_mor (Ze : Ptd) :
  is_nat_trans (δ_source C hsC opt Ze : functor C C) (δ_target C hsC opt Ze : functor C C)
     (δ_option_mor Ze).
Proof.
intros a b f; simpl.
destruct Ze as [Z e].
unfold BinCoproduct_of_functors_mor; simpl.
eapply pathscomp0.
  apply precompWithBinCoproductArrow.
rewrite id_left.
apply pathsinv0, BinCoproductArrowUnique.
- eapply pathscomp0.
    rewrite assoc.
    eapply cancel_postcomposition, BinCoproductIn1Commutes.
  rewrite <- assoc.
  eapply pathscomp0.
    eapply maponpaths, pathsinv0, (nat_trans_ax e).
  simpl; rewrite assoc.
  apply cancel_postcomposition.
  eapply pathscomp0.
    apply BinCoproductOfArrowsIn1.
  now rewrite id_left.
- rewrite assoc.
  eapply pathscomp0.
    eapply cancel_postcomposition, BinCoproductIn2Commutes.
  rewrite <- !functor_comp.
  now apply maponpaths, BinCoproductOfArrowsIn2.
Qed.

Lemma is_nat_trans_δ_option_mor_nat_trans : is_nat_trans (δ_source_functor_data C hsC opt)
     (δ_target_functor_data C hsC opt)
     (λ Ze : Ptd, δ_option_mor Ze,, is_nat_trans_δ_option_mor Ze).
Proof.
intros [Z e] [Z' e'] [α X]; simpl in *.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite id_left, functor_id, id_right.
unfold BinCoproduct_of_functors_mor, BinCoproduct_of_functors_ob, δ_option_mor; simpl.
rewrite precompWithBinCoproductArrow.
apply pathsinv0, BinCoproductArrowUnique.
- rewrite id_left, assoc.
  eapply pathscomp0.
    eapply cancel_postcomposition, BinCoproductIn1Commutes.
  rewrite <- assoc.
  now apply maponpaths, X.
- rewrite assoc.
  eapply pathscomp0.
    eapply cancel_postcomposition, BinCoproductIn2Commutes.
  now apply nat_trans_ax.
Qed.

Definition δ_option : δ_source C hsC opt ⟶ δ_target C hsC opt.
Proof.
mkpair.
- intro Ze.
  apply (tpair _ (δ_option_mor Ze) (is_nat_trans_δ_option_mor Ze)).
- apply is_nat_trans_δ_option_mor_nat_trans.
Defined.

Lemma δ_law1_option : δ_law1 C hsC opt δ_option.
Proof.
apply (nat_trans_eq hsC); intro c; simpl.
unfold δ_option_mor, BinCoproduct_of_functors_ob; simpl.
rewrite id_right.
apply pathsinv0, BinCoproduct_endo_is_identity.
- apply BinCoproductIn1Commutes.
- apply BinCoproductIn2Commutes.
Qed.

Lemma δ_law2_option : δ_law2 C hsC opt δ_option.
Proof.
intros [Z e] [Z' e'].
apply (nat_trans_eq hsC); intro c; simpl.
unfold δ_option_mor, BinCoproduct_of_functors_ob; simpl.
rewrite !id_left, id_right.
apply pathsinv0, BinCoproductArrowUnique.
- rewrite assoc.
  eapply pathscomp0.
    eapply cancel_postcomposition, BinCoproductIn1Commutes.
  rewrite <- assoc.
  eapply pathscomp0.
    eapply maponpaths, pathsinv0, (nat_trans_ax e').
  simpl; rewrite assoc.
  eapply pathscomp0.
    eapply cancel_postcomposition, BinCoproductIn1Commutes.
  rewrite <- !assoc.
  now apply maponpaths, (nat_trans_ax e').
- rewrite assoc.
  eapply pathscomp0.
    eapply cancel_postcomposition, BinCoproductIn2Commutes.
  eapply pathscomp0.
    eapply pathsinv0, functor_comp.
  now apply maponpaths, BinCoproductIn2Commutes.
Qed.

Definition precomp_option_Signature : Signature C hsC :=
  θ_from_δ_Signature _ hsC opt δ_option δ_law1_option δ_law2_option.

End option_sig.

(** Define δ for G = F^n *)
Section iter1_sig.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable F : functor C C.

Variable δ : δ_source C hsC F ⟶ δ_target C hsC F.
Hypothesis (H1 : δ_law1 C hsC F δ) (H2 : δ_law2 C hsC F δ).

Local Notation "'Ptd'" := (precategory_Ptd C hsC).

(* G^n+1 *)
Fixpoint iter_functor1 (n : nat) : functor C C := match n with
  | O => F
  | S n' => functor_composite (iter_functor1 n') F
  end.

Definition δ_iter_functor1 n : δ_source C hsC (iter_functor1 n) ⟶ δ_target C hsC (iter_functor1 n).
Proof.
induction n as [|n IHn].
- apply δ.
- apply δ_comp.
  + apply IHn.
  + apply δ.
Defined.

Lemma δ_law1_iter_functor1 n : δ_law1 C hsC (iter_functor1 n) (δ_iter_functor1 n).
Proof.
induction n; [|apply δ_comp_law1]; assumption.
Qed.

Lemma δ_law2_iter_functor1 n : δ_law2 C hsC (iter_functor1 n) (δ_iter_functor1 n).
Proof.
induction n; [|apply δ_comp_law2]; assumption.
Qed.

End iter1_sig.

Section id_signature.

Variable (C : precategory) (hsC : has_homsets C).

Definition θ_functor_identity : Σ
  θ : θ_source (functor_identity [C,C,hsC]) ⟶ θ_target (functor_identity [C,C,hsC]),
  θ_Strength1_int θ × θ_Strength2_int θ.
Proof.
mkpair; simpl.
+ mkpair; simpl.
  * intro x.
    { mkpair.
      - intro y; simpl; apply identity.
      - abstract (now intros y y' f; rewrite id_left, id_right).
    }
  * abstract (now intros y y' f; apply (nat_trans_eq hsC); intro z;
                  simpl; rewrite id_left, id_right).
(* If this part is abstract the eval cbn for the LC doesn't reduce properly *)
+ now split; intros x; intros; apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_left.
Defined.

(** Signature for the Id functor *)
Definition IdSignature : Signature C hsC :=
  tpair _ (functor_identity _) θ_functor_identity.

End id_signature.
