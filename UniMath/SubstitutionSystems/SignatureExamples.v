(**

Definitions of various signatures.

Written by: Anders Mörtberg, 2016
Based on a note by Ralph Matthes

Revised and extended by Ralph Matthes, 2017

*)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.

Local Open Scope cat.

Section around_δ.

Variable C : precategory.
Variable hsC : has_homsets C.


(* G^n+1 *)
Fixpoint iter_functor1 (G: functor C C) (n : nat) : functor C C := match n with
  | O => G
  | S n' => functor_composite (iter_functor1 G n') G
  end.

(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hsC).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hsC]) .

(** distributivity with laws as a simple form the strength with laws,
    for endofunctors on the base category *)
Section def_of_δ.

Variable G : functor C C.

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
- intros H1 H2 H3 H4 H5; induction H1 as [Z e]; induction H2 as [Z' e']; induction H3 as [Z'' e'']; induction H4 as [α a]; induction H5 as [β b].
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
- intros H1 H2 H3 H4 H5; induction H1 as [Z e]; induction H2 as [Z' e']; induction H3 as [Z'' e'']; induction H4 as [α a]; induction H5 as [β b].
  apply (nat_trans_eq hsC); intro c; simpl in *.
  now rewrite !functor_id, !id_right.
Qed.

Definition δ_target : functor Ptd EndC := tpair _ _ is_functor_δ_target.

Section δ_laws.

Variable δ : δ_source ⟹ δ_target.

(* Should be ρ_G^-1 ∘ λ_G ? *)
Definition δ_law1 : UU := δ (id_Ptd C hsC) = nat_trans_id G.
Let D' Ze Ze' :=
  nat_trans_comp (α_functor (pr1 Ze) (pr1 Ze') G)
 (nat_trans_comp (pre_whisker (pr1 Ze) (δ Ze'))
 (nat_trans_comp (α_functor_inv (pr1 Ze) G (pr1 Ze'))
 (nat_trans_comp (post_whisker (δ Ze) (pr1 Ze'))
                 (α_functor G (pr1 Ze) (pr1 Ze'))))).
Definition δ_law2 : UU := ∏ Ze Ze', δ (Ze p• Ze') = D' Ze Ze'.

End δ_laws.

Definition DistributiveLaw : UU :=
        ∑ δ : nat_trans δ_source δ_target , δ_law1 δ × δ_law2 δ.

Definition δ (DL : DistributiveLaw) : nat_trans δ_source δ_target := pr1 DL.

Definition distributive_law1 (DL : DistributiveLaw) : δ_law1 _ := pr1 (pr2 DL).

Definition distributive_law2 (DL : DistributiveLaw) : δ_law2 _ := pr2 (pr2 DL).

End def_of_δ.

Section δ_for_id.

Definition DL_id : DistributiveLaw (functor_identity C).
Proof.
use tpair; simpl.
+ use tpair; simpl.
  * intro x.
    { use tpair.
      - intro y; simpl; apply identity.
      - abstract (now intros y y' f; rewrite id_left, id_right).
    }
  * abstract (now intros y y' f; apply (nat_trans_eq hsC); intro z;
                  simpl; rewrite id_left, id_right, id_left, functor_id, id_right; apply idpath).
+ split.
  * apply (nat_trans_eq hsC); intro c; simpl; apply idpath.
  * intros Ze Ze'; apply (nat_trans_eq hsC); intro c; simpl. do 3 rewrite id_left. rewrite id_right. apply pathsinv0. apply functor_id.
Defined.

End δ_for_id.

(** Construct θ in a Signature in the case when the functor is
    precomposition with a functor G from a family of simpler
    distributive laws δ *)
Section θ_from_δ.

Variable G : functor C C.
Variable DL : DistributiveLaw G.

Let precompG := (pre_composition_functor _ _ _ hsC hsC G).

Definition θ_from_δ_mor (XZe : [C, C, hsC] XX Ptd) :
  [C, C, hsC] ⟦ θ_source precompG XZe, θ_target precompG XZe ⟧.
Proof.
set (X := pr1 XZe); set (Z := pr1 (pr2 XZe)).
set (F1 := α_functor G Z X).
set (F2 := post_whisker (δ G DL (pr2 XZe)) X).
set (F3 := α_functor_inv Z G X).
apply (nat_trans_comp F3 (nat_trans_comp F2 F1)).
Defined.

Lemma is_nat_trans_θ_from_δ_mor :
   is_nat_trans (θ_source precompG) (θ_target precompG) θ_from_δ_mor.
Proof.
intros H1 H2 H3; induction H1 as [F1 X1]; induction H2 as [F2 X2];induction H3 as [α X]; simpl in *.
apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_right, !id_left.
generalize (nat_trans_eq_pointwise (nat_trans_ax (δ G DL) X1 X2 X) c); simpl.
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

Definition θ_from_δ : θ_source precompG ⟹ θ_target precompG :=
  tpair _ _ is_nat_trans_θ_from_δ_mor.

Lemma θ_Strength1_int_from_δ : θ_Strength1_int θ_from_δ.
Proof.
intro F.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite id_left, !id_right.
eapply pathscomp0;
  [eapply maponpaths, (nat_trans_eq_pointwise (distributive_law1 G DL) c)|].
apply functor_id.
Qed.


Lemma θ_Strength2_int_from_δ : θ_Strength2_int θ_from_δ.
Proof.
intros F Ze Ze'; simpl.
set (Z := pr1 Ze); set (Z' := pr1 Ze').
apply (nat_trans_eq hsC); intro c; simpl.
generalize (nat_trans_eq_pointwise (distributive_law2 G DL Ze Ze') c); simpl.
rewrite !id_left, !id_right; intro H.
eapply pathscomp0;
  [eapply maponpaths, H|].
apply functor_comp.
Qed.

Definition θ_precompG : ∑ θ : θ_source precompG ⟹ θ_target precompG,
                              θ_Strength1_int θ × θ_Strength2_int θ :=
  tpair _ θ_from_δ (θ_Strength1_int_from_δ,,θ_Strength2_int_from_δ).

Definition θ_from_δ_Signature : Signature C hsC C hsC :=
  tpair _ precompG θ_precompG.

End θ_from_δ.

(* Composition of δ's *)
Section δ_mul.

  Variable G1 : functor C C.
  Variable DL1 : DistributiveLaw G1.
  Variable G2 : functor C C.
  Variable DL2 : DistributiveLaw G2.

Definition δ_comp_mor (Ze : ptd_obj C) :
       functor_composite_data (pr1 Ze) (functor_composite_data G1 G2)
   ⟹ functor_composite_data (functor_composite_data G1 G2) (pr1 Ze).
Proof.
set (Z := pr1 Ze).
set (F1 := α_functor_inv Z G1 G2).
set (F2 := post_whisker (δ G1 DL1 Ze) G2).
set (F3 := α_functor G1 Z G2).
set (F4 := pre_whisker G1 (δ G2 DL2 Ze)).
set (F5 := α_functor_inv G1 G2 Z).
exact (nat_trans_comp F1 (nat_trans_comp F2 (nat_trans_comp F3 (nat_trans_comp F4 F5)))).
Defined.

Lemma is_nat_trans_δ_comp_mor : is_nat_trans (δ_source (G2 • G1 : [C,C,hsC]))
                                             (δ_target (G2 • G1 : [C,C,hsC])) δ_comp_mor.
Proof.
intros Ze Z'e' αX; induction Ze as [Z e]; induction Z'e' as [Z' e']; induction αX as [α X]; simpl in *.
apply (nat_trans_eq hsC); intro c; simpl; rewrite functor_id, !id_right, !id_left.
eapply pathscomp0.
  rewrite assoc.
  eapply cancel_postcomposition, pathsinv0, functor_comp.
eapply pathscomp0.
  eapply cancel_postcomposition, maponpaths.
  generalize (nat_trans_eq_pointwise (nat_trans_ax (δ G1 DL1) (Z,,e) (Z',, e') (α,,X)) c).
  simpl; rewrite id_left, functor_id, id_right; intro H1.
  apply H1.
rewrite functor_comp, <- assoc.
eapply pathscomp0.
  eapply maponpaths.
  generalize (nat_trans_eq_pointwise (nat_trans_ax (δ G2 DL2) (Z,,e) (Z',, e') (α,,X)) (G1 c)).
  simpl; rewrite id_left, functor_id, id_right; intro H2.
  apply H2.
now rewrite assoc.
Qed.

Definition δ_comp : δ_source (G2 • G1 : [C,C,hsC]) ⟹ δ_target (G2 • G1 : [C,C,hsC]) :=
  tpair _ δ_comp_mor is_nat_trans_δ_comp_mor.

Lemma δ_comp_law1 : δ_law1 (G2 • G1 : [C,C,hsC]) δ_comp.
Proof.
apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_left, id_right.
eapply pathscomp0.
  eapply maponpaths, (nat_trans_eq_pointwise (distributive_law1 G2 DL2) (G1 c)).
eapply pathscomp0.
  eapply cancel_postcomposition, maponpaths, (nat_trans_eq_pointwise (distributive_law1  G1 DL1) c).
now rewrite id_right; apply functor_id.
Qed.

Lemma δ_comp_law2 : δ_law2 (G2 • G1 : [C,C,hsC]) δ_comp.
Proof.
intros Ze Ze'.
apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_left, !id_right.
eapply pathscomp0.
  eapply cancel_postcomposition, maponpaths, (nat_trans_eq_pointwise (distributive_law2 G1 DL1 Ze Ze') c).
eapply pathscomp0.
  eapply maponpaths, (nat_trans_eq_pointwise (distributive_law2 G2 DL2 Ze Ze') (G1 c)).
simpl; rewrite !id_left, !id_right.
eapply pathscomp0.
  eapply cancel_postcomposition, functor_comp.
rewrite <- !assoc.
apply maponpaths.
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition, (nat_trans_ax (δ G2 DL2 Ze') _ _ (pr1 (δ G1 DL1 Ze) c)).
simpl; rewrite <- !assoc.
now apply maponpaths, pathsinv0, functor_comp.
Qed.

Definition DL_comp : DistributiveLaw (G2 • G1 : [C,C,hsC]).
Proof.
use tpair.
  * exact δ_comp.
  * split.
    - exact δ_comp_law1.
    - exact δ_comp_law2.
Defined.

End δ_mul.

(** Construct the δ when G is generalized option *)
Section genoption_sig.

Variables (A : C) (CC : BinCoproducts C).

Let genopt := constcoprod_functor1 CC A.

Definition δ_genoption_mor (Ze : Ptd) (c : C) :  C ⟦ BinCoproductObject C (CC A (pr1 Ze c)),
                                                  pr1 Ze (BinCoproductObject C (CC A c)) ⟧.
Proof.
apply (@BinCoproductArrow _ _ _ (CC A (pr1 Ze c)) (pr1 Ze (BinCoproductObject C (CC A c)))).
- apply (BinCoproductIn1 _ (CC A c) · pr2 Ze (BinCoproductObject _ (CC A c))).
- apply (# (pr1 Ze) (BinCoproductIn2 _ (CC A c))).
Defined.

Lemma is_nat_trans_δ_genoption_mor (Ze : Ptd) :
  is_nat_trans (δ_source genopt Ze : functor C C) (δ_target genopt Ze : functor C C)
     (δ_genoption_mor Ze).
Proof.
intros a b f; simpl.
induction Ze as [Z e].
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

Lemma is_nat_trans_δ_genoption_mor_nat_trans : is_nat_trans (δ_source_functor_data genopt)
     (δ_target_functor_data genopt)
     (λ Ze : Ptd, δ_genoption_mor Ze,, is_nat_trans_δ_genoption_mor Ze).
Proof.
intro Ze; induction Ze as [Z e]; intro Z'e'; induction Z'e' as [Z' e']; intro αX; induction αX as [α X]; simpl in *.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite id_left, functor_id, id_right.
unfold BinCoproduct_of_functors_mor, BinCoproduct_of_functors_ob, δ_genoption_mor; simpl.
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

Definition δ_genoption : δ_source genopt ⟹ δ_target genopt.
Proof.
use tpair.
- intro Ze.
  apply (tpair _ (δ_genoption_mor Ze) (is_nat_trans_δ_genoption_mor Ze)).
- apply is_nat_trans_δ_genoption_mor_nat_trans.
Defined.

Lemma δ_law1_genoption : δ_law1 genopt δ_genoption.
Proof.
apply (nat_trans_eq hsC); intro c; simpl.
unfold δ_genoption_mor, BinCoproduct_of_functors_ob; simpl.
rewrite id_right.
apply pathsinv0, BinCoproduct_endo_is_identity.
- apply BinCoproductIn1Commutes.
- apply BinCoproductIn2Commutes.
Qed.

Lemma δ_law2_genoption : δ_law2 genopt δ_genoption.
Proof.
intros Ze Z'e'; induction Ze as [Z e]; induction Z'e' as [Z' e'].
apply (nat_trans_eq hsC); intro c; simpl.
unfold δ_genoption_mor, BinCoproduct_of_functors_ob; simpl.
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

Definition genoption_DistributiveLaw : DistributiveLaw genopt.
Proof.
exists δ_genoption.
    split.
    * exact δ_law1_genoption.
    * exact δ_law2_genoption.
Defined.

Definition precomp_genoption_Signature : Signature C hsC C hsC :=
  θ_from_δ_Signature genopt genoption_DistributiveLaw.


End genoption_sig.


(** trivially instantiate previous section to option functor *)
Section option_sig.

  Variables (TC : Terminal C) (CC : BinCoproducts C).
  Let opt := option_functor CC TC.
  Definition δ_option: δ_source opt ⟹ δ_target opt :=
    δ_genoption TC CC.

  Definition δ_law1_option :=  δ_law1_genoption TC CC.
  Definition δ_law2_option :=  δ_law2_genoption TC CC.


  Definition option_DistributiveLaw : DistributiveLaw opt :=
    genoption_DistributiveLaw TC CC.
  Definition precomp_option_Signature : Signature C hsC C hsC :=
    precomp_genoption_Signature TC CC.

End option_sig.

(** Define δ for G = F^n *)
Section iter1_dl.

Variable G : functor C C.
Variable DL : DistributiveLaw G.

Definition DL_iter_functor1 (n: nat) : DistributiveLaw (iter_functor1 G n).
Proof.
induction n as [|n IHn].
- exact DL.
- apply DL_comp.
  + apply IHn.
  + exact DL.
Defined.

End iter1_dl.

End around_δ.

Section id_signature.

Variable (C : precategory) (hsC : has_homsets C).

Definition θ_functor_identity : ∑
  θ : θ_source (functor_identity [C,C,hsC]) ⟹ θ_target (functor_identity [C,C,hsC]),
  θ_Strength1_int θ × θ_Strength2_int θ.
Proof.
use tpair; simpl.
+ use tpair; simpl.
  * intro x.
    { use tpair.
      - intro y; simpl; apply identity.
      - abstract (now intros y y' f; rewrite id_left, id_right).
    }
  * abstract (now intros y y' f; apply (nat_trans_eq hsC); intro z;
                  simpl; rewrite id_left, id_right).
(* If this part is abstract the eval cbn for the LC doesn't reduce properly *)
+ now split; intros x; intros; apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_left.
Defined.

(** Signature for the Id functor *)
Definition IdSignature : Signature C hsC C hsC :=
  tpair _ (functor_identity _) θ_functor_identity.


(** an alternative approach would be to go through θ_from_δ_Signature, based on the
observation that functor_identity [C,C,hsC] and
pre_composition_functor _ _ _ hsC hsC (functor_identity C) are isomorphic;
however, they are probably not propositionally equal, and so the benefit is marginal *)

End id_signature.

Section constantly_constant_signature.

  Variable (C D : category).
  Variable (d : D).

  Let H := constant_functor (functor_category C C) (functor_category C D) (constant_functor C D d).

  Definition θ_const_const : ∑
  θ : θ_source H  ⟹ θ_target H, θ_Strength1_int θ × θ_Strength2_int θ.
Proof.
use tpair; simpl.
+ use tpair; simpl.
  * intro x.
    { use tpair.
      - intro y; simpl; apply identity.
      - abstract (now intros y y' f; rewrite id_left, id_right).
    }
  * abstract (now intros y y' f; apply (nat_trans_eq (homset_property D)); intro z;
                  simpl; rewrite id_left, id_right).
+ now split; intros x; intros; apply (nat_trans_eq (homset_property D)); intro c; simpl; rewrite !id_left.
Defined.

Definition ConstConstSignature : Signature _ (homset_property C) _ (homset_property D) :=
  tpair _ H θ_const_const.

  End constantly_constant_signature.

(** Transform a signature with strength θ with underlying functor H into
    a signature with strength Gθ for the functor that comes from
    post-composition of all HX with a functor G

    G need not be an endofunctor, which is why the strength concept had
    to be given more heterogeneously than only on endofunctors on
    endofunctor categories
 *)
Section θ_for_postcomposition.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable D : precategory.
Variable hsD : has_homsets D.
Variable E : precategory.
Variable hsE : has_homsets E.

(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hsC).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hsC]) .

Variable S: Signature C hsC D hsD.
Let H : functor [C, C, hsC] [C, D, hsD] := Signature_Functor _ _ _ _ S.
Let θ : nat_trans (θ_source H) (θ_target H) := theta S.
Let θ_strength1 := Sig_strength_law1 _ _ _ _ S.
Let θ_strength2 := Sig_strength_law2 _ _ _ _ S.
Variable G : functor D E.

Let GH : functor [C, C, hsC] [C, E, hsE] := functor_composite H (post_composition_functor _ _ _ _ _ G).

Definition Gθ_mor (XZe : [C, C, hsC] XX Ptd) :
  [C, E, hsE] ⟦ θ_source GH XZe, θ_target GH XZe ⟧.
Proof.
set (X := pr1 XZe); set (Z := pr1 (pr2 XZe)).
set (F1 := α_functor_inv Z (H X) G).
set (F2 := post_whisker (θ XZe) G).
apply (nat_trans_comp F1 F2).
Defined.

Lemma is_nat_trans_Gθ_mor :
   is_nat_trans (θ_source GH) (θ_target GH) Gθ_mor.
Proof.
intros H1 H2 H3; induction H1 as [F1 X1]; induction H2 as [F2 X2]; induction H3 as [α X]; simpl in *.
apply (nat_trans_eq hsE); intro c; simpl.
do 2 rewrite <- assoc.
do 2 rewrite id_left.
eapply pathscomp0.
  + eapply maponpaths, pathsinv0, functor_comp.
  + eapply pathscomp0.
    - eapply pathsinv0, functor_comp.
    - apply pathsinv0. eapply pathscomp0.
      * eapply pathsinv0, functor_comp.
      * eapply maponpaths.
        apply pathsinv0.
        rewrite assoc.
        generalize (nat_trans_eq_pointwise (nat_trans_ax θ (F1,,X1)(F2,,X2)(α,,X)) c); simpl.
        intro Hyp.
        apply Hyp.
Qed.

Definition Gθ : θ_source GH ⟹ θ_target GH :=
  tpair _ _ is_nat_trans_Gθ_mor.


Lemma Gθ_Strength1_int : θ_Strength1_int Gθ.
Proof.
intro F.
apply (nat_trans_eq hsE); intro c; simpl.
rewrite <- assoc.
rewrite id_left.
eapply pathscomp0.
  + eapply pathsinv0, functor_comp.
  + apply pathsinv0. eapply pathscomp0.
    * eapply pathsinv0, functor_id.
    * eapply maponpaths.
      generalize (nat_trans_eq_pointwise (θ_strength1 F) c); simpl.
      intro Hyp.
      apply pathsinv0, Hyp.
Qed.

Lemma Gθ_Strength2_int : θ_Strength2_int Gθ.
Proof.
intros F Ze Ze'; simpl.
set (Z := pr1 Ze); set (Z' := pr1 Ze').
apply (nat_trans_eq hsE); intro c; simpl.
do 4 rewrite id_left.
eapply pathscomp0.
  + eapply pathsinv0, functor_comp.
  + apply pathsinv0. eapply pathscomp0.
    * eapply pathsinv0, functor_comp.
    * eapply maponpaths.
      generalize (nat_trans_eq_pointwise (θ_strength2 F Ze Ze') c); simpl.
      rewrite id_left.
      intro Hyp.
      apply pathsinv0, Hyp.
Qed.


Definition Gθ_with_laws : ∑ θ : θ_source GH ⟹ θ_target GH,
                              θ_Strength1_int θ × θ_Strength2_int θ :=
  tpair _ Gθ (Gθ_Strength1_int,,Gθ_Strength2_int).

Definition Gθ_Signature : Signature C hsC E hsE :=
  tpair _ GH Gθ_with_laws.


End θ_for_postcomposition.
