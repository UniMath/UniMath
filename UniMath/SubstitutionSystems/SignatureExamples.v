(**

Definitions of various signatures.

Written by: Anders Mörtberg, 2016
Based on a note by Ralph Matthes

Revised and extended by Ralph Matthes, 2017

*)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.SubstitutionSystems.Notation.

Local Open Scope subsys.

Require Import UniMath.CategoryTheory.PointedFunctorsComposition.

Local Open Scope cat.

Section around_δ.

Context (C : category).

(* G^n+1 *)
Fixpoint iter_functor1 (G: functor C C) (n : nat) : functor C C := match n with
  | O => G
  | S n' => functor_composite (iter_functor1 G n') G
  end.

(** The category of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (category_Ptd C).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C]) .

(** distributivity with laws as a simple form the strength with laws,
    for endofunctors on the base category

    in July 2023, it became clear that this should rather have been
    called a pointed lax commutator; since a paper is based on this
    notion, we keep the name
*)
Section def_of_δ.

Context (G : EndC).

Definition δ_source : functor Ptd EndC :=
  functor_compose (functor_ptd_forget C) (post_comp_functor G).

Definition δ_target : functor Ptd EndC :=
  functor_compose (functor_ptd_forget C) (pre_comp_functor G).

Section δ_laws.

Context (δ : δ_source ⟹ δ_target).

(* Should be ρ_G^-1 ∘ λ_G ? *)
Definition δ_law1 : UU := δ (id_Ptd C) = identity G.
Let D' Ze Ze' :=
  nat_trans_comp (rassociator_CAT (pr1 Ze) (pr1 Ze') G)
 (nat_trans_comp (lwhisker_CAT (pr1 Ze) (δ Ze'))
 (nat_trans_comp (lassociator_CAT (pr1 Ze) G (pr1 Ze'))
 (nat_trans_comp (rwhisker_CAT (pr1 Ze') (δ Ze))
                 (rassociator_CAT G (pr1 Ze) (pr1 Ze'))))).
Definition δ_law2 : UU := ∏ Ze Ze', δ (Ze p• Ze') = D' Ze Ze'.

(** the following variant is more suitable for communication about the results *)
Definition δ_law2_nicer : UU := ∏ Ze Ze',
    δ (Ze p• Ze') =
      # (pre_comp_functor (pr1 Ze)) (δ Ze') · # (post_comp_functor (pr1 Ze')) (δ Ze).

Lemma δ_law2_implies_δ_law2_nicer: δ_law2 -> δ_law2_nicer.
Proof.
  intros Hyp Ze Ze'.
  assert (Hypinst := Hyp Ze Ze').
  etrans. { exact Hypinst. }
  unfold D'.
  apply nat_trans_eq_alt.
  intro c.
  cbn.
  do 2 rewrite id_left.
  rewrite id_right.
  apply idpath.
Qed.

Lemma δ_law2_nicer_implies_δ_law2: δ_law2_nicer -> δ_law2.
Proof.
  intros Hyp Ze Ze'.
  assert (Hypinst := Hyp Ze Ze').
  etrans. { exact Hypinst. }
  unfold D'.
  apply nat_trans_eq_alt.
  intro c.
  cbn.
  do 2 rewrite id_left.
  rewrite id_right.
  apply idpath.
Qed.

End δ_laws.

Definition DistributiveLaw : UU := ∑ δ : δ_source ⟹ δ_target, δ_law1 δ × δ_law2 δ.

Definition δ (DL : DistributiveLaw) : δ_source ⟹ δ_target := pr1 DL.

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
  * abstract ( intros y y' f; apply nat_trans_eq_alt; intro z; simpl; rewrite id_left; apply id_right ).
+ split.
  * apply nat_trans_eq_alt; intro c; simpl; apply idpath.
  * intros Ze Ze'; apply nat_trans_eq_alt; intro c; simpl. do 3 rewrite id_left.
    rewrite id_right. apply pathsinv0. apply functor_id.
Defined.

End δ_for_id.

(** Construct θ in a Signature in the case when the functor is
    precomposition with a functor G from a family of simpler
    distributive laws δ *)
Section θ_from_δ.

Context (G : functor C C) (DL : DistributiveLaw G).

Let precompG := (pre_composition_functor _ C C G).

(** See Lemma 11 of "From Signatures to Monads in UniMath" in Ahrens, Matthes and Mörtberg *)
Definition θ_from_δ_mor (XZe : [C, C] ⊠ Ptd) :
  [C, C] ⟦ θ_source precompG XZe, θ_target precompG XZe ⟧.
Proof.
  set (X := pr1 XZe); set (Z := pr1 (pr2 XZe)).
  set (F1 := rassociator_CAT G Z X).
  set (F2 := rwhisker_CAT X (δ G DL (pr2 XZe))).
  set (F3 := lassociator_CAT Z G X).
  exact (F3 · (F2 · F1)).
Defined.

Lemma is_nat_trans_θ_from_δ_mor :
   is_nat_trans (θ_source precompG) (θ_target precompG) θ_from_δ_mor.
Proof.
  intros H1 H2 αη; induction H1 as [F1 Ze1]; induction H2 as [F2 Ze2]; induction αη as [α η].
  apply nat_trans_eq_alt; intro c.
  simpl; rewrite !id_right, !id_left.
  generalize (nat_trans_eq_pointwise (nat_trans_ax (δ G DL) Ze1 Ze2 η) c); simpl.
  intro H.
  rewrite assoc.
  etrans.
  2: { apply cancel_postcomposition.
       apply functor_comp. }
  etrans.
  2: { apply cancel_postcomposition. apply maponpaths. exact H. }
  clear H.
  rewrite functor_comp.
  do 2 rewrite <- assoc.
  apply maponpaths.
  apply pathsinv0, nat_trans_ax.
Qed.

Definition θ_from_δ : PrestrengthForSignature precompG := tpair _ _ is_nat_trans_θ_from_δ_mor.

Lemma θ_Strength1_int_from_δ : θ_Strength1_int θ_from_δ.
Proof.
  intro F.
  apply nat_trans_eq_alt; intro c; simpl.
  rewrite id_left, !id_right.
  etrans; [apply maponpaths, (nat_trans_eq_pointwise (distributive_law1 G DL) c)|].
  apply functor_id.
Qed.

Lemma θ_Strength2_int_from_δ : θ_Strength2_int θ_from_δ.
Proof.
  intros F Ze Ze'; simpl.
  set (Z := pr1 Ze); set (Z' := pr1 Ze').
  apply nat_trans_eq; [apply homset_property |] ; intro c; simpl.
  generalize (nat_trans_eq_pointwise (distributive_law2 G DL Ze Ze') c); simpl.
  rewrite !id_left, !id_right; intro H.
  etrans; [apply maponpaths, H|].
  apply functor_comp.
Qed.

Definition θ_precompG : StrengthForSignature precompG :=
  tpair _ θ_from_δ (θ_Strength1_int_from_δ ,, θ_Strength2_int_from_δ).

Definition θ_from_δ_Signature : Signature C C C := tpair _ precompG θ_precompG.

End θ_from_δ.

(* Composition of δ's *)
Section δ_mul.

  Context (G1 : [C, C]) (DL1 : DistributiveLaw G1)
          (G2 : [C, C]) (DL2 : DistributiveLaw G2).

  Definition δ_comp_mor (Ze : ptd_obj C) : [C, C] ⟦pr1 (δ_source (functor_compose G1 G2)) Ze,
                                                        pr1 (δ_target (functor_compose G1 G2)) Ze⟧.
Proof.
  set (Z := pr1 Ze).
  set (F1 := lassociator_CAT Z G1 G2).
  set (F2 := rwhisker_CAT G2 (δ G1 DL1 Ze)).
  set (F3 := rassociator_CAT G1 Z G2).
  set (F4 := lwhisker_CAT G1 (δ G2 DL2 Ze)).
  set (F5 := lassociator_CAT G1 G2 Z).
  exact (F1 · (F2 · (F3 · (F4 · F5)))).
Defined.

Lemma is_nat_trans_δ_comp_mor : is_nat_trans (δ_source (functor_compose G1 G2))
                                             (δ_target (functor_compose G1 G2)) δ_comp_mor.
Proof.
  intros Ze Z'e' αX; induction Ze as [Z e]; induction Z'e' as [Z' e']; induction αX as [α X]; simpl in *.
  apply nat_trans_eq; [apply homset_property |]; intro c; simpl.
  rewrite !id_right, !id_left.
  generalize (nat_trans_eq_pointwise (nat_trans_ax (δ G1 DL1) (Z,,e) (Z',, e') (α,,X)) c).
  generalize (nat_trans_eq_pointwise (nat_trans_ax (δ G2 DL2) (Z,,e) (Z',, e') (α,,X)) (G1 c)).
  intros Hyp1 Hyp2.
  cbn in Hyp1, Hyp2.
  etrans.
  2: { rewrite <- assoc. apply maponpaths. exact Hyp1. }
  clear Hyp1.
  etrans.
  { rewrite assoc. apply cancel_postcomposition.
    apply pathsinv0, functor_comp. }
  etrans.
  { apply cancel_postcomposition. apply maponpaths. exact Hyp2. }
  rewrite (functor_comp G2).
  apply assoc'.
Qed.

Definition δ_comp : δ_source (functor_compose G1 G2) ⟹ δ_target (functor_compose G1 G2) :=
  tpair _ δ_comp_mor is_nat_trans_δ_comp_mor.

Lemma δ_comp_law1 : δ_law1 (functor_compose G1 G2) δ_comp.
Proof.
  apply nat_trans_eq_alt; intro c; simpl; rewrite !id_left, id_right.
  etrans.
  { apply maponpaths, (nat_trans_eq_pointwise (distributive_law1 G2 DL2) (pr1 G1 c)). }
  etrans.
  { apply cancel_postcomposition, maponpaths, (nat_trans_eq_pointwise (distributive_law1  G1 DL1) c). }
  now rewrite id_right; apply functor_id.
Qed.

Lemma δ_comp_law2 : δ_law2 (functor_compose G1 G2) δ_comp.
Proof.
  intros Ze Ze'.
  apply nat_trans_eq_alt; intro c; simpl; rewrite !id_left, !id_right.
  etrans.
  { apply cancel_postcomposition, maponpaths, (nat_trans_eq_pointwise (distributive_law2 G1 DL1 Ze Ze') c). }
  etrans.
  { apply maponpaths, (nat_trans_eq_pointwise (distributive_law2 G2 DL2 Ze Ze') (pr1 G1 c)). }
  simpl; rewrite !id_left, !id_right.
  etrans.
  { apply cancel_postcomposition, functor_comp. }
  rewrite <- !assoc.
  apply maponpaths.
  rewrite assoc.
  etrans.
  { apply cancel_postcomposition, (nat_trans_ax (δ G2 DL2 Ze') _ _ (pr1 (δ G1 DL1 Ze) c)). }
  simpl; rewrite <- !assoc.
  now apply maponpaths, pathsinv0, functor_comp.
Qed.

Definition DL_comp : DistributiveLaw (functor_compose G1 G2).
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

Context (A : C) (CC : BinCoproducts C).

  Let genopt := constcoprod_functor1 CC A.

Definition δ_genoption_mor (Ze : Ptd) (c : C) :  C ⟦ BinCoproductObject (CC A (pr1 Ze c)),
                                                     pr1 Ze (BinCoproductObject (CC A c)) ⟧.
Proof.
  apply (@BinCoproductArrow _ _ _ (CC A (pr1 Ze c)) (pr1 Ze (BinCoproductObject (CC A c)))).
  - apply (BinCoproductIn1 (CC A c) · pr2 Ze (BinCoproductObject (CC A c))).
  - apply (# (pr1 Ze) (BinCoproductIn2 (CC A c))).
Defined.

Lemma is_nat_trans_δ_genoption_mor (Ze : Ptd) :
  is_nat_trans (δ_source genopt Ze : functor C C) (δ_target genopt Ze : functor C C)
     (δ_genoption_mor Ze).
Proof.
  intros a b f; simpl.
  induction Ze as [Z e].
  unfold BinCoproduct_of_functors_mor; simpl.
  etrans.
  { apply precompWithBinCoproductArrow. }
  rewrite id_left.
  apply pathsinv0, BinCoproductArrowUnique.
  - etrans.
    { rewrite assoc.
      apply cancel_postcomposition, BinCoproductIn1Commutes. }
    rewrite <- assoc.
    etrans.
    { apply maponpaths, pathsinv0, (nat_trans_ax e). }
    simpl; rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { apply BinCoproductOfArrowsIn1. }
    now rewrite id_left.
  - rewrite assoc.
    etrans.
    { apply cancel_postcomposition, BinCoproductIn2Commutes. }
    rewrite <- !functor_comp.
    now apply maponpaths, BinCoproductOfArrowsIn2.
Qed.

Lemma is_nat_trans_δ_genoption_mor_nat_trans : is_nat_trans (δ_source genopt) (δ_target genopt)
     (λ Ze : Ptd, δ_genoption_mor Ze,, is_nat_trans_δ_genoption_mor Ze).
Proof.
  intro Ze; induction Ze as [Z e]; intro Z'e'; induction Z'e' as [Z' e']; intro αX; induction αX as [α X]; simpl in *.
  apply nat_trans_eq; [apply homset_property |]; intro c; simpl.
  unfold BinCoproduct_of_functors_mor, BinCoproduct_of_functors_ob, δ_genoption_mor; simpl.
  rewrite precompWithBinCoproductArrow.
  apply pathsinv0, BinCoproductArrowUnique.
  - rewrite id_left, assoc.
    etrans.
    { apply cancel_postcomposition, BinCoproductIn1Commutes. }
    rewrite <- assoc.
    now apply maponpaths, X.
  - rewrite assoc.
    etrans.
    { apply cancel_postcomposition, BinCoproductIn2Commutes. }
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
  apply nat_trans_eq_alt; intro c; simpl.
  unfold δ_genoption_mor, BinCoproduct_of_functors_ob; simpl.
  rewrite id_right.
  apply pathsinv0, BinCoproduct_endo_is_identity.
  - apply BinCoproductIn1Commutes.
  - apply BinCoproductIn2Commutes.
Qed.

Lemma δ_law2_genoption : δ_law2 genopt δ_genoption.
Proof.
  intros Ze Z'e'; induction Ze as [Z e]; induction Z'e' as [Z' e'].
  apply nat_trans_eq_alt; intro c; simpl.
  unfold δ_genoption_mor, BinCoproduct_of_functors_ob; simpl.
  rewrite !id_left, id_right.
  apply pathsinv0, BinCoproductArrowUnique.
- rewrite assoc.
  etrans.
  { apply cancel_postcomposition, BinCoproductIn1Commutes. }
  rewrite <- assoc.
  etrans.
  { apply maponpaths, pathsinv0, (nat_trans_ax e'). }
  simpl; rewrite assoc.
  etrans.
  { apply cancel_postcomposition, BinCoproductIn1Commutes. }
  rewrite <- !assoc.
  now apply maponpaths.
- rewrite assoc.
  etrans.
  { apply cancel_postcomposition, BinCoproductIn2Commutes. }
  etrans.
  { apply pathsinv0, functor_comp. }
  now apply maponpaths, BinCoproductIn2Commutes.
Qed.

Definition genoption_DistributiveLaw : DistributiveLaw genopt.
Proof.
  exists δ_genoption.
  split.
  - exact δ_law1_genoption.
  - exact δ_law2_genoption.
Defined.

Definition precomp_genoption_Signature : Signature C C C :=
  θ_from_δ_Signature genopt genoption_DistributiveLaw.

End genoption_sig.

(** trivially instantiate previous section to option functor *)
Section option_sig.

Context (TC : Terminal C) (CC : BinCoproducts C).

  Let opt := option_functor CC TC.

  Definition δ_option: δ_source opt ⟹ δ_target opt := δ_genoption TC CC.
  Definition δ_law1_option :=  δ_law1_genoption TC CC.
  Definition δ_law2_option :=  δ_law2_genoption TC CC.
  Definition option_DistributiveLaw : DistributiveLaw opt := genoption_DistributiveLaw TC CC.
  Definition precomp_option_Signature : Signature C C C := precomp_genoption_Signature TC CC.

End option_sig.

(** Define δ for G = F^n *)
Section iter1_dl.

Context (G : functor C C) (DL : DistributiveLaw G).

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

  Context (C D : category).

Definition θ_functor_identity : StrengthForSignature (functor_identity [C, D]).
Proof.
  use tpair.
  + use tpair.
    * intro x.
      { use tpair.
        - intro y; simpl; apply identity.
        - abstract (now intros y y' f; rewrite id_left, id_right).
      }
    * abstract (now intros y y' f; apply nat_trans_eq_alt; intro z;
                simpl; rewrite id_left, id_right).
  (* If this part is abstract the eval cbn for the LC doesn't reduce properly *)
  + now split; intros x; intros; apply nat_trans_eq_alt; intro c; simpl; rewrite !id_left.
Defined.

(** Signature for the Id functor *)
Definition IdSignature : Signature C D D := tpair _ (functor_identity _) θ_functor_identity.
(** an alternative approach would be to go through θ_from_δ_Signature, based on the
observation that functor_identity [C,C,hsC] and
pre_comp_functor hsC hsC (functor_identity C) are isomorphic;
however, they are probably not propositionally equal, and so the benefit is marginal *)

End id_signature.

Section constantly_constant_signature.

  Context (C D D' : category) (d : D).

  Let H := constant_functor (functor_category C D') (functor_category C D) (constant_functor C D d).

Definition θ_const_const : StrengthForSignature H.
Proof.
  use tpair; simpl.
  + use tpair; simpl.
    * intro x.
      { use tpair.
        - intro y; simpl; apply identity.
        - abstract (now intros y y' f; rewrite id_left, id_right).
      }
    * abstract ( now intros y y' f; apply (nat_trans_eq (homset_property D)); intro z;
                simpl; rewrite id_left, id_right ).
  + now split; intros x; intros; apply (nat_trans_eq (homset_property D)); intro c; simpl; rewrite !id_left.
Defined.

Definition ConstConstSignature : Signature C D D' := tpair _ H θ_const_const.

End constantly_constant_signature.

(** Transform a signature with strength θ with underlying functor H into
    a signature with strength Gθ for the functor that comes from
    post-composition of all HX with a functor G
    G need not be an endofunctor, which is why the strength concept had
    to be given more heterogeneously than only on endofunctors on
    endofunctor categories
 *)
Section θ_for_postcomposition.

Context (C D D' E : category).

(** The category of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (category_Ptd C).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C]) .

Context (S: Signature C D D').

Let H : functor [C, D'] [C, D] := Signature_Functor S.
Let θ : nat_trans (θ_source H) (θ_target H) := theta S.
Let θ_strength1 := Sig_strength_law1 S.
Let θ_strength2 := Sig_strength_law2 S.
Context (G : [D, E]).

Let GH : functor [C, D'] [C, E] := functor_composite H (post_comp_functor G).

Definition Gθ_mor (XZe : [C, D'] ⊠ Ptd) : [C, E] ⟦ θ_source GH XZe, θ_target GH XZe ⟧.
Proof.
  set (X := pr1 XZe); set (Z := pr1 (pr2 XZe) : [C, C]).
  set (F1 := lassociator_CAT Z (H X) G).
  set (F2 := rwhisker_CAT G (θ XZe)).
  exact (F1 · F2).
Defined.

Lemma is_nat_trans_Gθ_mor : is_nat_trans (θ_source GH) (θ_target GH) Gθ_mor.
Proof.
  intros H1 H2 αX; induction H1 as [F1 X1]; induction H2 as [F2 X2].
  apply nat_trans_eq_alt; intro c; simpl.
  do 2 rewrite id_left.
  rewrite <- assoc.
  etrans.
  { apply maponpaths, pathsinv0, functor_comp. }
  etrans.
  { apply pathsinv0, functor_comp. }
  apply pathsinv0; etrans.
  { apply pathsinv0, functor_comp. }
  apply maponpaths.
  apply pathsinv0.
  rewrite assoc.
  generalize (nat_trans_eq_pointwise (nat_trans_ax θ (F1,,X1) (F2,,X2) αX) c).
  intro Hyp.
  apply Hyp.
Qed.

Definition Gθ : PrestrengthForSignature GH := tpair _ _ is_nat_trans_Gθ_mor.

Lemma Gθ_Strength1_int : θ_Strength1_int Gθ.
Proof.
  intro F.
  apply nat_trans_eq_alt; intro c; simpl.
  rewrite <- assoc.
  rewrite id_left.
  etrans.
  { apply pathsinv0, functor_comp. }
  apply pathsinv0; etrans.
  { apply pathsinv0, functor_id. }
  apply maponpaths.
  generalize (nat_trans_eq_pointwise (θ_strength1 F) c); simpl.
  intro Hyp.
  apply pathsinv0, Hyp.
Qed.

Lemma Gθ_Strength2_int : θ_Strength2_int Gθ.
Proof.
  intros F Ze Ze'.
  set (Z := pr1 Ze); set (Z' := pr1 Ze').
  apply nat_trans_eq_alt; intro c; simpl.
  do 4 rewrite id_left.
  etrans.
  { apply pathsinv0, functor_comp. }
  apply pathsinv0; etrans.
  { apply pathsinv0, functor_comp. }
  apply maponpaths.
  generalize (nat_trans_eq_pointwise (θ_strength2 F Ze Ze') c); simpl.
  rewrite id_left.
  intro Hyp.
  apply pathsinv0, Hyp.
Qed.

Definition Gθ_with_laws : StrengthForSignature GH := tpair _ Gθ (Gθ_Strength1_int ,, Gθ_Strength2_int).

Definition Gθ_Signature : Signature C E D' := tpair _ GH Gθ_with_laws.

End θ_for_postcomposition.
