(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)

(** **********************************************************

Contents:

- Definition of the sum of two signatures ([BinSum_of_Signatures]), in particular proof of strength
  laws for the sum

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.limits.binproducts.

Local Open Scope cat.

Section binsum_of_signatures.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable D : precategory.
Variable hs : has_homsets D.
Variable D' : precategory.
Variable hs' : has_homsets D'.
Variable CD : BinCoproducts D.

Section construction.

Local Notation "'CCD'" := (BinCoproducts_functor_precat C D CD hs : BinCoproducts [C, D, hs]).

Variables H1 H2 : functor [C, D', hs'] [C, D, hs].

Variable θ1 : θ_source(hs := hsC) H1 ⟹ θ_target H1.
Variable θ2 : θ_source(hs := hsC) H2 ⟹ θ_target H2.

Variable S11 : θ_Strength1 θ1.
Variable S12 : θ_Strength2 θ1.
Variable S21 : θ_Strength1 θ2.
Variable S22 : θ_Strength2 θ2.

(** * Definition of the data of the sum of two signatures *)

Definition H : functor [C, D', hs'] [C, D, hs] := BinCoproduct_of_functors _ _ CCD H1 H2.

(* This becomes too slow: *)
(* Definition H : functor [C, C, hs] [C, C, hs] := BinCoproduct_of_functors_alt CCC H1 H2. *)

Local Definition θ_ob_fun (X : [C, D', hs']) (Z : precategory_Ptd C hsC) :
   ∏ c : C,
    (functor_composite_data (pr1 Z)
     (BinCoproduct_of_functors_data C D CD (H1 X) (H2 X))) c
   --> (BinCoproduct_of_functors_data C D CD (H1 (functor_composite (pr1 Z) X))
       (H2 (functor_composite (pr1 Z) X))) c.
Proof.
  intro c.
  apply BinCoproductOfArrows.
  - exact (pr1 (θ1 (X ⊗ Z)) c).
  - exact (pr1 (θ2 (X ⊗ Z)) c).
Defined.

Local Lemma is_nat_trans_θ_ob_fun (X : [C, D', hs']) (Z : precategory_Ptd C hsC):
   is_nat_trans _ _ (θ_ob_fun X Z).
Proof.
  intros x x' f.
  eapply pathscomp0; [ apply BinCoproductOfArrows_comp | ].
  eapply pathscomp0; [ | eapply pathsinv0; apply BinCoproductOfArrows_comp].
  apply BinCoproductOfArrows_eq.
  * apply (nat_trans_ax (θ1 (X ⊗ Z))).
  * apply (nat_trans_ax (θ2 (X ⊗ Z))).
Qed.

Definition θ_ob : ∏ XF, θ_source(hs := hsC) H XF --> θ_target H XF.
Proof.
  intros [X Z].
  exists (θ_ob_fun X Z).
  apply is_nat_trans_θ_ob_fun.
Defined.

Local Lemma is_nat_trans_θ_ob :
  is_nat_trans (θ_source H) (θ_target H) θ_ob.
Proof.
  intros XZ X'Z' αβ.
  assert (Hyp1:= nat_trans_ax θ1 _ _ αβ).
  assert (Hyp2:= nat_trans_ax θ2 _ _ αβ).
  apply nat_trans_eq.
  - exact hs.
  - intro c; simpl.
    destruct XZ as [X Z].
    destruct X'Z' as [X' Z'].
    destruct αβ as [α β]. simpl in *.
    (* on the right-hand side, there is a second but unfolded BinCoproductOfArrows in the row -
       likewise a first such on the left-hand side, to be treater further below *)
    eapply pathscomp0; [ | eapply pathsinv0; apply BinCoproductOfArrows_comp].
    eapply pathscomp0. apply cancel_postcomposition. apply BinCoproductOfArrows_comp.
    eapply pathscomp0. apply BinCoproductOfArrows_comp.
    apply BinCoproductOfArrows_eq.
    + apply (nat_trans_eq_pointwise Hyp1 c).
    + apply (nat_trans_eq_pointwise Hyp2 c).
Qed.

Local Definition θ : θ_source(hs := hsC) H ⟹ θ_target H.
Proof.
  exists θ_ob.
  apply is_nat_trans_θ_ob.
Defined.

(** * Proof of the laws of the sum of two signatures *)

Lemma SumStrength1 : θ_Strength1 θ.
Proof.
  intro X.
  apply (nat_trans_eq hs).
  intro x; simpl.
  eapply pathscomp0; [ apply BinCoproductOfArrows_comp |].
  apply pathsinv0, BinCoproduct_endo_is_identity.
  + rewrite BinCoproductOfArrowsIn1.
    unfold θ_Strength1 in S11.
    assert (Ha := nat_trans_eq_pointwise (S11 X) x).
    eapply pathscomp0; [ | apply id_left].
    apply cancel_postcomposition.
    apply Ha.
  + rewrite BinCoproductOfArrowsIn2.
    unfold θ_Strength1 in S21.
    assert (Ha := nat_trans_eq_pointwise (S21 X) x).
    eapply pathscomp0; [ | apply id_left].
    apply cancel_postcomposition.
    apply Ha.
Qed.

Lemma SumStrength2 : θ_Strength2 θ.
Proof.
  intros X Z Z' Y α.
  apply (nat_trans_eq hs); intro x.
  eapply pathscomp0; [ apply BinCoproductOfArrows_comp |].
  apply pathsinv0.
  eapply pathscomp0. apply cancel_postcomposition. simpl. apply BinCoproductOfArrows_comp.
  eapply pathscomp0. apply BinCoproductOfArrows_comp.
  apply pathsinv0.
  apply BinCoproductOfArrows_eq.
  - assert (Ha:=S12 X Z Z' Y α).
    simpl in Ha.
    assert (Ha_x := nat_trans_eq_pointwise Ha x).
    apply Ha_x.
  - assert (Ha:=S22 X Z Z' Y α).
    simpl in Ha.
    assert (Ha_x := nat_trans_eq_pointwise Ha x).
    apply Ha_x.
Qed.

Variable S11' : θ_Strength1_int θ1.
Variable S12' : θ_Strength2_int θ1.
Variable S21' : θ_Strength1_int θ2.
Variable S22' : θ_Strength2_int θ2.

Lemma SumStrength1' : θ_Strength1_int θ.
Proof.
  clear S11 S12 S21 S22 S12' S22'; intro X.
  apply (nat_trans_eq hs); intro x.
  eapply pathscomp0. apply BinCoproductOfArrows_comp.
  apply pathsinv0, BinCoproduct_endo_is_identity.
  + rewrite BinCoproductOfArrowsIn1.
    assert (Ha := nat_trans_eq_pointwise (S11' X) x).
    simpl in Ha.
    eapply pathscomp0; [ | apply id_left].
    apply cancel_postcomposition.
    apply Ha.
  + rewrite BinCoproductOfArrowsIn2.
    assert (Ha := nat_trans_eq_pointwise (S21' X) x).
    simpl in Ha.
    eapply pathscomp0; [ | apply id_left].
    apply cancel_postcomposition.
    apply Ha.
Qed.

Lemma SumStrength2' : θ_Strength2_int θ.
Proof.
  clear S11 S12 S21 S22 S11' S21'; intros X Z Z'.
  apply (nat_trans_eq hs); intro x; simpl; rewrite id_left.
  eapply pathscomp0. apply BinCoproductOfArrows_comp.
  apply pathsinv0.
  eapply pathscomp0. apply BinCoproductOfArrows_comp.
  apply pathsinv0.
  apply BinCoproductOfArrows_eq.
  - assert (Ha:=S12' X Z Z').
    simpl in Ha.
    assert (Ha_x := nat_trans_eq_pointwise Ha x).
    simpl in Ha_x.
    rewrite id_left in Ha_x.
    apply Ha_x.
  - assert (Ha:=S22' X Z Z').
    simpl in Ha.
    assert (Ha_x := nat_trans_eq_pointwise Ha x).
    simpl in Ha_x.
    rewrite id_left in Ha_x.
    apply Ha_x.
Qed.

End construction.

Definition BinSum_of_Signatures (S1 S2 : Signature C hsC D hs D' hs') : Signature C hsC D hs D' hs'.
Proof.
  destruct S1 as [H1 [θ1 [S11' S12']]].
  destruct S2 as [H2 [θ2 [S21' S22']]].
  exists (H H1 H2).
  exists (θ H1 H2 θ1 θ2).
  split.
  + apply SumStrength1'; assumption.
  + apply SumStrength2'; assumption.
Defined.

Lemma is_omega_cocont_BinSum_of_Signatures (S1 S2 : Signature C hsC D hs D' hs')
  (h1 : is_omega_cocont S1) (h2 : is_omega_cocont S2) :
  is_omega_cocont (BinSum_of_Signatures S1 S2).
Proof.
destruct S1 as [F1 [F2 [F3 F4]]]; simpl in *.
destruct S2 as [G1 [G2 [G3 G4]]]; simpl in *.
unfold H.
apply is_omega_cocont_BinCoproduct_of_functors; try assumption.
apply functor_category_has_homsets.
Defined.

End binsum_of_signatures.
