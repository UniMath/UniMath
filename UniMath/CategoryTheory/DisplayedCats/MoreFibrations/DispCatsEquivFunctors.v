(** This file is meant to provide an equivalence between the displayed categories on a base category and the functors into the base category.
For now it only contains the construction of a displayed category from a functor. *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence. (* only coercions *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.Core.TransportMorphisms.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.Prefibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.CartesiannessOfComposites.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Section TransportMorphisms. (* In the transport of morphisms we have to make a choice in the order of transports, which we denote by "st" and "ts" (source/target). Of course the results are propositionally equal.*)

Definition transportf_mor_ts
    {C : category} {c0 c1 c0' c1' : C} (H0 : c0 = c0') (H1 : c1 = c1')
  : (c0 --> c1) -> (c0' --> c1').
Proof.
  intro f.
  apply (transportf _ H1).
  apply (transportf (λ c, C⟦c, c1⟧) H0).
  exact f.
Defined.

Definition transportf_mor_st
    {C : category} {c0 c1 c0' c1' : C} (H0 : c0 = c0') (H1 : c1 = c1')
  : (c0 --> c1) -> (c0' --> c1').
Proof.
  intro f.
  apply (transportf (λ c, C⟦c, c1'⟧) H0).
  apply (transportf _ H1).
  exact f.
Defined.

Definition transportf_mor_eq
    {C : category} {c0 c1 c0' c1' : C} (H0 : c0 = c0') (H1 : c1 = c1') (f: c0 --> c1)
  : transportf_mor_ts H0 H1 f = transportf_mor_st H0 H1 f.
Proof.
  induction H0. induction H1.
  apply idpath_transportf.
Qed.

(* Choose which to use as standard. *)
Definition transportf_mor
    {C : category} {c0 c1 c0' c1' : C} (H0 : c0 = c0') (H1 : c1 = c1')
  := transportf_mor_ts H0 H1.

Definition transp_pres_id
    {C : category} {c c' : C} (H : c = c')
  : identity c' = transportf_mor H H (identity c).
Proof.
  induction H.
  apply idpath_transportf.
Qed.

Definition transp_pres_comp
    {C : category} {c0 c0' c1 c2 c2' : C} (H0 : c0 = c0') (H2 : c2 = c2')
    (f0: c0 --> c1) (f1 : c1 --> c2)
  : transportf_mor H0 H2 (f0 · f1) =
    (transportf_mor H0 (idpath _) f0) · (transportf_mor (idpath _) H2 f1).
Proof.
  induction H2. induction H0.
  apply idpath_transportf.
Qed.

Definition transp_pres_comp'
    {C : category} {c0 c0' c1 c1' c2 c2' : C} (H0 : c0 = c0') (H1 : c1 = c1') (H2 : c2 = c2')
    (f0: c0 --> c1) (f1 : c1 --> c2)
  : transportf_mor H0 H2 (f0 · f1) =
    (transportf_mor H0 H1 f0) · (transportf_mor H1 H2 f1).
Proof.
  eapply pathscomp0.
  - apply transp_pres_comp.
  - apply pathsinv0.
    eapply pathscomp0.
    + apply (maponpaths _ (transportf_mor_eq H1 H2 _)).
    + apply transport_compose'.
Qed.

End TransportMorphisms.


Section DispCatOfFibers.

Definition disp_cat_of_fibers_ob
    {B C : category} (F : functor C B)
  : B -> UU.
Proof.
  intro b.
  exact (∑ c : C, b = F c).
Defined.

Definition disp_cat_of_fibers_mor
    {B C : category} (F : functor C B)
  : ∏ (b b' : B),
    disp_cat_of_fibers_ob F b -> disp_cat_of_fibers_ob F b' -> (b --> b') -> UU.
Proof.
  intros b b' [c H_ob] [c' H'_ob] f.
  exact (∑ (g : c --> c'), (functor_on_morphisms F) g = transportf_mor H_ob H'_ob f).
Defined.

Definition disp_cat_of_fibers_mor'
    {B C : category} {F : functor C B} {b b' : B}
    (c : disp_cat_of_fibers_ob F b) (c' : disp_cat_of_fibers_ob F b')
  : (b --> b') -> UU
:= disp_cat_of_fibers_mor F b b' c c'.

Definition disp_cat_of_fibers_ob_mor
    {B C : category} (F : functor C B)
  : disp_cat_ob_mor B.
Proof.
  exists (disp_cat_of_fibers_ob F).
  exact (disp_cat_of_fibers_mor F).
Defined.

Definition disp_cat_of_fibers_id
    {B C : category} (F : functor C B)
  : (∏ (b : B) (c_H : disp_cat_of_fibers_ob F b),
     disp_cat_of_fibers_mor' c_H c_H (identity b)).
Proof.
  intros b [c H].
  exists (identity c).
  eapply pathscomp0.
  - apply functor_id.
  - apply transp_pres_id.
Defined.

Definition disp_cat_of_fibers_id'
    {B C : category} {F : functor C B} {b : B} (c_H : disp_cat_of_fibers_ob F b)
  : disp_cat_of_fibers_mor' c_H c_H (identity b)
:= disp_cat_of_fibers_id F b c_H.

Definition disp_cat_of_fibers_comp
    {B C : category} (F : functor C B)
  : ∏ (b b' b'' : B) (f : b --> b') (f': b' --> b'') (c : disp_cat_of_fibers_ob F b)
       (c' : disp_cat_of_fibers_ob F b') (c'' : disp_cat_of_fibers_ob F b''),
    (disp_cat_of_fibers_mor' c c' f) -> (disp_cat_of_fibers_mor' c' c'' f')
    -> (disp_cat_of_fibers_mor' c c'' (f · f')).
Proof.
  intros b b' b'' f f' [c H_ob] [c' H'_ob] [c'' H''_ob] [g H_mor] [g' H'_mor].
  exists (g · g').
  eapply pathscomp0.
  - apply functor_comp.
  - eapply pathscomp0.
    2: { apply pathsinv0. apply (transp_pres_comp' H_ob H'_ob H''_ob). }
    + eapply pathscomp0.
      * exact (maponpaths (λ mor, mor · ((# F)%Cat g')) H_mor).
      * exact (maponpaths (λ mor, (transportf_mor H_ob H'_ob f) · mor) H'_mor).
Defined.

Definition disp_cat_of_fibers_comp'
    {B C : category} {F : functor C B} {b b' b'' : B} {f : b --> b'} {f': b' --> b''}
    {c : disp_cat_of_fibers_ob F b} {c' : disp_cat_of_fibers_ob F b'} {c'' : disp_cat_of_fibers_ob F b''}
    (g : disp_cat_of_fibers_mor F b b' c c' f) (g' : disp_cat_of_fibers_mor F b' b'' c' c'' f')
  : (disp_cat_of_fibers_mor F b b'' c c'' (f · f'))
:= disp_cat_of_fibers_comp F b b' b'' f f' c c' c'' g g'.

Definition disp_cat_of_fibers_id_comp
    {B C : category} (F : functor C B)
  : disp_cat_id_comp B (disp_cat_of_fibers_ob_mor F)
:= (disp_cat_of_fibers_id F ,, disp_cat_of_fibers_comp F).

Definition disp_cat_of_fibers_data
    {B C : category} (F : functor C B)
  : disp_cat_data B.
Proof.
  exists (disp_cat_of_fibers_ob_mor F).
  apply disp_cat_of_fibers_id_comp.
Defined.

Definition disp_cat_of_fibers_id_left
    {B C : category} (F : functor C B)
  : ∏ (b b' : B) (f : b --> b') (c : disp_cat_of_fibers_ob F b)
      (c' : disp_cat_of_fibers_ob F b')
      (g : disp_cat_of_fibers_mor' c c' f),
    disp_cat_of_fibers_comp' (disp_cat_of_fibers_id F _ _) g
    = transportb _ (id_left _) g.
Proof.
  intros b b' f [c H_ob] [c' H'_ob] [g H_mor].
  apply subtypePath.
  - intros mor.
    apply homset_property.
  - simpl.
    apply pathsinv0.
    eapply pathscomp0.
    + apply (@pr1_transportf _ _ (λ mor, (λ mor', (functor_on_morphisms F) mor' = transportf_mor H_ob H'_ob mor))).
    + simpl.
      eapply pathscomp0.
      * apply (eqtohomot (transportf_const _ _)).
      * apply pathsinv0.
        apply id_left.
Qed.

Definition disp_cat_of_fibers_id_left'
    {B C : category} {F : functor C B} {b b' : B} {f : b --> b'} {c : disp_cat_of_fibers_ob F b}
    {c' : disp_cat_of_fibers_ob F b'} (g : disp_cat_of_fibers_mor' c c' f)
  : disp_cat_of_fibers_comp' (disp_cat_of_fibers_id F _ _) g = transportb _ (id_left _) g
:= disp_cat_of_fibers_id_left F b b' f c c' g.

Definition disp_cat_of_fibers_id_right
    {B C : category} (F : functor C B)
  : ∏ (b b' : B) (f : b --> b') (c : disp_cat_of_fibers_ob F b)
      (c' : disp_cat_of_fibers_ob F b')
      (g : disp_cat_of_fibers_mor' c c' f),
    disp_cat_of_fibers_comp' g (disp_cat_of_fibers_id F _ _)
    = transportb _ (id_right _) g.
Proof.
  intros b b' f [c H_ob] [c' H'_ob] [g H_mor].
  apply subtypePath.
  - intros mor.
    apply homset_property.
  - simpl.
    apply pathsinv0.
    eapply pathscomp0.
    + apply (@pr1_transportf _ _ (λ mor, (λ mor', (functor_on_morphisms F) mor' = transportf_mor H_ob H'_ob mor))).
    +  simpl.
       eapply pathscomp0.
       * apply (eqtohomot (transportf_const _ _)).
       * apply pathsinv0.
         apply id_right.
Qed.

Definition disp_cat_of_fibers_id_right'
    {B C : category} {F : functor C B} {b b' : B} {f : b --> b'} {c : disp_cat_of_fibers_ob F b}
    {c' : disp_cat_of_fibers_ob F b'} (g : disp_cat_of_fibers_mor' c c' f)
  : disp_cat_of_fibers_comp' g (disp_cat_of_fibers_id F _ _) = transportb _ (id_right _) g
:= disp_cat_of_fibers_id_right F b b' f c c' g.

Definition disp_cat_of_fibers_assoc
    {B C : category} (F : functor C B)
  : ∏ (b0 b1 b2 b3 : B)
      (f1 : b0 --> b1) (f2 : b1 --> b2) (f3 : b2 --> b3)
      (c0 : disp_cat_of_fibers_ob F b0) (c1 : disp_cat_of_fibers_ob F b1)
      (c2 : disp_cat_of_fibers_ob F b2) (c3 : disp_cat_of_fibers_ob F b3)
      (g1 : disp_cat_of_fibers_mor' c0 c1 f1) (g2 : disp_cat_of_fibers_mor' c1 c2 f2)
      (g3 : disp_cat_of_fibers_mor' c2 c3 f3),
    disp_cat_of_fibers_comp' g1 (disp_cat_of_fibers_comp' g2 g3)
    = transportb _ (assoc _ _ _) (disp_cat_of_fibers_comp' (disp_cat_of_fibers_comp' g1 g2) g3).
Proof.
  intros b0 b1 b2 b3 f1 f2 f3 [c0 H0_ob] [c1 H1_ob] [c2 H2_ob] [c3 H3_ob]
         [g1 H1_mor] [g2 H2_mor] [g3 H3_mor].
  apply subtypePath.
  - intros mor.
    apply homset_property.
  - simpl.
    apply pathsinv0.
    eapply pathscomp0.
    + (*set (pr1trans := pr1_transportf (assoc f1 f2 f3)
          (disp_cat_of_fibers_comp' (disp_cat_of_fibers_comp' (g1,, H1_mor) (g2,, H2_mor)) (g3,, H3_mor))).*)
      apply (@pr1_transportf _ _ (λ mor, (λ mor', (functor_on_morphisms F) mor' = transportf_mor H0_ob H3_ob mor))).
    + simpl.
      eapply pathscomp0.
      * apply (eqtohomot (transportf_const _ _)).
      * apply pathsinv0.
        apply assoc.
Qed.

Definition disp_cat_of_fibers_assoc'
    {B C : category} {F : functor C B}
    {b0 b1 b2 b3 : B} {f1 : b0 --> b1} {f2 : b1 --> b2} {f3 : b2 --> b3}
    {c0 : disp_cat_of_fibers_ob F b0} {c1 : disp_cat_of_fibers_ob F b1}
    {c2 : disp_cat_of_fibers_ob F b2} {c3 : disp_cat_of_fibers_ob F b3}
    (g1 : disp_cat_of_fibers_mor' c0 c1 f1) (g2 : disp_cat_of_fibers_mor' c1 c2 f2)
    (g3 : disp_cat_of_fibers_mor' c2 c3 f3)
  : disp_cat_of_fibers_comp' g1 (disp_cat_of_fibers_comp' g2 g3)
    = transportb _ (assoc _ _ _) (disp_cat_of_fibers_comp' (disp_cat_of_fibers_comp' g1 g2) g3)
:= disp_cat_of_fibers_assoc F b0 b1 b2 b3 f1 f2 f3 c0 c1 c2 c3 g1 g2 g3.

Definition disp_cat_of_fibers_homsets
    {B C : category} (F : functor C B)
  : ∏ (b b' : B) (f : b --> b')
      (c_H : disp_cat_of_fibers_ob F b) (c'_H : disp_cat_of_fibers_ob F b'),
    isaset (disp_cat_of_fibers_mor' c_H c'_H f).
Proof.
  intros b b' f c_H c'_H.
  apply isaset_total2.
  - apply (homset_property C).
  - intros g.
    apply isasetaprop.
    apply (homset_property B).
Qed.

Definition disp_cat_of_fibers_homsets'
    {B C : category} {F : functor C B}
    {b b' : B} (f : b --> b')
    (c_H : disp_cat_of_fibers_ob F b) (c'_H : disp_cat_of_fibers_ob F b')
  : isaset (disp_cat_of_fibers_mor' c_H c'_H f)
:= disp_cat_of_fibers_homsets F b b' f c_H c'_H.

Definition disp_cat_of_fibers_axioms
    {B C : category} (F : functor C B)
  : disp_cat_axioms B (disp_cat_of_fibers_data F).
Proof.
  exists (disp_cat_of_fibers_id_left F).
  exists (disp_cat_of_fibers_id_right F).
  exists (disp_cat_of_fibers_assoc F).
  exact (disp_cat_of_fibers_homsets F).
Qed.

Definition disp_cat_of_fibers
    {B C : category} (F : functor C B)
  : disp_cat B.
Proof.
  exists (disp_cat_of_fibers_data F).
  exact (disp_cat_of_fibers_axioms F).
Defined.

End DispCatOfFibers.
