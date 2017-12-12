
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Rezk completion

 - Construction of the Rezk completion via Yoneda

 - Universal property of the Rezk completion

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.sub_precategories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.precomp_fully_faithful.
Require Import UniMath.CategoryTheory.precomp_ess_surj.

(** * Construction of the Rezk completion via Yoneda *)

Section rezk.

Variable A : precategory.
Hypothesis hsA: has_homsets A.

Definition Rezk_completion : univalent_category.
Proof.
  exists (full_img_sub_precategory (yoneda A hsA)).
  apply is_univalent_full_subcat.
  apply (is_univalent_functor_category _ _ is_univalent_HSET).
Defined.

Definition Rezk_eta : functor A Rezk_completion.
Proof.
  apply (functor_full_img (yoneda A hsA)).
Defined.

Lemma Rezk_eta_fully_faithful : fully_faithful Rezk_eta.
Proof.
  apply (functor_full_img_fully_faithful_if_fun_is _ _ (yoneda A hsA)).
  apply yoneda_fully_faithful.
Defined.

Lemma Rezk_eta_essentially_surjective : essentially_surjective Rezk_eta.
Proof.
  apply (functor_full_img_essentially_surjective _ _ (yoneda A hsA)).
Defined.

End rezk.

(** * Universal property of the Rezk completion *)

Definition functor_from (C : precategory) : UU
  := ∑ D : univalent_category, functor C D.

Coercion target_category (C : precategory) (X : functor_from C) : univalent_category := pr1 X.
Definition func_functor_from {C : precategory} (X : functor_from C) : functor C X := pr2 X.

Definition is_initial_functor_from (C : precategory) (X : functor_from C) : UU
  := ∏ X' : functor_from C,
     ∃! H : functor X X',
       functor_composite (func_functor_from X) H = func_functor_from X'.

Section rezk_universal_property.

Variables A : precategory.
Hypothesis hsA: has_homsets A.

Section fix_a_category.

Variable C : precategory.
Hypothesis Ccat : is_univalent C.

Lemma pre_comp_rezk_eta_is_fully_faithful :
    fully_faithful (pre_composition_functor A (Rezk_completion A hsA) C
                (pr2 (pr2 (Rezk_completion A hsA))) (pr2 Ccat) ((Rezk_eta A hsA))).
Proof.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful.
  apply Rezk_eta_essentially_surjective.
  apply Rezk_eta_fully_faithful.
Defined.

Lemma pre_comp_rezk_eta_is_ess_surj :
   essentially_surjective (pre_composition_functor A (Rezk_completion A hsA) C
   (pr2 (pr2 (Rezk_completion A hsA))) (pr2 Ccat)
   (Rezk_eta A hsA)).
Proof.
  apply pre_composition_essentially_surjective.
  apply Rezk_eta_essentially_surjective.
  apply Rezk_eta_fully_faithful.
Defined.

Definition Rezk_adj_equiv : adj_equivalence_of_precats
  (pre_composition_functor A (Rezk_completion A hsA) C
       (pr2 (pr2 (Rezk_completion A hsA))) (pr2 Ccat)
       (Rezk_eta A hsA)).
Proof.
  apply (@rad_equivalence_of_precats
           [Rezk_completion A hsA, C, pr2 Ccat]
           [A, C, pr2 Ccat]
           (is_univalent_functor_category _ _ _ )
           _
           (pre_comp_rezk_eta_is_fully_faithful)
           (pre_comp_rezk_eta_is_ess_surj)).
Defined.

Theorem Rezk_eta_Universal_Property :
  isweq (pre_composition_functor A (Rezk_completion A hsA) C
   (pr2 (pr2 (Rezk_completion A hsA))) (pr2 Ccat) (Rezk_eta A hsA)).
Proof.
  apply adj_equiv_of_cats_is_weq_of_objects.
  - apply is_univalent_functor_category;
    assumption.
  - apply is_univalent_functor_category;
    assumption.
  - apply Rezk_adj_equiv.
Defined.

Definition Rezk_weq : [Rezk_completion A hsA, C, pr2 Ccat] ≃ [A, C, pr2 Ccat ]
  := weqpair _ Rezk_eta_Universal_Property.

End fix_a_category.

Lemma Rezk_initial_functor_from : is_initial_functor_from A
      (tpair _ (Rezk_completion A hsA) (Rezk_eta A hsA)).
Proof.
  intro D.
  destruct D as [D F].
  set (T:= Rezk_eta_Universal_Property D (pr2 D)).
  apply T.
Defined.

Lemma path_to_ctr (A' : UU) (B : A' -> UU) (isc : iscontr (total2 (λ a, B a)))
           (a : A') (p : B a) : a = pr1 (pr1 isc).
Proof.
  exact (maponpaths pr1 (pr2 isc (tpair _ a p))).
Defined.

Definition Rezk_completion_endo_is_identity (D : functor_from A)
           (DH : is_initial_functor_from A D)
  : ∏ X : functor D D, functor_composite (func_functor_from D) X = func_functor_from D
        ->
        X = functor_identity D.
Proof.
  intros X H.
  set (DH' := DH D).
  intermediate_path (pr1 (pr1 DH')).
  - apply path_to_ctr.
    apply H.
  - apply pathsinv0.
    apply path_to_ctr.
    apply functor_identity_right.
Defined.


End rezk_universal_property.

Section opp_rezk_universal_property.

Variables A : precategory.
Hypothesis hsA: has_homsets A.

Let hsAop : has_homsets A^op := has_homsets_opp hsA.
Let hsRAop : has_homsets (Rezk_completion A hsA)^op :=
           has_homsets_opp (pr2 (pr2 (Rezk_completion A hsA))).

Section fix_a_category.

Variable C : precategory.
Hypothesis Ccat : is_univalent C.

Lemma pre_comp_rezk_eta_opp_is_fully_faithful :
    fully_faithful
       (pre_composition_functor A^op (Rezk_completion A hsA)^op C
                hsRAop (pr2 Ccat) (functor_opp (Rezk_eta A hsA))).
Proof.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful.
  - apply opp_functor_essentially_surjective.
    apply Rezk_eta_essentially_surjective.
  - apply opp_functor_fully_faithful.
    apply Rezk_eta_fully_faithful.
Defined.

Lemma pre_comp_rezk_eta_opp_is_ess_surj :
   essentially_surjective
      (pre_composition_functor A^op (Rezk_completion A hsA)^op C
           hsRAop (pr2 Ccat) (functor_opp (Rezk_eta A hsA))).
Proof.
  apply pre_composition_essentially_surjective.
  - apply opp_functor_essentially_surjective.
    apply Rezk_eta_essentially_surjective.
  - apply opp_functor_fully_faithful.
    apply Rezk_eta_fully_faithful.
Defined.

Definition Rezk_op_adj_equiv :
 adj_equivalence_of_precats
     (pre_composition_functor A^op (Rezk_completion A hsA)^op C hsRAop
        (pr2 Ccat) (functor_opp (Rezk_eta A hsA))).
Proof.
  apply (@rad_equivalence_of_precats
           [(Rezk_completion A hsA)^op, C, pr2 Ccat]
           [A^op, C, pr2 Ccat]
           (is_univalent_functor_category _ _ _ )
           _
           (pre_comp_rezk_eta_opp_is_fully_faithful)
           (pre_comp_rezk_eta_opp_is_ess_surj)).
Defined.

Theorem Rezk_eta_opp_Universal_Property :
  isweq (pre_composition_functor A^op (Rezk_completion A hsA)^op C
          hsRAop (pr2 Ccat) (functor_opp (Rezk_eta A hsA))).
Proof.
  apply adj_equiv_of_cats_is_weq_of_objects.
  - apply is_univalent_functor_category;
    assumption.
  - apply is_univalent_functor_category;
    assumption.
  - apply Rezk_op_adj_equiv.
Defined.

Definition Rezk_opp_weq : [(Rezk_completion A hsA)^op, C, pr2 Ccat] ≃ [A^op, C, pr2 Ccat]
  := weqpair _ Rezk_eta_opp_Universal_Property.

End fix_a_category.

End opp_rezk_universal_property.
