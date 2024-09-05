(**************************************************************************************************

  The Rezk completion

  For any category A, there exists a univalent category D with a weak equivalence F : A ⟶ D. D
  consists of all objects in PreShv H that are isomorphic to the Yoneda embedding of an object in A.
  Since F is a weak equivalence, precomposition with it gives an adjoint equivalence between the
  functor categories [A, C] and [D, C], and also between [A^op, C] and [D^op, C], for any univalent
  category C.
  Another way to phrase this, is the fact that F is the "initial functor from A": any functor from A
  to a univalent category factors uniquely through F.
  Using this, we can show that two Rezk completions (D, F) and (D', F') are equal.

  Contents
  1. The definition of an initial functor, and its properties
    [functor_from] [is_initial_functor_from]
  2. The construction of the Rezk completion and the embedding F [Rezk_completion] [Rezk_eta]
  3. The equivalence between the covariant functor categories
    [Rezk_adj_equiv] [Rezk_eta_Universal_Property]
  4. The equivalence between the contravariant functor categories
    [Rezk_op_adj_equiv] [Rezk_eta_opp_Universal_Property]
  5. The uniqueness of the Rezk completion [rezk_completion_unique]

  Original authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman
    january 2013

 **************************************************************************************************)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Propositions.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

(** * 1. The definition of an initial functor, and its properties *)

Definition functor_from (C : precategory) : UU
  := ∑ D : univalent_category, functor C D.

#[reversible=no] Coercion target_category (C : precategory) (X : functor_from C) : univalent_category := pr1 X.
Definition func_functor_from {C : precategory} (X : functor_from C) : functor C X := pr2 X.

Definition is_initial_functor_from (C : precategory) (X : functor_from C) : UU
  := ∏ X' : functor_from C,
     ∃! H : functor X X',
       functor_composite (func_functor_from X) H = func_functor_from X'.

Definition initial_functor_endo_is_identity
    {A : category}
    (D : functor_from A)
    (DH : is_initial_functor_from A D)
  : ∏ X : functor D D,
    functor_composite (func_functor_from D) X = func_functor_from D
    → X = functor_identity D.
Proof.
  intros X H.
  apply (uniqueExists (DH D)).
  - exact H.
  - apply functor_identity_right.
Defined.

Lemma weak_equivalence_initial_functor_from
  {A : category}
  (B : univalent_category)
  (F : A ⟶ B)
  (HF1 : fully_faithful F)
  (HF2 : essentially_surjective F)
  : is_initial_functor_from A (B ,, F).
Proof.
  intro D.
  refine ((_ : isweq (pre_composition_functor _ _ _ _)) (func_functor_from D)).
  apply adj_equiv_of_cats_is_weq_of_objects;
    [ apply is_univalent_functor_category
    | apply is_univalent_functor_category
    | apply (precomp_adjoint_equivalence (make_univalent_category _ _) _ HF2 HF1)];
    apply univalent_category_is_univalent.
Defined.

(** * 2. The construction of the Rezk completion and the embedding F *)

Section rezk.

  Context (A : category).

  Definition category_Rezk_completion : category.
  Proof.
    exists (full_img_sub_precategory (yoneda A)).
    exact (has_homsets_full_img_sub_precategory (yoneda A)).
  Defined.

  Definition Rezk_completion : univalent_category.
  Proof.
    exists category_Rezk_completion.
    apply is_univalent_full_sub_category.
    apply (is_univalent_functor_category _ _ is_univalent_HSET).
  Defined.

  Definition Rezk_eta : functor A Rezk_completion.
  Proof.
    apply (functor_full_img (yoneda A)).
  Defined.

  Lemma Rezk_eta_fully_faithful : fully_faithful Rezk_eta.
  Proof.
    apply (functor_full_img_fully_faithful_if_fun_is _ _ (yoneda A)).
    apply yoneda_fully_faithful.
  Defined.

  Lemma Rezk_eta_essentially_surjective : essentially_surjective Rezk_eta.
  Proof.
    apply (functor_full_img_essentially_surjective _ _ (yoneda A)).
  Defined.

End rezk.

Definition Rezk_completion_of_univalent
  (A : univalent_category)
  : adj_equivalence_of_cats (Rezk_eta A).
Proof.
  apply rad_equivalence_of_cats.
  - apply univalent_category_is_univalent.
  - apply Rezk_eta_fully_faithful.
  - apply Rezk_eta_essentially_surjective.
Defined.

(** * 3. The equivalence between the covariant functor categories *)

Section rezk_universal_property.

  Context (A : category).

  Section RezkFunctorWeq.

    Context (C : category) (Ccat : is_univalent C).

    Definition Rezk_adj_equiv
      : adj_equivalence_of_cats (pre_composition_functor _ _ C (Rezk_eta A)).
    Proof.
      use (precomp_adjoint_equivalence (make_univalent_category _ _)).
      - apply Ccat.
      - apply Rezk_eta_essentially_surjective.
      - apply Rezk_eta_fully_faithful.
    Defined.

    Theorem Rezk_eta_Universal_Property :
      isweq (pre_composition_functor _ _ C (Rezk_eta A)).
    Proof.
      apply adj_equiv_of_cats_is_weq_of_objects.
      - apply is_univalent_functor_category;
        assumption.
      - apply is_univalent_functor_category;
        assumption.
      - apply Rezk_adj_equiv.
    Defined.

    Definition Rezk_weq : [Rezk_completion A, C] ≃ [A, C]
      := make_weq _ Rezk_eta_Universal_Property.

  End RezkFunctorWeq.

  Lemma Rezk_initial_functor_from : is_initial_functor_from A
        (tpair _ (Rezk_completion A) (Rezk_eta A)).
  Proof.
    intro D.
    destruct D as [D F].
    set (T:= Rezk_eta_Universal_Property D (pr2 D)).
    apply T.
  Defined.

End rezk_universal_property.

(** * 4. The equivalence between the contravariant functor categories *)

Section opp_rezk_universal_property.

  Context (A : category).

  Section fix_a_category.

    Context (C : category).
    Context (Ccat : is_univalent C).

    Definition Rezk_op_adj_equiv :
      adj_equivalence_of_cats
        (pre_composition_functor A^op (Rezk_completion A)^op C
            (functor_opp (Rezk_eta A))).
    Proof.
      use (precomp_adjoint_equivalence (make_univalent_category _ _)).
      - apply Ccat.
      - apply opp_functor_essentially_surjective.
        apply Rezk_eta_essentially_surjective.
      - apply opp_functor_fully_faithful.
        apply Rezk_eta_fully_faithful.
    Defined.

    Theorem Rezk_eta_opp_Universal_Property :
      isweq (pre_composition_functor A^op (Rezk_completion A)^op C
              (functor_opp (Rezk_eta A))).
    Proof.
      apply adj_equiv_of_cats_is_weq_of_objects.
      - apply is_univalent_functor_category;
        assumption.
      - apply is_univalent_functor_category;
        assumption.
      - apply Rezk_op_adj_equiv.
    Defined.

    Definition Rezk_opp_weq : [(Rezk_completion A)^op, C] ≃ [A^op, C]
      := make_weq _ Rezk_eta_opp_Universal_Property.

  End fix_a_category.

End opp_rezk_universal_property.

(** * 5. The uniqueness of the Rezk completion *)

Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.WeakEquivalences.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.CategoryTheory.RezkCompletion.

Definition functor_from_eq
  {A : category}
  {D D' : univalent_category}
  (F : A ⟶ D)
  (F' : A ⟶ D')
  (H1 : D = D')
  (H2 : F ∙ (idtoiso_2_0 (C := bicat_of_univ_cats) D D' H1 : bicat_of_univ_cats⟦D, D'⟧) = F')
  : (D ,, F : functor_from A) = D' ,, F'.
Proof.
  induction H1.
  apply maponpaths.
  refine (_ @ H2).
  exact (!functor_identity_right _ _ _).
Defined.

Section InitialFunctorUnique.

  Context {A : category}.
  Context {D D' : functor_from A}.
  Context (HD : is_initial_functor_from _ D).
  Context (HD' : is_initial_functor_from _ D').

  Let G := pr11 (HD D') : D ⟶ D'.
  Let G' := pr11 (HD' D) : D' ⟶ D.

  Local Lemma G'_after_G : functor_identity D = G ∙ G'.
  Proof.
    refine (!initial_functor_endo_is_identity _ HD _ _).
    refine (!functor_assoc _ _ _ _ _ _ _ @ _).
    refine (maponpaths (λ x, x ∙ _) (pr21 (HD D')) @ _).
    exact (pr21 (HD' D)).
  Qed.

  Local Lemma G_after_G' : G' ∙ G = functor_identity D'.
  Proof.
    refine (initial_functor_endo_is_identity _ HD' _ _).
    refine (!functor_assoc _ _ _ _ _ _ _ @ _).
    refine (maponpaths (λ x, x ∙ _) (pr21 (HD' D)) @ _).
    apply (pr21 (HD D')).
  Qed.

  Let η := idtoiso (C := [_, _]) G'_after_G : z_iso (C := [_, _]) (functor_identity D) (G ∙ G').
  Let ɛ := idtoiso (C := [_, _]) G_after_G' : z_iso (C := [_, _]) (G' ∙ G) (functor_identity D').

  Definition initial_functor_unique
    : D = D'.
  Proof.
    use functor_from_eq.
    - apply (isotoid_2_0 univalent_cat_is_univalent_2_0).
      exists G.
      abstract (
        apply (invmap (adj_equiv_is_equiv_cat _));
        use (adjointification (make_equivalence_of_cats (make_adjunction_data G _ _ _) (make_forms_equivalence _ _ _)));
        [ exact G'
        | refine (z_iso_mor η)
        | refine (z_iso_mor ɛ)
        | intro;
          apply (is_functor_z_iso_pointwise_if_z_iso _ _ (homset_property _) _ _ η);
          apply z_iso_is_z_isomorphism
        | intro;
          apply (is_functor_z_iso_pointwise_if_z_iso _ _ (homset_property _) _ _ ɛ);
          apply z_iso_is_z_isomorphism ]
      ).
    - refine (_ @ pr21 (HD D')).
      apply maponpaths.
      exact (maponpaths (λ (f : adjoint_equivalence _ _), (f : bicat_of_univ_cats⟦_, _⟧))
        (idtoiso_2_0_isotoid_2_0 univalent_cat_is_univalent_2_0 _)).
  Defined.

End InitialFunctorUnique.

Definition rezk_completion_unique
  {A : category}
  (D D' : rezk_completion_type A)
  : D = D'.
Proof.
  refine (invmaponpathsweq (weqtotal2asstol _ (λ F, is_weak_equiv (pr2 F))) _ _ _).
  apply subtypePath.
  {
    intro.
    apply isaprop_is_weak_equiv.
  }
  induction (pr22 D) as [HDE HDF].
  induction (pr22 D') as [HDE' HDF'].
  now apply initial_functor_unique;
    apply weak_equivalence_initial_functor_from.
Defined.
