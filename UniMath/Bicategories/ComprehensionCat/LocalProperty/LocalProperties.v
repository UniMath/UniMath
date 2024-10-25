(*******************************************************************************************

 Local Properties of Categories

 There are numerous type formers that one would like to consider in the categorical semantics
 of dependent type theory. If we have a comprehension category with a fibration `D` over `C`,
 then such type formers are interpreted by finding suitable structure in the fiber categories
 `D[{x}]` of `x`. Such structure tends to correspond with categorical properties that have
 been established over the time in category theory. For example, empty types correspond to
 fiberwise initial objects that are stable under pullback and sum types correspond to
 fiberwise coproducts that are stable under pullback.

 Now we would like to extend the biequivalence between categories with finite limits and
 DFL comprehension categories to include additional type formers. More concretely, we are
 looking to obtain a biequivalence between:
 - Categories with finite limits that satisfy some property `P`
 - DFL comprehension categories for which each fiber satisfies the property `P` and such that
   the substitution functors preserve `P`.
 Concrete instances of `P` would be:
 - Initial objects that are stable under pullback (i.e., empty types)
 - Binary coproducts that are stable under pullback (i.e., sum types)
 - Subobject classifiers (i.e., a universe of propositions)
 - Exactness (i.e., quotient types)
 - Extensiveness (i.e., sum types with a disjointness axiom)

 For that purpose, we look at local properties of categories following Maietti (Proposition
 2.13 in "Modular correspondence between dependent type theories and categories including
 pretopoi and topoi"). A local property ([local_property]) is given by:
 - A type-valued predicate `P₀` on categories that is a proposition for univalent categories
 - A predicate `P₁` on functors
 - The predicate `P₁` is satisfied by the identity functor
 - The predicate `P₁` is preserved under composition
 - If `C` satisfies `P₀`, then so does `C/x` for every `x`
 - The substitution functors `C/y ⟶ C/x` satisfy `P₁`
 - If we have a functor `F : C₁ ⟶ C₂` satisfying `P₁`, then the fiber functors
   `C₁/x ⟶ C₂/(F x)` satisfy `P₁`
 Note that in the formalization, we give `P₀` as a type family on categories. This is purely
 for convenience, because we do not have to carry proofs of categories being univalent around.
 In addition, we think of a local property as a property on univalent categories rather than
 as structure on categories. The main examples (initial objects, coproducts, extensiveness,
 and exactness) give rise to a predicate on univalent categories, but not to a predicate on
 categories that are not necessarily univalent. These examples are actually instance of
 'property-like structure' since they are unique up to isomorphism. This means that in
 univalent categories they actually are unique, and they thus form a proposition. It is also
 good to note that the notion of `cat_property` is quite similar to a notion of structure as
 defined in Definition 9.8.1 of the HoTT book. The main difference is that we require
 uniqueness of structures for univalent categories, while in Definition 9.8.1, there is no
 such requirement. In addition, our local properties are automatically standard if we restrict
 our attention to univalent categories: this follows directly from the fact they form a
 proposition in that case.

 Note that if we look at univalent categories, `P₀` and `P₁` are automatically closed under
 adjoint equivalence and natural isomorphism respectively.

 Concretely, a local property is one that is closed under slicing. The reason why local
 properties are useful in the study of dependent type theories, is because they generalize
 a common pattern among type formers. To provide categorical semantics for a type former,
 we must show that each fiber has some structure and that this structure is preserved
 under substitution. Local properties describe this precisely for the codomain fibration.

 Note that the final requirement is not required in the work by Maietti. We add this
 requirement, because then our operations are suitably functorial, which guarantees that
 we obtain a biequivalence.

 References
 - "Modular correspondence between dependent type theories and categories including pretopoi
   and topoi" by Maietti
 - The HoTT book

 Contents
 1. Properties of categories
 2. Fiberwise versions of properties
 3. Local properties

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.PreservationProperties.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.

Local Open Scope cat.

(** * 1. Properties of categories *)
Definition cat_property_data
  : UU
  := ∑ (P₀ : univ_cat_with_finlim → UU),
     ∏ (C₁ C₂ : univ_cat_with_finlim),
     P₀ C₁ → P₀ C₂ → C₁ --> C₂ → UU.

Definition make_cat_property_data
           (P₀ : univ_cat_with_finlim → UU)
           (P₁ : ∏ (C₁ C₂ : univ_cat_with_finlim),
                 P₀ C₁ → P₀ C₂ → C₁ --> C₂ → UU)
  : cat_property_data
  := P₀ ,, P₁.

Definition cat_property_ob
           (P : cat_property_data)
           (C : univ_cat_with_finlim)
  : UU
  := pr1 P C.

Coercion cat_property_ob : cat_property_data >-> Funclass.

Definition cat_property_functor
           (P : cat_property_data)
           {C₁ C₂ : univ_cat_with_finlim}
           (H₁ : P C₁)
           (H₂ : P C₂)
           (F : C₁ --> C₂)
  : UU
  := pr2 P C₁ C₂ H₁ H₂ F.

Definition cat_property_laws
           (P : cat_property_data)
  : UU
  := (∏ (C : univ_cat_with_finlim),
      isaprop (P C))
     ×
     (∏ (C₁ C₂ : univ_cat_with_finlim)
        (H₁ : P C₁)
        (H₂ : P C₂)
        (F : C₁ --> C₂),
      isaprop (cat_property_functor P H₁ H₂ F))
     ×
     (∏ (C : univ_cat_with_finlim)
        (H : P C),
      cat_property_functor P H H (identity C))
     ×
     (∏ (C₁ C₂ C₃ : univ_cat_with_finlim)
        (H₁ : P C₁)
        (H₂ : P C₂)
        (H₃ : P C₃)
        (F : C₁ --> C₂)
        (G : C₂ --> C₃),
      cat_property_functor P H₁ H₂ F
      →
      cat_property_functor P H₂ H₃ G
      →
      cat_property_functor P H₁ H₃ (F · G)).

Definition cat_property
  : UU
  := ∑ (P : cat_property_data), cat_property_laws P.

Definition make_cat_property
           (P : cat_property_data)
           (H : cat_property_laws P)
  : cat_property
  := P ,, H.

Coercion cat_property_to_data
         (P : cat_property)
  : cat_property_data.
Proof.
  exact (pr1 P).
Defined.

Section CatPropertyLaws.
  Context (P : cat_property).

  Proposition isaprop_cat_property_ob
              (C : univ_cat_with_finlim)
    : isaprop (P C).
  Proof.
    exact (pr1 (pr2 P) C).
  Defined.

  Proposition isaprop_cat_property_functor
              {C₁ C₂ : univ_cat_with_finlim}
              (H₁ : P C₁)
              (H₂ : P C₂)
              (F : C₁ --> C₂)
    : isaprop (cat_property_functor P H₁ H₂ F).
  Proof.
    exact (pr12 (pr2 P) C₁ C₂ H₁ H₂ F).
  Defined.

  Proposition cat_property_id_functor
              {C : univ_cat_with_finlim}
              (H : P C)
    : cat_property_functor P H H (identity C).
  Proof.
    exact (pr122 (pr2 P) C H).
  Defined.

  Proposition cat_property_id_functor'
              {C : univ_cat_with_finlim}
              (H H' : P C)
    : cat_property_functor P H H' (identity C).
  Proof.
    assert (H = H') as p.
    {
      apply isaprop_cat_property_ob.
    }
    induction p.
    apply cat_property_id_functor.
  Qed.

  Proposition cat_property_comp_functor
              {C₁ C₂ C₃ : univ_cat_with_finlim}
              {H₁ : P C₁}
              {H₂ : P C₂}
              {H₃ : P C₃}
              {F : C₁ --> C₂}
              {G : C₂ --> C₃}
              (HF : cat_property_functor P H₁ H₂ F)
              (HG : cat_property_functor P H₂ H₃ G)
    : cat_property_functor P H₁ H₃ (F · G).
  Proof.
    exact (pr222 (pr2 P) C₁ C₂ C₃ H₁ H₂ H₃ F G HF HG).
  Defined.

  Proposition cat_property_adj_equiv
              {C₁ C₂ : univ_cat_with_finlim}
              (F : adjoint_equivalence C₁ C₂)
              (H₁ : P C₁)
              (H₂ : P C₂)
    : cat_property_functor P H₁ H₂ F.
  Proof.
    revert C₁ C₂ F H₁ H₂.
    use J_2_0.
    {
      exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
    }
    intros C H₁ H₂.
    apply cat_property_id_functor'.
  Qed.

  Proposition cat_property_adj_equivalence_of_cats
              {C₁ C₂ : univ_cat_with_finlim}
              (F : C₁ --> C₂)
              (HF : adj_equivalence_of_cats (pr1 F))
              (H₁ : P C₁)
              (H₂ : P C₂)
    : cat_property_functor P H₁ H₂ F.
  Proof.
    refine (cat_property_adj_equiv (F ,, _) H₁ H₂).
    use left_adjoint_equivalence_univ_cat_with_finlim.
    exact HF.
  Qed.

  Proposition cat_property_adj_equivalence_of_cats'
              {C₁ C₂ : univ_cat_with_finlim}
              (F : C₁ --> C₂)
              (HF : adj_equivalence_of_cats (pr1 F))
              (H₁ : P C₁)
              (H₂ : P C₂)
    : cat_property_functor P H₁ H₂ F.
  Proof.
    exact (@cat_property_adj_equivalence_of_cats
              _ _
              F
              HF
              H₁
              H₂).
  Qed.

  Proposition cat_property_ob_adj_equiv_f_help
              {C₁ C₂ : univ_cat_with_finlim}
              (F : adjoint_equivalence C₁ C₂)
              (H : P C₁)
    : P C₂.
  Proof.
    revert C₁ C₂ F H.
    use J_2_0.
    {
      exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
    }
    intros C H.
    exact H.
  Qed.

  Proposition cat_property_ob_left_adjoint_equivalence_f
              {C₁ C₂ : univ_cat_with_finlim}
              (F : C₁ --> C₂)
              (HF : left_adjoint_equivalence F)
              (H : P C₁)
    : P C₂.
  Proof.
    use (cat_property_ob_adj_equiv_f_help _ H).
    exact (F ,, HF).
  Qed.

  Proposition cat_property_ob_adj_equiv_f
              {C₁ C₂ : univ_cat_with_finlim}
              (F : C₁ --> C₂)
              (HF : adj_equivalence_of_cats (pr1 F))
              (H : P C₁)
    : P C₂.
  Proof.
    use (cat_property_ob_left_adjoint_equivalence_f _ _ H).
    - exact F.
    - use left_adjoint_equivalence_univ_cat_with_finlim.
      exact HF.
  Qed.

  Proposition cat_property_ob_adj_equiv_f'
              {C₁ C₂ : univ_cat_with_finlim}
              (F : (C₁ : category) ⟶ C₂)
              (HF : adj_equivalence_of_cats F)
              (H : P C₁)
    : P C₂.
  Proof.
    use (cat_property_ob_left_adjoint_equivalence_f _ _ H).
    - exact (make_functor_finlim_adjequiv F HF).
    - use left_adjoint_equivalence_univ_cat_with_finlim.
      exact HF.
  Qed.

  Proposition cat_property_functor_nat_z_iso_f_help
              {C₁ C₂ : univ_cat_with_finlim}
              {H₁ : P C₁}
              {H₂ : P C₂}
              {F G : C₁ --> C₂}
              (τ : invertible_2cell F G)
              (HF : cat_property_functor P H₁ H₂ F)
    : cat_property_functor P H₁ H₂ G.
  Proof.
    revert C₁ C₂ F G τ H₁ H₂ HF.
    use J_2_1.
    {
      exact is_univalent_2_1_bicat_of_univ_cat_with_finlim.
    }
    intros C₁ C₂ F H₁ H₂ HF.
    exact HF.
  Qed.

  Proposition cat_property_functor_nat_z_iso_f
              {C₁ C₂ : univ_cat_with_finlim}
              {H₁ : P C₁}
              {H₂ : P C₂}
              {F G : C₁ --> C₂}
              (τ : nat_z_iso (pr1 F) (pr1 G))
              (HF : cat_property_functor P H₁ H₂ F)
    : cat_property_functor P H₁ H₂ G.
  Proof.
    use (cat_property_functor_nat_z_iso_f_help _ HF).
    use invertible_2cell_cat_with_finlim.
    exact τ.
  Qed.

  Proposition cat_property_functor_nat_z_iso_adj_equiv_f_help
              {C₁ C₂ D₁ D₂ : univ_cat_with_finlim}
              {HC₁ : P C₁}
              {HC₂ : P C₂}
              {HD₁ : P D₁}
              {HD₂ : P D₂}
              (EC : adjoint_equivalence C₁ C₂)
              (ED : adjoint_equivalence D₁ D₂)
              (F : C₁ --> D₁)
              (G : C₂ --> D₂)
              (τ : nat_z_iso (pr1 F ∙ pr11 ED) (pr11 EC ∙ pr1 G))
              (HF : cat_property_functor P HC₁ HD₁ F)
    : cat_property_functor P HC₂ HD₂ G.
  Proof.
    revert C₁ C₂ EC D₁ D₂ ED HC₁ HC₂ HD₁ HD₂ F G τ HF.
    use J_2_0.
    {
      exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
    }
    intros C.
    use J_2_0.
    {
      exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
    }
    intros D HC₁ HC₂ HD₁ HD₂ F G τ HF.
    assert (HC₁ = HC₂) as p.
    {
      apply isaprop_cat_property_ob.
    }
    induction p.
    assert (HD₁ = HD₂) as p.
    {
      apply isaprop_cat_property_ob.
    }
    induction p.
    use (cat_property_functor_nat_z_iso_f τ).
    cbn.
    refine (transportf _ _ HF).
    apply idpath.
  Qed.

  Proposition cat_property_functor_nat_z_iso_adj_equiv_f
              {C₁ C₂ D₁ D₂ : univ_cat_with_finlim}
              {HC₁ : P C₁}
              {HC₂ : P C₂}
              {HD₁ : P D₁}
              {HD₂ : P D₂}
              {EC : C₁ --> C₂} {ED : D₁ --> D₂}
              (HEC : adj_equivalence_of_cats (pr1 EC))
              (HED : adj_equivalence_of_cats (pr1 ED))
              (F : C₁ --> D₁)
              (G : C₂ --> D₂)
              (τ : nat_z_iso (pr1 F ∙ pr1 ED) (pr1 EC ∙ pr1 G))
              (HF : cat_property_functor P HC₁ HD₁ F)
    : cat_property_functor P HC₂ HD₂ G.
  Proof.
    refine (cat_property_functor_nat_z_iso_adj_equiv_f_help (EC ,, _) (ED ,, _) _ _ τ HF).
    - use left_adjoint_equivalence_univ_cat_with_finlim.
      exact HEC.
    - use left_adjoint_equivalence_univ_cat_with_finlim.
      exact HED.
  Qed.

  Proposition cat_property_functor_nat_z_iso_adj_equiv_f'
              {C₁ C₂ D₁ D₂ : univ_cat_with_finlim}
              {HC₁ : P C₁}
              {HC₂ : P C₂}
              {HD₁ : P D₁}
              {HD₂ : P D₂}
              {EC : functor C₁ C₂} {ED : functor D₁ D₂}
              (HEC : adj_equivalence_of_cats EC)
              (HED : adj_equivalence_of_cats ED)
              (F : C₁ --> D₁)
              (G : C₂ --> D₂)
              (τ : nat_z_iso (pr1 F ∙ ED) (EC ∙ pr1 G))
              (HF : cat_property_functor P HC₁ HD₁ F)
    : cat_property_functor P HC₂ HD₂ G.
  Proof.
    exact (cat_property_functor_nat_z_iso_adj_equiv_f
             (EC := make_functor_finlim_adjequiv _ HEC)
             (ED := make_functor_finlim_adjequiv _ HED)
             HEC HED
             F G
             τ
             HF).
  Qed.
End CatPropertyLaws.

(** * 2. Fiberwise versions of properties *)
Definition fiberwise_cat_property
           (P : cat_property)
           (C : dfl_full_comp_cat)
  : UU
  := ∑ (H : ∏ (Γ : C), P (dfl_full_comp_cat_fiber Γ)),
     ∏ (Γ₁ Γ₂ : C)
       (s : Γ₁ --> Γ₂),
     cat_property_functor P (H Γ₂) (H Γ₁) (dfl_full_comp_cat_fiber_functor s).

Definition make_fiberwise_cat_property
           (P : cat_property)
           (C : dfl_full_comp_cat)
           (H : ∏ (Γ : C), P (dfl_full_comp_cat_fiber Γ))
           (H' : ∏ (Γ₁ Γ₂ : C)
                   (s : Γ₁ --> Γ₂),
                 cat_property_functor
                   P
                   (H Γ₂) (H Γ₁)
                   (dfl_full_comp_cat_fiber_functor s))
  : fiberwise_cat_property P C
  := H ,, H'.

Definition fiberwise_cat_property_ob
           {P : cat_property}
           {C : dfl_full_comp_cat}
           (H : fiberwise_cat_property P C)
           (Γ : C)
  : P (dfl_full_comp_cat_fiber Γ)
  := pr1 H Γ.

Coercion fiberwise_cat_property_ob : fiberwise_cat_property >-> Funclass.

Definition fiberwise_cat_property_mor
           {P : cat_property}
           {C : dfl_full_comp_cat}
           (H : fiberwise_cat_property P C)
           {Γ₁ Γ₂ : C}
           (s : Γ₁ --> Γ₂)
  : cat_property_functor
      P
      (H Γ₂) (H Γ₁)
      (dfl_full_comp_cat_fiber_functor s).
Proof.
  exact (pr2 H Γ₁ Γ₂ s).
Defined.

Proposition isaprop_fiberwise_cat_property
            {P : cat_property}
            (C : dfl_full_comp_cat)
  : isaprop (fiberwise_cat_property P C).
Proof.
  use isaproptotal2.
  - intro H.
    do 3 (use impred ; intro).
    apply isaprop_cat_property_functor.
  - intros.
    use funextsec ; intro.
    apply (isaprop_cat_property_ob P).
Qed.

Proposition cat_property_fiber_functor_id
            (P : cat_property)
            (C : dfl_full_comp_cat)
            (Γ : C)
            (p : P (dfl_full_comp_cat_fiber Γ))
  : cat_property_functor P p p (identity _).
Proof.
  use (cat_property_functor_nat_z_iso_f
         P
         _
         (cat_property_id_functor P _)).
  apply fiber_functor_identity.
Qed.

Proposition cat_property_fiber_functor_id'
            (P : cat_property)
            (C : dfl_full_comp_cat)
            (Γ : C)
            (p : P (dfl_full_comp_cat_fiber Γ))
  : cat_property_functor
      P
      p p
      (dfl_full_comp_cat_functor_fiber_functor (identity C) Γ).
Proof.
  refine (transportf
            (cat_property_functor P p p)
            _
            (cat_property_fiber_functor_id P C Γ p)).
  use subtypePath.
  {
    intro ; simpl.
    repeat (use isapropdirprod).
    - apply isapropunit.
    - apply isaprop_preserves_terminal.
    - apply isapropunit.
    - apply isaprop_preserves_pullback.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_is_functor.
    apply homset_property.
  }
  apply idpath.
Qed.

Proposition cat_property_fiber_functor_comp
            (P : cat_property)
            {C₁ C₂ C₃ : dfl_full_comp_cat}
            {F : dfl_full_comp_cat_functor C₁ C₂}
            {G : dfl_full_comp_cat_functor C₂ C₃}
            {Γ : C₁}
            {p₁ : P (dfl_full_comp_cat_fiber Γ)}
            {p₂ : P (dfl_full_comp_cat_fiber (F Γ))}
            {p₃ : P (dfl_full_comp_cat_fiber (G(F Γ)))}
            (HF : cat_property_functor P p₁ p₂ (dfl_full_comp_cat_functor_fiber_functor F Γ))
            (HG : cat_property_functor P p₂ p₃ (dfl_full_comp_cat_functor_fiber_functor G (F Γ)))
  : cat_property_functor P p₁ p₃ (dfl_full_comp_cat_functor_fiber_functor (F · G) Γ).
Proof.
  use (cat_property_functor_nat_z_iso_f
         P
         _
         (cat_property_comp_functor P HF HG)).
  apply fiber_functor_comp_nat_z_iso.
Qed.

Definition fiberwise_cat_property_functor
           {P : cat_property}
           {C₁ C₂ : dfl_full_comp_cat}
           (F : dfl_full_comp_cat_functor C₁ C₂)
           (H₁ : fiberwise_cat_property P C₁)
           (H₂ : fiberwise_cat_property P C₂)
  : UU
  := ∏ (Γ : C₁),
     cat_property_functor
       P
       (H₁ Γ) (H₂ (F Γ))
       (dfl_full_comp_cat_functor_fiber_functor F Γ).

(** * 3. Local properties *)
Definition slice_univ_cat_with_finlim
           {C : univ_cat_with_finlim}
           (x : C)
  : univ_cat_with_finlim.
Proof.
  use make_univ_cat_with_finlim.
  - refine (C/x ,, _).
    apply is_univalent_cod_slice.
  - apply codomain_fib_terminal.
  - use codomain_fiberwise_pullbacks.
    exact (pullbacks_univ_cat_with_finlim C).
Defined.

Definition slice_univ_cat_pb_finlim
           {C : univ_cat_with_finlim}
           {x y : C}
           (f : x --> y)
  : functor_finlim
      (slice_univ_cat_with_finlim y)
      (slice_univ_cat_with_finlim x).
Proof.
  use make_functor_finlim.
  - exact (cod_pb (pullbacks_univ_cat_with_finlim C) f).
  - apply codomain_fib_preserves_terminal.
  - use preserves_pullback_from_binproduct_equalizer.
    + use codomain_fib_binproducts.
      apply pullbacks_univ_cat_with_finlim.
    + use codomain_fib_equalizer.
      apply equalizers_univ_cat_with_finlim.
    + apply codomain_fib_preserves_binproduct.
    + apply codomain_fib_preserves_equalizer.
Defined.

Definition slice_univ_cat_fiber
           {C₁ C₂ : univ_cat_with_finlim}
           (F : functor_finlim C₁ C₂)
           (x : C₁)
  : functor_finlim
      (slice_univ_cat_with_finlim x)
      (slice_univ_cat_with_finlim (F x)).
Proof.
  use make_functor_finlim.
  - exact (fiber_functor (disp_codomain_functor F) x).
  - apply preserves_terminal_fiber_disp_codomain_functor.
  - use preserves_pullback_from_binproduct_equalizer.
    + use codomain_fib_binproducts.
      apply pullbacks_univ_cat_with_finlim.
    + use codomain_fib_equalizer.
      apply equalizers_univ_cat_with_finlim.
    + apply preserves_binproduct_fiber_disp_codomain_functor.
      exact (functor_finlim_preserves_pullback F).
    + use preserves_equalizer_fiber_disp_codomain_functor.
      apply functor_finlim_preserves_equalizer.
Defined.

Definition is_local_property
           (P : cat_property)
  : UU
  := ∑ (H : ∏ (C : univ_cat_with_finlim) (x : C),
            P C → P (slice_univ_cat_with_finlim x)),
     (∏ (C : univ_cat_with_finlim)
        (p : P C)
        (x y : C)
        (f : x --> y),
      cat_property_functor
        P
        (H C y p) (H C x p)
        (slice_univ_cat_pb_finlim f))
     ×
     (∏ (C₁ C₂ : univ_cat_with_finlim)
        (p₁ : P C₁)
        (p₂ : P C₂)
        (F : functor_finlim C₁ C₂)
        (HF : cat_property_functor P p₁ p₂ F)
        (x : C₁),
      cat_property_functor
        P
        (H C₁ x p₁) (H C₂ (F x) p₂)
        (slice_univ_cat_fiber F x)).

Definition make_is_local_property
           {P : cat_property}
           (H : ∏ (C : univ_cat_with_finlim) (x : C),
                P C → P (slice_univ_cat_with_finlim x))
           (Hpb : ∏ (C : univ_cat_with_finlim)
                    (p : P C)
                    (x y : C)
                    (f : x --> y),
                  cat_property_functor
                    P
                    (H C y p) (H C x p)
                    (slice_univ_cat_pb_finlim f))
           (Hfib : ∏ (C₁ C₂ : univ_cat_with_finlim)
                     (p₁ : P C₁)
                     (p₂ : P C₂)
                     (F : functor_finlim C₁ C₂)
                     (HF : cat_property_functor P p₁ p₂ F)
                     (x : C₁),
                   cat_property_functor
                     P
                     (H C₁ x p₁) (H C₂ (F x) p₂)
                     (slice_univ_cat_fiber F x))
  : is_local_property P
  := H ,, Hpb ,, Hfib.

Definition local_property
  : UU
  := ∑ (P : cat_property), is_local_property P.

Definition make_local_property
           (P : cat_property)
           (H : is_local_property P)
  : local_property
  := P ,, H.

Coercion local_property_to_cat_property
         (P : local_property)
  : cat_property.
Proof.
  exact (pr1 P).
Defined.

Section LocalPropertyLaws.
  Context (P : local_property).

  Definition local_property_slice
             (C : univ_cat_with_finlim)
             (x : C)
             (H : P C)
    : P (slice_univ_cat_with_finlim x).
  Proof.
    exact (pr12 P C x H).
  Defined.

  Definition local_property_pb
             {C : univ_cat_with_finlim}
             (p : P C)
             {x y : C}
             (f : x --> y)
    : cat_property_functor
        P
        (local_property_slice C y p) (local_property_slice C x p)
        (slice_univ_cat_pb_finlim f).
  Proof.
    exact (pr122 P C p x y f).
  Defined.

  Definition local_property_fiber_functor
             {C₁ C₂ : univ_cat_with_finlim}
             (p₁ : P C₁)
             (p₂ : P C₂)
             (F : functor_finlim C₁ C₂)
             (HF : cat_property_functor P p₁ p₂ F)
             (x : C₁)
    : cat_property_functor
        P
        (local_property_slice C₁ x p₁) (local_property_slice C₂ (F x) p₂)
        (slice_univ_cat_fiber F x).
  Proof.
    exact (pr222 P C₁ C₂ p₁ p₂ F HF x).
  Defined.
End LocalPropertyLaws.
