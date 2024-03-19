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
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.

Local Open Scope cat.

(** * 1. Properties of categories *)
Definition cat_property_data
  : UU
  := ∑ (P₀ : category → UU),
     ∏ (C₁ C₂ : category),
     P₀ C₁ → P₀ C₂ → C₁ ⟶ C₂ → UU.

Definition make_cat_property_data
           (P₀ : category → UU)
           (P₁ : ∏ (C₁ C₂ : category),
                 P₀ C₁ → P₀ C₂ → C₁ ⟶ C₂ → UU)
  : cat_property_data
  := P₀ ,, P₁.

Definition cat_property_ob
           (P : cat_property_data)
           (C : category)
  : UU
  := pr1 P C.

Coercion cat_property_ob : cat_property_data >-> Funclass.

Definition cat_property_functor
           (P : cat_property_data)
           {C₁ C₂ : category}
           (H₁ : P C₁)
           (H₂ : P C₂)
           (F : C₁ ⟶ C₂)
  : UU
  := pr2 P C₁ C₂ H₁ H₂ F.

Definition cat_property_laws
           (P : cat_property_data)
  : UU
  := (∏ (C : univalent_category),
      isaprop (P C))
     ×
     (∏ (C₁ C₂ : univalent_category)
        (H₁ : P C₁)
        (H₂ : P C₂)
        (F : C₁ ⟶ C₂),
      isaprop (cat_property_functor P H₁ H₂ F))
     ×
     (∏ (C : category)
        (H : P C),
      cat_property_functor P H H (functor_identity C))
     ×
     (∏ (C₁ C₂ C₃ : category)
        (H₁ : P C₁)
        (H₂ : P C₂)
        (H₃ : P C₃)
        (F : C₁ ⟶ C₂)
        (G : C₂ ⟶ C₃),
      cat_property_functor P H₁ H₂ F
      →
      cat_property_functor P H₂ H₃ G
      →
      cat_property_functor P H₁ H₃ (F ∙ G)).

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
              (C : univalent_category)
    : isaprop (P C).
  Proof.
    exact (pr1 (pr2 P) C).
  Defined.

  Proposition isaprop_cat_property_functor
              {C₁ C₂ : univalent_category}
              (H₁ : P C₁)
              (H₂ : P C₂)
              (F : C₁ ⟶ C₂)
    : isaprop (cat_property_functor P H₁ H₂ F).
  Proof.
    exact (pr12 (pr2 P) C₁ C₂ H₁ H₂ F).
  Defined.

  Proposition cat_property_id_functor
              {C : category}
              (H : P C)
    : cat_property_functor P H H (functor_identity C).
  Proof.
    exact (pr122 (pr2 P) C H).
  Defined.

  Proposition cat_property_id_functor'
              {C : univalent_category}
              (H H' : P C)
    : cat_property_functor P H H' (functor_identity C).
  Proof.
    assert (H = H') as p.
    {
      apply isaprop_cat_property_ob.
    }
    induction p.
    apply cat_property_id_functor.
  Qed.

  Proposition cat_property_comp_functor
              {C₁ C₂ C₃ : category}
              {H₁ : P C₁}
              {H₂ : P C₂}
              {H₃ : P C₃}
              {F : C₁ ⟶ C₂}
              {G : C₂ ⟶ C₃}
              (HF : cat_property_functor P H₁ H₂ F)
              (HG : cat_property_functor P H₂ H₃ G)
    : cat_property_functor P H₁ H₃ (F ∙ G).
  Proof.
    exact (pr222 (pr2 P) C₁ C₂ C₃ H₁ H₂ H₃ F G HF HG).
  Defined.

  Proposition cat_property_adj_equiv
              {C₁ C₂ : bicat_of_univ_cats}
              (F : adjoint_equivalence C₁ C₂)
              (H₁ : P (C₁ : univalent_category))
              (H₂ : P (C₂ : univalent_category))
    : cat_property_functor P H₁ H₂ (F : C₁ --> C₂).
  Proof.
    revert C₁ C₂ F H₁ H₂.
    use J_2_0.
    {
      exact univalent_cat_is_univalent_2_0.
    }
    intros C H₁ H₂.
    apply cat_property_id_functor'.
  Qed.

  Proposition cat_property_left_adjoint_equivalence
              {C₁ C₂ : univalent_category}
              (F : bicat_of_univ_cats ⟦ C₁, C₂ ⟧)
              (HF : left_adjoint_equivalence F)
              (H₁ : P C₁)
              (H₂ : P C₂)
    : cat_property_functor P H₁ H₂ F.
  Proof.
    exact (cat_property_adj_equiv (F ,, HF) H₁ H₂).
  Qed.

  Proposition cat_property_adj_equivalence_of_cats
              {C₁ C₂ : univalent_category}
              (F : C₁ ⟶ C₂)
              (HF : adj_equivalence_of_cats F)
              (H₁ : P C₁)
              (H₂ : P C₂)
    : cat_property_functor P H₁ H₂ F.
  Proof.
    refine (cat_property_left_adjoint_equivalence F _ H₁ H₂).
    use equiv_cat_to_adj_equiv.
    exact HF.
  Qed.

  Proposition cat_property_adj_equivalence_of_cats'
              {C₁ C₂ : category}
              (HC₁ : is_univalent C₁)
              (HC₂ : is_univalent C₂)
              (F : C₁ ⟶ C₂)
              (HF : adj_equivalence_of_cats F)
              (H₁ : P C₁)
              (H₂ : P C₂)
    : cat_property_functor P H₁ H₂ F.
  Proof.
    exact (@cat_property_adj_equivalence_of_cats
             (make_univalent_category C₁ HC₁)
             (make_univalent_category C₂ HC₂)
             F
             HF
             H₁
             H₂).
  Qed.

  Proposition cat_property_ob_adj_equiv_f_help
              {C₁ C₂ : bicat_of_univ_cats}
              (F : adjoint_equivalence C₁ C₂)
              (H : P (C₁ : univalent_category))
    : P (C₂ : univalent_category).
  Proof.
    revert C₁ C₂ F H.
    use J_2_0.
    {
      exact univalent_cat_is_univalent_2_0.
    }
    intros C H.
    exact H.
  Qed.

  Proposition cat_property_ob_left_adjoint_equivalence_f
              {C₁ C₂ : univalent_category}
              (F : bicat_of_univ_cats ⟦ C₁ , C₂ ⟧)
              (HF : left_adjoint_equivalence F)
              (H : P C₁)
    : P C₂.
  Proof.
    use (cat_property_ob_adj_equiv_f_help _ H).
    exact (F ,, HF).
  Qed.

  Proposition cat_property_ob_adj_equiv_f
              {C₁ C₂ : univalent_category}
              (F : C₁ ⟶ C₂)
              (HF : adj_equivalence_of_cats F)
              (H : P C₁)
    : P C₂.
  Proof.
    use (cat_property_ob_left_adjoint_equivalence_f _ _ H).
    - exact F.
    - use equiv_cat_to_adj_equiv.
      exact HF.
  Qed.

  Proposition cat_property_ob_adj_equiv_f'
              {C₁ C₂ : category}
              (HC₁ : is_univalent C₁)
              (HC₂ : is_univalent C₂)
              (F : C₁ ⟶ C₂)
              (HF : adj_equivalence_of_cats F)
              (H : P C₁)
    : P C₂.
  Proof.
    exact (@cat_property_ob_adj_equiv_f
             (make_univalent_category C₁ HC₁)
             (make_univalent_category C₂ HC₂)
             F
             HF
             H).
  Qed.

  Proposition cat_property_functor_nat_z_iso_f_help
              {C₁ C₂ : univalent_category}
              {H₁ : P C₁}
              {H₂ : P C₂}
              {F G : bicat_of_univ_cats ⟦ C₁ , C₂ ⟧}
              (τ : invertible_2cell F G)
              (HF : cat_property_functor P H₁ H₂ F)
    : cat_property_functor P H₁ H₂ G.
  Proof.
    revert C₁ C₂ F G τ H₁ H₂ HF.
    use (J_2_1 (B := bicat_of_univ_cats)).
    {
      exact univalent_cat_is_univalent_2_1.
    }
    intros C₁ C₂ F H₁ H₂ HF.
    exact HF.
  Qed.

  Proposition cat_property_functor_nat_z_iso_f
              {C₁ C₂ : univalent_category}
              {H₁ : P C₁}
              {H₂ : P C₂}
              {F G : C₁ ⟶ C₂}
              (τ : nat_z_iso F G)
              (HF : cat_property_functor P H₁ H₂ F)
    : cat_property_functor P H₁ H₂ G.
  Proof.
    use (cat_property_functor_nat_z_iso_f_help _ HF).
    use nat_z_iso_to_invertible_2cell.
    exact τ.
  Qed.

  Proposition cat_property_functor_nat_z_iso_adj_equiv_f_help
              {C₁ C₂ D₁ D₂ : bicat_of_univ_cats}
              {HC₁ : P (C₁ : univalent_category)}
              {HC₂ : P (C₂ : univalent_category)}
              {HD₁ : P (D₁ : univalent_category)}
              {HD₂ : P (D₂ : univalent_category)}
              (EC : adjoint_equivalence C₁ C₂)
              (ED : adjoint_equivalence D₁ D₂)
              {F : C₁ --> D₁}
              {G : C₂ --> D₂}
              (τ : nat_z_iso (F ∙ pr1 ED) (pr1 EC ∙ G))
              (HF : cat_property_functor P HC₁ HD₁ F)
    : cat_property_functor P HC₂ HD₂ G.
  Proof.
    revert C₁ C₂ EC D₁ D₂ ED HC₁ HC₂ HD₁ HD₂ F G τ HF.
    use J_2_0.
    {
      exact univalent_cat_is_univalent_2_0.
    }
    intros C.
    use J_2_0.
    {
      exact univalent_cat_is_univalent_2_0.
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
    use functor_eq ; [ apply homset_property | ].
    apply idpath.
  Qed.

  Proposition cat_property_functor_nat_z_iso_adj_equiv_f
              {C₁ C₂ D₁ D₂ : univalent_category}
              {HC₁ : P C₁}
              {HC₂ : P C₂}
              {HD₁ : P D₁}
              {HD₂ : P D₂}
              {EC : C₁ ⟶ C₂} {ED : D₁ ⟶ D₂}
              (HEC : adj_equivalence_of_cats EC)
              (HED : adj_equivalence_of_cats ED)
              {F : C₁ ⟶ D₁}
              {G : C₂ ⟶ D₂}
              (τ : nat_z_iso (F ∙ ED) (EC ∙ G))
              (HF : cat_property_functor P HC₁ HD₁ F)
    : cat_property_functor P HC₂ HD₂ G.
  Proof.
    refine (cat_property_functor_nat_z_iso_adj_equiv_f_help (EC ,, _) (ED ,, _) τ HF).
    - use equiv_cat_to_adj_equiv.
      exact HEC.
    - use equiv_cat_to_adj_equiv.
      exact HED.
  Qed.

  Proposition cat_property_functor_nat_z_iso_adj_equiv_f'
              {C₁ C₂ D₁ D₂ : category}
              {HC₁ : P C₁}
              {HC₂ : P C₂}
              {HD₁ : P D₁}
              {HD₂ : P D₂}
              (HC₁' : is_univalent C₁)
              (HC₂' : is_univalent C₂)
              (HD₁' : is_univalent D₁)
              (HD₂' : is_univalent D₂)
              {EC : C₁ ⟶ C₂} {ED : D₁ ⟶ D₂}
              (HEC : adj_equivalence_of_cats EC)
              (HED : adj_equivalence_of_cats ED)
              {F : C₁ ⟶ D₁}
              {G : C₂ ⟶ D₂}
              (τ : nat_z_iso (F ∙ ED) (EC ∙ G))
              (HF : cat_property_functor P HC₁ HD₁ F)
    : cat_property_functor P HC₂ HD₂ G.
  Proof.
    exact (cat_property_functor_nat_z_iso_adj_equiv_f
             (C₁ := make_univalent_category C₁ HC₁')
             (C₂ := make_univalent_category C₂ HC₂')
             (D₁ := make_univalent_category D₁ HD₁')
             (D₂ := make_univalent_category D₂ HD₂')
             HEC HED
             τ
             HF).
  Qed.
End CatPropertyLaws.

(** * 2. Fiberwise versions of properties *)
Definition fiberwise_cat_property
           (P : cat_property)
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := ∑ (H : ∏ (x : C), P (D[{x}])),
     ∏ (x y : C)
       (f : x --> y),
     cat_property_functor P (H y) (H x) (fiber_functor_from_cleaving D HD f).

Definition make_fiberwise_cat_property
           (P : cat_property)
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
           (H : ∏ (x : C), P (D[{x}]))
           (H' : ∏ (x y : C)
                   (f : x --> y),
                 cat_property_functor
                   P
                   (H y) (H x)
                   (fiber_functor_from_cleaving D HD f))
  : fiberwise_cat_property P HD
  := H ,, H'.

Definition fiberwise_cat_property_ob
           {P : cat_property}
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (H : fiberwise_cat_property P HD)
           (x : C)
  : P (D[{x}])
  := pr1 H x.

Coercion fiberwise_cat_property_ob : fiberwise_cat_property >-> Funclass.

Definition fiberwise_cat_property_mor
           {P : cat_property}
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (H : fiberwise_cat_property P HD)
           {x y : C}
           (f : x --> y)
  : cat_property_functor P (H y) (H x) (fiber_functor_from_cleaving D HD f).
Proof.
  exact (pr2 H x y f).
Defined.

Proposition isaprop_fiberwise_cat_property
            (P : cat_property)
            {C : univalent_category}
            {D : disp_univalent_category C}
            (HD : cleaving D)
  : isaprop (fiberwise_cat_property P HD).
Proof.
  use isaproptotal2.
  - intro H.
    do 3 (use impred ; intro).
    apply (@isaprop_cat_property_functor
              P
              (univalent_fiber_category _ _)
              (univalent_fiber_category _ _)).
  - intros.
    use funextsec ; intro.
    apply (isaprop_cat_property_ob P (univalent_fiber_category _ _)).
Qed.

Proposition cat_property_fiber_functor_id
            (P : cat_property)
            {C : univalent_category}
            {D : disp_univalent_category C}
            (x : C)
            (p : (P D[{x}]))
  : cat_property_functor P p p (fiber_functor (disp_functor_identity D) x).
Proof.
  use (cat_property_functor_nat_z_iso_f
         (C₁ := univalent_fiber_category _ _)
         (C₂ := univalent_fiber_category _ _)
         P
         _
         (cat_property_id_functor P _)).
  apply fiber_functor_identity.
Qed.

Proposition cat_property_fiber_functor_comp
            (P : cat_property)
            {C₁ C₂ C₃ : univalent_category}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {D₁ : disp_univalent_category C₁}
            {D₂ : disp_univalent_category C₂}
            {D₃ : disp_univalent_category C₃}
            {FF : disp_functor F D₁ D₂}
            {GG : disp_functor G D₂ D₃}
            {x : C₁}
            {p₁ : P (D₁[{x}])}
            {p₂ : P (D₂[{F x}])}
            {p₃ : P (D₃[{G(F x)}])}
            (HF : cat_property_functor P p₁ p₂ (fiber_functor FF x))
            (HG : cat_property_functor P p₂ p₃ (fiber_functor GG (F x)))
  : cat_property_functor P p₁ p₃ (fiber_functor (disp_functor_composite FF GG) x).
Proof.
  use (cat_property_functor_nat_z_iso_f
         (C₁ := univalent_fiber_category _ _)
         (C₂ := univalent_fiber_category _ _)
         P
         _
         (cat_property_comp_functor P HF HG)).
  apply fiber_functor_comp_nat_z_iso.
Qed.

Definition fiberwise_cat_property_functor
           {P : cat_property}
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {HD₁ : cleaving D₁}
           {D₂ : disp_cat C₂}
           {HD₂ : cleaving D₂}
           (FF : disp_functor F D₁ D₂)
           (H₁ : fiberwise_cat_property P HD₁)
           (H₂ : fiberwise_cat_property P HD₂)
  : UU
  := ∏ (x : C₁),
     cat_property_functor P (H₁ x) (H₂ (F x)) (fiber_functor FF x).

(** * 3. Local properties *)
Definition is_local_property
           (P : cat_property)
  : UU
  := ∑ (H : ∏ (C : univ_cat_with_finlim) (x : C),
            P C → P (C/x)),
     (∏ (C : univ_cat_with_finlim)
        (p : P C)
        (x y : C)
        (f : x --> y),
      cat_property_functor
        P
        (H C y p) (H C x p)
        (cod_pb (pullbacks_univ_cat_with_finlim C) f))
     ×
     (∏ (C₁ C₂ : univ_cat_with_finlim)
        (p₁ : P C₁)
        (p₂ : P C₂)
        (F : C₁ ⟶ C₂)
        (HF : cat_property_functor P p₁ p₂ F)
        (x : C₁),
      cat_property_functor
        P
        (H C₁ x p₁) (H C₂ (F x) p₂)
        (fiber_functor (disp_codomain_functor F) x)).

Definition make_is_local_property
           {P : cat_property}
           (H : ∏ (C : univ_cat_with_finlim) (x : C),
                P C → P (C/x))
           (Hpb : ∏ (C : univ_cat_with_finlim)
                    (p : P C)
                    (x y : C)
                    (f : x --> y),
                  cat_property_functor
                    P
                    (H C y p) (H C x p)
                    (cod_pb (pullbacks_univ_cat_with_finlim C) f))
           (Hfib : ∏ (C₁ C₂ : univ_cat_with_finlim)
                     (p₁ : P C₁)
                     (p₂ : P C₂)
                     (F : C₁ ⟶ C₂)
                     (HF : cat_property_functor P p₁ p₂ F)
                     (x : C₁),
                   cat_property_functor
                     P
                     (H C₁ x p₁) (H C₂ (F x) p₂)
                     (fiber_functor (disp_codomain_functor F) x))
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
    : P (C/x).
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
        (local_property_slice C y p)
        (local_property_slice C x p)
        (cod_pb (pullbacks_univ_cat_with_finlim C) f).
  Proof.
    exact (pr122 P C p x y f).
  Defined.

  Definition local_property_fiber_functor
             {C₁ C₂ : univ_cat_with_finlim}
             (p₁ : P C₁)
             (p₂ : P C₂)
             (F : C₁ ⟶ C₂)
             (HF : cat_property_functor P p₁ p₂ F)
             (x : C₁)
    : cat_property_functor
        P
        (local_property_slice C₁ x p₁)
        (local_property_slice C₂ (F x) p₂)
        (fiber_functor (disp_codomain_functor F) x).
  Proof.
    exact (pr222 P C₁ C₂ p₁ p₂ F HF x).
  Defined.
End LocalPropertyLaws.
