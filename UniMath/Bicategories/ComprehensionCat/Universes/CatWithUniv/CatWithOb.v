(***********************************************************************************************

 Universes in categories with finite limits

 In this file, we look at the categorical semantics of universes. To do so, we define a notion
 of universe in categories with finite limits.

 One way to give the categorical semantics of universes, is by giving a class of small maps and
 a universal small map (see, for instance, 'Algebraic Set Theory'). More specifically, we give a
 predicate on morphisms `A --> Γ`, which expresses whether a type is considered small. A universe
 for a class of small maps would be an type containing all small types. Categorically, this
 is expressed as a morphism `π : U_* --> U` which is universal with respect to the class of
 small maps. Universality means that every small map `A --> Γ` can be obtained as a pullback of
 the universal map `π`. Note that this pullback is not necessarily unique.

 We take a slightly different but equivalent approach. A universe in a category `C` with finite
 limits is given by
 - an object `U : C`
 - for each morphism `t : Γ --> U` an object `El t : C` a morphism `f_t : El t --> Γ`
 - for each `s : Γ --> Δ` and `t : Δ --> U`, we have a pullback square given by the morphisms
   `El (s · t) --> Γ --> Δ` and `El(s · t) --> El(t) --> Δ`
 - we require suitable coherences
 To understand this definition, we can view by interpreting it in the internal language of `C`.
 The object `U` gives rise to a type `U` in the empty context, and hence every context due to
 weakening. Since every morphism `t : Γ --> U` gives rise to  an object `El t : C` a morphism
 `f_t : El t --> Γ`, we have that every term `t` of type `U` in context `Γ` gives rise to a
 type `El t` in context `Γ`. Finally, the last two requirement expresses stability under
 substitution, i.e. (El t)[ s ] ≃ El(t [ s ])`.

 We want to construct the bicategory of categories with finite limits and a universe. To do so,
 we use displayed bicategories. We define this bicategory in two steps:
 - we define a displayed bicategory `disp_bicat_finlim_ob` over `bicat_of_univ_cat_with_finlim`.
   This displayed bicategory adds an object `U`, and the objects of its total bicategory consist
   of a univalent category `C` with finite limits together with an object of `C`.
 - over the total bicategory of this displayed bicategory, we define another displayed bicategory.
   This new displayed bicategory adds the remaining data for `U` to be a universe, and thus its
   total bicategory has univalent categories with finite limits and universes as objects.
 Both of these bicategories are univalent.

 The goal of this file is to construct the displayed bicategory of univalent categories with
 finite limits and an object. We also prove that it is univalent.

 References
 - 'Algebraic Set Theory' by Joyal and Moerdijk

 Contents
 1. Construction of the displayed bicategory
 2. Local univalence
 3. Invertible 2-cells and adjoint equivalences
 4. Global univalence
 5. Accessors

 ***********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

(** * 1. Construction of the displayed bicategory *)
Definition disp_cat_ob_mor_finlim_ob
  : disp_cat_ob_mor bicat_of_univ_cat_with_finlim.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C : univ_cat_with_finlim), C).
  - exact (λ (C₁ C₂ : univ_cat_with_finlim)
             (u₁ : C₁)
             (u₂ : C₂)
             (F : functor_finlim C₁ C₂),
           z_iso (F u₁) u₂).
Defined.

Definition disp_cat_id_comp_finlim_ob
  : disp_cat_id_comp _ disp_cat_ob_mor_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C : univ_cat_with_finlim)
             (u : C),
           identity_z_iso u).
  - exact (λ (C₁ C₂ C₃ : univ_cat_with_finlim)
             (F : functor_finlim C₁ C₂)
             (G : functor_finlim C₂ C₃)
             (u₁ : C₁)
             (u₂ : C₂)
             (u₃ : C₃)
             (f : z_iso (F u₁) u₂)
             (g : z_iso (G u₂) u₃),
           z_iso_comp
             (functor_on_z_iso G f)
             g).
Defined.

Definition disp_cat_data_finlim_ob
  : disp_cat_data bicat_of_univ_cat_with_finlim.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_finlim_ob.
  - exact disp_cat_id_comp_finlim_ob.
Defined.

Definition disp_prebicat_1_id_comp_cells_finlim_ob
  : disp_prebicat_1_id_comp_cells bicat_of_univ_cat_with_finlim.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_finlim_ob.
  - exact (λ (C₁ C₂ : univ_cat_with_finlim)
             (F G : functor_finlim C₁ C₂)
             (τ : nat_trans_finlim F G)
             (u₁ : C₁)
             (u₂ : C₂)
             (f : z_iso (F u₁) u₂)
             (g : z_iso (G u₁) u₂),
           τ u₁ · g = f).
Defined.

Proposition disp_prebicat_ops_finlim_ob
  : disp_prebicat_ops disp_prebicat_1_id_comp_cells_finlim_ob.
Proof.
  repeat split.
  - intros ; cbn.
    apply id_left.
  - intros ; cbn.
    rewrite functor_id.
    apply idpath.
  - intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros ; cbn.
    rewrite functor_id.
    rewrite !id_left.
    apply idpath.
  - intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros ; cbn.
    rewrite id_left.
    rewrite functor_comp.
    rewrite assoc.
    apply idpath.
  - intros ; cbn.
    rewrite id_left.
    rewrite functor_comp.
    rewrite assoc.
    apply idpath.
  - intros C₁ C₂ F₁ F₂ F₃ τ₁ τ₂ u₁ u₂ u₃ f g p q ; cbn in p, q ; cbn.
    rewrite <- p.
    rewrite !assoc'.
    apply maponpaths.
    exact q.
  - intros C₁ C₂ F₁ F₂ F₃ τ₁ τ₂ u₁ u₂ u₃ f g h p ; cbn in p ; cbn.
    rewrite <- p.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    apply nat_trans_ax.
  - intros C₁ C₂ F₁ F₂ F₃ τ₁ τ₂ u₁ u₂ u₃ f g h p ; cbn in p ; cbn.
    rewrite <- p.
    rewrite functor_comp.
    rewrite !assoc'.
    apply idpath.
Qed.

Definition disp_prebicat_data_finlim_ob
  : disp_prebicat_data bicat_of_univ_cat_with_finlim.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_finlim_ob.
  - exact disp_prebicat_ops_finlim_ob.
Defined.

Proposition isaprop_disp_2cell_finlim_ob
            {C₁ C₂ : bicat_of_univ_cat_with_finlim}
            {F G : C₁ --> C₂}
            (τ : F ==> G)
            {u₁ : disp_prebicat_data_finlim_ob C₁}
            {u₂ : disp_prebicat_data_finlim_ob C₂}
            (f : u₁ -->[ F ] u₂)
            (g : u₁ -->[ G ] u₂)
  : isaprop (f ==>[ τ ] g).
Proof.
  apply homset_property.
Qed.

Proposition disp_prebicat_laws_finlim_ob
  : disp_prebicat_laws disp_prebicat_data_finlim_ob.
Proof.
  repeat split ; intro ; intros ; apply isaprop_disp_2cell_finlim_ob.
Qed.

Definition disp_prebicat_finlim_ob
  : disp_prebicat bicat_of_univ_cat_with_finlim.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_finlim_ob.
  - exact disp_prebicat_laws_finlim_ob.
Defined.

Proposition has_disp_cellset_disp_bicat_finlim_ob
  : has_disp_cellset disp_prebicat_finlim_ob.
Proof.
  intro ; intros.
  apply isasetaprop.
  apply isaprop_disp_2cell_finlim_ob.
Qed.

Definition disp_bicat_finlim_ob
  : disp_bicat bicat_of_univ_cat_with_finlim.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_finlim_ob.
  - exact has_disp_cellset_disp_bicat_finlim_ob.
Defined.

(** * 2. Local univalence *)
Proposition disp_univalent_2_1_disp_bicat_finlim_ob
  : disp_univalent_2_1 disp_bicat_finlim_ob.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros C₁ C₂ F u₁ u₂ f f'.
  use isweqimplimpl.
  - cbn ; intro τ.
    use z_iso_eq.
    pose (p := pr1 τ) ; cbn in p.
    rewrite id_left in p.
    exact (!p).
  - apply isaset_z_iso.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_disp_invertible_2cell.
    + intros.
      apply isaprop_disp_2cell_finlim_ob.
Qed.

(** * 3. Invertible 2-cells and adjoint equivalences *)
Proposition disp_2cells_isaprop_disp_bicat_finlim_ob
  : disp_2cells_isaprop disp_bicat_finlim_ob.
Proof.
  intro ; intros.
  apply isaprop_disp_2cell_finlim_ob.
Qed.

Proposition is_disp_invertible_2cell_disp_bicat_finlim_ob
            {C₁ C₂ : bicat_of_univ_cat_with_finlim}
            {F G : C₁ --> C₂}
            {τ : invertible_2cell F G}
            {u₁ : disp_bicat_finlim_ob C₁}
            {u₂ : disp_bicat_finlim_ob C₂}
            {f : u₁ -->[ F ] u₂}
            {g : u₁ -->[ G ] u₂}
            (p : f ==>[ τ ] g)
  : is_disp_invertible_2cell τ p.
Proof.
  simple refine (_ ,, _ ,, _).
  - cbn in p ; cbn.
    rewrite <- p.
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    exact (maponpaths (λ (z : nat_trans_finlim _ _), z u₁) (vcomp_linv τ)).
  - apply isaprop_disp_2cell_finlim_ob.
  - apply isaprop_disp_2cell_finlim_ob.
Qed.

Proposition disp_locally_groupoid_disp_bicat_finlim_ob
  : disp_locally_groupoid disp_bicat_finlim_ob.
Proof.
  intro ; intros.
  apply is_disp_invertible_2cell_disp_bicat_finlim_ob.
Qed.

Section AdjEquivs.
  Context {C : univ_cat_with_finlim}
          (u u' : C).

  Definition disp_bicat_finlim_ob_to_adj_equiv
             (f : z_iso u u')
    : disp_left_adjoint_equivalence
        (D := disp_bicat_finlim_ob)
        (internal_adjoint_equivalence_identity C)
        f.
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
    - exact (z_iso_inv f).
    - abstract
        (cbn ;
         rewrite id_left ;
         rewrite z_iso_inv_after_z_iso ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite id_left ;
         rewrite z_iso_after_z_iso_inv ;
         apply idpath).
    - abstract
        (split ; apply isaprop_disp_2cell_finlim_ob).
    - abstract
        (split ; apply is_disp_invertible_2cell_disp_bicat_finlim_ob).
  Defined.

  Definition disp_bicat_finlim_ob_adj_equiv_weq
    : z_iso u u'
      ≃
      disp_adjoint_equivalence
        (D := disp_bicat_finlim_ob)
        (internal_adjoint_equivalence_identity C)
        u u'.
  Proof.
    use weq_iso.
    - exact (λ f, f ,, disp_bicat_finlim_ob_to_adj_equiv f).
    - exact (λ f, pr1 f).
    - abstract
        (intro f ;
         use z_iso_eq ;
         apply idpath).
    - abstract
        (intro f ;
         use subtypePath ;
         [ intro ;
           apply (isaprop_disp_left_adjoint_equivalence
                    _ _
                    is_univalent_2_1_bicat_of_univ_cat_with_finlim
                    disp_univalent_2_1_disp_bicat_finlim_ob)
         | ] ;
         apply idpath).
  Defined.
End AdjEquivs.

(** * 4. Global univalence *)
Proposition disp_univalent_2_0_disp_bicat_finlim_ob
  : disp_univalent_2_0 disp_bicat_finlim_ob.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  refine (λ (C : univ_cat_with_finlim) (u u' : C), _).
  use weqhomot.
  - exact (disp_bicat_finlim_ob_adj_equiv_weq u u'
           ∘ make_weq _ (univalent_category_is_univalent C u u'))%weq.
  - intro p ; cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      apply (isaprop_disp_left_adjoint_equivalence
               _ _
               is_univalent_2_1_bicat_of_univ_cat_with_finlim
               disp_univalent_2_1_disp_bicat_finlim_ob).
    }
    cbn.
    apply idpath.
Qed.

Proposition disp_univalent_2_disp_bicat_finlim_ob
  : disp_univalent_2 disp_bicat_finlim_ob.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_finlim_ob.
  - exact disp_univalent_2_1_disp_bicat_finlim_ob.
Qed.

(** * 5. Accessors *)
Definition bicat_of_univ_cat_with_finlim_ob
  : bicat
  := total_bicat disp_bicat_finlim_ob.

Proposition is_univalent_2_bicat_of_univ_cat_with_finlim_ob
  : is_univalent_2 bicat_of_univ_cat_with_finlim_ob.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_finlim_ob.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Proposition is_univalent_2_1_bicat_of_univ_cat_with_finlim_ob
  : is_univalent_2_1 bicat_of_univ_cat_with_finlim_ob.
Proof.
  exact (pr2 is_univalent_2_bicat_of_univ_cat_with_finlim_ob).
Qed.

Proposition is_univalent_2_0_bicat_of_univ_cat_with_finlim_ob
  : is_univalent_2_0 bicat_of_univ_cat_with_finlim_ob.
Proof.
  exact (pr1 is_univalent_2_bicat_of_univ_cat_with_finlim_ob).
Qed.

Definition univ_cat_with_finlim_ob
  : UU
  := bicat_of_univ_cat_with_finlim_ob.

Coercion univ_cat_with_finlim_ob_to_univ_cat_finlim
         (C : univ_cat_with_finlim_ob)
  : univ_cat_with_finlim
  := pr1 C.

Definition univ_cat_universe
           (C : univ_cat_with_finlim_ob)
  : C
  := pr2 C.

Definition functor_finlim_ob
           (C₁ C₂ : univ_cat_with_finlim_ob)
  : UU
  := C₁ --> C₂.

Coercion functor_finlim_ob_to_functor_finlim
         {C₁ C₂ : univ_cat_with_finlim_ob}
         (F : functor_finlim_ob C₁ C₂)
  : functor_finlim C₁ C₂
  := pr1 F.

Definition functor_on_universe
           {C₁ C₂ : univ_cat_with_finlim_ob}
           (F : functor_finlim_ob C₁ C₂)
  : z_iso
      (F (univ_cat_universe C₁))
      (univ_cat_universe C₂)
  := pr2 F.

Definition nat_trans_finlim_ob
           {C₁ C₂ : univ_cat_with_finlim_ob}
           (F G : functor_finlim_ob C₁ C₂)
  : UU
  := F ==> G.

Coercion nat_trans_finlim_ob_to_functor_nat_trans
         {C₁ C₂ : univ_cat_with_finlim_ob}
         {F G : functor_finlim_ob C₁ C₂}
         (τ : nat_trans_finlim_ob F G)
  : nat_trans_finlim F G
  := pr1 τ.

Proposition nat_trans_universe_eq
            {C₁ C₂ : univ_cat_with_finlim_ob}
            {F G : functor_finlim_ob C₁ C₂}
            (τ : nat_trans_finlim_ob F G)
  : τ (univ_cat_universe C₁)
    · functor_on_universe G
    =
    functor_on_universe F.
Proof.
  exact (pr2 τ).
Defined.

Definition invertible_2cell_to_nat_z_iso_cat_with_finlim_ob
           {C₁ C₂ : univ_cat_with_finlim_ob}
           {F G : functor_finlim_ob C₁ C₂}
           (τ : invertible_2cell F G)
  : nat_z_iso F G.
Proof.
  use make_nat_z_iso.
  - exact (pr111 τ).
  - intro x.
    use make_is_z_isomorphism.
    + exact (pr111 (τ^-1) x).
    + abstract
        (split ;
         [ exact (maponpaths (λ z, pr111 z x) (vcomp_rinv τ))
         | exact (maponpaths (λ z, pr111 z x) (vcomp_linv τ)) ]).
Defined.

Proposition invertible_2cell_cat_with_finlim_ob
            {C₁ C₂ : univ_cat_with_finlim_ob}
            {F G : functor_finlim_ob C₁ C₂}
            (τ : invertible_2cell F G)
            (x : C₁)
  : (τ^-1 : nat_trans_finlim_ob G F) x
    =
    inv_from_z_iso
      (nat_z_iso_pointwise_z_iso
         (invertible_2cell_to_nat_z_iso_cat_with_finlim_ob τ)
         x).
Proof.
  refine (_ @ id_left _).
  use z_iso_inv_on_left.
  refine (!_).
  exact (maponpaths (λ z, pr111 z x) (vcomp_linv τ)).
Qed.
