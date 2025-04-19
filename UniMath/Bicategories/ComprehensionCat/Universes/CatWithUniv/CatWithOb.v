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



(*
(** * 2. Universes in categories *)
Definition cat_el_map_data
           (C : univ_cat_with_finlim_ob)
  : UU
  := ∏ (Γ : C),
     Γ --> univ_cat_with_finlim_universe C
     →
     ∑ (e : C), e --> Γ.

Definition cat_el_map_el
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map_data C)
           {Γ : C}
           (t : Γ --> univ_cat_with_finlim_universe C)
  : C
  := pr1 (el Γ t).

Definition cat_el_map_el_eq
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map_data C)
           {Γ : C}
           {t t' : Γ --> univ_cat_with_finlim_universe C}
           (p : t = t')
  : z_iso (cat_el_map_el el t) (cat_el_map_el el t').
Proof.
  induction p.
  apply identity_z_iso.
Defined.

Proposition cat_el_map_el_eq_comp
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map_data C)
            {Γ : C}
            {t t' t'' : Γ --> univ_cat_with_finlim_universe C}
            (p : t = t')
            (q : t' = t'')
  : cat_el_map_el_eq el p · cat_el_map_el_eq el q
    =
    cat_el_map_el_eq el (p @ q).
Proof.
  induction p, q ; cbn.
  apply id_left.
Qed.

Definition cat_el_map_mor
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map_data C)
           {Γ : C}
           (t : Γ --> univ_cat_with_finlim_universe C)
  : cat_el_map_el el t --> Γ
  := pr2 (el Γ t).

Proposition cat_el_map_mor_eq
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map_data C)
            {Γ : C}
            {t t' : Γ --> univ_cat_with_finlim_universe C}
            (p : t = t')
  : cat_el_map_el_eq el p · cat_el_map_mor el t'
    =
    cat_el_map_mor el t.
Proof.
  induction p ; cbn.
  apply id_left.
Qed.

Definition cat_el_map_stable
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map_data C)
  : UU
  := ∏ (Γ Δ : C)
       (s : Γ --> Δ)
       (t : Δ --> univ_cat_with_finlim_universe C),
     ∑ (f : cat_el_map_el el (s · t) --> cat_el_map_el el t)
       (p : f · cat_el_map_mor el t
            =
            cat_el_map_mor el (s · t) · s),
     isPullback p.

Definition cat_el_map
           (C : univ_cat_with_finlim_ob)
  : UU
  := ∑ (el : cat_el_map_data C),
     cat_el_map_stable el.

Definition make_cat_el_map
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map_data C)
           (H_el : cat_el_map_stable el)
  : cat_el_map C
  := el ,, H_el.

Coercion cat_el_map_to_data
         {C : univ_cat_with_finlim_ob}
         (el : cat_el_map C)
  : cat_el_map_data C
  := pr1 el.

Definition cat_el_map_pb_mor
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (t : Δ --> univ_cat_with_finlim_universe C)
  : cat_el_map_el el (s · t) --> cat_el_map_el el t
  := pr1 (pr2 el Γ Δ s t).

Proposition cat_el_map_pb_mor_eq
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t t' : Δ --> univ_cat_with_finlim_universe C}
            (p : t' = t)
            (q : s · t' = s · t)
  : cat_el_map_el_eq el q · cat_el_map_pb_mor el s t
    =
    cat_el_map_pb_mor el s t' · cat_el_map_el_eq el p.
Proof.
  induction p.
  assert (q = idpath _) as ->.
  {
    apply homset_property.
  }
  cbn.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition cat_el_map_pb
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (t : Δ --> univ_cat_with_finlim_universe C)
  : Pullback (cat_el_map_mor el t) s.
Proof.
  use make_Pullback.
  - exact (cat_el_map_el el (s · t)).
  - exact (cat_el_map_pb_mor el s t).
  - exact (cat_el_map_mor el (s · t)).
  - exact (pr12 (pr2 el Γ Δ s t)).
  - exact (pr22 (pr2 el Γ Δ s t)).
Defined.

Definition cat_el_map_coherence
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
  : UU
  := (∏ (Γ : C)
        (t : Γ --> univ_cat_with_finlim_universe C),
      cat_el_map_pb_mor el (identity _) t
      =
      cat_el_map_el_eq el (id_left t))
     ×
     (∏ (Γ₁ Γ₂ Γ₃ : C)
        (s₁ : Γ₁ --> Γ₂)
        (s₂ : Γ₂ --> Γ₃)
        (t : Γ₃ --> univ_cat_with_finlim_universe C),
      cat_el_map_pb_mor el (s₁ · s₂) t
      =
      cat_el_map_el_eq el (assoc' s₁ s₂ t)
      · cat_el_map_pb_mor el s₁ (s₂ · t)
      · cat_el_map_pb_mor el s₂ t).


(*
Proposition cat_el_map_pb_mor_eq_comp
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map C)
            {Γ₁ Γ₂ : C}
            {s : Γ₁ --> Γ₂}
            {t : Γ₂ --> univ_cat_with_finlim_universe C}
  : cat_el_map_el_eq el (assoc' s t (identity _))
    · cat_el_map_pb_mor el s (t · identity _)
    · cat_el_map_pb_mor el t (identity _)
    =
    cat_el_map_pb_mor el (s · t) (identity _).
Proof.
  Check cat_el_map_el_eq el (assoc' s t (identity _)).
  Check (cat_el_map_mor el (s · t · id₁ (univ_cat_with_finlim_universe C))).

  assert (cat_el_map_el_eq el (assoc' s t (id₁ (univ_cat_with_finlim_universe C)))
  · cat_el_map_pb_mor el s (t · id₁ (univ_cat_with_finlim_universe C))
  · cat_el_map_mor el (t · id₁ (univ_cat_with_finlim_universe C)) =
            cat_el_map_mor el (s · t · id₁ (univ_cat_with_finlim_universe C)) · s)
    as p.
  {
    admit.
  }
  assert (∏ (X : UU), X) as TODO by admit.
  assert (cat_el_map_el el (s · t · id₁ (univ_cat_with_finlim_universe C))
          -->
          cat_el_map_el el (t · id₁ (univ_cat_with_finlim_universe C))).
  {
    Check PullbackArrow (cat_el_map_pb el t (identity _)).
    refine (cat_el_map_pb_mor el (s · t) (id₁ (univ_cat_with_finlim_universe C)) · _).
    Check cat_el_map_pb_mor el t (identity _).
    Check cat_el_map_pb_mor.

  assert (pr1 (cat_el_map_el_eq el (assoc' s t (identity _)))
          =
          PullbackArrow (cat_el_map_pb el s (t · identity _)) _ _ (cat_el_map_mor _ _) (TODO _)).
  {
    use (PullbackArrowUnique' _ _ _ (cat_el_map_pb el s _)).
    - cbn.
      apply idpath.
    - cbn.
      apply cat_el_map_mor_eq.
  }
  etrans.
  {
    do 2 apply maponpaths_2.
    exact X.
  }
  etrans.
  {
    apply maponpaths_2.
    apply (PullbackArrow_PullbackPr1 (cat_el_map_pb el s _)).
  }

  refine (assoc _ _ _ @ _).
  pose (PullbackArrow_PullbackPr1 ((cat_el_map_pb el s (t · id₁ (univ_cat_with_finlim_universe C))))).
  cbn in p0.
    rewrite X.
Admitted.
 *)

Proposition koe
            {C : univ_cat_with_finlim_ob}
            {Γ₁ Γ₂ : C}
            {el₁ el₂ : cat_el_map_data C}
            (p : el₁ = el₂)
            (t : Γ₂ --> univ_cat_with_finlim_universe C)
            (s : Γ₁ --> Γ₂)
            (f : cat_el_map_el el₁ (s · t) --> cat_el_map_el el₁ t)
  : transportf
      (λ (el : cat_el_map_data C), cat_el_map_el el (s · t) --> cat_el_map_el el t)
      p
      f
    =
    idtoiso (!base_paths _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ p _) (s · t))) · f · idtoiso (base_paths _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ p _) t)).
Proof.
  induction p ; cbn.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Proposition cat_el_map_eq
            {C : univ_cat_with_finlim_ob}
            {el₁ el₂ : cat_el_map C}
            (p : ∏ (Γ : C)
                   (t : Γ --> univ_cat_with_finlim_universe C),
                 z_iso (cat_el_map_el el₁ t) (cat_el_map_el el₂ t))
            (q : ∏ (Γ : C)
                   (t : Γ --> univ_cat_with_finlim_universe C),
                 p Γ t · cat_el_map_mor el₂ t
                 =
                 cat_el_map_mor el₁ t)
             (r : ∏ (Γ Δ : C)
                    (s : Γ --> Δ)
                    (t : Δ --> univ_cat_with_finlim_universe C),
                  cat_el_map_pb_mor el₁ s t · p _ _
                  =
                  p _ _ · cat_el_map_pb_mor el₂ s t)
  : el₁ = el₂.
Proof.
  induction el₁ as [ el₁ H₁ ].
  induction el₂ as [ el₂ H₂ ].
  use total2_paths_f.
  {
    use funextsec ; intro Γ.
    use funextsec ; intro t.
    use total2_paths_f.
    {
      use isotoid.
      {
        apply univalent_category_is_univalent.
      }
      apply p.
    }
    rewrite transportf_isotoid.
    use z_iso_inv_on_right.
    refine (!_).
    apply q.
  }
  cbn.
  unfold cat_el_map_stable.
  use funextsec ; intro Γ.
  rewrite transportf_sec_constant.
  use funextsec ; intro Δ.
  rewrite transportf_sec_constant.
  use funextsec ; intro s.
  rewrite transportf_sec_constant.
  use funextsec ; intro t.
  rewrite transportf_sec_constant.
  use subtypePath.
  {
    intro.
    use isaproptotal2.
    {
      intro.
      apply isaprop_isPullback.
    }
    intros.
    apply homset_property.
  }
  rewrite pr1_transportf.
  rewrite koe.
  rewrite !toforallpaths_funextsec.
  rewrite !base_total2_paths.
  rewrite idtoiso_inv.
  cbn.
  rewrite !idtoiso_isotoid.
  rewrite !assoc'.
  use z_iso_inv_on_right.
  apply r.
Qed.

(** * 3. Universes as morphisms *)
Section UniverseAsMorphism.
  Context (C : univ_cat_with_finlim_ob).

  Definition cat_el_map_to_mor
             (el : cat_el_map C)
    : ∑ (e : C), e --> univ_cat_with_finlim_universe C.
  Proof.
    simple refine (_ ,, _).
    - exact (cat_el_map_el el (identity _)).
    - exact (cat_el_map_mor el (identity _)).
  Defined.

  Section MorphismsToUniverse.
    Context {e : C}
            (p : e --> univ_cat_with_finlim_universe C).

    Definition cat_el_map_data_from_mor
      : cat_el_map_data C.
    Proof.
      intros Γ t.
      pose (P := pullbacks_univ_cat_with_finlim C _ _ _ p t).
      exact (PullbackObject P ,, PullbackPr2 P).
    Defined.

    Definition morphism_to_pb_mor_univ
               {Γ Δ : C}
               (s : Γ --> Δ)
               (t : Δ --> univ_cat_with_finlim_universe C)
      : pullbacks_univ_cat_with_finlim C (univ_cat_with_finlim_universe C) e Γ p (s · t)
        -->
        pullbacks_univ_cat_with_finlim C (univ_cat_with_finlim_universe C) e Δ p t.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _).
      - exact (PullbackPr2 _ · s).
      - abstract
          (rewrite !assoc' ;
           rewrite <- PullbackSqrCommutes ;
           apply idpath).
    Defined.

    Proposition morphism_to_pb_mor_univ_comm
                {Γ Δ : C}
                (s : Γ --> Δ)
                (t : Δ --> univ_cat_with_finlim_universe C)
      : morphism_to_pb_mor_univ s t
        · PullbackPr2
            (pullbacks_univ_cat_with_finlim
               C
               (univ_cat_with_finlim_universe C)
               e Δ p t)
        =
        PullbackPr2
          (pullbacks_univ_cat_with_finlim
             C
             (univ_cat_with_finlim_universe C)
             e Γ p (s · t))
        · s.
    Proof.
      apply PullbackArrow_PullbackPr2.
    Qed.

    Section UMP.
      Context {Γ Δ : C}
              (s : Γ --> Δ)
              (t : Δ --> univ_cat_with_finlim_universe C)
              {A : C}
              (h : A
                   -->
                   pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_with_finlim_universe C)
                     e Δ p t)
              (k : A --> Γ)
              (q : h
                   · PullbackPr2
                       (pullbacks_univ_cat_with_finlim
                          C
                          (univ_cat_with_finlim_universe C) e Δ p t)
                   =
                   k · s).

      Definition is_pb_morphism_to_pb_mor_univ_mor
        : A
          -->
          pullbacks_univ_cat_with_finlim C (univ_cat_with_finlim_universe C) e Γ p (s · t).
      Proof.
        use PullbackArrow.
        - exact (h · PullbackPr1 _).
        - exact k.
        - abstract
            (rewrite !assoc ;
             rewrite <- q ;
             rewrite !assoc' ;
             rewrite <- PullbackSqrCommutes ;
             apply idpath).
      Defined.

      Proposition is_pb_morphism_to_pb_mor_univ_pr1
        : is_pb_morphism_to_pb_mor_univ_mor · morphism_to_pb_mor_univ s t
          =
          h.
      Proof.
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_with_finlim_universe C)
                     e Δ p t))).
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          apply PullbackArrow_PullbackPr1.
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          rewrite !assoc.
          unfold is_pb_morphism_to_pb_mor_univ_mor.
          rewrite PullbackArrow_PullbackPr2.
          rewrite q.
          apply idpath.
      Qed.

      Proposition is_pb_morphism_to_pb_mor_univ_unique
        : isaprop
            (∑ hk,
             (hk · morphism_to_pb_mor_univ s t = h)
             ×
             (hk
              · PullbackPr2
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_with_finlim_universe C)
                     e Γ p (s · t))
              =
              k)).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_with_finlim_universe C)
                     e Γ p (s · t)))).
        - pose proof (maponpaths
                        (λ z, z · PullbackPr1 _)
                        (pr12 ζ₁ @ !(pr12 ζ₂)))
            as r.
          cbn in r.
          unfold morphism_to_pb_mor_univ in r.
          rewrite !assoc' in r.
          rewrite PullbackArrow_PullbackPr1 in r.
          exact r.
        - refine (pr22 ζ₁ @ _).
          refine (_ @ !(pr22 ζ₂)).
          apply idpath.
      Qed.
    End UMP.

    Definition is_pb_morphism_to_pb_mor_univ
               {Γ Δ : C}
               (s : Γ --> Δ)
               (t : Δ --> univ_cat_with_finlim_universe C)
      : isPullback (morphism_to_pb_mor_univ_comm s t).
    Proof.
      intros A h k q ; cbn in q.
      use iscontraprop1.
      - apply is_pb_morphism_to_pb_mor_univ_unique.
      - simple refine (_ ,, _ ,, _).
        + exact (is_pb_morphism_to_pb_mor_univ_mor s t h k q).
        + exact (is_pb_morphism_to_pb_mor_univ_pr1 s t h k q).
        + abstract
            (cbn ;
             apply PullbackArrow_PullbackPr2).
    Defined.

    Definition cat_el_map_stable_from_mor
      : cat_el_map_stable cat_el_map_data_from_mor.
    Proof.
      intros Γ Δ s t.
      simple refine (_ ,, _ ,, _).
      - exact (morphism_to_pb_mor_univ s t).
      - exact (morphism_to_pb_mor_univ_comm s t).
      - exact (is_pb_morphism_to_pb_mor_univ s t).
    Defined.

    Definition cat_el_map_from_mor
      : cat_el_map C.
    Proof.
      use make_cat_el_map.
      - exact cat_el_map_data_from_mor.
      - exact cat_el_map_stable_from_mor.
    Defined.
  End MorphismsToUniverse.

  Section UniverseToMorphismToUniverse.
    Context (el : cat_el_map C).

    Section Isomorphism.
      Context {Γ : C}
              (t : Γ --> univ_cat_with_finlim_universe C).

      Let P : Pullback (cat_el_map_mor el (identity _)) t
        := cat_el_map_pb el t (identity _).

      Definition mor_to_cat_el_map_to_mor_z_iso_mor
        : cat_el_map_el
            (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
            t
          -->
          cat_el_map_el el (t · identity _).
      Proof.
        use (PullbackArrow P _ _ _ _) ; cbn.
        - exact (PullbackPr1 _).
        - exact (PullbackPr2 _).
        - apply PullbackSqrCommutes.
      Defined.

      Definition mor_to_cat_el_map_to_mor_z_iso_inv
        : cat_el_map_el el (t · identity _)
          -->
          cat_el_map_el
            (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
            t.
      Proof.
        use PullbackArrow.
        - exact (cat_el_map_pb_mor el t (identity _)).
        - exact (cat_el_map_mor el _).
        - apply (PullbackSqrCommutes P).
      Defined.

      Proposition mor_to_cat_el_map_to_mor_z_iso_eqs
        : is_inverse_in_precat
            mor_to_cat_el_map_to_mor_z_iso_mor
            mor_to_cat_el_map_to_mor_z_iso_inv.
      Proof.
        split.
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply PullbackArrow_PullbackPr1.
            }
            refine (PullbackArrow_PullbackPr1 P _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply PullbackArrow_PullbackPr2.
            }
            refine (PullbackArrow_PullbackPr2 P _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply (PullbackArrow_PullbackPr1 P).
            }
            refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply (PullbackArrow_PullbackPr2 P).
            }
            refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
      Qed.

      Definition mor_to_cat_el_map_to_mor_z_iso
        : z_iso
            (cat_el_map_el
               (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
               t)
            (cat_el_map_el el (t · identity _)).
      Proof.
        use make_z_iso.
        - exact mor_to_cat_el_map_to_mor_z_iso_mor.
        - exact mor_to_cat_el_map_to_mor_z_iso_inv.
        - exact mor_to_cat_el_map_to_mor_z_iso_eqs.
      Defined.
    End Isomorphism.

    Arguments mor_to_cat_el_map_to_mor_z_iso_mor /.

    Lemma mor_to_cat_el_map_to_mor_eq1
          {Γ : C}
          (t : Γ --> univ_cat_with_finlim_universe C)
      : mor_to_cat_el_map_to_mor_z_iso_mor t
        · cat_el_map_el_eq el (id_right t)
        · cat_el_map_mor el t
        =
        PullbackPr2 _.
    Proof.
      cbn.
      rewrite !assoc'.
      rewrite cat_el_map_mor_eq.
      exact (PullbackArrow_PullbackPr2 (cat_el_map_pb el t (identity _)) _ _ _ _).
    Qed.

    Lemma mor_to_cat_el_map_to_mor_eq2
          {Γ Δ : C}
          (s : Γ --> Δ)
          (t : Δ --> univ_cat_with_finlim_universe C)
      : morphism_to_pb_mor_univ (cat_el_map_mor el (identity _)) s t
        · mor_to_cat_el_map_to_mor_z_iso_mor t
        · cat_el_map_el_eq el (id_right t)
        =
        mor_to_cat_el_map_to_mor_z_iso_mor (s · t)
        · cat_el_map_el_eq el (id_right (s · t))
        · cat_el_map_pb_mor el s t.
    Proof.·
      (*

      rewrite !assoc'.
      assert (cat_el_map_el_eq el (id_right (s · t))
              · cat_el_map_pb_mor el s t
              =
              cat_el_map_el_eq el (assoc' _ _ _)
              · cat_el_map_pb_mor el s (t · identity _)
              · cat_el_map_el_eq el (id_right t))
        as ->.
      {
        refine (_ @ assoc _ _ _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          use cat_el_map_pb_mor_eq.
          refine (assoc _ _ _ @ id_right _).
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (cat_el_map_el_eq_comp _ _ _ @ _).
        do 2 apply maponpaths.
        apply homset_property.
      }
      pose (P := cat_el_map_pb el (s · t) (identity _)).
      rewrite !assoc.
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (cat_el_map_pb el t _))).
      - refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (cat_el_map_pb el t _)).
        }
        unfold morphism_to_pb_mor_univ.
        rewrite PullbackArrow_PullbackPr1.
        cbn.
        refine (!_).
        assert (cat_el_map_el_eq el (assoc' s t (identity _))
                · cat_el_map_pb_mor el s (t · identity _)
                · cat_el_map_pb_mor el t (identity _)
                =
                PullbackPr1 P)
          as p.
        {
          cbn.

          Check cat_el_map_pb_mor_eq el s (id_right t) (assoc _ _ _ @ id_right _).
          Check cat_el_map_pb_mor el s t.
          pose (cat_el_map_el_eq el (assoc' s t (id₁ (univ_cat_with_finlim_universe C)))).
          pose (cat_el_map_pb_mor el s (t · id₁ (univ_cat_with_finlim_universe C))).
          pose (cat_el_map_pb_mor el t (id₁ (univ_cat_with_finlim_universe C))).
          pose (cat_el_map_pb_mor el (s · t) (id₁ (univ_cat_with_finlim_universe C))).

          Check cat_el_map_pb_mor el (s · t) (id₁ (univ_cat_with_finlim_universe C)).
          Check cat_el_map_el_eq el (id_right (s · t)).
          Check cat_el_map_pb_mor el (s · t) (id₁ (univ_cat_with_finlim_universe C)).
          admit.
        }
        etrans.
        {
          do 2 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          exact p.
        }
        apply (PullbackArrow_PullbackPr1 P).
      - refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (cat_el_map_pb el t _)).
        }
        unfold morphism_to_pb_mor_univ.
        rewrite PullbackArrow_PullbackPr2.
        cbn.
        refine (!_).
        assert (PullbackPr2 (cat_el_map_pb el (s · t) (identity _)) · s
                =
                cat_el_map_el_eq el (assoc' s t (identity _))
                · cat_el_map_pb_mor el s (t · identity _)
                · cat_el_map_mor el (t · identity _))
          as p.
        {
          cbn.
          refine (!_).
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            exact (PullbackSqrCommutes (cat_el_map_pb el s _)).
          }
          cbn.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply cat_el_map_mor_eq.
        }        etrans.
        {
          do 2 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          exact (!p).
        }
        rewrite !assoc.
        apply maponpaths_2.
        apply (PullbackArrow_PullbackPr2 P).
       *)
    Admitted.

    Definition mor_to_cat_el_map_to_mor
      : cat_el_map_from_mor (cat_el_map_mor el (identity _)) = el.
    Proof.
      use cat_el_map_eq.
      - intros Γ t.
        refine (z_iso_comp
                  (mor_to_cat_el_map_to_mor_z_iso t)
                  _).
        use make_z_iso.
        + Check (cat_el_map_pb_mor el t (identity _)).
          refine (cat_el_map_mor el _ · _).
                 (cat_el_map_el_eq el (id_right _))).
        exact (z_iso_comp
                 (mor_to_cat_el_map_to_mor_z_iso t)
                 (cat_el_map_el_eq el (id_right _))).
      - intros Γ t.
        exact (mor_to_cat_el_map_to_mor_eq1 t).
      - intros Γ Δ s t.
        refine (_ @ mor_to_cat_el_map_to_mor_eq2 s t).
        apply assoc.
    Qed.
  End UniverseToMorphismToUniverse.

  Section MorphismToUniverseToMorphism.
    Context {e : C}
            (p : e --> univ_cat_with_finlim_universe C).

    Definition cat_el_map_to_mor_to_map_z_iso_inv
      : e --> pullbacks_univ_cat_with_finlim C _ _ _ p (identity _).
    Proof.
      use PullbackArrow.
      - apply identity.
      - exact p.
      - abstract
          (rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Proposition cat_el_map_to_mor_to_map_z_iso_invs
      : is_inverse_in_precat
          (PullbackPr1 _)
          cat_el_map_to_mor_to_map_z_iso_inv.
    Proof.
      unfold cat_el_map_to_mor_to_map_z_iso_inv.
      split.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite id_left, id_right.
          apply idpath.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          rewrite id_left.
          refine (PullbackSqrCommutes _ @ _).
          apply id_right.
      - apply PullbackArrow_PullbackPr1.
    Qed.

    Definition cat_el_map_to_mor_to_map_z_iso
      : z_iso
          (pullbacks_univ_cat_with_finlim
             C
             _ _ _
             p
             (identity _))
          e.
    Proof.
      use make_z_iso.
      - exact (PullbackPr1 _).
      - exact cat_el_map_to_mor_to_map_z_iso_inv.
      - exact cat_el_map_to_mor_to_map_z_iso_invs.
    Defined.
  End MorphismToUniverseToMorphism.

  Proposition cat_el_map_to_mor_to_map
              (ep : ∑ (e : C), e --> univ_cat_with_finlim_universe C)
    : cat_el_map_to_mor (cat_el_map_from_mor (pr2 ep)) = ep.
  Proof.
    induction ep as [ e p ].
    use total2_paths_f.
    - use isotoid.
      {
        apply univalent_category_is_univalent.
      }
      exact (cat_el_map_to_mor_to_map_z_iso p).
    - abstract
        (cbn ;
         rewrite transportf_isotoid ;
         cbn ;
         unfold cat_el_map_to_mor_to_map_z_iso_inv ;
         apply PullbackArrow_PullbackPr2).
  Qed.

  Definition cat_el_map_mor_weq
    : cat_el_map C
      ≃
      ∑ (e : C), e --> univ_cat_with_finlim_universe C.
  Proof.
    use weq_iso.
    - exact cat_el_map_to_mor.
    - exact (λ ep, cat_el_map_from_mor (pr2 ep)).
    - intros el.
      exact (mor_to_cat_el_map_to_mor el).
    - intros ep.
      exact (cat_el_map_to_mor_to_map ep).
  Defined.
End UniverseAsMorphism.

(** * 4. Preservation of universes *)



Definition functor_el_map
           {C₁ C₂ : univ_cat_with_finlim_ob}
           (el₁ : cat_el_map C₁)
           (el₂ : cat_el_map C₂)
           (F : functor_finlim_ob C₁ C₂)
  : UU
  := ∏ (Γ : C₁)
       (t : Γ --> univ_cat_with_finlim_univ C₁),
     z_iso
       (F (el₁ Γ t))
       (el₂ (F Γ) (#F t · functor_finlim_univ_on_univ F)).


Definition disp_cat_ob_mor_finlim_el_map
  : disp_cat_ob_mor bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C : univ_cat_with_finlim_ob), cat_el_map C).
  - exact (λ (C₁ C₂ : univ_cat_with_finlim_ob)
             (el₁ : cat_el_map C₁)
             (el₂ : cat_el_map C₂)
             (F : functor_finlim_ob C₁ C₂),
           functor_el_map el₁ el₂ F).
Defined.

Definition disp_cat_id_comp_finlim_el_map
  : disp_cat_id_comp _ disp_cat_ob_mor_finlim_el_map.
Proof.
  simple refine (_ ,, _).
  - refine (λ (C : univ_cat_with_finlim_ob)
              (el : cat_el_map C)
              (Γ : C)
              (t : Γ --> univ_cat_with_finlim_univ C),
             _).
    cbn.
    admit.
  - refine (λ (C₁ C₂ C₃ : univ_cat_with_finlim_ob)
              (F : functor_finlim_ob C₁ C₂)
              (G : functor_finlim_ob C₂ C₃)
              (el₁ : cat_el_map C₁)
              (el₂ : cat_el_map C₂)
              (el₃ : cat_el_map C₃)
              (Fe : functor_el_map el₁ el₂ F)
              (Ge : functor_el_map el₂ el₃ G)
              (Γ : C₁)
              (t : Γ --> univ_cat_with_finlim_univ C₁),
             _).
    admit.
Admitted.

Definition disp_cat_data_finlim_el_map
  : disp_cat_data bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_finlim_el_map.
  - exact disp_cat_id_comp_finlim_el_map.
Defined.

Definition disp_prebicat_1_id_comp_cells_finlim_el_map
  : disp_prebicat_1_id_comp_cells bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_finlim_el_map.
  - refine (λ (C₁ C₂ : univ_cat_with_finlim_ob)
              (F G : functor_finlim_ob C₁ C₂)
              (τ : nat_trans_finlim_ob F G)
              (el₁ : cat_el_map C₁)
              (el₂ : cat_el_map C₂)
              (Fe : functor_el_map el₁ el₂ F)
              (Ge : functor_el_map el₁ el₂ G),
            ∏ (Γ : C₁)
              (t : Γ --> univ_cat_with_finlim_univ C₁),
             τ _ · Ge Γ t = Fe Γ t · _).
    rewrite <- (nat_trans_finlim_univ_eq τ).
    rewrite assoc.
    rewrite (nat_trans_ax τ _ _ t).
    cbn.
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




∏ (Γ : C), Γ --> u → ∑ (e : C), e --> Γ

(*
  - u : C
  - for each
      t : Γ --> u
    we have
      El t : C
      El t --> Γ

    s.t.


     El (s · t)       El t


      Δ ------------> Γ ---> u
         s      t
 *)
 *)
