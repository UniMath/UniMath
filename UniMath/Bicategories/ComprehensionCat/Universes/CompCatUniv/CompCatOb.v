(**
 Comprehension categories with an object

 Our goal is to define the bicategory of comprehension categories with a universe type. A
 universe in a comprehension category `C` consists of a type `u` in the empty context such
 that each term `t : tm Γ u` gives rise to a type `el t` in context `Γ`. This operation must
 be coherently stable under substitution. This formulation of universes is close to the
 syntax of comprehension categories, because universes generally are not defined using a
 universal property.

 We define the bicategory of comprehension categories in two steps.
 - First, we define the bicategory of comprehension categories together with a type in the
   empty context.
 - Second, we add the `el`-map, which we also require to be stable under substitution.
 Both of these bicategories are defined using displayed bicategories. In this file, we define
 the first of these displayed bicategories, and we prove that it is univalent.

 Content
 1. Construction of the displayed bicategory of comprehension categories with an object
 2. Invertible 2-cells in this displayed bicategory
 3. Local univalence
 4. Adjoint equivalences
 5. Global univalence
 6. The total bicategory
 7. Accessors for the total bicategory
 8. Equational lemmas for functors
 9. Equational lemmas for natural transformations
                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Construction of the displayed bicategory of comprehension categories with an object *)
Definition disp_cat_ob_mor_comp_cat_with_ob
  : disp_cat_ob_mor bicat_comp_cat.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C : comp_cat), ty ([] : C)).
  - exact (λ (C₁ C₂ : comp_cat)
             (u₁ : ty ([] : C₁))
             (u₂ : ty ([] : C₂))
             (F : comp_cat_functor C₁ C₂),
           z_iso_disp
             (comp_cat_functor_empty_context_z_iso F)
             (comp_cat_type_functor F _ u₁)
             u₂).
Defined.

Definition disp_cat_id_comp_cat_with_ob
           {C : comp_cat}
           (u : ty ([] : C))
  : z_iso_disp (comp_cat_functor_empty_context_z_iso (id₁ C)) u u.
Proof.
  use make_z_iso_disp.
  - refine (transportf
              (λ z, _ -->[ z ] _)
              _
              (id_disp _)).
    abstract (apply TerminalArrowUnique).
  - simple refine (_ ,, _ ,, _).
    + refine (transportf
                (λ z, _ -->[ z ] _)
                _
                (id_disp _)).
      abstract (apply TerminalArrowEq).
    + abstract
        (rewrite mor_disp_transportf_postwhisker ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite id_left_disp ;
         unfold transportb ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (unfold transportb ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite id_left_disp ;
         unfold transportb ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

Definition disp_cat_comp_comp_cat_with_ob
           {C₁ C₂ C₃ : comp_cat}
           {F : comp_cat_functor C₁ C₂}
           {G : comp_cat_functor C₂ C₃}
           {u₁ : ty ([] : C₁)}
           {u₂ : ty ([] : C₂)}
           {u₃ : ty ([] : C₃)}
           (f : z_iso_disp
                  (comp_cat_functor_empty_context_z_iso F)
                  (comp_cat_type_functor F _ u₁)
                  u₂)
           (g : z_iso_disp
                  (comp_cat_functor_empty_context_z_iso G)
                  (comp_cat_type_functor G _ u₂)
                  u₃)
  : z_iso_disp
      (comp_cat_functor_empty_context_z_iso (F · G))
      (comp_cat_type_functor G _ (comp_cat_type_functor F _ u₁))
      u₃.
Proof.
  refine (z_iso_disp_transportf
            _
            (z_iso_disp_comp
               (disp_functor_on_z_iso_disp (comp_cat_type_functor G) f)
               g)).
  abstract
    (apply TerminalArrowEq).
Defined.

Definition disp_cat_id_comp_comp_cat_with_ob
  : disp_cat_id_comp bicat_comp_cat
      disp_cat_ob_mor_comp_cat_with_ob.
Proof.
  split.
  - intros C u ; simpl.
    exact (disp_cat_id_comp_cat_with_ob u).
  - intros C₁ C₂ C₃ F G u₁ u₂ u₃ f g ; simpl.
    exact (disp_cat_comp_comp_cat_with_ob f g).
Defined.

Definition disp_cat_data_comp_cat_with_ob
  : disp_cat_data bicat_comp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_comp_cat_with_ob.
  - exact disp_cat_id_comp_comp_cat_with_ob.
Defined.

Definition disp_prebicat_1_id_comp_cells_comp_cat_with_ob
  : disp_prebicat_1_id_comp_cells bicat_comp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_comp_cat_with_ob.
  - refine (λ (C₁ C₂ : comp_cat)
              (F G : comp_cat_functor C₁ C₂)
              (τ : comp_cat_nat_trans F G)
              (u₁ : ty ([] : C₁))
              (u₂ : ty ([] : C₂))
              (f : z_iso_disp
                     (comp_cat_functor_empty_context_z_iso F)
                     (comp_cat_type_functor F _ u₁)
                     u₂)
              (g : z_iso_disp
                     (comp_cat_functor_empty_context_z_iso G)
                     (comp_cat_type_functor G _ u₁)
                     u₂),
            transportf
              (λ z, _ -->[ z ] _)
              _
              (comp_cat_type_nat_trans τ _ u₁ ;; g)%mor_disp
            =
            f).
    abstract (apply TerminalArrowEq).
Defined.

Proposition disp_2cells_isaprop_disp_bicat_comp_cat_with_ob
  : disp_2cells_isaprop
      disp_prebicat_1_id_comp_cells_comp_cat_with_ob.
Proof.
  intro ; intros.
  apply homsets_disp.
Qed.

Definition disp_prebicat_ops_comp_cat_with_ob
  : disp_prebicat_ops disp_prebicat_1_id_comp_cells_comp_cat_with_ob.
Proof.
  repeat split.
  - intros C₁ C₂ F u₁ u₂ f ; simpl.
    rewrite id_left_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply transportf_set.
    apply homset_property.
  - intros C₁ C₂ F u₁ u₂ f ; simpl.
    rewrite id_left_disp.
    rewrite disp_functor_transportf.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite disp_functor_id.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  - intros C₁ C₂ F u₁ u₂ f ; simpl.
    rewrite id_left_disp.
    rewrite mor_disp_transportf_prewhisker.
    rewrite id_right_disp.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  - intros C₁ C₂ F u₁ u₂ f ; simpl.
    rewrite id_left_disp.
    rewrite disp_functor_transportf.
    rewrite disp_functor_id.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite !transport_f_f.
    apply transportf_set.
    apply homset_property.
  - intros C₁ C₂ F u₁ u₂ f ; simpl.
    rewrite id_left_disp.
    rewrite mor_disp_transportf_prewhisker.
    rewrite id_right_disp.
    unfold transportb.
    rewrite !transport_f_f.
    apply transportf_set.
    apply homset_property.
  - intros C₁ C₂ C₃ C₄ F G H u₁ u₂ u₃ u₄ f g h ; simpl.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply disp_functor_comp_var.
    }
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  - intros C₁ C₂ C₃ C₄ F G H u₁ u₂ u₃ u₄ f g h ; simpl.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply disp_functor_comp.
    }
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  - intros C₁ C₂ F G H τ₁ τ₂ u₁ u₂ f g h ; simpl.
    intros p q.
    refine (_ @ p) ; clear p.
    rewrite <- q ; clear q.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  - intros C₁ C₂ C₃ F G₁ G₂ τ u₁ u₂ u₃ f g₁ g₂ ; simpl.
    intro p.
    rewrite <- p.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite !transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply disp_nat_trans_ax_var.
    }
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  - intros C₁ C₂ C₃ F₁ F₂ G τ u₁ u₂ u₃ f₁ f₂ g ; simpl.
    intro p.
    rewrite <- p.
    rewrite disp_functor_transportf.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite disp_functor_comp.
    rewrite assoc_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
Qed.

Definition disp_prebicat_data_comp_cat_with_ob
  : disp_prebicat_data bicat_comp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_comp_cat_with_ob.
  - exact disp_prebicat_ops_comp_cat_with_ob.
Defined.

Proposition disp_prebicat_laws_comp_cat_with_ob
  : disp_prebicat_laws disp_prebicat_data_comp_cat_with_ob.
Proof.
  repeat split ;
    intro ; intros ;
    apply disp_2cells_isaprop_disp_bicat_comp_cat_with_ob.
Qed.

Definition disp_prebicat_comp_cat_with_ob
  : disp_prebicat bicat_comp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_comp_cat_with_ob.
  - exact disp_prebicat_laws_comp_cat_with_ob.
Defined.

Definition disp_bicat_comp_cat_with_ob
  : disp_bicat bicat_comp_cat.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_comp_cat_with_ob.
  - abstract
      (intro ; intros ;
       apply isasetaprop ;
       apply disp_2cells_isaprop_disp_bicat_comp_cat_with_ob).
Defined.

(** * 2. Invertible 2-cells in this displayed bicategory *)
Proposition is_disp_invertible_2cell_disp_bicat_comp_cat_with_ob
            {C₁ C₂ : bicat_comp_cat}
            {F G : C₁ --> C₂}
            {τ : invertible_2cell F G}
            {u₁ : disp_bicat_comp_cat_with_ob C₁}
            {u₂ : disp_bicat_comp_cat_with_ob C₂}
            {f : u₁ -->[ F ] u₂}
            {g : u₁ -->[ G ] u₂}
            (p : f ==>[ τ ] g)
  : is_disp_invertible_2cell τ p.
Proof.
  simple refine (_ ,, _ ,, _) ;
    [
    | apply disp_2cells_isaprop_disp_bicat_comp_cat_with_ob
    | apply disp_2cells_isaprop_disp_bicat_comp_cat_with_ob ].
  cbn in p ; cbn.
  rewrite <- p.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite assoc_disp.
  unfold transportb.
  rewrite transport_f_f.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply (from_eq_2cell_comp_cat_disp (vcomp_linv τ)).
  }
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  etrans.
  {
    apply maponpaths.
    apply id_left_disp.
  }
  unfold transportb.
  rewrite transport_f_f.
  apply transportf_set.
  apply homset_property.
Qed.

Proposition disp_locally_groupoid_disp_bicat_comp_cat_with_ob
  : disp_locally_groupoid disp_bicat_comp_cat_with_ob.
Proof.
  intro ; intros.
  apply is_disp_invertible_2cell_disp_bicat_comp_cat_with_ob.
Qed.

(** * 3. Local univalence *)
Definition disp_univalent_2_1_disp_bicat_comp_cat_with_ob
  : disp_univalent_2_1 disp_bicat_comp_cat_with_ob.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros C₁ C₂ F u₁ u₂ f f'.
  use isweqimplimpl.
  - cbn ; intro τ.
    use subtypePath.
    {
      intro.
      apply isaprop_is_z_iso_disp.
    }
    pose (p := pr1 τ).
    refine (!p @ _).
    etrans.
    {
      apply maponpaths.
      apply id_left_disp.
    }
    unfold transportb.
    rewrite transport_f_f.
    apply transportf_set.
    apply homset_property.
  - apply isaset_z_iso_disp.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_disp_invertible_2cell.
    + intros.
      apply disp_2cells_isaprop_disp_bicat_comp_cat_with_ob.
Qed.

(** * 4. Adjoint equivalences *)
Section ToDispAdjEquiv.
  Context {C : comp_cat}
          {u₁ u₂ : disp_bicat_comp_cat_with_ob C}
          (f : u₁ -->[ identity _ ] u₂).

  Definition to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id_inv
    : u₂ -->[ identity _ ] u₁.
  Proof.
    cbn.
    refine (z_iso_disp_transportf _ (z_iso_inv_from_z_iso_disp f)).
    abstract
      (apply TerminalArrowEq).
  Defined.

  Proposition to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id_unit
    : id_disp u₁
      ==>[ linvunitor _ ]
      f ;; to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id_inv.
  Proof.
    simpl.
    rewrite id_left_disp.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply (pr22 f).
    }
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Proposition to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id_counit
    : to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id_inv ;; f
      ==>[ lunitor _ ]
      id_disp u₂.
  Proof.
    simpl.
    rewrite id_left_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (pr22 f).
    }
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id
    : disp_left_adjoint_equivalence
        (internal_adjoint_equivalence_identity C)
        f.
  Proof.
    simple refine (_ ,, (_ ,, _)) ;
      [
      | split ; apply disp_2cells_isaprop_disp_bicat_comp_cat_with_ob
      | split ; apply is_disp_invertible_2cell_disp_bicat_comp_cat_with_ob ].
    simple refine(_ ,, _ ,, _).
    - exact to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id_inv.
    - exact to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id_unit.
    - exact to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id_counit.
  Defined.
End ToDispAdjEquiv.

Section AdjointEquivalences.
  Context {C : comp_cat}
          (u₁ u₂ : ty ([] : C)).

  Definition disp_bicat_comp_cat_with_ob_to_adjequiv
             (f : z_iso_disp (identity_z_iso []) u₁ u₂)
    : disp_adjoint_equivalence
        (D := disp_bicat_comp_cat_with_ob)
        (internal_adjoint_equivalence_identity C)
        u₁ u₂.
  Proof.
    simple refine (_ ,, (_ ,, (_ ,, _))) ;
      [
      |
      | split ; apply disp_2cells_isaprop_disp_bicat_comp_cat_with_ob
      | split ; apply is_disp_invertible_2cell_disp_bicat_comp_cat_with_ob ].
    - cbn.
      refine (z_iso_disp_transportf _ f).
      abstract
        (apply TerminalArrowEq).
    - apply to_disp_bicat_comp_cat_with_ob_to_adjequiv_over_id.
  Defined.

  Definition disp_bicat_comp_cat_with_ob_from_adjequiv
             (f : disp_adjoint_equivalence
                    (D := disp_bicat_comp_cat_with_ob)
                    (internal_adjoint_equivalence_identity C)
                    u₁ u₂)
    : z_iso_disp (identity_z_iso []) u₁ u₂.
  Proof.
    refine (z_iso_disp_transportf _ (pr1 f)).
    abstract
      (apply TerminalArrowEq).
  Defined.

  Definition disp_bicat_comp_cat_with_ob_adjequiv_weq
    : z_iso_disp (identity_z_iso []) u₁ u₂
      ≃
      disp_adjoint_equivalence
        (D := disp_bicat_comp_cat_with_ob)
        (internal_adjoint_equivalence_identity C)
        u₁ u₂.
  Proof.
    use weq_iso.
    - exact disp_bicat_comp_cat_with_ob_to_adjequiv.
    - exact disp_bicat_comp_cat_with_ob_from_adjequiv.
    - abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         cbn ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
    - abstract
        (intro f ;
         use subtypePath ;
         [ intro ;
           exact (isaprop_disp_left_adjoint_equivalence
                    _ _
                    is_univalent_2_1_bicat_comp_cat
                    disp_univalent_2_1_disp_bicat_comp_cat_with_ob)
         | ] ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         cbn ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
  Defined.
End AdjointEquivalences.

(** * 5. Global univalence *)
Definition disp_univalent_2_0_disp_bicat_comp_cat_with_ob
  : disp_univalent_2_0 disp_bicat_comp_cat_with_ob.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  refine (λ (C : comp_cat) (u₁ u₂ : ty ([] : C)), _).
  use weqhomot.
  - exact (disp_bicat_comp_cat_with_ob_adjequiv_weq u₁ u₂
           ∘ make_weq
               (idtoiso_disp (idpath _))
               (disp_univalent_category_is_univalent_disp _ _ _ _ _ _))%weq.
  - intro p.
    cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      exact (isaprop_disp_left_adjoint_equivalence
               _ _
               is_univalent_2_1_bicat_comp_cat
               disp_univalent_2_1_disp_bicat_comp_cat_with_ob).
    }
    cbn.
    use subtypePath.
    {
      intro.
      apply isaprop_is_z_iso_disp.
    }
    cbn.
    apply maponpaths_2.
    apply homset_property.
Qed.

Proposition disp_univalent_2_disp_bicat_comp_cat_with_ob
  : disp_univalent_2 disp_bicat_comp_cat_with_ob.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_comp_cat_with_ob.
  - exact disp_univalent_2_1_disp_bicat_comp_cat_with_ob.
Qed.

(** * 6. The total bicategory *)
Definition bicat_comp_cat_with_ob
  : bicat
  := total_bicat disp_bicat_comp_cat_with_ob.

Proposition is_univalent_2_bicat_comp_cat_with_ob
  : is_univalent_2 bicat_comp_cat_with_ob.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_comp_cat_with_ob.
  - exact is_univalent_2_bicat_comp_cat.
Qed.

Proposition is_univalent_2_1_bicat_comp_cat_with_ob
  : is_univalent_2_1 bicat_comp_cat_with_ob.
Proof.
  exact (pr2 is_univalent_2_bicat_comp_cat_with_ob).
Qed.

Proposition is_univalent_2_0_bicat_comp_cat_with_ob
  : is_univalent_2_0 bicat_comp_cat_with_ob.
Proof.
  exact (pr1 is_univalent_2_bicat_comp_cat_with_ob).
Qed.

(** * 7. Accessors for the total bicategory *)
Definition comp_cat_with_ob
  : UU
  := ob bicat_comp_cat_with_ob.

Coercion comp_cat_with_ob_to_comp_cat
         (C : comp_cat_with_ob)
  : comp_cat
  := pr1 C.

Definition ob_of_comp_cat_ob
           (C : comp_cat_with_ob)
  : ty ([] : C)
  := pr2 C.

Definition comp_cat_univ
           {C : comp_cat_with_ob}
           (Γ : C)
  : ty Γ
  := (ob_of_comp_cat_ob C) [[ TerminalArrow _ _ ]].

Definition sub_comp_cat_univ_iso
           {C : comp_cat_with_ob}
           {Γ Δ : C}
           (s : Γ --> Δ)
  : z_iso
      (C := fiber_category _ _)
      (comp_cat_univ Δ [[ s ]])
      (comp_cat_univ Γ).
Proof.
  unfold comp_cat_univ.
  refine (z_iso_comp (comp_subst_ty_iso _ _ _) (eq_subst_ty_iso _ _)).
  apply TerminalArrowEq.
Defined.

Definition sub_comp_cat_univ
           {C : comp_cat_with_ob}
           {Γ Δ : C}
           (s : Γ --> Δ)
  : comp_cat_univ Δ [[ s ]] <: comp_cat_univ Γ
  := (sub_comp_cat_univ_iso s : _ --> _).

Definition sub_comp_cat_univ_inv
           {C : comp_cat_with_ob}
           {Γ Δ : C}
           (s : Γ --> Δ)
  : comp_cat_univ Γ <: comp_cat_univ Δ [[ s ]]
  := inv_from_z_iso (sub_comp_cat_univ_iso s).

Definition comp_cat_functor_ob
           (C₁ C₂ : comp_cat_with_ob)
  : UU
  := C₁ --> C₂.

Coercion functor_comp_cat_ob_to_functor
         {C₁ C₂ : comp_cat_with_ob}
         (F : comp_cat_functor_ob C₁ C₂)
  : comp_cat_functor C₁ C₂
  := pr1 F.

Definition ob_of_functor_comp_cat_ob
           {C₁ C₂ : comp_cat_with_ob}
           (F : comp_cat_functor_ob C₁ C₂)
  : z_iso_disp
      (comp_cat_functor_empty_context_z_iso F)
      (comp_cat_type_functor F _ (ob_of_comp_cat_ob C₁))
      (ob_of_comp_cat_ob C₂)
  := pr2 F.

Lemma functor_comp_cat_on_univ_z_iso_eq
      {C₁ C₂ : comp_cat_with_ob}
      (F : comp_cat_functor_ob C₁ C₂)
      (Γ : C₁)
  : identity (F Γ) · (identity (F Γ) · identity (F Γ))
    =
    identity (F Γ).
Proof.
  rewrite !id_left.
  apply idpath.
Qed.

Lemma functor_comp_cat_on_univ_z_iso_terminal_eq
      {C₁ C₂ : comp_cat_with_ob}
      (F : comp_cat_functor_ob C₁ C₂)
      (Γ : C₁)
  : # F (TerminalArrow [] Γ) · comp_cat_functor_empty_context_z_iso F
    =
    TerminalArrow [] (F Γ).
Proof.
  apply TerminalArrowEq.
Qed.

Definition functor_comp_cat_on_univ_z_iso
           {C₁ C₂ : comp_cat_with_ob}
           (F : comp_cat_functor_ob C₁ C₂)
           (Γ : C₁)
  : z_iso
      (C := fiber_category _ _)
      (comp_cat_type_functor F _ (comp_cat_univ Γ))
      (comp_cat_univ (F Γ)).
Proof.
  use z_iso_fiber_from_z_iso_disp.
  refine (z_iso_disp_transportf
            _
            (z_iso_disp_comp
               (comp_cat_functor_subst_ty F _ _)
               (z_iso_disp_comp
                  (subst_ty_iso
                     _
                     _
                     (ob_of_functor_comp_cat_ob F))
                  (subst_ty_eq_disp_iso
                     _
                     _)))).
  - apply functor_comp_cat_on_univ_z_iso_eq.
  - apply functor_comp_cat_on_univ_z_iso_terminal_eq.
Defined.

Definition functor_comp_cat_on_univ
           {C₁ C₂ : comp_cat_with_ob}
           (F : comp_cat_functor_ob C₁ C₂)
           (Γ : C₁)
  : comp_cat_type_functor F Γ (comp_cat_univ Γ) <: comp_cat_univ (F Γ)
  := functor_comp_cat_on_univ_z_iso F Γ : _ --> _.

Definition functor_comp_cat_on_univ_inv
           {C₁ C₂ : comp_cat_with_ob}
           (F : comp_cat_functor_ob C₁ C₂)
           (Γ : C₁)
  : comp_cat_univ (F Γ) <: comp_cat_type_functor F Γ (comp_cat_univ Γ)
  := inv_from_z_iso (functor_comp_cat_on_univ_z_iso F Γ).

Definition comp_cat_nat_trans_ob
           {C₁ C₂ : comp_cat_with_ob}
           (F G : comp_cat_functor_ob C₁ C₂)
  : UU
  := F ==> G.

Coercion comp_cat_nat_trans_ob_to_comp_cat_nat_trans
         {C₁ C₂ : comp_cat_with_ob}
         {F G : comp_cat_functor_ob C₁ C₂}
         (τ : comp_cat_nat_trans_ob F G)
  : comp_cat_nat_trans F G
  := pr1 τ.

Proposition comp_cat_nat_trans_univ_comm
            {C₁ C₂ : comp_cat_with_ob}
            {F G : comp_cat_functor_ob C₁ C₂}
            (τ : comp_cat_nat_trans_ob F G)
            (p : τ [] · comp_cat_functor_empty_context_z_iso G
                 =
                 comp_cat_functor_empty_context_z_iso F)
  : transportf
      (λ z, _ -->[ z ] _)
      p
      (comp_cat_type_nat_trans τ _ _ ;; ob_of_functor_comp_cat_ob G)%mor_disp
    =
    ob_of_functor_comp_cat_ob F.
Proof.
  refine (_ @ pr2 τ).
  apply maponpaths_2.
  apply homset_property.
Qed.

(** The following makes the upcoming proofs more readable *)
Local Arguments transportf {_ _ _ _ _} _.

Proposition comp_cat_nat_trans_on_univ_comm
            {C₁ C₂ : comp_cat_with_ob}
            {F G : comp_cat_functor_ob C₁ C₂}
            (τ : comp_cat_nat_trans_ob F G)
            (Γ : C₁)
  : functor_comp_cat_on_univ F Γ
    · sub_comp_cat_univ_inv (τ Γ)
    =
    comp_cat_type_fib_nat_trans τ (comp_cat_univ Γ)
    · coerce_subst_ty (τ Γ) (functor_comp_cat_on_univ G Γ).
Proof.
  cbn -[eq_subst_ty_iso].
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  rewrite !assoc_disp_var.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    do 5 apply maponpaths.
    apply cartesian_factorisation_commutes.
  }
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    apply cartesian_factorisation_commutes.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !assoc_disp_var.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    do 5 apply maponpaths.
    apply subst_ty_eq_disp_iso_comm.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    do 3 apply maponpaths.
    rewrite assoc_disp.
    unfold transportb.
    apply maponpaths.
    apply maponpaths_2.
    apply cartesian_factorisation_commutes.
  }
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths.
    apply maponpaths_2.
    apply cartesian_factorisation_commutes.
  }
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  refine (!_).
  rewrite cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    do 4 apply maponpaths.
    apply subst_ty_eq_disp_iso_inv_comm.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    do 3 apply maponpaths.
    apply subst_ty_eq_disp_iso_comm.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths.
    apply maponpaths_2.
    apply cartesian_factorisation_commutes.
  }
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  etrans.
  {
    do 2 apply maponpaths.
    refine (!_).
    use (comp_cat_nat_trans_univ_comm τ).
    apply TerminalArrowUnique.
  }
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths.
    apply maponpaths_2.
    apply (disp_nat_trans_ax (comp_cat_type_nat_trans τ)).
  }
  unfold transportb.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_nat_trans_on_univ_comm_alt
            {C₁ C₂ : comp_cat_with_ob}
            {F G : comp_cat_functor_ob C₁ C₂}
            (τ : comp_cat_nat_trans_ob F G)
            (Γ : C₁)
  : functor_comp_cat_on_univ F Γ
    =
    comp_cat_type_fib_nat_trans τ (comp_cat_univ Γ)
    · coerce_subst_ty (τ Γ) (functor_comp_cat_on_univ G Γ)
    · sub_comp_cat_univ (τ Γ).
Proof.
  rewrite <- (comp_cat_nat_trans_on_univ_comm τ Γ).
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply z_iso_after_z_iso_inv.
  }
  apply id_right.
Qed.

(** * 8. Equational lemmas for functors *)
Proposition id_functor_comp_cat_on_univ
            {C : comp_cat_with_ob}
            (Γ : C)
  : functor_comp_cat_on_univ (id₁ C) Γ = id_disp _.
Proof.
  cbn.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  rewrite id_left_disp.
  rewrite mor_disp_transportf_prewhisker.
  rewrite mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  rewrite !assoc_disp_var.
  rewrite mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    do 3 apply maponpaths.
    apply subst_ty_eq_disp_iso_comm.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  unfold fiber_functor_natural_inv, comp_cat_subst.
  rewrite cartesian_factorisation_commutes.
  rewrite transport_f_f.
  cbn.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_functor_comp_cat_on_univ
            {C₁ C₂ C₃ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            (G : comp_cat_functor_ob C₂ C₃)
            (Γ : C₁)
  : functor_comp_cat_on_univ (F · G) Γ
    =
    comp_cat_functor_coerce G (functor_comp_cat_on_univ F Γ)
    · functor_comp_cat_on_univ G _.
Proof.
  cbn.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  rewrite !assoc_disp_var.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite disp_functor_transportf.
  rewrite mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    do 3 apply maponpaths.
    apply subst_ty_eq_disp_iso_comm.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    unfold fiber_functor_natural_inv, comp_cat_subst.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    do 4 apply maponpaths.
    apply subst_ty_eq_disp_iso_comm.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    unfold fiber_functor_natural_inv, comp_cat_subst.
    do 2 apply maponpaths.
    rewrite assoc_disp.
    rewrite cartesian_factorisation_commutes.
    apply idpath.
  }
  etrans.
  {
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite <- disp_functor_comp_var.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      rewrite !assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        apply subst_ty_eq_disp_iso_comm.
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      apply idpath.
    }
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply idpath.
  }
  rewrite assoc_disp.
  unfold transportb.
  rewrite transport_f_f.
  rewrite disp_functor_comp.
  unfold transportb.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

(** * 9. Equational lemmas for natural transformations *)
Proposition comp_cat_type_fib_nat_trans_on_id2
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (id₂ F : comp_cat_nat_trans_ob _ _) A
    =
    id_subst_ty _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans, id_subst_ty.
  simpl.
  rewrite !cartesian_factorisation_commutes.
  cbn ; unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_lunitor
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (lunitor F : comp_cat_nat_trans_ob _ _) A
    =
    id_subst_ty _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans, id_subst_ty.
  simpl.
  rewrite !cartesian_factorisation_commutes.
  cbn ; unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_runitor
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (runitor F : comp_cat_nat_trans_ob _ _) A
    =
    id_subst_ty _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans, id_subst_ty.
  simpl.
  rewrite !cartesian_factorisation_commutes.
  cbn ; unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_linvunitor
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (linvunitor F : comp_cat_nat_trans_ob _ _) A
    =
    id_subst_ty _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans, id_subst_ty.
  simpl.
  rewrite !cartesian_factorisation_commutes.
  cbn ; unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_rinvunitor
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (rinvunitor F : comp_cat_nat_trans_ob _ _) A
    =
    id_subst_ty _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans, id_subst_ty.
  simpl.
  rewrite !cartesian_factorisation_commutes.
  cbn ; unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_lassociator
            {C₁ C₂ C₃ C₄ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            (G : comp_cat_functor_ob C₂ C₃)
            (H : comp_cat_functor_ob C₃ C₄)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (lassociator F G H : comp_cat_nat_trans_ob _ _) A
    =
    id_subst_ty _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans, id_subst_ty.
  simpl.
  rewrite !cartesian_factorisation_commutes.
  cbn ; unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_rassociator
            {C₁ C₂ C₃ C₄ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            (G : comp_cat_functor_ob C₂ C₃)
            (H : comp_cat_functor_ob C₃ C₄)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (rassociator F G H : comp_cat_nat_trans_ob _ _) A
    =
    id_subst_ty _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans, id_subst_ty.
  simpl.
  rewrite !cartesian_factorisation_commutes.
  cbn ; unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_vcomp
            {C₁ C₂ : comp_cat_with_ob}
            {F G H : comp_cat_functor_ob C₁ C₂}
            (τ : comp_cat_nat_trans_ob F G)
            (θ : comp_cat_nat_trans_ob G H)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (τ • θ : comp_cat_nat_trans_ob _ _) A
    =
    comp_cat_type_fib_nat_trans τ A
    · coerce_subst_ty _ (comp_cat_type_fib_nat_trans θ _)
    · comp_subst_ty _ _ _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans, comp_subst_ty.
  cbn.
  unfold transportb.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite !assoc_disp_var.
  rewrite !transport_f_f.
  rewrite !cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  refine (!_).
  etrans.
  {
    do 3 apply maponpaths.
    rewrite assoc_disp.
    rewrite cartesian_factorisation_commutes.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    apply idpath.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite assoc_disp.
  unfold transportb.
  rewrite cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_lwhisker
            {C₁ C₂ C₃ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            {G₁ G₂ : comp_cat_functor_ob C₂ C₃}
            (τ : comp_cat_nat_trans_ob G₁ G₂)
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (F ◃ τ : comp_cat_nat_trans_ob _ _) A
    =
    comp_cat_type_fib_nat_trans τ (comp_cat_type_functor F Γ A).
Proof.
  apply idpath.
Qed.

Proposition comp_cat_type_fib_nat_trans_on_rwhisker
            {C₁ C₂ C₃ : comp_cat_with_ob}
            {F₁ F₂ : comp_cat_functor_ob C₁ C₂}
            (G : comp_cat_functor_ob C₂ C₃)
            {τ : comp_cat_nat_trans_ob F₁ F₂}
            {Γ : C₁}
            (A : ty Γ)
  : comp_cat_type_fib_nat_trans (τ ▹ G : comp_cat_nat_trans_ob _ _) A
    =
    comp_cat_functor_coerce G (comp_cat_type_fib_nat_trans τ A)
    · comp_cat_functor_subst_ty_coe _ _ _.
Proof.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  unfold comp_cat_type_fib_nat_trans.
  cbn.
  unfold fiber_functor_natural_inv.
  cbn.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite assoc_disp_var.
  rewrite !transport_f_f.
  rewrite !cartesian_factorisation_commutes.
  rewrite mor_disp_transportf_prewhisker.
  rewrite <- disp_functor_comp_var.
  rewrite cartesian_factorisation_commutes.
  rewrite disp_functor_transportf.
  rewrite !transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.
