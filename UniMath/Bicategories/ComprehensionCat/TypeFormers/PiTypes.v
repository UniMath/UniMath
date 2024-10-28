(*******************************************************************************************

 Comprehension categories with pi-types

 We define the displayed bicategory of pi-types for comprehension categories. Note that we
 only consider right adjoints along weakenings and not arbitrary morphisms. We also provide
 the necessary infrastructure to construct comprehension categories with pi-types in case
 one has all right adjoints.

 The main challenge in this file lies in defining when a functor preserves dependent products.
 Formulating this requirement is a bit tedious, because weakening is only preserved up to
 isomorphism. We need to take this into account, and that makes the formulation of preservation
 more convoluted. In addition, we need to work with pseudomorphisms to guarantee that
 substitution is actually preserved up to isomorphism. Note that we also make use univalence
 in this development. This is so that we can treat isomorphisms as equalities, and so that
 we can use induction on isomorphisms.

 Contents
 1. Preliminaries on pi-types
 2. Dependent products for morphisms that are isomorphic to projections
 3. Builders for dependent products
 4. Uniqueness of dependent products
 5. Preservation of dependent products
 6. Examples of functors that preserve dependent products
 6.1. Functors that preserve all dependent products
 6.2. The identity
 6.3. Composition
 7. The displayed bicategory of pi-types
 8. This displayed bicategory is univalent
 9. Pi-types for DFL full comprehension categories
 10. Adjoint equivalences

 *******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LiftDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Preliminaries on pi-types *)
Definition comp_cat_dependent_prod
           (C : comp_cat)
  : UU
  := ∑ (prd : ∏ (Γ : C) (A : ty Γ), dependent_product (cleaving_of_types C) (π A)),
     ∏ (Γ₁ Γ₂ : C)
       (A₁ : ty Γ₁)
       (A₂ : ty Γ₂)
       (s₁ : Γ₁ --> Γ₂)
       (s₂ : Γ₁ & A₁ --> Γ₂ & A₂)
       (p : s₂ · π A₂ = π A₁ · s₁)
       (Hp : isPullback p),
     right_beck_chevalley
       _
       (π A₂) s₁ (π A₁) s₂
       p
       (prd _ A₂)
       (prd _ A₁).

Section Projections.
  Context {C : comp_cat}
          (P : comp_cat_dependent_prod C)
          {Γ : C}
          (A : ty Γ).

  Definition dep_prod_cc
             (B : ty (Γ & A))
    : ty Γ
    := Adjunctions.Core.right_adjoint (pr1 P Γ A) B.

  Definition dep_prod_unit_cc
             (B : ty Γ)
    : B -->[ identity _ ] dep_prod_cc (subst_ty (π A) B)
    := unit_from_left_adjoint (pr1 P Γ A) B.

  Definition dep_prod_counit_cc
             (B : ty (Γ & A))
    : subst_ty (π A) (dep_prod_cc B) -->[ identity _ ] B
    := counit_from_left_adjoint (pr1 P Γ A) B.
End Projections.

(** * 2. Dependent products for morphisms that are isomorphic to projections *)
Definition dep_prod_comp_cat_iso_help
           {C : comp_cat}
           (P : comp_cat_dependent_prod C)
           {Γ Δ : C}
           (A : ty Γ)
           (s : (Γ & A) = Δ)
           (s' : Δ --> Γ)
           (p : idtoiso (!s) · π A = s')
  : dependent_product (cleaving_of_types C) s'.
Proof.
  induction s ; cbn in p.
  induction p.
  rewrite id_left.
  apply P.
Qed.

Definition dep_prod_comp_cat_iso
           {C : comp_cat}
           (P : comp_cat_dependent_prod C)
           {Γ Δ : C}
           (A : ty Γ)
           (s : z_iso Δ (Γ & A))
           (s' : Δ --> Γ)
           (p : s · π A = s')
  : dependent_product (cleaving_of_types C) s'.
Proof.
  use dep_prod_comp_cat_iso_help.
  - exact P.
  - exact A.
  - refine (!(isotoid _ _ s)).
    apply univalent_category_is_univalent.
  - rewrite pathsinv0inv0.
    rewrite idtoiso_isotoid.
    exact p.
Qed.

(** * 3. Builders for dependent products *)
Definition make_comp_cat_dependent_prod
           {C : comp_cat}
           (prd : ∏ (Γ : C) (A : ty Γ),
                  dependent_product (cleaving_of_types C) (π A))
           (stable : ∏ (Γ₁ Γ₂ : C)
                       (A₁ : ty Γ₁)
                       (A₂ : ty Γ₂)
                       (s₁ : Γ₁ --> Γ₂)
                       (s₂ : Γ₁ & A₁ --> Γ₂ & A₂)
                       (p : s₂ · π A₂ = π A₁ · s₁)
                       (Hp : isPullback p),
                     right_beck_chevalley
                       _
                       (π A₂) s₁ (π A₁) s₂
                       p
                       (prd _ A₂)
                       (prd _ A₁))
  : comp_cat_dependent_prod C
  := prd ,, stable.

Definition make_comp_cat_dependent_prod_all
           {C : comp_cat}
           (HC : has_dependent_products (cleaving_of_types C))
  : comp_cat_dependent_prod C.
Proof.
  use make_comp_cat_dependent_prod.
  - exact (λ Γ A, pr1 HC _ _ (π A)).
  - intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp.
    exact (pr2 HC _ _ _ _ _ _ _ _ _ Hp).
Defined.

(** * 4. Uniqueness of dependent products *)
Proposition isaprop_dependent_product
            {C : cat_with_terminal_cleaving}
            {x y : C}
            (f : x --> y)
  : isaprop (dependent_product (cleaving_of_types C) f).
Proof.
  pose (D₁ := univalent_fiber_category (disp_cat_of_types C) y : bicat_of_univ_cats).
  pose (D₂ := univalent_fiber_category (disp_cat_of_types C) x : bicat_of_univ_cats).
  pose (F := (fiber_functor_from_cleaving _ (cleaving_of_types C) f : D₁ --> D₂)).
  apply (isaprop_is_left_adjoint F).
Qed.

Proposition isaprop_comp_cat_dependent_prod
            (C : comp_cat)
  : isaprop (comp_cat_dependent_prod C).
Proof.
  use isaproptotal2.
  - intro.
    do 8 (use impred ; intro).
    apply isaprop_right_beck_chevalley.
  - intros.
    do 2 (use funextsec ; intro).
    apply isaprop_dependent_product.
Qed.

(** * 5. Preservation of dependent products *)
Definition preserves_comp_cat_dependent_prod
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (P₁ : comp_cat_dependent_prod C₁)
           (P₂ : comp_cat_dependent_prod C₂)
  : UU.
Proof.
  simple refine (∏ (Γ : C₁)
                   (A : ty Γ)
                   (B : ty (Γ & A)),
                 is_z_isomorphism
                   (right_beck_chevalley_nat_trans
                      (pr1 P₁ Γ A)
                      _
                      (fiber_functor_natural_nat_z_iso
                         (cleaving_of_types C₁) (cleaving_of_types C₂)
                         (cartesian_comp_cat_type_functor F)
                         _)
                      B)).
  use (dep_prod_comp_cat_iso P₂).
  - exact (comp_cat_type_functor F Γ A).
  - exact (full_comp_cat_functor_z_iso F A).
  - apply (comprehension_nat_trans_mor_comm (comp_cat_functor_comprehension F)).
Defined.

Proposition isaprop_preserves_comp_cat_dependent_prod
            {C₁ C₂ : full_comp_cat}
            (F : full_comp_cat_functor C₁ C₂)
            (P₁ : comp_cat_dependent_prod C₁)
            (P₂ : comp_cat_dependent_prod C₂)
  : isaprop (preserves_comp_cat_dependent_prod F P₁ P₂).
Proof.
  do 3 (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.

(** * 6. Examples of functors that preserve dependent products *)

(** ** 6.1. Functors that preserve all dependent products *)
Lemma preserves_comp_cat_dependent_prod_all_lemma
      {C₁ C₂ C₃ C₄ : category}
      (HC₁ : is_univalent C₁)
      (HC₂ : is_univalent C₂)
      (HC₃ : is_univalent C₃)
      (HC₄ : is_univalent C₄)
      {F : C₁ ⟶ C₂} {G : C₁ ⟶ C₃}
      {H : C₃ ⟶ C₄} {K : C₂ ⟶ C₄}
      {HF HF' : is_left_adjoint F} {HH HH' : is_left_adjoint H}
      {τ : nat_z_iso (G ∙ H) (F ∙ K)}
      {x : C₂}
      (Hx : is_z_isomorphism (right_beck_chevalley_nat_trans HF HH τ x))
  : is_z_isomorphism (right_beck_chevalley_nat_trans HF' HH' τ x).
Proof.
  pose (C₁' := make_univalent_category C₁ HC₁).
  pose (C₂' := make_univalent_category C₂ HC₂).
  pose (C₃' := make_univalent_category C₃ HC₃).
  pose (C₄' := make_univalent_category C₄ HC₄).
  assert (HF = HF') as ->.
  {
    apply (@isaprop_is_left_adjoint C₁' C₂' F).
  }
  assert (HH = HH') as ->.
  {
    apply (@isaprop_is_left_adjoint C₃' C₄' H).
  }
  apply Hx.
Qed.

Definition preserves_comp_cat_dependent_prod_all
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (HC₁ : has_dependent_products (cleaving_of_types C₁))
           (HC₂ : has_dependent_products (cleaving_of_types C₂))
           (HF : preserves_dependent_products (cartesian_comp_cat_type_functor F) HC₁ HC₂)
  : preserves_comp_cat_dependent_prod
      F
      (make_comp_cat_dependent_prod_all HC₁)
      (make_comp_cat_dependent_prod_all HC₂).
Proof.
  intros Γ A B.
  refine (preserves_comp_cat_dependent_prod_all_lemma _ _ _ _ (HF (Γ & A) Γ (π A) B)) ;
    apply is_univalent_fiber ;
    apply disp_univalent_category_is_univalent_disp.
Qed.

(** ** 6.2. The identity *)
Proposition id_preserves_comp_cat_dependent_prod_lem
            {C : full_comp_cat}
            {x y : C}
            (f : x --> y)
            (P P' : dependent_product (cleaving_of_types C) f)
            (a : ty x)
            (p := pr1 (isaprop_dependent_product f P P') : P = P')
  : right_beck_chevalley_nat_trans
      P P'
      (fiber_functor_natural_nat_z_iso _ _ (id_cartesian_disp_functor _) f)
      a
    =
    idtoiso (maponpaths (λ z, right_adjoint z _) p).
Proof.
  induction p.
  apply right_beck_chevalley_nat_trans_id.
Qed.

Proposition id_preserves_comp_cat_dependent_prod
            (C : full_comp_cat)
            (P : comp_cat_dependent_prod C)
            (F := id₁ C : full_comp_cat_functor C C)
  : preserves_comp_cat_dependent_prod (id₁ C) P P.
Proof.
  intros Γ A B.
  refine (is_z_isomorphism_path _ _).
  - refine (!(id_preserves_comp_cat_dependent_prod_lem _ _ _ B) @ _).
    refine (maponpaths (λ z, right_beck_chevalley_nat_trans _ _ z _) _).
    exact (fiber_functor_natural_nat_z_iso_eq
             (cleaving_of_types C) (cleaving_of_types C)
             (disp_functor_identity _)
             _ _
             (π A)).
  - apply z_iso_is_z_isomorphism.
Qed.

(** ** 6.3. Composition *)
Proposition preserves_comp_cat_dependent_prod_iso_eq
            {C₁ C₂ : full_comp_cat}
            (F : full_comp_cat_functor C₁ C₂)
            {Γ Δ : C₁}
            {A : ty Γ}
            {s : z_iso Δ (Γ & A)}
            {s' : Δ --> Γ}
            (p : s · π A = s')
  : z_iso_comp
      (functor_on_z_iso F s)
      (full_comp_cat_functor_z_iso F A)
    · π (comp_cat_type_functor F Γ A)
    =
    #F s'.
Proof.
  cbn.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply comprehension_nat_trans_mor_comm.
  }
  rewrite <- functor_comp.
  apply maponpaths.
  exact p.
Qed.

Proposition right_beck_chevalley_nat_trans_mor_eq
            {C₁ C₂ : full_comp_cat}
            (F : full_comp_cat_functor C₁ C₂)
            {Γ₁ Γ₂ : C₁}
            {s s' : Γ₁ --> Γ₂}
            (p : s = s')
            (P₁ : dependent_product (cleaving_of_types C₁) s)
            (P₂ : dependent_product (cleaving_of_types C₂) (#F s))
            (P₁' : dependent_product (cleaving_of_types C₁) s')
            (P₂' : dependent_product (cleaving_of_types C₂) (#F s'))
            (B : ty Γ₁)
            (H : is_z_isomorphism
                   (right_beck_chevalley_nat_trans
                      P₁
                      P₂
                      (fiber_functor_natural_nat_z_iso
                         (cleaving_of_types C₁) (cleaving_of_types C₂)
                         (cartesian_comp_cat_type_functor F)
                         _)
                      B))
  : is_z_isomorphism
      (right_beck_chevalley_nat_trans
         P₁'
         P₂'
         (fiber_functor_natural_nat_z_iso
            (cleaving_of_types C₁) (cleaving_of_types C₂)
            (cartesian_comp_cat_type_functor F)
            _)
         B).
Proof.
  induction p.
  assert (P₁ = P₁') as ->.
  {
    apply isaprop_dependent_product.
  }
  assert (P₂ = P₂') as ->.
  {
    apply isaprop_dependent_product.
  }
  exact H.
Qed.

Definition preserves_comp_cat_dependent_prod_iso_help
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (P₁ : comp_cat_dependent_prod C₁)
           (P₂ : comp_cat_dependent_prod C₂)
           (HF : preserves_comp_cat_dependent_prod F P₁ P₂)
           {Γ Δ : C₁}
           (A : ty Γ)
           (s : (Γ & A) = Δ)
           (s' : Δ --> Γ)
           (p : idtoiso (!s) · π A = s')
           (B : ty Δ)
  : is_z_isomorphism
      (right_beck_chevalley_nat_trans
         (dep_prod_comp_cat_iso P₁ _ _ _ p)
         (dep_prod_comp_cat_iso P₂ _ _ _ (preserves_comp_cat_dependent_prod_iso_eq F p))
         (fiber_functor_natural_nat_z_iso
            (cleaving_of_types C₁) (cleaving_of_types C₂)
            (cartesian_comp_cat_type_functor F)
            _)
         B).
Proof.
  induction s ; cbn in p.
  induction p.
  refine (right_beck_chevalley_nat_trans_mor_eq _ _ _ _ _ _ _ (HF Γ A B)).
  exact (!(id_left _)).
Qed.

Definition preserves_comp_cat_dependent_prod_iso
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (P₁ : comp_cat_dependent_prod C₁)
           (P₂ : comp_cat_dependent_prod C₂)
           (HF : preserves_comp_cat_dependent_prod F P₁ P₂)
           {Γ Δ : C₁}
           (A : ty Γ)
           (s : z_iso Δ (Γ & A))
           (s' : Δ --> Γ)
           (p : s · π A = s')
           (B : ty Δ)
           (q : z_iso_comp (functor_on_z_iso F s) (full_comp_cat_functor_z_iso F A)
       · π (comp_cat_type_functor F Γ A) = # F s')
  : is_z_isomorphism
      (right_beck_chevalley_nat_trans
         (dep_prod_comp_cat_iso P₁ _ _ _ p)
         (dep_prod_comp_cat_iso P₂ _ _ _ q)
         (fiber_functor_natural_nat_z_iso
            (cleaving_of_types C₁) (cleaving_of_types C₂)
            (cartesian_comp_cat_type_functor F)
            _)
         B).
Proof.
  assert (q = preserves_comp_cat_dependent_prod_iso_eq F p) as ->.
  {
    apply homset_property.
  }
  assert (idtoiso (!(!isotoid C₁ (univalent_category_is_univalent C₁) s)) · π A = s')
    as r.
  {
    rewrite pathsinv0inv0.
    rewrite idtoiso_isotoid.
    apply p.
  }
  use (preserves_comp_cat_dependent_prod_all_lemma
         _ _ _ _
         (preserves_comp_cat_dependent_prod_iso_help _ _ _ HF A _ s' r B)) ;
    apply is_univalent_fiber ;
    apply disp_univalent_category_is_univalent_disp.
Qed.

Proposition preserves_dependent_products_comp_cartesian
            (C₁ C₂ C₃ : full_comp_cat)
            (P₁ : comp_cat_dependent_prod C₁)
            (P₂ : comp_cat_dependent_prod C₂)
            (P₃ : comp_cat_dependent_prod C₃)
            (F : full_comp_cat_functor C₁ C₂)
            (G : full_comp_cat_functor C₂ C₃)
            (HF : preserves_comp_cat_dependent_prod F P₁ P₂)
            (HG : preserves_comp_cat_dependent_prod G P₂ P₃)
  : preserves_comp_cat_dependent_prod (F · G) P₁ P₃.
Proof.
  intros Γ A B.
  refine (is_z_isomorphism_path _ _).
  - refine (!(right_beck_chevalley_nat_trans_comp
                (cartesian_comp_cat_type_functor F)
                (cartesian_comp_cat_type_functor G)
                (π A)
                B
                _ _ _) @ _).
    + use (dep_prod_comp_cat_iso P₂).
      * exact (comp_cat_type_functor F Γ A).
      * exact (full_comp_cat_functor_z_iso F A).
      * exact (comprehension_nat_trans_mor_comm (comp_cat_functor_comprehension F) Γ A).
    + refine (maponpaths (λ z, right_beck_chevalley_nat_trans _ _ z _) _).
      exact (fiber_functor_natural_nat_z_iso_eq
               (cleaving_of_types C₁) (cleaving_of_types C₃)
               (disp_functor_composite _ _)
               _ _ _).
  - use is_z_isomorphism_comp.
    + use functor_on_is_z_isomorphism.
      apply HF.
    + exact (preserves_comp_cat_dependent_prod_iso
               _ _ _
               HG
               (comp_cat_type_functor F Γ A)
               _ _ _ _ _).
Qed.

(** * 7. The displayed bicategory of pi-types *)
Definition disp_bicat_of_pi_type
  : disp_bicat bicat_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact (λ (C : full_comp_cat), comp_cat_dependent_prod C).
  - exact (λ (C₁ C₂ : full_comp_cat)
             (P₁ : comp_cat_dependent_prod C₁)
             (P₂ : comp_cat_dependent_prod C₂)
             (F : full_comp_cat_functor C₁ C₂),
           preserves_comp_cat_dependent_prod F P₁ P₂).
  - exact id_preserves_comp_cat_dependent_prod.
  - exact preserves_dependent_products_comp_cartesian.
Defined.

(** * 8. This displayed bicategory is univalent *)
Definition univalent_2_1_disp_bicat_of_pi_type
  : disp_univalent_2_1 disp_bicat_of_pi_type.
Proof.
  use disp_subbicat_univalent_2_1.
  intros C₁ C₂ P₁ P₂ f.
  apply isaprop_preserves_comp_cat_dependent_prod.
Qed.

Definition univalent_2_0_disp_bicat_of_pi_type
  : disp_univalent_2_0 disp_bicat_of_pi_type.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_full_comp_cat.
  - intro C.
    apply isaprop_comp_cat_dependent_prod.
  - intros C₁ C₂ P₁ P₂ f.
    apply isaprop_preserves_comp_cat_dependent_prod.
Qed.

Definition univalent_2_disp_bicat_of_pi_type
  : disp_univalent_2 disp_bicat_of_pi_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_pi_type.
  - exact univalent_2_1_disp_bicat_of_pi_type.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_pi_type
  : disp_2cells_isaprop disp_bicat_of_pi_type.
Proof.
  apply disp_2cells_isaprop_subbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_pi_type
  : disp_locally_groupoid disp_bicat_of_pi_type.
Proof.
  apply disp_locally_groupoid_subbicat.
  apply is_univalent_2_bicat_full_comp_cat.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_pi_type
  : disp_2cells_iscontr disp_bicat_of_pi_type.
Proof.
  apply disp_2cells_iscontr_subbicat.
Qed.

(** * 9. Pi-types for DFL full comprehension categories *)
Definition disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_bicat bicat_of_dfl_full_comp_cat
  := lift_disp_bicat _ disp_bicat_of_pi_type.

Definition univalent_2_1_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_univalent_2_1 disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_pi_type.
Qed.

Definition univalent_2_0_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_univalent_2_0 disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_pi_type.
  - exact univalent_2_1_disp_bicat_of_pi_type.
  - exact is_univalent_2_1_bicat_full_comp_cat.
  - exact is_univalent_2_1_disp_bicat_of_dfl_full_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_univalent_2 disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_pi_type_dfl_full_comp_cat.
  - exact univalent_2_1_disp_bicat_of_pi_type_dfl_full_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_2cells_isaprop disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_pi_type.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_locally_groupoid disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_pi_type.
Qed.

Definition disp_2cells_iscontr_disp_bicat_of_pi_type_dfl_full_comp_cat
  : disp_2cells_iscontr disp_bicat_of_pi_type_dfl_full_comp_cat.
Proof.
  use disp_2cells_iscontr_lift_disp_bicat.
  exact disp_2cells_iscontr_disp_bicat_of_pi_type.
Qed.

(** * 10. Adjoint equivalences *)
Definition disp_adjoint_equiv_disp_bicat_of_pi_type_help
           {C₁ C₂ : full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {P₁ : comp_cat_dependent_prod C₁}
           {P₂ : comp_cat_dependent_prod C₂}
  : preserves_comp_cat_dependent_prod (pr1 F) P₁ P₂.
Proof.
  revert C₁ C₂ F P₁ P₂.
  use J_2_0.
  - exact is_univalent_2_0_bicat_full_comp_cat.
  - intros C P₁ P₂.
    assert (P₁ = P₂) as p.
    {
      apply isaprop_comp_cat_dependent_prod.
    }
    induction p.
    apply id_preserves_comp_cat_dependent_prod.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat_help
           {C₁ C₂ : dfl_full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {P₁ : disp_bicat_of_pi_type_dfl_full_comp_cat C₁}
           {P₂ : disp_bicat_of_pi_type_dfl_full_comp_cat C₂}
           (FF : P₁ -->[ F ] P₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F P₁ P₂ FF.
  use J_2_0.
  - exact is_univalent_2_0_bicat_of_dfl_full_comp_cat.
  - intros C P₁ P₂ FF.
    use to_disp_left_adjoint_equivalence_over_id_lift.
    use disp_left_adjoint_equivalence_subbicat.
    + clear C P₁ P₂ FF.
      intros C₁ C₂ P₁ P₂ F HF.
      exact (disp_adjoint_equiv_disp_bicat_of_pi_type_help (F ,, HF)).
    + exact is_univalent_2_bicat_full_comp_cat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat
           {C₁ C₂ : dfl_full_comp_cat}
           (F : dfl_full_comp_cat_functor C₁ C₂)
           (HF : left_adjoint_equivalence F)
           {T₁ : disp_bicat_of_pi_type_dfl_full_comp_cat C₁}
           {T₂ : disp_bicat_of_pi_type_dfl_full_comp_cat C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  exact (disp_adjoint_equiv_disp_bicat_of_pi_type_dfl_full_comp_cat_help (F ,, HF) FF).
Defined.
