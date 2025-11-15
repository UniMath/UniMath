(*******************************************************************************************

 Comprehension categories with strong sigma types

 In this file, we define when a comprehension category has strong sigma types. Note that
 sigma types are called strong if the canonical map from `Γ . A . B` to `Γ . ∑ A , B` is an
 isomorphism (Definition 5.8 in 'Comprehension categories and the semantics of type
 dependency' by Jacobs).

 We define the displayed bicategory of sigma types as a full subbicategory. The reason for
 that is given by Proposition 3.5 in 'The biequivalence of locally cartesian closed categories
 and Martin-Löf type theories' by Clairambault and Dybjer. Morphisms automatically preserve
 sigma types, and the proof of this fact uses that the sigma types are strong.

 We also lift this displayed bicategory to full comprehension categories.

 References
 - 'Comprehension categories and the semantics of type dependency' by Jacobs
 - 'The biequivalence of locally cartesian closed categories and Martin-Löf type theories' by
   Clairambault and Dybjer

 Contents
 1. The displayed bicategory of sigma types
 2. The univalence of this displayed bicategory
 3. Sigma types for comprehension categories
 4. Adjoint equivalences

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInBicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInOp1Bicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LiftDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. The displayed bicategory of sigma types *)
Definition comp_cat_dependent_sum
           (C : comp_cat)
  : UU
  := ∑ (sig : ∏ (Γ : C) (A : ty Γ), dependent_sum (cleaving_of_types C) (π A)),
     ∏ (Γ₁ Γ₂ : C)
       (A₁ : ty Γ₁)
       (A₂ : ty Γ₂)
       (s₁ : Γ₁ --> Γ₂)
       (s₂ : Γ₁ & A₁ --> Γ₂ & A₂)
       (p : s₂ · π A₂ = π A₁ · s₁)
       (Hp : isPullback p),
     left_beck_chevalley
       _
       (π A₂) s₁ (π A₁) s₂
       p
       (sig _ A₂)
       (sig _ A₁).

Section Projections.
  Context {C : comp_cat}
          (S : comp_cat_dependent_sum C)
          {Γ : C}
          (A : ty Γ).

  Definition dep_sum_is_right_adjoint
    : is_right_adjoint
        (fiber_functor_from_cleaving
           (disp_cat_of_types C)
           (cleaving_of_types C)
           (π A))
    := pr1 S Γ A.

  Definition dep_sum_cc
             (B : ty (Γ & A))
    : ty Γ
    := Adjunctions.Core.left_adjoint (pr1 S Γ A) B.

  Definition dep_sum_unit_cc
             (B : ty (Γ & A))
    : B -->[ identity _ ] subst_ty (π A) (dep_sum_cc B)
    := unit_from_right_adjoint (pr1 S Γ A) B.

  Definition dep_sum_counit_cc
             (B : ty Γ)
    : dep_sum_cc (subst_ty (π A) B) -->[ identity _ ] B
    := counit_from_right_adjoint (pr1 S Γ A) B.
End Projections.

Definition dep_sum_comp_cat_iso_help
           {C : comp_cat}
           (P : comp_cat_dependent_sum C)
           {Γ Δ : C}
           (A : ty Γ)
           (s : (Γ & A) = Δ)
           (s' : Δ --> Γ)
           (p : idtoiso (!s) · π A = s')
  : dependent_sum (cleaving_of_types C) s'.
Proof.
  induction s ; cbn in p.
  induction p.
  rewrite id_left.
  apply P.
Qed.

Definition dep_sum_comp_cat_iso
           {C : comp_cat}
           (P : comp_cat_dependent_sum C)
           {Γ Δ : C}
           (A : ty Γ)
           (s : z_iso Δ (Γ & A))
           (s' : Δ --> Γ)
           (p : s · π A = s')
  : dependent_sum (cleaving_of_types C) s'.
Proof.
  use dep_sum_comp_cat_iso_help.
  - exact P.
  - exact A.
  - refine (!(isotoid _ _ s)).
    apply univalent_category_is_univalent.
  - rewrite pathsinv0inv0.
    rewrite idtoiso_isotoid.
    exact p.
Qed.

Definition dep_sum_comp_cat_iso_ty
           {C : comp_cat}
           (P : comp_cat_dependent_sum C)
           {Γ Δ : C}
           (A : ty Γ)
           (B : ty Δ)
           (s : z_iso Δ (Γ & A))
           (s' : Δ --> Γ)
           (p : s · π A = s')
  : ty Γ
  := pr1 (dep_sum_comp_cat_iso P A s s' p) B.

Proposition isaprop_dependent_sum
            {C : cat_with_terminal_cleaving}
            {x y : C}
            (f : x --> y)
  : isaprop (dependent_sum (cleaving_of_types C) f).
Proof.
  pose (D₁ := univalent_fiber_category (disp_cat_of_types C) y : bicat_of_univ_cats).
  pose (D₂ := univalent_fiber_category (disp_cat_of_types C) x : bicat_of_univ_cats).
  pose (F := (fiber_functor_from_cleaving _ (cleaving_of_types C) f : D₁ --> D₂)).
  use (isofhlevelweqf _ (right_adjoint_weq_is_right_adjoint F)).
  use (isofhlevelweqf _ op1_left_adjoint_weq_right_adjoint).
  apply isaprop_left_adjoint.
  use op1_bicat_is_univalent_2_1.
  exact univalent_cat_is_univalent_2_1.
Qed.

Proposition isaprop_comp_cat_dependent_sum
            (C : comp_cat)
  : isaprop (comp_cat_dependent_sum C).
Proof.
  use isaproptotal2.
  - intro.
    do 8 (use impred ; intro).
    apply isaprop_left_beck_chevalley.
  - intros.
    do 2 (use funextsec ; intro).
    apply isaprop_dependent_sum.
Qed.

Definition make_comp_cat_dependent_sum
           {C : comp_cat}
           (sig : ∏ (Γ : C) (A : ty Γ),
                  dependent_sum (cleaving_of_types C) (π A))
           (stable : ∏ (Γ₁ Γ₂ : C)
                       (A₁ : ty Γ₁)
                       (A₂ : ty Γ₂)
                       (s₁ : Γ₁ --> Γ₂)
                       (s₂ : Γ₁ & A₁ --> Γ₂ & A₂)
                       (p : s₂ · π A₂ = π A₁ · s₁)
                       (Hp : isPullback p),
                     left_beck_chevalley
                       _
                       (π A₂) s₁ (π A₁) s₂
                       p
                       (sig _ A₂)
                       (sig _ A₁))
  : comp_cat_dependent_sum C
  := sig ,, stable.

Definition make_comp_cat_dependent_sum_all
           {C : comp_cat}
           (HC : has_dependent_sums (cleaving_of_types C))
  : comp_cat_dependent_sum C.
Proof.
  use make_comp_cat_dependent_sum.
  - exact (λ Γ A, pr1 HC _ _ (π A)).
  - intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp.
    exact (pr2 HC _ _ _ _ _ _ _ _ _ Hp).
Defined.

Definition dependent_sum_map
           {C : comp_cat}
           (D : comp_cat_dependent_sum C)
           {Γ : C}
           (A : ty Γ)
           (B : ty (Γ & A))
  : Γ & A & B --> Γ & dep_sum_cc D A B
  := comp_cat_comp_mor (dep_sum_unit_cc D A B)
     · comp_cat_extend_over (dep_sum_cc D A B) (π A).

Proposition dependent_sum_map_eq
            {C : comp_cat}
            (D : comp_cat_dependent_sum C)
            {Γ : C}
            (A : ty Γ)
            (B : ty (Γ & A))
  : dependent_sum_map D A B · π (dep_sum_cc D A B)
    =
    π B · π A.
Proof.
  unfold dependent_sum_map, comp_cat_extend_over.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply comprehension_functor_mor_comm.
  }
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    apply comprehension_functor_mor_comm.
  }
  rewrite id_right.
  apply idpath.
Qed.

Definition strong_dependent_sums
           (C : comp_cat)
  : UU
  := ∑ (D : comp_cat_dependent_sum C),
     ∏ (Γ : C)
       (A : ty Γ)
       (B : ty (Γ & A)),
     is_z_isomorphism (dependent_sum_map D A B).

Coercion strong_dependent_sum_to_dependent_sums
         {C : comp_cat}
         (D : strong_dependent_sums C)
  : comp_cat_dependent_sum C.
Proof.
  exact (pr1 D).
Defined.

Definition strong_dependent_sums_iso
           {C : comp_cat}
           (D : strong_dependent_sums C)
           {Γ : C}
           (A : ty Γ)
           (B : ty (Γ & A))
  : is_z_isomorphism (dependent_sum_map D A B)
  := pr2 D Γ A B.

Definition strong_dependent_sum_z_iso
           {C : comp_cat}
           (D : strong_dependent_sums C)
           {Γ : C}
           (A : ty Γ)
           (B : ty (Γ & A))
  : z_iso (Γ & A & B) (Γ & dep_sum_cc D A B)
  := _ ,, strong_dependent_sums_iso D A B.

Proposition isaprop_strong_dependent_sums
            (C : comp_cat)
  : isaprop (strong_dependent_sums C).
Proof.
  use isaproptotal2.
  - intro.
    do 3 (use impred ; intro).
    apply isaprop_is_z_isomorphism.
  - intros.
    apply isaprop_comp_cat_dependent_sum.
Qed.

Definition disp_bicat_of_sigma_type
  : disp_bicat bicat_comp_cat
  := disp_fullsubbicat _ strong_dependent_sums.

(** * 2. The univalence of this displayed bicategory *)
Definition univalent_2_1_disp_bicat_of_sigma_type
  : disp_univalent_2_1 disp_bicat_of_sigma_type.
Proof.
  apply disp_fullsubbicat_univalent_2_1.
Qed.

Definition univalent_2_0_disp_bicat_of_sigma_type
  : disp_univalent_2_0 disp_bicat_of_sigma_type.
Proof.
  use disp_univalent_2_0_fullsubbicat.
  - exact is_univalent_2_bicat_comp_cat.
  - intro C.
    apply isaprop_strong_dependent_sums.
Qed.

Definition univalent_2_disp_bicat_of_sigma_type
  : disp_univalent_2 disp_bicat_of_sigma_type.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_sigma_type.
  - exact univalent_2_1_disp_bicat_of_sigma_type.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_sigma_type
  : disp_2cells_isaprop disp_bicat_of_sigma_type.
Proof.
  apply disp_2cells_isaprop_fullsubbicat.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_sigma_type
  : disp_locally_groupoid disp_bicat_of_sigma_type.
Proof.
  apply disp_locally_groupoid_fullsubbicat.
Qed.

(** * 3. Sigma types for comprehension categories *)
Definition disp_bicat_of_sigma_type_full_comp_cat
  : disp_bicat bicat_full_comp_cat
  := lift_disp_bicat _ disp_bicat_of_sigma_type.

Definition univalent_2_1_disp_bicat_of_sigma_type_full_comp_cat
  : disp_univalent_2_1 disp_bicat_of_sigma_type_full_comp_cat.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact univalent_2_1_disp_bicat_of_sigma_type.
Qed.

Definition univalent_2_0_disp_bicat_of_sigma_type_full_comp_cat
  : disp_univalent_2_0 disp_bicat_of_sigma_type_full_comp_cat.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact univalent_2_0_disp_bicat_of_sigma_type.
  - exact univalent_2_1_disp_bicat_of_sigma_type.
  - exact is_univalent_2_1_bicat_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat.
Qed.

Definition univalent_2_disp_bicat_of_sigma_type_full_comp_cat
  : disp_univalent_2 disp_bicat_of_sigma_type_full_comp_cat.
Proof.
  split.
  - exact univalent_2_0_disp_bicat_of_sigma_type_full_comp_cat.
  - exact univalent_2_1_disp_bicat_of_sigma_type_full_comp_cat.
Defined.

Definition disp_2cells_isaprop_disp_bicat_of_sigma_type_full_comp_cat
  : disp_2cells_isaprop disp_bicat_of_sigma_type_full_comp_cat.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_of_sigma_type.
Qed.

Definition disp_locally_groupoid_disp_bicat_of_sigma_type_full_comp_cat
  : disp_locally_groupoid disp_bicat_of_sigma_type_full_comp_cat.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_of_sigma_type.
Qed.

(** * 4. Adjoint equivalences *)
Definition disp_adjoint_equiv_disp_bicat_of_sigma_type_full_comp_cat_help
           {C₁ C₂ : full_comp_cat}
           (F : adjoint_equivalence C₁ C₂)
           {T₁ : disp_bicat_of_sigma_type_full_comp_cat C₁}
           {T₂ : disp_bicat_of_sigma_type_full_comp_cat C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence F FF.
Proof.
  revert C₁ C₂ F T₁ T₂ FF.
  use J_2_0.
  - exact is_univalent_2_0_bicat_full_comp_cat.
  - intros C T₁ T₂ FF.
    use to_disp_left_adjoint_equivalence_over_id_lift.
    apply disp_left_adjoint_equivalence_fullsubbicat.
Qed.

Definition disp_adjoint_equiv_disp_bicat_of_sigma_type_full_comp_cat
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           (HF : left_adjoint_equivalence F)
           {T₁ : disp_bicat_of_sigma_type_full_comp_cat C₁}
           {T₂ : disp_bicat_of_sigma_type_full_comp_cat C₂}
           (FF : T₁ -->[ F ] T₂)
  : disp_left_adjoint_equivalence HF FF.
Proof.
  exact (disp_adjoint_equiv_disp_bicat_of_sigma_type_full_comp_cat_help (F ,, HF) FF).
Defined.
