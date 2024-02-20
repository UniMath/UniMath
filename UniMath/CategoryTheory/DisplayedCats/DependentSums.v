(*******************************************************************************************

 Dependent sums in fibrations

 In this file, we define when a fibration supports dependent sums. Concretely, this means
 two things.
 - For every morphism `f : x --> y`, substitution along `f` has a left adjoint.
 - These left adjoints are preserved under substitution. This is formulated using the left
   Beck-Chevalley condition.

 Contents
 1. The natural transformation from the left Beck-Chevalley condition
 2. Fibrations with dependent sums
 3. Accessors for dependent sums
 4. Preservation of dependent sums by functors between fibrations

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Local Open Scope cat.

(** * 1. The natural transformation from the left Beck-Chevalley condition *)
Definition left_beck_chevalley_nat_trans
           {C₁ C₂ C₃ C₄ : category}
           {F : C₁ ⟶ C₂}
           {G : C₁ ⟶ C₃}
           {H : C₃ ⟶ C₄}
           {K : C₂ ⟶ C₄}
           (HF : is_right_adjoint F)
           (FL := left_adjoint HF)
           (η₁ := unit_from_right_adjoint HF)
           (HH : is_right_adjoint H)
           (HL := left_adjoint HH)
           (ε₂ := counit_from_right_adjoint HH)
           (τ : nat_z_iso (F ∙ K) (G ∙ H))
  : K ∙ HL ⟹ FL ∙ G
  := nat_trans_comp
       _ _ _
       (post_whisker η₁ (K ∙ HL))
       (nat_trans_comp
          _ _ _
          (pre_whisker
             FL
             (post_whisker
                τ
                HL))
          (pre_whisker (FL ∙ G) ε₂)).

Proposition left_beck_chevalley_nat_trans_ob
            {C₁ C₂ C₃ C₄ : category}
            {F : C₁ ⟶ C₂}
            {G : C₁ ⟶ C₃}
            {H : C₃ ⟶ C₄}
            {K : C₂ ⟶ C₄}
            (HF : is_right_adjoint F)
            (FL := left_adjoint HF)
            (η₁ := unit_from_right_adjoint HF)
            (HH : is_right_adjoint H)
            (HL := left_adjoint HH)
            (ε₂ := counit_from_right_adjoint HH)
            (τ : nat_z_iso (F ∙ K) (G ∙ H))
            (x : C₂)
  : left_beck_chevalley_nat_trans HF HH τ x
    =
    #HL (#K (η₁ x))
    · #HL (τ (FL x))
    · ε₂ (G (FL x)).
Proof.
  apply assoc.
Qed.

(** * 2. Fibrations with dependent sums *)
Section DependentSum.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D).

  Definition dependent_sum
             {x y : C}
             (f : x --> y)
    : UU
    := is_right_adjoint
         (fiber_functor_from_cleaving D HD f).

  Definition comm_nat_z_iso
             {w x y z : C}
             (f : x --> w)
             (g : y --> w)
             (h : z --> y)
             (k : z --> x)
             (p : k · f = h · g)
             (F := fiber_functor_from_cleaving D HD f : D[{w}] ⟶ D[{x}])
             (G := fiber_functor_from_cleaving D HD g : D[{w}] ⟶ D[{y}])
             (H := fiber_functor_from_cleaving D HD h : D[{y}] ⟶ D[{z}])
             (K := fiber_functor_from_cleaving D HD k : D[{x}] ⟶ D[{z}])
    : nat_z_iso (F ∙ K) (G ∙ H)
    := nat_z_iso_comp
         (fiber_functor_from_cleaving_comp_nat_z_iso _ _ _)
         (nat_z_iso_comp
            (fiber_functor_on_eq_nat_z_iso HD p)
            (nat_z_iso_inv
               (fiber_functor_from_cleaving_comp_nat_z_iso _ _ _))).

  Proposition comm_nat_z_iso_ob
              {w x y z : C}
              (f : x --> w)
              (g : y --> w)
              (h : z --> y)
              (k : z --> x)
              (p : k · f = h · g)
              (F := fiber_functor_from_cleaving D HD f : D[{w}] ⟶ D[{x}])
              (G := fiber_functor_from_cleaving D HD g : D[{w}] ⟶ D[{y}])
              (H := fiber_functor_from_cleaving D HD h : D[{y}] ⟶ D[{z}])
              (K := fiber_functor_from_cleaving D HD k : D[{x}] ⟶ D[{z}])
              (φ : D[{w}])
    : comm_nat_z_iso f g h k p φ
      =
      fiber_functor_from_cleaving_comp _ _ _ φ
      · fiber_functor_on_eq HD p φ
      · fiber_functor_from_cleaving_comp_inv _ _ _ φ.
  Proof.
    apply assoc.
  Qed.

  Definition left_beck_chevalley
             {w x y z : C}
             (f : x --> w)
             (g : y --> w)
             (h : z --> y)
             (k : z --> x)
             (p : k · f = h · g)
             (L₁ : dependent_sum f)
             (L₂ : dependent_sum h)
    : UU
    := ∏ (a : D[{x}]),
       is_z_isomorphism
         (left_beck_chevalley_nat_trans L₁ L₂ (comm_nat_z_iso f g h k p) a).

  Proposition isaprop_left_beck_chevalley
              {w x y z : C}
              (f : x --> w)
              (g : y --> w)
              (h : z --> y)
              (k : z --> x)
              (p : k · f = h · g)
              (L₁ : dependent_sum f)
              (L₂ : dependent_sum h)
    : isaprop (left_beck_chevalley f g h k p L₁ L₂).
  Proof.
    use impred ; intro.
    apply isaprop_is_z_isomorphism.
  Qed.

  Definition has_dependent_sums
    : UU
    := ∑ (L : ∏ (x y : C) (f : x --> y), dependent_sum f),
       ∏ (w x y z : C)
         (f : x --> w)
         (g : y --> w)
         (h : z --> y)
         (k : z --> x)
         (p : k · f = h · g)
         (H : isPullback p),
       left_beck_chevalley f g h k p (L _ _ f) (L _ _ h).
End DependentSum.

(** * 3. Accessors for dependent sums *)
Section DependentSum.
  Context {C : category}
          {D : disp_cat C}
          {HD : cleaving D}
          (S : has_dependent_sums HD)
          {x y : C}
          (f : x --> y).

  Definition dep_sum
             (xx : D[{x}])
    : D[{y}]
    := left_adjoint (pr1 S x y f) xx.

  Definition dep_sum_unit
             (xx : D[{x}])
    : xx -->[ identity x ] fiber_functor_from_cleaving D HD f (dep_sum xx)
    := unit_from_right_adjoint (pr1 S x y f) xx.

  Definition dep_sum_counit
             (yy : D[{y}])
    : dep_sum (fiber_functor_from_cleaving D HD f yy) -->[ identity y ] yy
    := counit_from_right_adjoint (pr1 S x y f) yy.
End DependentSum.

(** * 4. Preservation of dependent sums by functors between fibrations *)
Definition preserves_dependent_sums
           {C₁ C₂ : category}
           {D₁ : disp_cat C₁}
           {HD₁ : cleaving D₁}
           {D₂ : disp_cat C₂}
           {HD₂ : cleaving D₂}
           {F : C₁ ⟶ C₂}
           (FF : cartesian_disp_functor F D₁ D₂)
           (L₁ : has_dependent_sums HD₁)
           (L₂ : has_dependent_sums HD₂)
  : UU
  := ∏ (x y : C₁)
       (f : x --> y)
       (a : D₁[{x}]),
     is_z_isomorphism
       (left_beck_chevalley_nat_trans
          (pr1 L₁ x y f)
          (pr1 L₂ (F x) (F y) (#F f))
          (nat_z_iso_inv
             (fiber_functor_natural_nat_z_iso HD₁ HD₂ FF f))
          a).

Proposition isaprop_preserves_dependent_sums
            {C₁ C₂ : category}
            {D₁ : disp_cat C₁}
            {HD₁ : cleaving D₁}
            {D₂ : disp_cat C₂}
            {HD₂ : cleaving D₂}
            {F : C₁ ⟶ C₂}
            (FF : cartesian_disp_functor F D₁ D₂)
            (L₁ : has_dependent_sums HD₁)
            (L₂ : has_dependent_sums HD₂)
  : isaprop (preserves_dependent_sums FF L₁ L₂).
Proof.
  do 4 (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.
