(*****************************************************************************

 Orthogonal factorization systems in bicategory

 In this file, we define the notion of orthogonal factorization system in a
 bicategory. An orthogonal factorization system consists of two classes of maps,
 which we call `L` and `R` respectively. These classes of maps must satisfy
 the following requirements:
 - Each 1-cell can be factorized as a composition of a map in `L` followed by
   a map in `R`. Note that we require strong existence for this factorization
   (via a `∑`-type) instead of ordinary existence (via a `∃`-type).
 - `L` and `R` are closed under invertible 2-cells.
 - Maps in `L` and `R` are orthogonal to each other. This means that we can
   solve lifting problems of the following shape

<<
         b₁ --------> c₁
         |            |
    in L |            | in R
         |            |
         V            V
         b₂ --------> c₂
>>

 In an orthogonal factorization system, factorizations are unique up to unique
 invertible 2-cell. As such, it does not matter whether we use strong existence
 or ordinary existence for the factorizations. In a weak factorization (where
 the factorization are not necessarily unique), this distinction does matter.

 Note that in the literature, the second property (closure under invertible
 2-cells) is often formulated stronger. Suppose, that we have a diagram as
 follows:

<<
         b₁ --------> c₁
         |            |
    in L |            |
         |            |
         V            V
         b₂ --------> c₂
>>

 If `b₁ --> c₁` and `b₂ --> c₂` are adjoint equivalences, then this diagram
 gives rise to an adjoint equivalence in the arrow bicategory. Usually, one
 requires `L` and `R` to be closed under adjoint equivalences in the arrow
 bicategory. However, by assuming univalence, we can simplify this requirement.
 By using equivalence induction on both `b₁ --> c₁` and `b₂ --> c₂`, we can
 assume that both the top and bottom morphism in this diagram are identities.
 This way, we get that `L` and `R` must be closed under invertible 2-cells.

 Finally, we show that every morphism that is both in `L` and `R` must also
 be an adjoint equivalence.

 A source for the definition of orthogonal factorization system in a bicategory
 is "Categorical notions of fibration" by Loregian and Riehl.

 Contents
 1. Factorizations
 2. Orthogonal factorization systems
 3. Builder for orthogonal factorization systems
 4. Projections for orthogonal factorization systems
 5. Properties of orthogonal factorization systems

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.OrthogonalFactorization.Orthogonality.

Local Open Scope cat.

(** * 1. Factorizations *)
Definition factorization_1cell
           {B : bicat}
           (L R : ∏ (x y : B), x --> y → hProp)
           {x y : B}
           (f : x --> y)
  : UU
  := ∑ (a : B)
       (l : x --> a)
       (r : a --> y),
     L _ _ l
     ×
     R _ _ r
     ×
     invertible_2cell (l · r) f.

Definition make_factorization_1cell
           {B : bicat}
           {L R : ∏ (x y : B), x --> y → hProp}
           {x y : B}
           {f : x --> y}
           (a : B)
           (l : x --> a)
           (r : a --> y)
           (Ll : L _ _ l)
           (Rr : R _ _ r)
           (τ : invertible_2cell (l · r) f)
  : factorization_1cell L R f
  := a ,, l ,, r ,, Ll ,, Rr ,, τ.

Coercion factorization_1cell_ob
         {B : bicat}
         {L R : ∏ (x y : B), x --> y → hProp}
         {x y : B}
         {f : x --> y}
         (fact : factorization_1cell L R f)
  : B
  := pr1 fact.

Section ProjectionsFactorization.
  Context {B : bicat}
          {L R : ∏ (x y : B), x --> y → hProp}
          {x y : B}
          {f : x --> y}
          (fact : factorization_1cell L R f).

  Definition factorization_1cell_left
    : x --> fact
    := pr12 fact.

  Definition factorization_1cell_right
    : fact --> y
    := pr122 fact.

  Definition factorization_1cell_left_class
    : L _ _ factorization_1cell_left
    := pr1 (pr222 fact).

  Definition factorization_1cell_right_class
    : R _ _ factorization_1cell_right
    := pr12 (pr222 fact).

  Definition factorization_1cell_commutes
    : invertible_2cell
        (factorization_1cell_left · factorization_1cell_right)
        f
    := pr22 (pr222 fact).
End ProjectionsFactorization.

(** * 2. Orthogonal factorization systems *)
Definition closed_under_invertible_2cell
           {B : bicat}
           (P : ∏ (x y : B), x --> y → hProp)
  : UU
  := ∏ (x y : B)
       (f g : x --> y)
       (τ : invertible_2cell f g),
     P _ _ f
     →
     P _ _ g.

Definition orthogonal_maps
           {B : bicat}
           (L R : ∏ (x y : B), x --> y → hProp)
  : UU
  := ∏ (b₁ b₂ c₁ c₂ : B)
       (f : b₁ --> b₂)
       (g : c₁ --> c₂),
     L _ _ f
     →
     R _ _ g
     →
     f ⊥ g.

Definition orthogonal_factorization_system
           (B : bicat)
  : UU
  := ∑ (L R : ∏ (x y : B), x --> y → hProp),
     (∏ (x y : B) (f : x --> y), factorization_1cell L R f)
     ×
     closed_under_invertible_2cell L
     ×
     closed_under_invertible_2cell R
     ×
     orthogonal_maps L R.

(** * 3. Builder for orthogonal factorization systems *)
Section MakeFactorizationSystem.
  Context {B : bicat}
          (L R : ∏ (x y : B), x --> y → UU)
          (isapropL : ∏ (x y : B) (f : x --> y), isaprop (L _ _ f))
          (isapropR : ∏ (x y : B) (f : x --> y), isaprop (R _ _ f)).

  Let L' : ∏ (x y : B), x --> y → hProp := λ x y f, L x y f ,, isapropL x y f.
  Let R' : ∏ (x y : B), x --> y → hProp := λ x y f, R x y f ,, isapropR x y f.

  Context (fact : ∏ (x y : B) (f : x --> y), factorization_1cell L' R' f)
          (HL : closed_under_invertible_2cell L')
          (HR : closed_under_invertible_2cell R')
          (LR : orthogonal_maps L' R').

  Definition make_orthogonal_factorization_system
    : orthogonal_factorization_system B
    := L' ,, R' ,, fact ,, HL ,, HR ,, LR.
End MakeFactorizationSystem.

(** * 4. Projections for orthogonal factorization systems *)
Section Projections.
  Context {B : bicat}
          (fact_B : orthogonal_factorization_system B).

  Definition orthogonal_left_class
             {x y : B}
             (f : x --> y)
    : hProp
    := pr1 fact_B x y f.

  Definition orthogonal_right_class
             {x y : B}
             (f : x --> y)
    : hProp
    := pr12 fact_B x y f.

  Definition orthogonal_factorization_ob
             {x y : B}
             (f : x --> y)
    : B
    := factorization_1cell_ob (pr122 fact_B x y f).

  Definition orthogonal_factorization_left
             {x y : B}
             (f : x --> y)
    : x --> orthogonal_factorization_ob f
    := factorization_1cell_left (pr122 fact_B x y f).

  Definition orthogonal_factorization_right
             {x y : B}
             (f : x --> y)
    : orthogonal_factorization_ob f --> y
    := factorization_1cell_right (pr122 fact_B x y f).

  Definition orthogonal_factorization_left_class
             {x y : B}
             (f : x --> y)
    : orthogonal_left_class (orthogonal_factorization_left f)
    := factorization_1cell_left_class (pr122 fact_B x y f).

  Definition orthogonal_factorization_right_class
             {x y : B}
             (f : x --> y)
    : orthogonal_right_class (orthogonal_factorization_right f)
    := factorization_1cell_right_class (pr122 fact_B x y f).

  Definition orthogonal_factorization_commutes
             {x y : B}
             (f : x --> y)
    : invertible_2cell
        (orthogonal_factorization_left f · orthogonal_factorization_right f)
        f
    := factorization_1cell_commutes (pr122 fact_B x y f).

  Definition orthogonal_left_inv2cell
             {x y : B}
             (f g : x --> y)
             (τ : invertible_2cell f g)
             (Lf : orthogonal_left_class f)
    : orthogonal_left_class g
    := pr1 (pr222 fact_B) _ _ f g τ Lf.

  Definition orthogonal_right_inv2cell
             {x y : B}
             (f g : x --> y)
             (τ : invertible_2cell f g)
             (Lf : orthogonal_right_class f)
    : orthogonal_right_class g
    := pr12 (pr222 fact_B) _ _ f g τ Lf.

  Definition orthogonal_lifting
             {b₁ b₂ c₁ c₂ : B}
             (f : b₁ --> b₂)
             (g : c₁ --> c₂)
             (Lf : orthogonal_left_class f)
             (Rg : orthogonal_right_class g)
    : f ⊥ g
    := pr22 (pr222 fact_B) _ _ _ _ f g Lf Rg.
End Projections.

(** * 5. Properties of orthogonal factorization systems *)
Section Properties.
  Context {B : bicat}
          (fact_B : orthogonal_factorization_system B)
          {x y : B}
          (f : x --> y)
          (Lf : orthogonal_left_class fact_B f)
          (Rf : orthogonal_right_class fact_B f).

  Let α : invertible_2cell (id₁ _ · f) (f · id₁ _)
    := comp_of_invertible_2cell
         (lunitor_invertible_2cell _)
         (rinvunitor_invertible_2cell _).

  Definition orthogonal_left_right_to_equiv
    : left_equivalence f.
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, _ ,, _) ; cbn.
    - refine (orthogonal_lift_1 _ _ _ α).
      exact (orthogonal_lifting fact_B f f Lf Rf).
    - exact (inv_of_invertible_2cell (orthogonal_lift_1_comm_left _ _ _ α)).
    - exact ((orthogonal_lift_1_comm_right _ _ _ α)).
    - apply property_from_invertible_2cell.
    - apply property_from_invertible_2cell.
  Defined.

  Definition orthogonal_left_right_to_adjequiv
    : left_adjoint_equivalence f.
  Proof.
    use equiv_to_adjequiv.
    exact orthogonal_left_right_to_equiv.
  Defined.
End Properties.
