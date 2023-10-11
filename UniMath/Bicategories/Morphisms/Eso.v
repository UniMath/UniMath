(*****************************************************************************

 Eso 1-cells

 One way to define epimorphisms in categories, is via 'strong epimorphisms.
 A strong epimorphism is a morphism that has a lifting property with respect
 to monomorphisms.
 We can generalize this definition to bicategories since fully faithful 1-cells
 generalize monomorphisms. This gives rise to the notion of eso 1-cells.

 Usually, eso 1-cells are defined as follows:

    a 1-cell `f : b₁ --> b₂` is eso if for all fully faithful `m : c₁ --> c₂`
    the follow square is a weak pullback of categories

       B(b₁, c₁) -------------> B(b₁, c₂)
           |                        |
           |                        |
           V                        V
       B(b₂, c₁) -------------> B(b₂, c₂)

 We also consider an alternative definition in which we say that the canonical
 map from `B(b₁, c₁)` to the iso-comma category is an equivalence. We can then
 construct esos by using that fully faithful and essentially surjective
 functors are equivalences if the involved categories are univalent. From this
 formulation, we can also deduce a universal mapping property.

 For both definitions, we use the notion of orthogonality for 1-cells in
 bicategories.

 In this file, we consider both definitions, and we show that they are indeed
 equivalent.

 Contents
 1. Esos
 2. Constructing esos
 3. Projections for esos
 4. Esos via pullbacks
 5. Equivalence of the definitions
 6. (eso, ff)-factorization
 7. Closure under pullbacks

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderInvertibles.
Require Import UniMath.Bicategories.OrthogonalFactorization.Orthogonality.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Import PullbackFunctions.Notations.
Require Import UniMath.Bicategories.Limits.PullbackEquivalences.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.

Local Open Scope cat.

Section EsoMorphisms.
  Context {B : bicat}
          {b₁ b₂ : B}
          (f : b₁ --> b₂).

  (**
   1. Esos
   *)

  Definition is_eso
    : UU
    := ∏ (c₁ c₂ : B)
         (m : c₁ --> c₂)
         (Hm : fully_faithful_1cell m),
       f ⊥ m.

  Definition isaprop_is_eso
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop is_eso.
  Proof.
    use impred ; intro c₁.
    use impred ; intro c₂.
    use impred ; intro m.
    use impred ; intro H.
    exact (isaprop_orthogonal f m HB_2_1).
  Defined.

  (**
   2. Constructing esos
   *)

  (**
   To construct an eso, one should do 3 things.
   First of all, one needs to construct a lift for diagrams of the following shape

              g₁
        b₁ -------> c₁
        |           |
      f |           | m
        |           |
        V           V
        b₂ -------> c₂
              g₂

   where m is a fully faithful 1-cell. This diagram commutes up to an invertible 2-cell.
   The resulting triangles should commute up to an invertible 2-cell and the obvious
   coherency must be satisfied up to equality.

   This expresses that the relevant functor is essentially surjective.
   *)
  Definition is_eso_essentially_surjective
    : UU
    := ∏ (c₁ c₂ : B)
         (m : c₁ --> c₂)
         (Hm : fully_faithful_1cell m)
         (g₁ : b₁ --> c₁)
         (g₂ : b₂ --> c₂)
         (α : invertible_2cell (g₁ · m) (f · g₂)),
       ∑ (l : b₂ --> c₁)
         (ζ₁ : invertible_2cell (f · l) g₁)
         (ζ₂ : invertible_2cell (l · m) g₂),
       (ζ₁ ▹ m) • α = rassociator _ _ _ • (f ◃ ζ₂).

  (**
   The second thing allows us to construct 2-cells between lifts.

   This expresses that the relevant functor is full.
   *)
  Definition is_eso_full
    : UU
    := ∏ (c₁ c₂ : B)
         (m : c₁ --> c₂)
         (Hm : fully_faithful_1cell m)
         (l₁ l₂ : b₂ --> c₁)
         (k₁ : f · l₁ ==> f · l₂)
         (k₂ : l₁ · m ==> l₂ · m)
         (p : (k₁ ▹ m) • rassociator _ _ _
              =
              rassociator _ _ _ • (f ◃ k₂)),
       ∑ (ξ : l₁ ==> l₂),
       f ◃ ξ = k₁
       ×
       ξ ▹ m = k₂.

  (**
   The last thing allows us to prove that 2-cells between lifts are equal.

   This expresses that the relevant functor is faithful.
   *)
  Definition is_eso_faithful
    : UU
    := ∏ (c₁ c₂ : B)
         (m : c₁ --> c₂)
         (Hm : fully_faithful_1cell m)
         (l₁ l₂ : b₂ --> c₁)
         (ζ₁ ζ₂ : l₁ ==> l₂),
       f ◃ ζ₁ = f ◃ ζ₂
       →
       ζ₁ ▹ m = ζ₂ ▹ m
       →
       ζ₁ = ζ₂.

  (**
   Now we can give a constructor for eso morphisms if the bicategory is locally univalent.

   Note that local univalence is needed so that we can get an equivalence from functors
   that are essentially surjective and fully faithful.
   *)
  Definition make_is_eso
             (HB_2_1 : is_univalent_2_1 B)
             (H₁ : is_eso_full)
             (H₂ : is_eso_faithful)
             (H₃ : is_eso_essentially_surjective)
    : is_eso.
  Proof.
    intros c₁ c₂ m Hm.
    use make_orthogonal.
    - exact HB_2_1.
    - exact (H₁ c₁ c₂ m Hm).
    - exact (H₂ c₁ c₂ m Hm).
    - exact (H₃ c₁ c₂ m Hm).
  Defined.

  (**
   3. Projections for esos
   *)
  Section Projections.
    Context (H : is_eso).

    (** Lifting property for for 1-cells *)
    Section LiftOne.
      Context {c₁ c₂ : B}
              {m : c₁ --> c₂}
              (Hm : fully_faithful_1cell m)
              (g₁ : b₁ --> c₁)
              (g₂ : b₂ --> c₂)
              (α : invertible_2cell (g₁ · m) (f · g₂)).

      Definition is_eso_lift_1
        : b₂ --> c₁
        := orthogonal_lift_1 (H c₁ c₂ m Hm) g₁ g₂ α.

      Definition is_eso_lift_1_comm_left
        : invertible_2cell (f · is_eso_lift_1) g₁
        := orthogonal_lift_1_comm_left (H c₁ c₂ m Hm) g₁ g₂ α.

      Definition is_eso_lift_1_comm_right
        : invertible_2cell (is_eso_lift_1 · m) g₂
        := orthogonal_lift_1_comm_right (H c₁ c₂ m Hm) g₁ g₂ α.

      Definition is_eso_lift_1_eq
        : (is_eso_lift_1_comm_left ▹ m) • α
          =
          rassociator _ _ _ • (f ◃ is_eso_lift_1_comm_right)
        := orthogonal_lift_1_eq (H c₁ c₂ m Hm) g₁ g₂ α.
    End LiftOne.

    (** Lifting property for for 2-cells *)
    Section LiftTwo.
      Context {c₁ c₂ : B}
              {m : c₁ --> c₂}
              (Hm : fully_faithful_1cell m)
              (l₁ l₂ : b₂ --> c₁)
              (k₁ : f · l₁ ==> f · l₂)
              (k₂ : l₁ · m ==> l₂ · m)
              (p : (k₁ ▹ m) • rassociator _ _ _
                   =
                   rassociator _ _ _ • (f ◃ k₂)).

      Definition is_eso_lift_2
        : l₁ ==> l₂
        := orthogonal_lift_2 (H c₁ c₂ m Hm) l₁ l₂ k₁ k₂ p.

      Definition is_eso_lift_2_left
        : f ◃ is_eso_lift_2 = k₁
        := orthogonal_lift_2_left (H c₁ c₂ m Hm) l₁ l₂ k₁ k₂ p.

      Definition is_eso_lift_2_right
        : is_eso_lift_2 ▹ m = k₂
        := orthogonal_lift_2_right (H c₁ c₂ m Hm) l₁ l₂ k₁ k₂ p.
    End LiftTwo.

    (** Lifting property for for equalities *)
    Definition is_eso_lift_eq
               {c₁ c₂ : B}
               {m : c₁ --> c₂}
               (Hm : fully_faithful_1cell m)
               {l₁ l₂ : b₂ --> c₁}
               (ζ₁ ζ₂ : l₁ ==> l₂)
               (p₁ : f ◃ ζ₁ = f ◃ ζ₂)
               (p₂ : ζ₁ ▹ m = ζ₂ ▹ m)
      : ζ₁ = ζ₂.
    Proof.
      exact (orthogonal_lift_eq (H c₁ c₂ m Hm) ζ₁ ζ₂ p₁ p₂).
    Qed.
  End Projections.

  (**
   4. Esos via pullbacks
   *)
  Definition is_eso_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : UU
    := ∏ (c₁ c₂ : B)
         (m : c₁ --> c₂)
         (Hm : fully_faithful_1cell m),
       orthogonal_via_pb f m HB_2_1.

  Definition isaprop_is_eso_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop (is_eso_via_pb HB_2_1).
  Proof.
    use impred ; intro c₁.
    use impred ; intro c₂.
    use impred ; intro m.
    use impred ; intro Hm.
    exact (isaprop_orthogonal_via_pb f m HB_2_1).
  Defined.

  Definition is_eso_weq_is_eso_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : is_eso ≃ is_eso_via_pb HB_2_1.
  Proof.
    use weqonsecfibers ; intro c₁.
    use weqonsecfibers ; intro c₂.
    use weqonsecfibers ; intro m.
    use weqonsecfibers ; intro Hm₁.
    exact (orthogonal_weq_orthogonal_via_pb f m HB_2_1).
  Defined.
End EsoMorphisms.

(**
 6. (eso, ff)-factorization
 *)
Definition eso_ff_factorization
           (B : bicat)
    : UU
  := ∏ (b₁ b₂ : B)
       (f : b₁ --> b₂),
     ∑ (im : B)
       (f' : b₁ --> im)
       (m : im --> b₂),
     is_eso f'
     ×
     fully_faithful_1cell m
     ×
     invertible_2cell (f' · m) f.

(**
 7. Closure under pullbacks
 *)
Definition is_eso_closed_under_pb
           (B : bicat_with_pb)
  : UU
  := ∏ (x y z : B)
       (f : x --> z)
       (Hf : is_eso f)
       (g : y --> z),
     is_eso (π₂ : f /≃ g --> y).
