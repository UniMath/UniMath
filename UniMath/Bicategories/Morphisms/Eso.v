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
  Definition is_eso_via_pb_cone
             (HB_2_1 : is_univalent_2_1 B)
             {c₁ c₂ : B}
             (m : c₁ --> c₂)
             (Hm : fully_faithful_1cell m)
    : @pb_cone
        bicat_of_univ_cats
        (univ_hom HB_2_1 b₁ c₁)
        (univ_hom HB_2_1 b₂ c₂)
        (univ_hom HB_2_1 b₁ c₂)
        (post_comp b₁ m)
        (pre_comp c₂ f).
  Proof.
    use make_pb_cone.
    - exact (univ_hom HB_2_1 b₂ c₁).
    - exact (pre_comp c₁ f).
    - exact (post_comp b₂ m).
    - use nat_z_iso_to_invertible_2cell.
      exact (pre_comp_post_comp_commute_z_iso f m).
  Defined.

  Definition is_eso_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : UU
    := ∏ (c₁ c₂ : B)
         (m : c₁ --> c₂)
         (Hm : fully_faithful_1cell m),
       has_pb_ump (is_eso_via_pb_cone HB_2_1 m Hm).

  Definition isaprop_is_eso_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop (is_eso_via_pb HB_2_1).
  Proof.
    use impred ; intro c₁.
    use impred ; intro c₂.
    use impred ; intro m.
    use impred ; intro Hm.
    use isaprop_has_pb_ump.
    exact univalent_cat_is_univalent_2_1.
  Defined.

  (**
   5. Equivalence of the definitions
   *)
  Definition is_eso_to_is_eso_via_pb
             (HB_2_1 : is_univalent_2_1 B)
             (Hf : is_eso)
    : is_eso_via_pb HB_2_1.
  Proof.
    intros c₁ c₂ m Hm.
    specialize (Hf c₁ c₂ m Hm).
    use (left_adjoint_equivalence_to_pb
           _ _ _
           (@iso_comma_has_pb_ump
               (univ_hom HB_2_1 b₁ c₁)
               (univ_hom HB_2_1 b₂ c₂)
               (univ_hom HB_2_1 b₁ c₂)
               (post_comp b₁ m)
               (pre_comp c₂ f))
           _
           _).
    - exact univalent_cat_is_univalent_2_0.
    - exact (orthogonal_functor f m).
    - exact (@equiv_cat_to_adj_equiv
               (univ_hom HB_2_1 b₂ c₁)
               (@univalent_iso_comma
                  (univ_hom HB_2_1 b₁ c₁)
                  (univ_hom HB_2_1 b₂ c₂)
                  (univ_hom HB_2_1 b₁ c₂)
                  (post_comp b₁ m)
                  (pre_comp c₂ f))
               (orthogonal_functor f m)
               Hf).
    - use nat_z_iso_to_invertible_2cell.
      use make_nat_z_iso.
      + use make_nat_trans.
        * exact (λ _, id2 _).
        * abstract
            (intros h₁ h₂ α ; cbn ;
             rewrite id2_left, id2_right ;
             apply idpath).
      + intro.
        use is_inv2cell_to_is_z_iso ; cbn.
        is_iso.
    - use nat_z_iso_to_invertible_2cell.
      use make_nat_z_iso.
      + use make_nat_trans.
        * exact (λ _, id2 _).
        * abstract
            (intros h₁ h₂ α ; cbn ;
             rewrite id2_left, id2_right ;
             apply idpath).
      + intro.
        use is_inv2cell_to_is_z_iso ; cbn.
        is_iso.
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         rewrite id2_rwhisker, lwhisker_id2 ;
         rewrite !id2_left, !id2_right ;
         apply idpath).
  Defined.

  Definition is_eso_via_pb_to_is_eso_nat_trans
             (HB_2_1 : is_univalent_2_1 B)
             {c₁ c₂ : B}
             {m : c₁ --> c₂}
             (Hm : fully_faithful_1cell m)
    : orthogonal_functor f m
      ⟹
      pr1 (pb_ump_mor
             (@iso_comma_has_pb_ump
                (univ_hom HB_2_1 b₁ c₁)
                (univ_hom HB_2_1 b₂ c₂)
                (univ_hom HB_2_1 b₁ c₂)
                (post_comp b₁ m)
                (pre_comp c₂ f))
             (is_eso_via_pb_cone HB_2_1 m Hm)).
  Proof.
    use make_nat_trans.
    - intro h.
      simple refine ((id2 _ ,, id2 _) ,, _).
      abstract
        (cbn ;
         rewrite id2_rwhisker, lwhisker_id2, id2_left, id2_right ;
         apply idpath).
    - abstract
        (intros h₁ h₂ γ ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         cbn ;
         rewrite !id2_left, !id2_right ;
         apply idpath).
  Defined.

  Definition is_eso_via_pb_to_is_eso
             (HB_2_1 : is_univalent_2_1 B)
             (Hf : is_eso_via_pb HB_2_1)
    : is_eso.
  Proof.
    intros c₁ c₂ m Hm.
    specialize (Hf c₁ c₂ m Hm).
    apply (@adj_equiv_to_equiv_cat
             (univ_hom HB_2_1 b₂ c₁)
             (@univalent_iso_comma
                (univ_hom HB_2_1 b₁ c₁)
                (univ_hom HB_2_1 b₂ c₂)
                (univ_hom HB_2_1 b₁ c₂)
                (post_comp b₁ m)
                (pre_comp c₂ f))
             (orthogonal_functor f m)).
    pose (pb_ump_mor_left_adjoint_equivalence
            _
            _
            (@iso_comma_has_pb_ump
               (univ_hom HB_2_1 b₁ c₁)
               (univ_hom HB_2_1 b₂ c₂)
               (univ_hom HB_2_1 b₁ c₂)
               (post_comp b₁ m)
               (pre_comp c₂ f))
            Hf)
      as p.
    use (left_adjoint_equivalence_invertible p).
    - exact (is_eso_via_pb_to_is_eso_nat_trans HB_2_1 Hm).
    - use is_nat_z_iso_to_is_invertible_2cell.
      intro.
      use is_z_iso_iso_comma.
      + use is_inv2cell_to_is_z_iso ; cbn.
        is_iso.
      + use is_inv2cell_to_is_z_iso ; cbn.
        is_iso.
  Defined.

  Definition is_eso_weq_is_eso_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : is_eso ≃ is_eso_via_pb HB_2_1.
  Proof.
    use weqimplimpl.
    - exact (is_eso_to_is_eso_via_pb HB_2_1).
    - exact (is_eso_via_pb_to_is_eso HB_2_1).
    - exact (isaprop_is_eso HB_2_1).
    - exact (isaprop_is_eso_via_pb HB_2_1).
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
       (m : im --> b₂)
       (f' : b₁ --> im),
     fully_faithful_1cell m
     ×
     is_eso f'
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
