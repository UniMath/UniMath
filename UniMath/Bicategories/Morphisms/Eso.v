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
 formulation, we can also deduce a universla mapping property.

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
  Definition pre_comp_post_comp_commute
             {c₁ c₂ : B}
             (m : c₁ --> c₂)
    : pre_comp c₁ f ∙ post_comp b₁ m
      ⟹
      post_comp b₂ m ∙ pre_comp c₂ f.
  Proof.
    use make_nat_trans.
    - exact (λ _, rassociator _ _ _).
    - abstract
        (intros h₁ h₂ α ;
         cbn ;
         rewrite rwhisker_lwhisker_rassociator ;
         apply idpath).
  Defined.

  Definition pre_comp_post_comp_commute_iso
             {c₁ c₂ : B}
             (m : c₁ --> c₂)
    : nat_iso
        (pre_comp c₁ f ∙ post_comp b₁ m)
        (post_comp b₂ m ∙ pre_comp c₂ f).
  Proof.
    use make_nat_iso.
    - exact (pre_comp_post_comp_commute m).
    - intro.
      use is_inv2cell_to_is_iso ; cbn.
      is_iso.
  Defined.

  Definition is_eso_functor
             {c₁ c₂ : B}
             (m : c₁ --> c₂)
    : hom b₂ c₁ ⟶ iso_comma (post_comp b₁ m) (pre_comp c₂ f).
  Proof.
    use iso_comma_ump1.
    - exact (pre_comp c₁ f).
    - exact (post_comp b₂ m).
    - exact (pre_comp_post_comp_commute_iso m).
  Defined.

  Definition is_eso
    : UU
    := ∏ (c₁ c₂ : B)
         (m : c₁ --> c₂)
         (Hm : fully_faithful_1cell m),
       adj_equivalence_of_cats
         (is_eso_functor m).

  Definition isaprop_is_eso
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop is_eso.
  Proof.
    use impred ; intro c₁.
    use impred ; intro c₂.
    use impred ; intro m.
    use impred ; intro H.
    use (isofhlevelweqf
             1
             (@adj_equiv_is_equiv_cat
                (univ_hom HB_2_1 b₂ c₁)
                (@univalent_iso_comma
                   (univ_hom HB_2_1 b₁ c₁)
                   (univ_hom HB_2_1 b₂ c₂)
                   (univ_hom HB_2_1 b₁ c₂)
                   (post_comp b₁ m)
                   (pre_comp c₂ f))
                (is_eso_functor m))).
    apply isaprop_left_adjoint_equivalence.
    exact univalent_cat_is_univalent_2_1.
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
  Section MakeEso.
    Context (HB_2_1 : is_univalent_2_1 B)
            (H₁ : is_eso_full)
            (H₂ : is_eso_faithful)
            (H₃ : is_eso_essentially_surjective).

    Section MakeEsoHelp.
      Context {c₁ c₂ : B}
              {m : c₁ --> c₂}
              (Hm : fully_faithful_1cell m).

      Definition make_is_eso_full
        : full (is_eso_functor m).
      Proof.
        intros l₁ l₂.
        intro k.
        apply hinhpr.
        simple refine (_ ,, _) ; cbn.
        - exact (pr1 (H₁ c₁ c₂ m Hm l₁ l₂ (pr11 k) (pr21 k) (pr2 k))).
        - abstract
            (use subtypePath ; [ intro ; apply cellset_property | ] ;
             cbn ;
             exact (pathsdirprod
                      (pr12 (H₁ c₁ c₂ m Hm l₁ l₂ (pr11 k) (pr21 k) (pr2 k)))
                      (pr22 (H₁ c₁ c₂ m Hm l₁ l₂ (pr11 k) (pr21 k) (pr2 k))))).
      Defined.

      Definition make_is_eso_faithful
        : faithful (is_eso_functor m).
      Proof.
        intros l₁ l₂.
        intro im.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use (H₂ c₁ c₂ m Hm l₁ l₂ (pr1 ζ₁) (pr1 ζ₂)).
        - exact (maponpaths (λ z, pr11 z) (pr2 ζ₁)
                 @ !(maponpaths (λ z, pr11 z) (pr2 ζ₂))).
        - exact (maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr2 ζ₁)
                            @ !(maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr2 ζ₂))).
      Qed.

      Definition make_is_eso_fully_faithful
        : fully_faithful (is_eso_functor m).
      Proof.
        use full_and_faithful_implies_fully_faithful.
        split.
        - exact make_is_eso_full.
        - exact make_is_eso_faithful.
      Defined.

      Definition make_is_eso_essentially_surjective
        : essentially_surjective (is_eso_functor m).
      Proof.
        intros h.
        pose (ℓ := H₃ c₁ c₂ m Hm (pr11 h) (pr21 h) (iso_to_inv2cell (pr2 h))).
        apply hinhpr.
        simple refine (_ ,, _).
        - exact (pr1 ℓ).
        - use make_iso.
          + simple refine ((_ ,, _) ,, _) ; cbn.
            * exact (pr12 ℓ).
            * exact (pr122 ℓ).
            * exact (pr222 ℓ).
          + use is_iso_iso_comma.
            * use is_inv2cell_to_is_iso.
              apply property_from_invertible_2cell.
            * use is_inv2cell_to_is_iso.
              apply property_from_invertible_2cell.
      Defined.
    End MakeEsoHelp.

    Definition make_is_eso
      : is_eso.
    Proof.
      intros c₁ c₂ m Hm.
      use rad_equivalence_of_cats.
      - use is_univ_hom.
        exact HB_2_1.
      - exact (make_is_eso_fully_faithful Hm).
      - exact (make_is_eso_essentially_surjective Hm).
    Defined.
  End MakeEso.

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
        := right_adjoint (H c₁ c₂ m Hm) ((g₁ ,, g₂) ,, inv2cell_to_iso α).

      Definition is_eso_lift_1_comm_left
        : invertible_2cell (f · is_eso_lift_1) g₁.
      Proof.
        apply iso_to_inv2cell.
        exact (functor_on_iso
                (iso_comma_pr1 _ _)
                (counit_pointwise_iso_from_adj_equivalence
                   (H c₁ c₂ m Hm)
                   ((g₁ ,, g₂) ,, inv2cell_to_iso α))).
      Defined.

      Definition is_eso_lift_1_comm_right
        : invertible_2cell (is_eso_lift_1 · m) g₂.
      Proof.
        apply iso_to_inv2cell.
        exact (functor_on_iso
                 (iso_comma_pr2 _ _)
                 (counit_pointwise_iso_from_adj_equivalence
                    (H c₁ c₂ m Hm)
                    ((g₁ ,, g₂) ,, inv2cell_to_iso α))).
      Defined.

      Definition is_eso_lift_1_eq
        : (is_eso_lift_1_comm_left ▹ m) • α
          =
          rassociator _ _ _ • (f ◃ is_eso_lift_1_comm_right)
        := pr2 (counit_from_left_adjoint
                  (pr1 (H c₁ c₂ m Hm))
                  ((g₁ ,, g₂) ,, inv2cell_to_iso α)).
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

      Let R : iso_comma (post_comp b₁ m) (pre_comp c₂ f) ⟶ hom b₂ c₁
        := right_adjoint (H c₁ c₂ m Hm).

      Let φ : iso_comma (post_comp b₁ m) (pre_comp c₂ f)
        := (f · l₁ ,, l₁ · m) ,, inv2cell_to_iso (rassociator_invertible_2cell _ _ _).
      Let ψ : iso_comma (post_comp b₁ m) (pre_comp c₂ f)
        := (f · l₂ ,, l₂ · m) ,, inv2cell_to_iso (rassociator_invertible_2cell _ _ _).
      Let μ : φ --> ψ
        := (k₁ ,, k₂) ,, p.

      Let η₁ : l₁ ==> R φ
        := unit_from_left_adjoint (H c₁ c₂ m Hm) l₁.
      Let η₂ : R ψ ==> l₂
        := iso_to_inv2cell (unit_pointwise_iso_from_adj_equivalence (H c₁ c₂ m Hm) l₂)^-1.
      Let ε₁ : f · R φ ==> f · l₁
        := pr11 (counit_from_left_adjoint (pr1 (H c₁ c₂ m Hm)) φ).
      Let ε₂ : f · R ψ ==> f · l₂
        := pr11 (counit_from_left_adjoint (pr1 (H c₁ c₂ m Hm)) ψ).
      Let ε₁' : R φ · m ==> l₁ · m
        := pr21 (counit_from_left_adjoint (pr1 (H c₁ c₂ m Hm)) φ).
      Let ε₂' : R ψ · m ==> l₂ · m
        := pr21 (counit_from_left_adjoint (pr1 (H c₁ c₂ m Hm)) ψ).

      Definition is_eso_lift_2
        : l₁ ==> l₂
        := η₁ • #R μ • η₂.

      Local Lemma is_eso_lift_2_counit_invertible
        : is_invertible_2cell ε₂.
      Proof.
        exact (property_from_invertible_2cell
                 (iso_to_inv2cell
                    (functor_on_iso
                       (iso_comma_pr1 _ _)
                       (counit_pointwise_iso_from_adj_equivalence (H c₁ c₂ m Hm) ψ)))).
      Qed.

      Local Lemma is_eso_lift_2_left_path_1
        : (f ◃ #R μ) • ε₂ = ε₁ • k₁.
      Proof.
        exact (maponpaths
                 (λ z, pr11 z)
                 (nat_trans_ax (counit_from_left_adjoint (H c₁ c₂ m Hm)) _ _ μ)).
      Qed.

      Local Lemma is_eso_lift_2_left_path_2
        : (f ◃ η₁) • ε₁ = id2 _.
      Proof.
        exact (maponpaths
                 (λ z, pr11 z)
                 (triangle_id_left_ad (pr21 (H c₁ c₂ m Hm)) l₁)).
      Qed.

      Definition is_eso_lift_2_left
        : f ◃ is_eso_lift_2 = k₁.
      Proof.
        unfold is_eso_lift_2.
        rewrite <- !lwhisker_vcomp.
        use vcomp_move_R_Mp.
        {
          unfold η₂.
          is_iso.
        }
        use (vcomp_rcancel ε₂).
        {
          exact is_eso_lift_2_counit_invertible.
        }
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          exact is_eso_lift_2_left_path_1.
        }
        cbn.
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          exact is_eso_lift_2_left_path_2.
        }
        rewrite id2_left.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   (λ z, pr11 z)
                   (triangle_id_left_ad (pr21 (H c₁ c₂ m Hm)) l₂)).
        }
        cbn.
        rewrite id2_right.
        apply idpath.
      Qed.

      Local Lemma is_eso_lift_2_counit_invertible'
        : is_invertible_2cell ε₂'.
      Proof.
        exact (property_from_invertible_2cell
                 (iso_to_inv2cell
                    (functor_on_iso
                       (iso_comma_pr2 _ _)
                       (counit_pointwise_iso_from_adj_equivalence (H c₁ c₂ m Hm) ψ)))).
      Qed.

      Local Lemma is_eso_lift_2_right_path_1
        : (#R μ ▹ m) • ε₂' = ε₁' • k₂.
      Proof.
        exact (maponpaths
                 (λ z, dirprod_pr2 (pr1 z))
                 (nat_trans_ax (counit_from_left_adjoint (H c₁ c₂ m Hm)) _ _ μ)).
      Qed.

      Local Lemma is_eso_lift_2_right_path_2
        : (η₁ ▹ m) • ε₁' = id2 _.
      Proof.
        exact (maponpaths
                 (λ z, dirprod_pr2 (pr1 z))
                 (triangle_id_left_ad (pr21 (H c₁ c₂ m Hm)) l₁)).
      Qed.

      Definition is_eso_lift_2_right
        : is_eso_lift_2 ▹ m = k₂.
      Proof.
        unfold is_eso_lift_2.
        rewrite <- !rwhisker_vcomp.
        use vcomp_move_R_Mp.
        {
          unfold η₂.
          is_iso.
        }
        cbn.
        use (vcomp_rcancel ε₂').
        {
          exact is_eso_lift_2_counit_invertible'.
        }
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          exact is_eso_lift_2_right_path_1.
        }
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          exact is_eso_lift_2_right_path_2.
        }
        rewrite id2_left.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   (λ z, dirprod_pr2 (pr1 z))
                   (triangle_id_left_ad (pr21 (H c₁ c₂ m Hm)) l₂)).
        }
        apply id2_right.
      Qed.
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
      pose (pr2 (fully_faithful_implies_full_and_faithful
                   _ _ _
                   (fully_faithful_from_equivalence _ _ _ (H c₁ c₂ m Hm)))
                l₁ l₂)
        as Heq.
      assert (((f ◃ ζ₁) ▹ m) • rassociator f l₂ m
              =
              rassociator f l₁ m • (f ◃ (ζ₁ ▹ m)))
        as r₁.
      {
        refine (!_).
        apply rwhisker_lwhisker_rassociator.
      }
      assert (((f ◃ ζ₂) ▹ m) • rassociator f l₂ m
              =
              rassociator f l₁ m • (f ◃ (ζ₂ ▹ m)))
        as r₂.
      {
        refine (!_).
        apply rwhisker_lwhisker_rassociator.
      }
      pose (proofirrelevance
              _
              (Heq ((f ◃ ζ₁ ,, ζ₁ ▹ m) ,, r₁)))
        as Hprop.
      refine (maponpaths pr1 (Hprop (_ ,, _) (_ ,, _))).
      - use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        cbn.
        apply idpath.
      - use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        cbn.
        use pathsdirprod.
        + exact (!p₁).
        + exact (!p₂).
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
    - use nat_iso_to_invertible_2cell.
      exact (pre_comp_post_comp_commute_iso m).
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
    - exact (is_eso_functor m).
    - exact (@equiv_cat_to_adj_equiv
               (univ_hom HB_2_1 b₂ c₁)
               (@univalent_iso_comma
                  (univ_hom HB_2_1 b₁ c₁)
                  (univ_hom HB_2_1 b₂ c₂)
                  (univ_hom HB_2_1 b₁ c₂)
                  (post_comp b₁ m)
                  (pre_comp c₂ f))
               (is_eso_functor m)
               Hf).
    - use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      + use make_nat_trans.
        * exact (λ _, id2 _).
        * abstract
            (intros h₁ h₂ α ; cbn ;
             rewrite id2_left, id2_right ;
             apply idpath).
      + intro.
        use is_inv2cell_to_is_iso ; cbn.
        is_iso.
    - use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      + use make_nat_trans.
        * exact (λ _, id2 _).
        * abstract
            (intros h₁ h₂ α ; cbn ;
             rewrite id2_left, id2_right ;
             apply idpath).
      + intro.
        use is_inv2cell_to_is_iso ; cbn.
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
    : is_eso_functor m
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
             (is_eso_functor m)).
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
    - use is_nat_iso_to_is_invertible_2cell.
      intro.
      use is_iso_iso_comma.
      + use is_inv2cell_to_is_iso ; cbn.
        is_iso.
      + use is_inv2cell_to_is_iso ; cbn.
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
