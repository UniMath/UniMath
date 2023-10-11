(*****************************************************************************

 Orthogonality

 In this file, we define the left and right lifting properties of 1-cells in
 bicategories.

 The context in which we are interested in this notion, is given by orthogonal
 factorization system. In such a factorization, we have two classes of
 morphisms, which we call `L` and `R`. Each 1-cell in the bicategory can be
 factorized as `f · g` where `f` is in `L` and where `g` is in `R`. To
 guarantee that this factorization is unique up to unique invertible 2-cell,
 we require that a lifting property between maps in `L` and maps in `R`.
 This lifting property is expressed via orthogonal morphisms.

 Suppose that we have 1-cells `f : b₁ --> b₂` and `g` : c₁ --> c₂`. Then we
 say that `f` is left orthogonal to `g` (which we write as `f ⊥ g`) if the
 following diagrams is a weak pullback of categories:

<<
       B(b₂, c₁) -------------> B(b₁, c₁)
           |                        |
           |                        |
           V                        V
       B(b₂, c₂) -------------> B(b₁, c₂)
>>

 The maps are given as follows:
 - `B(b₂, c₁) --> B(b₁, c₁)`: precomposition with `f`
 - `B(b₂, c₁) --> B(b₂, c₂)`: postcomposition with `g`
 - `B(b₂, c₂) --> B(b₁, c₂)`: precomposition with `f`
 - `B(b₁, c₁) --> B(b₁, c₂)`: postcomposition with `g`

 Note that weak pullbacks of categories are given by iso-comma categories. We
 express this lifting property by saying that a certain functor is an adjoint
 equivalence of categories ([orthogonal]). This functor ([orthogonal_functor])
 has type: `hom b₂ c₁ ⟶ iso_comma (post_comp b₁ g) (pre_comp c₂ f)`, so it
 is the functor that we obtain from the universal property of the iso-comma
 category.

 To verify whether two classes of morphisms are orthogonal, one needs to
 establish that a certain functor is an equivalence. To do so, it suffices to
 check that this functor is essentially surjective and fully faithful (assuming
 that the bicategory is locally univalent. Each of these properties has a
 rather natural interpretation.
 - Essential surjectivity ([orthogonal_essentially_surjective]): if we are given
   a square as follows

<<
       b₁ ------------> c₁
       |                |
     f |                | g
       |                |
       V                V
       b₂ ------------> c₂
>>

   where `f` is in the left class and where `g` is in the right class, then
   we can find a lift `l : b₂ --> c₁` such that the resulting triangle commute
   up to invertible 2-cell (and some coherence condition).
 - Fullness ([orthogonal_full]): if we are given two lifts `l₁, l₂ : b₂ --> c₁`,
   then we can obtain a 2-cell `l₁ ==> l₂` if we have 2-cells `f · l₁ ==> f · l₂`
   and `l₁ · g ==> l₂ · g` (again requiring some coherence condition)
 - Faithfulness ([orthogonal_faithful]) expresses the uniqueness of the 2-cell
   obtained from fullness.

 Finally, we show that the definition in this file, is equivalent to definition
 of orthogonality expressed via pullbacks.

 Contents
 1. Orthogonality
 2. Constructing orthogonal morphisms
 3. Projections of orthogonal morphisms
 3.1. Lifting property for for 1-cells
 3.2. Lifting property for for 2-cells
 3.3. Lifting property for for equalities
 4. Orthogonality via pullbacks
 5. Equivalence of the definitions

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
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
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderInvertibles.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Import PullbackFunctions.Notations.
Require Import UniMath.Bicategories.Limits.PullbackEquivalences.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.

Local Open Scope cat.

Section Comp.
  Context {B : bicat}.

  Definition pre_comp_post_comp_commute
             {b₁ b₂ : B}
             (f : b₁ --> b₂)
             {c₁ c₂ : B}
             (g : c₁ --> c₂)
    : pre_comp c₁ f ∙ post_comp b₁ g
      ⟹
      post_comp b₂ g ∙ pre_comp c₂ f.
  Proof.
    use make_nat_trans.
    - exact (λ _, rassociator _ _ _).
    - abstract
        (intros h₁ h₂ α ;
         cbn ;
         rewrite rwhisker_lwhisker_rassociator ;
         apply idpath).
  Defined.

  Definition pre_comp_post_comp_commute_z_iso
             {b₁ b₂ : B}
             (f : b₁ --> b₂)
             {c₁ c₂ : B}
             (g : c₁ --> c₂)
    : nat_z_iso
        (pre_comp c₁ f ∙ post_comp b₁ g)
        (post_comp b₂ g ∙ pre_comp c₂ f).
  Proof.
    use make_nat_z_iso.
    - exact (pre_comp_post_comp_commute f g).
    - intro.
      use is_inv2cell_to_is_z_iso ; cbn.
      is_iso.
  Defined.
End Comp.

(** * 1. Orthogonality *)
Definition orthogonal_functor
           {B : bicat}
           {b₁ b₂ : B}
           (f : b₁ --> b₂)
           {c₁ c₂ : B}
           (g : c₁ --> c₂)
  : hom b₂ c₁ ⟶ iso_comma (post_comp b₁ g) (pre_comp c₂ f).
Proof.
  use iso_comma_ump1.
  - exact (pre_comp c₁ f).
  - exact (post_comp b₂ g).
  - exact (pre_comp_post_comp_commute_z_iso f g).
Defined.

Definition orthogonal
           {B : bicat}
           {b₁ b₂ c₁ c₂ : B}
           (f : b₁ --> b₂)
           (g : c₁ --> c₂)
  : UU
  := adj_equivalence_of_cats (orthogonal_functor f g).

Notation "f ⊥ g" := (orthogonal f g) (at level 60) : cat.

Definition isaprop_orthogonal
           {B : bicat}
           {b₁ b₂ c₁ c₂ : B}
           (f : b₁ --> b₂)
           (g : c₁ --> c₂)
           (HB_2_1 : is_univalent_2_1 B)
  : isaprop (f ⊥ g).
Proof.
  use (isofhlevelweqf
         1
         (@adj_equiv_is_equiv_cat
            (univ_hom HB_2_1 b₂ c₁)
            (@univalent_iso_comma
               (univ_hom HB_2_1 b₁ c₁)
               (univ_hom HB_2_1 b₂ c₂)
               (univ_hom HB_2_1 b₁ c₂)
               (post_comp b₁ g)
               (pre_comp c₂ f))
            (orthogonal_functor f g))).
  apply isaprop_left_adjoint_equivalence.
  exact univalent_cat_is_univalent_2_1.
Qed.

(** * 2. Constructing orthogonal morphisms *)
Section ConstructOrthogonality.
  Context {B : bicat}
          {b₁ b₂ c₁ c₂ : B}
          (f : b₁ --> b₂)
          (g : c₁ --> c₂).

  Definition orthogonal_essentially_surjective
    : UU
    := ∏ (φ₁ : b₁ --> c₁)
         (φ₂ : b₂ --> c₂)
         (α : invertible_2cell (φ₁ · g) (f · φ₂)),
       ∑ (l : b₂ --> c₁)
         (ζ₁ : invertible_2cell (f · l) φ₁)
         (ζ₂ : invertible_2cell (l · g) φ₂),
       (ζ₁ ▹ g) • α = rassociator _ _ _ • (f ◃ ζ₂).

  Definition orthogonal_full
    : UU
    := ∏ (l₁ l₂ : b₂ --> c₁)
         (k₁ : f · l₁ ==> f · l₂)
         (k₂ : l₁ · g ==> l₂ · g)
         (p : (k₁ ▹ g) • rassociator _ _ _
              =
              rassociator _ _ _ • (f ◃ k₂)),
       ∑ (ξ : l₁ ==> l₂),
       f ◃ ξ = k₁
       ×
       ξ ▹ g = k₂.

  Definition orthogonal_faithful
    : UU
    := ∏ (l₁ l₂ : b₂ --> c₁)
         (ζ₁ ζ₂ : l₁ ==> l₂),
       f ◃ ζ₁ = f ◃ ζ₂
       →
       ζ₁ ▹ g = ζ₂ ▹ g
       →
       ζ₁ = ζ₂.

  Section MakeOrthogonal.
    Context (HB_2_1 : is_univalent_2_1 B)
            (H₁ : orthogonal_full)
            (H₂ : orthogonal_faithful)
            (H₃ : orthogonal_essentially_surjective).

    Definition make_orthogonal_full
      : full (orthogonal_functor f g).
    Proof.
      intros l₁ l₂.
      intro k.
      apply hinhpr.
      simple refine (_ ,, _) ; cbn.
      - exact (pr1 (H₁ l₁ l₂ (pr11 k) (pr21 k) (pr2 k))).
      - abstract
          (use subtypePath ; [ intro ; apply cellset_property | ] ;
           cbn ;
           exact (pathsdirprod
                    (pr12 (H₁ l₁ l₂ (pr11 k) (pr21 k) (pr2 k)))
                    (pr22 (H₁ l₁ l₂ (pr11 k) (pr21 k) (pr2 k))))).
    Defined.

    Definition make_orthogonal_faithful
      : faithful (orthogonal_functor f g).
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
      use (H₂ l₁ l₂ (pr1 ζ₁) (pr1 ζ₂)).
      - exact (maponpaths (λ z, pr11 z) (pr2 ζ₁)
               @ !(maponpaths (λ z, pr11 z) (pr2 ζ₂))).
      - exact (maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr2 ζ₁)
               @ !(maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr2 ζ₂))).
    Qed.

    Definition make_orthogonal_fully_faithful
      : fully_faithful (orthogonal_functor f g).
    Proof.
      use full_and_faithful_implies_fully_faithful.
      split.
      - exact make_orthogonal_full.
      - exact make_orthogonal_faithful.
    Defined.

    Definition make_orthogonal_essentially_surjective
      : essentially_surjective (orthogonal_functor f g).
    Proof.
      intros h.
      pose (ℓ := H₃ (pr11 h) (pr21 h) (z_iso_to_inv2cell (pr2 h))).
      apply hinhpr.
      simple refine (_ ,, _).
      - exact (pr1 ℓ).
      - use make_z_iso'.
        + simple refine ((_ ,, _) ,, _) ; cbn.
          * exact (pr12 ℓ).
          * exact (pr122 ℓ).
          * exact (pr222 ℓ).
        + use is_z_iso_iso_comma.
          * use is_inv2cell_to_is_z_iso.
            apply property_from_invertible_2cell.
          * use is_inv2cell_to_is_z_iso.
            apply property_from_invertible_2cell.
    Defined.

    Definition make_orthogonal : f ⊥ g.
    Proof.
      use rad_equivalence_of_cats.
      - use is_univ_hom.
        exact HB_2_1.
      - exact make_orthogonal_fully_faithful.
      - exact make_orthogonal_essentially_surjective.
    Defined.
  End MakeOrthogonal.
End ConstructOrthogonality.

(** * 3. Projections of orthogonal morphisms *)
Section OrthogonalityProjections.
  Context {B : bicat}
          {b₁ b₂ c₁ c₂ : B}
          {f : b₁ --> b₂}
          {g : c₁ --> c₂}
          (H : f ⊥ g).

  (** ** 3.1. Lifting property for for 1-cells *)
  Section LiftOne.
    Context (φ₁ : b₁ --> c₁)
            (φ₂ : b₂ --> c₂)
            (α : invertible_2cell (φ₁ · g) (f · φ₂)).

      Definition orthogonal_lift_1
        : b₂ --> c₁
        := right_adjoint (H : adj_equivalence_of_cats _) ((φ₁ ,, φ₂) ,, inv2cell_to_z_iso α).

      Definition orthogonal_lift_1_comm_left
        : invertible_2cell (f · orthogonal_lift_1) φ₁.
      Proof.
        apply z_iso_to_inv2cell.
        exact (functor_on_z_iso
                (iso_comma_pr1 _ _)
                (counit_pointwise_z_iso_from_adj_equivalence
                   H
                   ((φ₁ ,, φ₂) ,, inv2cell_to_z_iso α))).
      Defined.

      Definition orthogonal_lift_1_comm_right
        : invertible_2cell (orthogonal_lift_1 · g) φ₂.
      Proof.
        apply z_iso_to_inv2cell.
        exact (functor_on_z_iso
                 (iso_comma_pr2 _ _)
                 (counit_pointwise_z_iso_from_adj_equivalence
                    H
                    ((φ₁ ,, φ₂) ,, inv2cell_to_z_iso α))).
      Defined.

      Definition orthogonal_lift_1_eq
        : (orthogonal_lift_1_comm_left ▹ g) • α
          =
          rassociator _ _ _ • (f ◃ orthogonal_lift_1_comm_right)
        := pr2 (counit_from_left_adjoint
                  (pr1 H)
                  ((φ₁ ,, φ₂) ,, inv2cell_to_z_iso α)).
    End LiftOne.

    (** ** 3.2. Lifting property for for 2-cells *)
    Section LiftTwo.
      Context (l₁ l₂ : b₂ --> c₁)
              (k₁ : f · l₁ ==> f · l₂)
              (k₂ : l₁ · g ==> l₂ · g)
              (p : (k₁ ▹ g) • rassociator _ _ _
                   =
                   rassociator _ _ _ • (f ◃ k₂)).

      Let R : iso_comma (post_comp b₁ g) (pre_comp c₂ f) ⟶ hom b₂ c₁
        := right_adjoint (H : adj_equivalence_of_cats _).

      Let φ : iso_comma (post_comp b₁ g) (pre_comp c₂ f)
        := (f · l₁ ,, l₁ · g) ,, inv2cell_to_z_iso (rassociator_invertible_2cell _ _ _).
      Let ψ : iso_comma (post_comp b₁ g) (pre_comp c₂ f)
        := (f · l₂ ,, l₂ · g) ,, inv2cell_to_z_iso (rassociator_invertible_2cell _ _ _).
      Let μ : φ --> ψ
        := (k₁ ,, k₂) ,, p.

      Let η₁ : l₁ ==> R φ
        := unit_from_left_adjoint (H : adj_equivalence_of_cats _) l₁.
      Let η₂ : R ψ ==> l₂
        := z_iso_to_inv2cell (unit_pointwise_z_iso_from_adj_equivalence H l₂)^-1.
      Let ε₁ : f · R φ ==> f · l₁
        := pr11 (counit_from_left_adjoint (pr1 H) φ).
      Let ε₂ : f · R ψ ==> f · l₂
        := pr11 (counit_from_left_adjoint (pr1 H) ψ).
      Let ε₁' : R φ · g ==> l₁ · g
        := pr21 (counit_from_left_adjoint (pr1 H) φ).
      Let ε₂' : R ψ · g ==> l₂ · g
        := pr21 (counit_from_left_adjoint (pr1 H) ψ).

      Definition orthogonal_lift_2
        : l₁ ==> l₂
        := η₁ • #R μ • η₂.

      Local Lemma orthogonal_lift_2_counit_invertible
        : is_invertible_2cell ε₂.
      Proof.
        exact (property_from_invertible_2cell
                 (z_iso_to_inv2cell
                    (functor_on_z_iso
                       (iso_comma_pr1 _ _)
                       (counit_pointwise_z_iso_from_adj_equivalence H ψ)))).
      Qed.

      Local Lemma orthogonal_lift_2_left_path_1
        : (f ◃ #R μ) • ε₂ = ε₁ • k₁.
      Proof.
        exact (maponpaths
                 (λ z, pr11 z)
                 (nat_trans_ax
                    (counit_from_left_adjoint (H : adj_equivalence_of_cats _))
                    _ _
                    μ)).
      Qed.

      Local Lemma orthogonal_lift_2_left_path_2
        : (f ◃ η₁) • ε₁ = id2 _.
      Proof.
        exact (maponpaths
                 (λ z, pr11 z)
                 (triangle_id_left_ad (pr21 H) l₁)).
      Qed.

      Definition orthogonal_lift_2_left
        : f ◃ orthogonal_lift_2 = k₁.
      Proof.
        unfold orthogonal_lift_2.
        rewrite <- !lwhisker_vcomp.
        use vcomp_move_R_Mp.
        {
          unfold η₂.
          is_iso.
        }
        use (vcomp_rcancel ε₂).
        {
          exact orthogonal_lift_2_counit_invertible.
        }
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          exact orthogonal_lift_2_left_path_1.
        }
        cbn.
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          exact orthogonal_lift_2_left_path_2.
        }
        rewrite id2_left.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   (λ z, pr11 z)
                   (triangle_id_left_ad (pr21 H) l₂)).
        }
        cbn.
        rewrite id2_right.
        apply idpath.
      Qed.

      Local Lemma orthogonal_lift_2_counit_invertible'
        : is_invertible_2cell ε₂'.
      Proof.
        exact (property_from_invertible_2cell
                 (z_iso_to_inv2cell
                    (functor_on_z_iso
                       (iso_comma_pr2 _ _)
                       (counit_pointwise_z_iso_from_adj_equivalence H ψ)))).
      Qed.

      Local Lemma orthogonal_lift_2_right_path_1
        : (#R μ ▹ g) • ε₂' = ε₁' • k₂.
      Proof.
        exact (maponpaths
                 (λ z, dirprod_pr2 (pr1 z))
                 (nat_trans_ax
                    (counit_from_left_adjoint (H : adj_equivalence_of_cats _))
                    _ _
                    μ)).
      Qed.

      Local Lemma orthogonal_lift_2_right_path_2
        : (η₁ ▹ g) • ε₁' = id2 _.
      Proof.
        exact (maponpaths
                 (λ z, dirprod_pr2 (pr1 z))
                 (triangle_id_left_ad (pr21 H) l₁)).
      Qed.

      Definition orthogonal_lift_2_right
        : orthogonal_lift_2 ▹ g = k₂.
      Proof.
        unfold orthogonal_lift_2.
        rewrite <- !rwhisker_vcomp.
        use vcomp_move_R_Mp.
        {
          unfold η₂.
          is_iso.
        }
        cbn.
        use (vcomp_rcancel ε₂').
        {
          exact orthogonal_lift_2_counit_invertible'.
        }
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          exact orthogonal_lift_2_right_path_1.
        }
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths_2.
          exact orthogonal_lift_2_right_path_2.
        }
        rewrite id2_left.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   (λ z, dirprod_pr2 (pr1 z))
                   (triangle_id_left_ad (pr21 H) l₂)).
        }
        apply id2_right.
      Qed.
    End LiftTwo.

    (** ** 3.3. Lifting property for for equalities *)
    Definition orthogonal_lift_eq
               {l₁ l₂ : b₂ --> c₁}
               (ζ₁ ζ₂ : l₁ ==> l₂)
               (p₁ : f ◃ ζ₁ = f ◃ ζ₂)
               (p₂ : ζ₁ ▹ g = ζ₂ ▹ g)
      : ζ₁ = ζ₂.
    Proof.
      pose (pr2 (fully_faithful_implies_full_and_faithful
                   _ _ _
                   (fully_faithful_from_equivalence _ _ _ H))
                l₁ l₂)
        as Heq.
      assert (((f ◃ ζ₁) ▹ g) • rassociator f l₂ g
              =
              rassociator f l₁ g • (f ◃ (ζ₁ ▹ g)))
        as r₁.
      {
        refine (!_).
        apply rwhisker_lwhisker_rassociator.
      }
      assert (((f ◃ ζ₂) ▹ g) • rassociator f l₂ g
              =
              rassociator f l₁ g • (f ◃ (ζ₂ ▹ g)))
        as r₂.
      {
        refine (!_).
        apply rwhisker_lwhisker_rassociator.
      }
      pose (proofirrelevance
              _
              (Heq ((f ◃ ζ₁ ,, ζ₁ ▹ g) ,, r₁)))
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
End OrthogonalityProjections.

Section OrthogonalityViaPullback.
  Context {B : bicat}
          {b₁ b₂ c₁ c₂ : B}
          (f : b₁ --> b₂)
          (g : c₁ --> c₂).

  (**
   4. Orthogonality via pullbacks
   *)
  Definition orthogonal_via_pb_cone
             (HB_2_1 : is_univalent_2_1 B)
    : @pb_cone
        bicat_of_univ_cats
        (univ_hom HB_2_1 b₁ c₁)
        (univ_hom HB_2_1 b₂ c₂)
        (univ_hom HB_2_1 b₁ c₂)
        (post_comp b₁ g)
        (pre_comp c₂ f).
  Proof.
    use make_pb_cone.
    - exact (univ_hom HB_2_1 b₂ c₁).
    - exact (pre_comp c₁ f).
    - exact (post_comp b₂ g).
    - use nat_z_iso_to_invertible_2cell.
      exact (pre_comp_post_comp_commute_z_iso f g).
  Defined.

  Definition orthogonal_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : UU
    := has_pb_ump (orthogonal_via_pb_cone HB_2_1).

  Definition isaprop_orthogonal_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop (orthogonal_via_pb HB_2_1).
  Proof.
    use isaprop_has_pb_ump.
    exact univalent_cat_is_univalent_2_1.
  Defined.

  (**
   5. Equivalence of the definitions
   *)
  Definition orthogonal_to_orthogonal_via_pb
             (HB_2_1 : is_univalent_2_1 B)
             (Hf : f ⊥ g)
    : orthogonal_via_pb HB_2_1.
  Proof.
    use (left_adjoint_equivalence_to_pb
           _ _ _
           (@iso_comma_has_pb_ump
               (univ_hom HB_2_1 b₁ c₁)
               (univ_hom HB_2_1 b₂ c₂)
               (univ_hom HB_2_1 b₁ c₂)
               (post_comp b₁ g)
               (pre_comp c₂ f))
           _
           _).
    - exact univalent_cat_is_univalent_2_0.
    - exact (orthogonal_functor f g).
    - exact (@equiv_cat_to_adj_equiv
               (univ_hom HB_2_1 b₂ c₁)
               (@univalent_iso_comma
                  (univ_hom HB_2_1 b₁ c₁)
                  (univ_hom HB_2_1 b₂ c₂)
                  (univ_hom HB_2_1 b₁ c₂)
                  (post_comp b₁ g)
                  (pre_comp c₂ f))
               (orthogonal_functor f g)
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

  Definition orthogonal_via_pb_to_orthogonal_nat_trans
             (HB_2_1 : is_univalent_2_1 B)
    : orthogonal_functor f g
      ⟹
      pr1 (pb_ump_mor
             (@iso_comma_has_pb_ump
                (univ_hom HB_2_1 b₁ c₁)
                (univ_hom HB_2_1 b₂ c₂)
                (univ_hom HB_2_1 b₁ c₂)
                (post_comp b₁ g)
                (pre_comp c₂ f))
             (orthogonal_via_pb_cone HB_2_1)).
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

  Definition orthogonal_via_pb_to_orthogonal
             (HB_2_1 : is_univalent_2_1 B)
             (Hf : orthogonal_via_pb HB_2_1)
    : f ⊥ g.
  Proof.
    apply (@adj_equiv_to_equiv_cat
             (univ_hom HB_2_1 b₂ c₁)
             (@univalent_iso_comma
                (univ_hom HB_2_1 b₁ c₁)
                (univ_hom HB_2_1 b₂ c₂)
                (univ_hom HB_2_1 b₁ c₂)
                (post_comp b₁ g)
                (pre_comp c₂ f))
             (orthogonal_functor f g)).
    pose (pb_ump_mor_left_adjoint_equivalence
            _
            _
            (@iso_comma_has_pb_ump
               (univ_hom HB_2_1 b₁ c₁)
               (univ_hom HB_2_1 b₂ c₂)
               (univ_hom HB_2_1 b₁ c₂)
               (post_comp b₁ g)
               (pre_comp c₂ f))
            Hf)
      as p.
    use (left_adjoint_equivalence_invertible p).
    - exact (orthogonal_via_pb_to_orthogonal_nat_trans HB_2_1).
    - use is_nat_z_iso_to_is_invertible_2cell.
      intro.
      use is_z_iso_iso_comma.
      + use is_inv2cell_to_is_z_iso ; cbn.
        is_iso.
      + use is_inv2cell_to_is_z_iso ; cbn.
        is_iso.
  Defined.

  Definition orthogonal_weq_orthogonal_via_pb
             (HB_2_1 : is_univalent_2_1 B)
    : f ⊥ g ≃ orthogonal_via_pb HB_2_1.
  Proof.
    use weqimplimpl.
    - exact (orthogonal_to_orthogonal_via_pb HB_2_1).
    - exact (orthogonal_via_pb_to_orthogonal HB_2_1).
    - exact (isaprop_orthogonal f g HB_2_1).
    - exact (isaprop_orthogonal_via_pb HB_2_1).
  Defined.
End OrthogonalityViaPullback.
