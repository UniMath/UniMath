(****************************************************************

 Products in bicategories

 In this file we define the notion of product diagram in arbitrary
 bicategories. For this definition, there are 2 possibilities. One
 could either write universal properties, which expresses the
 existence of a morphism up to a unique 2-cell. Alternatively, one
 could define the universal property via the hom-categories.
 Here, we choose the first approach.

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Local Open Scope cat.

Definition maponpaths_pr1_pathsdirprod
           {X Y : UU}
           {x₁ x₂ : X}
           {y₁ y₂ : Y}
           (p : x₁ = x₂)
           (q : y₁ = y₂)
  : maponpaths dirprod_pr1 (pathsdirprod p q) = p.
Proof.
  induction p, q.
  apply idpath.
Defined.

Definition maponpaths_pr2_pathsdirprod
           {X Y : UU}
           {x₁ x₂ : X}
           {y₁ y₂ : Y}
           (p : x₁ = x₂)
           (q : y₁ = y₂)
  : maponpaths dirprod_pr2 (pathsdirprod p q) = q.
Proof.
  induction p, q.
  apply idpath.
Defined.

Definition pathsdirprod_eta
           {X Y : UU}
           {x y : X × Y}
           (p : x = y)
  : p
    =
    pathsdirprod (maponpaths dirprod_pr1 p) (maponpaths dirprod_pr2 p).
Proof.
  induction p.
  apply idpath.
Defined.

Section Product.
  Context {B : bicat}
          {b₁ b₂ : B}.

  (** Cones on the diagram *)
  Definition binprod_cone
    : UU
    := ∑ (p : B), p --> b₁ × p --> b₂.

  Coercion binprod_cone_obj
           (p : binprod_cone)
    : B
    := pr1 p.

  Definition binprod_cone_pr1
             (p : binprod_cone)
    : p --> b₁
    := pr12 p.

  Definition binprod_cone_pr2
             (p : binprod_cone)
    : p --> b₂
    := pr22 p.

  Definition make_binprod_cone
             (p : B)
             (π₁ : p --> b₁)
             (π₂ : p --> b₂)
    : binprod_cone
    := (p ,, π₁ ,, π₂).

  (** 1-cells between cones *)
  Definition binprod_1cell
             (p q : binprod_cone)
    : UU
    := ∑ (φ : p --> q),
       invertible_2cell
         (φ · binprod_cone_pr1 q)
         (binprod_cone_pr1 p)
       ×
       invertible_2cell
         (φ · binprod_cone_pr2 q)
         (binprod_cone_pr2 p).

  Coercion binprod_1cell_1cell
           {p q : binprod_cone}
           (φ : binprod_1cell p q)
    : p --> q
    := pr1 φ.

  Definition binprod_1cell_pr1
             {p q : binprod_cone}
             (φ : binprod_1cell p q)
    : invertible_2cell
        (φ · binprod_cone_pr1 q)
        (binprod_cone_pr1 p)
    := pr12 φ.

  Definition binprod_1cell_pr2
             {p q : binprod_cone}
             (φ : binprod_1cell p q)
    : invertible_2cell
        (φ · binprod_cone_pr2 q)
        (binprod_cone_pr2 p)
    := pr22 φ.

  Definition make_binprod_1cell
             {p q : binprod_cone}
             (φ : p --> q)
             (τ : invertible_2cell
                    (φ · binprod_cone_pr1 q)
                    (binprod_cone_pr1 p))
             (θ : invertible_2cell
                    (φ · binprod_cone_pr2 q)
                    (binprod_cone_pr2 p))
    : binprod_1cell p q
    := (φ ,, τ ,, θ).

  Definition eq_binprod_1cell
             {p q : binprod_cone}
             (φ ψ : binprod_1cell p q)
             (r₁ : pr1 φ = pr1 ψ)
             (r₂ : pr1 (binprod_1cell_pr1 φ)
                   =
                   (idtoiso_2_1 _ _ r₁ ▹ binprod_cone_pr1 q) • pr1 (binprod_1cell_pr1 ψ))
             (r₃ : pr1 (binprod_1cell_pr2 φ)
                   =
                   (idtoiso_2_1 _ _ r₁ ▹ binprod_cone_pr2 q) • pr1 (binprod_1cell_pr2 ψ))
    : φ = ψ.
  Proof.
    induction φ as [ φ₁ [ φ₂ [ φ₃ φ₄ ]]].
    induction ψ as [ ψ₁ [ ψ₂ [ ψ₃ ψ₄ ]]].
    cbn in r₁.
    induction r₁ ; cbn in r₂.
    apply maponpaths.
    assert (φ₂ = ψ₂) as r'.
    {
      use subtypePath.
      {
        intro ; apply isaprop_is_invertible_2cell.
      }
      rewrite id2_rwhisker, id2_left in r₂.
      exact r₂.
    }
    induction r'.
    apply maponpaths.
    use subtypePath.
    {
      intro ; apply isaprop_is_invertible_2cell.
    }
    cbn.
    cbn in r₃.
    rewrite id2_rwhisker, id2_left in r₃.
    exact r₃.
  Qed.


  (** Statements of universal mapping properties of products *)
  Section UniversalMappingPropertyStatements.
    Variable (p : binprod_cone).

    Definition binprod_ump_1
      : UU
      := ∏ (q : binprod_cone), binprod_1cell q p.

    Definition binprod_ump_2
      : UU
      := ∏ (a : B)
           (φ ψ : a --> p)
           (α : φ · binprod_cone_pr1 p
                ==>
                ψ · binprod_cone_pr1 p)
           (β : φ · binprod_cone_pr2 p
                ==>
                ψ · binprod_cone_pr2 p),
         ∃! (γ : φ ==> ψ),
         (γ ▹ binprod_cone_pr1 p = α)
         ×
         (γ ▹ binprod_cone_pr2 p = β).

    Definition has_binprod_ump
      : UU
      := binprod_ump_1 × binprod_ump_2.

    Definition has_binprod_ump_1
               (H : has_binprod_ump)
      : binprod_ump_1
      := pr1 H.

    Definition has_binprod_ump_2
               (H : has_binprod_ump)
      : binprod_ump_2
      := pr2 H.

    Definition has_binprod_ump_2_cell
      : UU
      := ∏ (a : B)
           (φ ψ : a --> p)
           (α : φ · binprod_cone_pr1 p
                ==>
                ψ · binprod_cone_pr1 p)
           (β : φ · binprod_cone_pr2 p
                ==>
                ψ · binprod_cone_pr2 p),
         φ ==> ψ.

    Definition has_binprod_ump_2_cell_pr1
               (υ : has_binprod_ump_2_cell)
      := ∏ (a : B)
           (φ ψ : a --> p)
           (α : φ · binprod_cone_pr1 p
                ==>
                ψ · binprod_cone_pr1 p)
           (β : φ · binprod_cone_pr2 p
                ==>
                ψ · binprod_cone_pr2 p),
         υ a φ ψ α β ▹ binprod_cone_pr1 p = α.

    Definition has_binprod_ump_2_cell_pr2
               (υ : has_binprod_ump_2_cell)
      := ∏ (a : B)
           (φ ψ : a --> p)
           (α : φ · binprod_cone_pr1 p
                ==>
                ψ · binprod_cone_pr1 p)
           (β : φ · binprod_cone_pr2 p
                ==>
                ψ · binprod_cone_pr2 p),
         υ a φ ψ α β ▹ binprod_cone_pr2 p = β.

    Definition has_binprod_ump_2_cell_unique
      : UU
      := ∏ (a : B)
           (φ ψ : a --> p)
           (α : φ · binprod_cone_pr1 p
                ==>
                ψ · binprod_cone_pr1 p)
           (β : φ · binprod_cone_pr2 p
                ==>
                ψ · binprod_cone_pr2 p)
           (γ δ : φ ==> ψ)
           (γpr1 : γ ▹ binprod_cone_pr1 p = α)
           (γpr2 : γ ▹ binprod_cone_pr2 p = β)
           (δpr1 : δ ▹ binprod_cone_pr1 p = α)
           (δpr2 : δ ▹ binprod_cone_pr2 p = β),
         γ = δ.

    Definition make_binprod_ump
               (υ₁ : binprod_ump_1)
               (υ₂ : has_binprod_ump_2_cell)
               (υ₂pr1 : has_binprod_ump_2_cell_pr1 υ₂)
               (υ₂pr2 : has_binprod_ump_2_cell_pr2 υ₂)
               (υ₃ : has_binprod_ump_2_cell_unique)
      : has_binprod_ump.
    Proof.
      split.
      - exact υ₁.
      - intros q f₁ f₂ α β.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ;
             [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
             exact (υ₃ q
                       f₁ f₂
                       α β
                       (pr1 φ₁) (pr1 φ₂)
                       (pr12 φ₁) (pr22 φ₁)
                       (pr12 φ₂) (pr22 φ₂))).
        + simple refine (_ ,, _ ,, _).
          * exact (υ₂ q f₁ f₂ α β).
          * abstract (apply υ₂pr1).
          * abstract (apply υ₂pr2).
    Defined.
  End UniversalMappingPropertyStatements.

  Section Projections.
    Context {p : binprod_cone}
            (H : has_binprod_ump p).

    Definition binprod_ump_1cell
               {a : B}
               (apr1 : a --> b₁)
               (apr2 : a --> b₂)
      : a --> p
      := has_binprod_ump_1 _ H (make_binprod_cone a apr1 apr2).

    Definition binprod_ump_1cell_pr1
               (a : B)
               (apr1 : a --> b₁)
               (apr2 : a --> b₂)
      : invertible_2cell
          (binprod_ump_1cell apr1 apr2 · binprod_cone_pr1 p)
          apr1
      := binprod_1cell_pr1
           (has_binprod_ump_1 _ H (make_binprod_cone a apr1 apr2)).

    Definition binprod_ump_1cell_pr2
               (a : B)
               (apr1 : a --> b₁)
               (apr2 : a --> b₂)
      : invertible_2cell
          (binprod_ump_1cell apr1 apr2 · binprod_cone_pr2 p)
          apr2
      := binprod_1cell_pr2 (has_binprod_ump_1 _ H (make_binprod_cone a apr1 apr2)).

    Definition binprod_ump_2cell
               {a : B}
               {φ ψ : a --> p}
               (α : φ · binprod_cone_pr1 p
                    ==>
                    ψ · binprod_cone_pr1 p)
               (β : φ · binprod_cone_pr2 p
                    ==>
                    ψ · binprod_cone_pr2 p)
      : φ ==> ψ
      := pr11 (has_binprod_ump_2 _ H a φ ψ α β).

    Definition binprod_ump_2cell_pr1
               {a : B}
               {φ ψ : a --> p}
               (α : φ · binprod_cone_pr1 p
                    ==>
                    ψ · binprod_cone_pr1 p)
               (β : φ · binprod_cone_pr2 p
                    ==>
                    ψ · binprod_cone_pr2 p)
      : binprod_ump_2cell α β ▹ binprod_cone_pr1 p = α
      := pr121 (has_binprod_ump_2 _ H a φ ψ α β).

    Definition binprod_ump_2cell_pr2
               {a : B}
               {φ ψ : a --> p}
               (α : φ · binprod_cone_pr1 p
                    ==>
                    ψ · binprod_cone_pr1 p)
               (β : φ · binprod_cone_pr2 p
                    ==>
                    ψ · binprod_cone_pr2 p)
      : binprod_ump_2cell α β ▹ binprod_cone_pr2 p = β
      := pr221 (has_binprod_ump_2 _ H a φ ψ α β).

    Definition binprod_ump_2cell_unique
               {a : B}
               {φ ψ : a --> p}
               (α : φ · binprod_cone_pr1 p
                    ==>
                    ψ · binprod_cone_pr1 p)
               (β : φ · binprod_cone_pr2 p
                    ==>
                    ψ · binprod_cone_pr2 p)
               (γ δ : φ ==> ψ)
               (γpr1 : γ ▹ binprod_cone_pr1 p = α)
               (γpr2 : γ ▹ binprod_cone_pr2 p = β)
               (δpr1 : δ ▹ binprod_cone_pr1 p = α)
               (δpr2 : δ ▹ binprod_cone_pr2 p = β)
      : γ = δ.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (has_binprod_ump_2 _ H a φ ψ α β))
                  (γ ,, (γpr1 ,, γpr2))
                  (δ ,, (δpr1 ,, δpr2)))).
    Qed.

    Definition binprod_ump_2cell_unique_alt
               {a : B}
               {φ ψ : a --> p}
               (γ δ : φ ==> ψ)
               (ppr1 : γ ▹ binprod_cone_pr1 p = δ ▹ binprod_cone_pr1 p)
               (ppr2 : γ ▹ binprod_cone_pr2 p = δ ▹ binprod_cone_pr2 p)

      : γ = δ.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr
                     (has_binprod_ump_2
                        _
                        H a φ ψ
                        (γ ▹ binprod_cone_pr1 p)
                        (γ ▹ binprod_cone_pr2 p)))
                  (γ ,, (idpath _ ,, idpath _))
                  (δ ,, (!ppr1 ,, !ppr2)))).
    Qed.

    Definition binprod_ump_2cell_invertible
               {a : B}
               {φ ψ : a --> p}
               {α : φ · binprod_cone_pr1 p
                    ==>
                    ψ · binprod_cone_pr1 p}
               {β : φ · binprod_cone_pr2 p
                    ==>
                    ψ · binprod_cone_pr2 p}
               (Hα : is_invertible_2cell α)
               (Hβ : is_invertible_2cell β)
      : is_invertible_2cell (binprod_ump_2cell α β).
    Proof.
      use make_is_invertible_2cell.
      - exact (binprod_ump_2cell (Hα^-1) (Hβ^-1)).
      - use (binprod_ump_2cell_unique (id2 _) (id2 _)).
        + abstract
            (rewrite <- !rwhisker_vcomp ;
             rewrite !binprod_ump_2cell_pr1 ;
             rewrite vcomp_rinv ;
             apply idpath).
        + abstract
            (rewrite <- !rwhisker_vcomp ;
             rewrite !binprod_ump_2cell_pr2 ;
             rewrite vcomp_rinv ;
             apply idpath).
        + abstract (apply id2_rwhisker).
        + abstract (apply id2_rwhisker).
      - use (binprod_ump_2cell_unique (id2 _) (id2 _)).
        + abstract
            (rewrite <- !rwhisker_vcomp ;
             rewrite !binprod_ump_2cell_pr1 ;
             rewrite vcomp_linv ;
             apply idpath).
        + abstract
            (rewrite <- !rwhisker_vcomp ;
             rewrite !binprod_ump_2cell_pr2 ;
             rewrite vcomp_linv ;
             apply idpath).
        + abstract (apply id2_rwhisker).
        + abstract (apply id2_rwhisker).
    Defined.
  End Projections.

  Definition isaprop_has_binprod_ump
             (p : binprod_cone)
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop (has_binprod_ump p).
  Proof.
    use invproofirrelevance.
    intros χ₁ χ₂.
    use pathsdirprod.
    - use funextsec ; intro q.
      use eq_binprod_1cell.
      + use (isotoid_2_1 HB_2_1).
        use make_invertible_2cell.
        * use (binprod_ump_2cell χ₂).
          ** exact (comp_of_invertible_2cell
                      (binprod_1cell_pr1 (pr1 χ₁ q))
                      (inv_of_invertible_2cell
                         (binprod_1cell_pr1 (pr1 χ₂ q)))).
          ** exact (comp_of_invertible_2cell
                      (binprod_1cell_pr2 (pr1 χ₁ q))
                      (inv_of_invertible_2cell
                         (binprod_1cell_pr2 (pr1 χ₂ q)))).
        * use binprod_ump_2cell_invertible.
          ** apply property_from_invertible_2cell.
          ** apply property_from_invertible_2cell.
      + rewrite idtoiso_2_1_isotoid_2_1.
        cbn.
        rewrite binprod_ump_2cell_pr1.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      + rewrite idtoiso_2_1_isotoid_2_1.
        cbn.
        rewrite binprod_ump_2cell_pr2.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
    - repeat (use funextsec ; intro).
      apply isapropiscontr.
  Qed.

  Definition postcomp_binprod_cone
             (HB_2_1 : is_univalent_2_1 B)
             (p : binprod_cone)
             (x : B)
    : univ_hom HB_2_1 x p
      ⟶
      univalent_category_binproduct (univ_hom HB_2_1 x b₁) (univ_hom HB_2_1 x b₂).
  Proof.
    use bindelta_pair_functor.
    - exact (post_comp x (binprod_cone_pr1 p)).
    - exact (post_comp x (binprod_cone_pr2 p)).
  Defined.

  Definition binprod_cat_ump
             (HB_2_1 : is_univalent_2_1 B)
             (p : binprod_cone)
    : UU
    := ∏ (x : B),
       @left_adjoint_equivalence
         bicat_of_univ_cats
         _ _
         (postcomp_binprod_cone HB_2_1 p x).

  Definition isaprop_binprod_cat_ump
             (HB_2_1 : is_univalent_2_1 B)
             (p : binprod_cone)
    : isaprop (binprod_cat_ump HB_2_1 p).
  Proof.
    use impred ; intro x.
    apply isaprop_left_adjoint_equivalence.
    exact univalent_cat_is_univalent_2_1.
  Defined.

  Definition has_binprod_ump_binprod_cat_ump
             (HB_2_1 : is_univalent_2_1 B)
             (p : binprod_cone)
             (H : has_binprod_ump p)
    : binprod_cat_ump HB_2_1 p.
  Proof.
    intro x.
    use equiv_cat_to_adj_equiv.
    use rad_equivalence_of_precats.
    - apply is_univ_hom.
      exact HB_2_1.
    - use full_and_faithful_implies_fully_faithful.
      split.
      + intros f g α.
        use hinhpr.
        simple refine (_ ,, _).
        * exact (binprod_ump_2cell H (pr1 α) (pr2 α)).
        * use pathsdirprod.
          ** apply binprod_ump_2cell_pr1.
          ** apply binprod_ump_2cell_pr2.
      + unfold faithful.
        intros f g α.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro ; apply homset_property.
        }
        use (binprod_ump_2cell_unique H).
        * exact (pr1 α).
        * exact (pr2 α).
        * exact (maponpaths pr1 (pr2 φ₁)).
        * exact (maponpaths dirprod_pr2 (pr2 φ₁)).
        * exact (maponpaths pr1 (pr2 φ₂)).
        * exact (maponpaths dirprod_pr2 (pr2 φ₂)).
    - intros f g.
      use hinhpr.
      simple refine (binprod_ump_1cell H (pr1 f) (pr2 f) ,, _).
      use make_iso.
      + exact (pr1 (binprod_ump_1cell_pr1 H _ (pr1 f) (pr2 f))
               ,,
               pr1 (binprod_ump_1cell_pr2 H _ (pr1 f) (pr2 f))).
      + use is_iso_binprod_iso.
        * apply is_inv2cell_to_is_iso.
          apply property_from_invertible_2cell.
        * apply is_inv2cell_to_is_iso.
          apply property_from_invertible_2cell.
  Defined.
End Product.

Arguments binprod_cone {_} _ _.

Definition has_binprod
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ : B),
     ∑ (p : binprod_cone b₁ b₂),
     has_binprod_ump p.

Definition bicat_with_binprod
  : UU
  := ∑ (B : bicat), has_binprod B.

Coercion bicat_with_binprod_to_bicat
         (B : bicat_with_binprod)
  : bicat
  := pr1 B.

Definition binprod_of
           (B : bicat_with_binprod)
  : has_binprod B
  := pr2 B.

Section StandardFunctions.
  Context (B : bicat_with_binprod).

  Definition binprod
             (b₁ b₂ : B)
    : B
    := pr1 (binprod_of B b₁ b₂).

  Local Notation "b₁ ⊗ b₂" := (binprod b₁ b₂).

  Definition binprod_pr1
             (b₁ b₂ : B)
    : b₁ ⊗ b₂ --> b₁
    := binprod_cone_pr1 (pr1 (binprod_of B b₁ b₂)).

  Definition binprod_pr2
             (b₁ b₂ : B)
    : b₁ ⊗ b₂ --> b₂
    := binprod_cone_pr2 (pr1 (binprod_of B b₁ b₂)).

  Local Notation "'π₁'" := (binprod_pr1 _ _).
  Local Notation "'π₂'" := (binprod_pr2 _ _).

  Definition prod_1cell
             {a b₁ b₂ : B}
             (f : a --> b₁)
             (g : a --> b₂)
    : a --> b₁ ⊗ b₂
    := binprod_ump_1cell (pr2 (binprod_of B b₁ b₂)) f g.

  Local Notation "⟨ f , g ⟩" := (prod_1cell f g).

  Definition prod_1cell_pr1
             {a b₁ b₂ : B}
             (f : a --> b₁)
             (g : a --> b₂)
    : invertible_2cell (⟨ f , g ⟩ · π₁) f
    := binprod_ump_1cell_pr1 (pr2 (binprod_of B b₁ b₂)) _ f g.

  Definition prod_1cell_pr2
             {a b₁ b₂ : B}
             (f : a --> b₁)
             (g : a --> b₂)
    : invertible_2cell (⟨ f , g ⟩ · π₂) g
    := binprod_ump_1cell_pr2 (pr2 (binprod_of B b₁ b₂)) _ f g.

  Definition pair_1cell
             {a₁ a₂ b₁ b₂ : B}
             (f : a₁ --> b₁)
             (g : a₂ --> b₂)
    : a₁ ⊗ a₂ --> b₁ ⊗ b₂
    := ⟨ π₁ · f , π₂ · g ⟩.

  Local Notation "f '⊗₁' g" := (pair_1cell f g) (at level 40).

  Definition pair_1cell_pr1
             {a₁ a₂ b₁ b₂ : B}
             (f : a₁ --> b₁)
             (g : a₂ --> b₂)
    : invertible_2cell (f ⊗₁ g · π₁) (π₁ · f)
    := prod_1cell_pr1 (π₁ · f) (π₂ · g).

  Definition pair_1cell_pr2
             {a₁ a₂ b₁ b₂ : B}
             (f : a₁ --> b₁)
             (g : a₂ --> b₂)
    : invertible_2cell (f ⊗₁ g · π₂) (π₂ · g)
    := prod_1cell_pr2 (π₁ · f) (π₂ · g).

  Definition prod_2cell
             {a b₁ b₂ : B}
             {f₁ f₂ : a --> b₁}
             {g₁ g₂ : a --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ⟨ f₁ , g₁ ⟩ ==> ⟨ f₂ , g₂ ⟩.
  Proof.
    use (binprod_ump_2cell (pr2 (binprod_of B b₁ b₂))).
    - exact (prod_1cell_pr1 f₁ g₁ • α • (prod_1cell_pr1 f₂ g₂)^-1).
    - exact (prod_1cell_pr2 f₁ g₁ • β • (prod_1cell_pr2 f₂ g₂)^-1).
  Defined.

  Local Notation "⟪ α , β ⟫" := (prod_2cell α β).

  Definition prod_2cell_is_invertible
             {a b₁ b₂ : B}
             {f₁ f₂ : a --> b₁}
             {g₁ g₂ : a --> b₂}
             {α : f₁ ==> f₂}
             {β : g₁ ==> g₂}
             (Hα : is_invertible_2cell α)
             (Hβ : is_invertible_2cell β)
    : is_invertible_2cell ⟪ α , β ⟫.
  Proof.
    use binprod_ump_2cell_invertible.
    - is_iso.
      apply property_from_invertible_2cell.
    - is_iso.
      apply property_from_invertible_2cell.
  Defined.

  Definition prod_2cell_pr1
             {a b₁ b₂ : B}
             {f₁ f₂ : a --> b₁}
             {g₁ g₂ : a --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ⟪ α , β ⟫ ▹ π₁
      =
      prod_1cell_pr1 f₁ g₁ • α • (prod_1cell_pr1 f₂ g₂)^-1
    := binprod_ump_2cell_pr1 _ _ _.

  Definition prod_2cell_pr2
             {a b₁ b₂ : B}
             {f₁ f₂ : a --> b₁}
             {g₁ g₂ : a --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ⟪ α , β ⟫ ▹ π₂
      =
      prod_1cell_pr2 f₁ g₁ • β • (prod_1cell_pr2 f₂ g₂)^-1
    := binprod_ump_2cell_pr2 _ _ _.

  Definition prod_2cell_pr1_alt
             {a b₁ b₂ : B}
             {f₁ f₂ : a --> b₁}
             {g₁ g₂ : a --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ⟪ α , β ⟫ ▹ π₁ • prod_1cell_pr1 f₂ g₂
      =
      prod_1cell_pr1 f₁ g₁ • α.
  Proof.
    use vcomp_move_R_Mp.
    {
      apply property_from_invertible_2cell.
    }
    apply prod_2cell_pr1.
  Qed.

  Definition prod_2cell_pr2_alt
             {a b₁ b₂ : B}
             {f₁ f₂ : a --> b₁}
             {g₁ g₂ : a --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ⟪ α , β ⟫ ▹ π₂ • prod_1cell_pr2 f₂ g₂
      =
      prod_1cell_pr2 f₁ g₁ • β.
  Proof.
    use vcomp_move_R_Mp.
    {
      apply property_from_invertible_2cell.
    }
    apply prod_2cell_pr2.
  Qed.

  Definition pair_2cell
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ : a₁ --> b₁}
             {g₁ g₂ : a₂ --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : f₁ ⊗₁ g₁ ==> f₂ ⊗₁ g₂
    := prod_2cell (π₁ ◃ α) (π₂ ◃ β).

  Local Notation "α '⊗₂' β" := (pair_2cell α β) (at level 40).

  Definition pair_2cell_pr1
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ : a₁ --> b₁}
             {g₁ g₂ : a₂ --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : (α ⊗₂ β) ▹ π₁
      =
      prod_1cell_pr1 (π₁ · f₁) (π₂ · g₁)
      • (π₁ ◃ α)
      • (prod_1cell_pr1 (π₁ · f₂) (π₂ · g₂))^-1
    := prod_2cell_pr1 (π₁ ◃ α) (π₂ ◃ β).

  Definition pair_2cell_pr2
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ : a₁ --> b₁}
             {g₁ g₂ : a₂ --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : (α ⊗₂ β) ▹ π₂
      =
      prod_1cell_pr2 (π₁ · f₁) (π₂ · g₁)
      • (π₂ ◃ β)
      • (prod_1cell_pr2 (π₁ · f₂) (π₂ · g₂))^-1
    := prod_2cell_pr2 (π₁ ◃ α) (π₂ ◃ β).

  Definition pair_2cell_pr1_alt
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ : a₁ --> b₁}
             {g₁ g₂ : a₂ --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : (α ⊗₂ β) ▹ π₁
      • prod_1cell_pr1 (π₁ · f₂) (π₂ · g₂)
      =
      prod_1cell_pr1 (π₁ · f₁) (π₂ · g₁)
      • (π₁ ◃ α)
    := prod_2cell_pr1_alt (π₁ ◃ α) (π₂ ◃ β).

  Definition pair_2cell_pr2_alt
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ : a₁ --> b₁}
             {g₁ g₂ : a₂ --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : (α ⊗₂ β) ▹ π₂
      • prod_1cell_pr2 (π₁ · f₂) (π₂ · g₂)
      =
      prod_1cell_pr2 (π₁ · f₁) (π₂ · g₁)
      • (π₂ ◃ β)
    := prod_2cell_pr2_alt (π₁ ◃ α) (π₂ ◃ β).

  (** Laws for product of 1-cells *)
  Definition precomp_prod_1cell
             {a b c₁ c₂ : B}
             (f : a --> b)
             (g₁ : b --> c₁)
             (g₂ : b --> c₂)
    : f · ⟨ g₁ , g₂ ⟩ ==> ⟨ f · g₁ , f · g₂ ⟩.
  Proof.
    use (binprod_ump_2cell (pr2 (binprod_of B _ _))).
    - exact (rassociator _ _ _
             • (f ◃ prod_1cell_pr1 _ _)
             • (prod_1cell_pr1 _ _)^-1).
    - exact (rassociator _ _ _
             • (f ◃ prod_1cell_pr2 _ _)
             • (prod_1cell_pr2 _ _)^-1).
  Defined.

  Definition precomp_prod_1cell_invertible
             {a b c₁ c₂ : B}
             (f : a --> b)
             (g₁ : b --> c₁)
             (g₂ : b --> c₂)
    : invertible_2cell (f · ⟨ g₁ , g₂ ⟩) ⟨ f · g₁ , f · g₂ ⟩.
  Proof.
    use make_invertible_2cell.
    - exact (precomp_prod_1cell f g₁ g₂).
    - use binprod_ump_2cell_invertible.
      + is_iso.
        apply property_from_invertible_2cell.
      + is_iso.
        apply property_from_invertible_2cell.
  Defined.

  (** Pseudofunctoriality of pairing 1-cells *)
  Definition pair_1cell_id_id
             (a b : B)
    : id₁ a ⊗₁ id₁ b ==> id₁ (a ⊗ b).
  Proof.
    use (binprod_ump_2cell (pr2 (binprod_of B a b))).
    - exact (pair_1cell_pr1 _ _ • runitor _ • linvunitor _).
    - exact (pair_1cell_pr2 _ _ • runitor _ • linvunitor _).
  Defined.

  Definition pair_1cell_id_id_invertible
             (a b : B)
    : invertible_2cell (id₁ a ⊗₁ id₁ b) (id₁ (a ⊗ b)).
  Proof.
    use make_invertible_2cell.
    - exact (pair_1cell_id_id a b).
    - apply binprod_ump_2cell_invertible.
      + is_iso.
        apply property_from_invertible_2cell.
      + is_iso.
        apply property_from_invertible_2cell.
  Defined.

  Definition pair_1cell_comp
             {a₁ a₂ a₃ b₁ b₂ b₃ : B}
             (f₁ : a₁ --> a₂)
             (f₂ : a₂ --> a₃)
             (g₁ : b₁ --> b₂)
             (g₂ : b₂ --> b₃)
    : (f₁ ⊗₁ g₁) · (f₂ ⊗₁ g₂) ==> (f₁ · f₂) ⊗₁ (g₁ · g₂).
  Proof.
    use (binprod_ump_2cell (pr2 (binprod_of B _ _))).
    - exact (rassociator _ _ _
             • (_ ◃ pair_1cell_pr1 _ _)
             • lassociator _ _ _
             • (pair_1cell_pr1 _ _ ▹ _)
             • rassociator _ _ _
             • (pair_1cell_pr1 _ _)^-1).
    - exact (rassociator _ _ _
             • (_ ◃ pair_1cell_pr2 _ _)
             • lassociator _ _ _
             • (pair_1cell_pr2 _ _ ▹ _)
             • rassociator _ _ _
             • (pair_1cell_pr2 _ _)^-1).
  Defined.

  Definition pair_1cell_comp_invertible
             {a₁ a₂ a₃ b₁ b₂ b₃ : B}
             (f₁ : a₁ --> a₂)
             (f₂ : a₂ --> a₃)
             (g₁ : b₁ --> b₂)
             (g₂ : b₂ --> b₃)
    : invertible_2cell ((f₁ ⊗₁ g₁) · (f₂ ⊗₁ g₂)) ((f₁ · f₂) ⊗₁ (g₁ · g₂)).
  Proof.
    use make_invertible_2cell.
    - exact (pair_1cell_comp f₁ f₂ g₁ g₂).
    - apply binprod_ump_2cell_invertible.
      + is_iso.
        * apply property_from_invertible_2cell.
        * apply property_from_invertible_2cell.
      + is_iso.
        * apply property_from_invertible_2cell.
        * apply property_from_invertible_2cell.
  Defined.

  (** Functoriality of pairing 2-cells *)
  Definition pair_2cell_id_id
             {a₁ a₂ b₁ b₂ : B}
             {f : a₁ --> b₁}
             {g : a₂ --> b₂}
    : id₂ f ⊗₂ id₂ g = id₂ (f ⊗₁ g).
  Proof.
    use binprod_ump_2cell_unique.
    - exact (pr2 (binprod_of B b₁ b₂)).
    - apply id₂.
    - apply id₂.
    - refine (pair_2cell_pr1 _ _ @ _).
      rewrite lwhisker_id2.
      rewrite id2_right.
      rewrite vcomp_rinv.
      apply idpath.
    - refine (pair_2cell_pr2 _ _ @ _).
      rewrite lwhisker_id2.
      rewrite id2_right.
      rewrite vcomp_rinv.
      apply idpath.
    - rewrite id2_rwhisker.
      apply idpath.
    - rewrite id2_rwhisker.
      apply idpath.
  Qed.

  Definition pair_2cell_comp
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ f₃ : a₁ --> b₁}
             {g₁ g₂ g₃ : a₂ --> b₂}
             (α₁ : f₁ ==> f₂)
             (β₁ : g₁ ==> g₂)
             (α₂ : f₂ ==> f₃)
             (β₂ : g₂ ==> g₃)
    : (α₁ • α₂) ⊗₂ (β₁ • β₂)
      =
      (α₁ ⊗₂ β₁) • (α₂ ⊗₂ β₂).
  Proof.
    use binprod_ump_2cell_unique.
    - exact (pr2 (binprod_of B b₁ b₂)).
    - exact (prod_1cell_pr1 _ _ • (π₁ ◃ (α₁ • α₂)) • (prod_1cell_pr1 _ _)^-1).
    - exact (prod_1cell_pr2 _ _ • (π₂ ◃ (β₁ • β₂)) • (prod_1cell_pr2 _ _)^-1).
    - exact (pair_2cell_pr1 _ _).
    - exact (pair_2cell_pr2 _ _).
    - rewrite <- !rwhisker_vcomp.
      etrans.
      {
        apply maponpaths.
        apply pair_2cell_pr1.
      }
      etrans.
      {
        apply maponpaths_2.
        apply pair_2cell_pr1.
      }
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      etrans.
      {
        apply maponpaths.
        apply pair_2cell_pr2.
      }
      etrans.
      {
        apply maponpaths_2.
        apply pair_2cell_pr2.
      }
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
  Qed.
End StandardFunctions.

(** Products of 1-types *)
Definition one_types_binprod_cone
           (X Y : one_types)
  : binprod_cone X Y.
Proof.
  use make_binprod_cone.
  - use make_one_type.
    + exact (pr1 X × pr1 Y).
    + apply isofhleveldirprod.
      * exact (pr2 X).
      * exact (pr2 Y).
  - exact pr1.
  - exact pr2.
Defined.

Section OneTypesBinprodUMP.
  Context (X Y : one_types).

  Definition binprod_ump_1_one_types
    : binprod_ump_1 (one_types_binprod_cone X Y).
  Proof.
    intro q.
    use make_binprod_1cell.
    - exact (λ x, binprod_cone_pr1 q x ,, binprod_cone_pr2 q x).
    - use make_invertible_2cell.
      + intro x ; cbn.
        apply idpath.
      + apply one_type_2cell_iso.
    - use make_invertible_2cell.
      + intro x ; cbn.
        apply idpath.
      + apply one_type_2cell_iso.
  Defined.

  Definition binprod_ump_2_cell_one_types
    : has_binprod_ump_2_cell (one_types_binprod_cone X Y)
    := λ q f g p₁ p₂ x, pathsdirprod (p₁ x) (p₂ x).

  Definition binprod_ump_2_cell_pr1_one_types
    : has_binprod_ump_2_cell_pr1
        (one_types_binprod_cone X Y)
        binprod_ump_2_cell_one_types.
  Proof.
    intros q f g p₁ p₂.
    use funextsec.
    intro x.
    apply maponpaths_pr1_pathsdirprod.
  Qed.

  Definition binprod_ump_2_cell_pr2_one_types
    : has_binprod_ump_2_cell_pr2
        (one_types_binprod_cone X Y)
        binprod_ump_2_cell_one_types.
  Proof.
    intros q f g p₁ p₂.
    use funextsec.
    intro x.
    apply maponpaths_pr2_pathsdirprod.
  Qed.

  Definition binprod_ump_2_cell_unique_one_types
    : has_binprod_ump_2_cell_unique (one_types_binprod_cone X Y).
  Proof.
    intros q f g p₁ p₂ φ₁ φ₂ φ₁pr1 φ₁pr2 φ₂pr1 φ₂pr2.
    use funextsec.
    intro x.
    refine (pathsdirprod_eta _ @ _ @ !(pathsdirprod_eta _)).
    pose (eqtohomot φ₁pr1 x @ !(eqtohomot φ₂pr1 x)) as r₁.
    pose (eqtohomot φ₁pr2 x @ !(eqtohomot φ₂pr2 x)) as r₂.
    cbn in r₁, r₂ ; unfold homotfun in *.
    etrans.
    {
      apply maponpaths.
      exact r₂.
    }
    apply maponpaths_2.
    exact r₁.
  Qed.

  Definition has_binprod_ump_one_types
    : has_binprod_ump (one_types_binprod_cone X Y).
  Proof.
    use make_binprod_ump.
    - exact binprod_ump_1_one_types.
    - exact binprod_ump_2_cell_one_types.
    - exact binprod_ump_2_cell_pr1_one_types.
    - exact binprod_ump_2_cell_pr2_one_types.
    - exact binprod_ump_2_cell_unique_one_types.
  Defined.
End OneTypesBinprodUMP.

Definition has_binprod_one_types
  : has_binprod one_types.
Proof.
  intros X Y ; cbn in *.
  simple refine (_ ,, _).
  - exact (one_types_binprod_cone X Y).
  - exact (has_binprod_ump_one_types X Y).
Defined.

Definition univ_cat_binprod_cone
           (C₁ C₂ : bicat_of_univ_cats)
  : binprod_cone C₁ C₂.
Proof.
  use make_binprod_cone.
  - exact (univalent_category_binproduct C₁ C₂).
  - apply pr1_functor.
  - apply pr2_functor.
Defined.

Section CatsBinprodUMP.
  Context (C₁ C₂ : bicat_of_univ_cats).

  Definition binprod_ump_1_univ_cat
    : binprod_ump_1 (univ_cat_binprod_cone C₁ C₂).
  Proof.
    intro q.
    use make_binprod_1cell.
    - exact (bindelta_pair_functor (binprod_cone_pr1 q) (binprod_cone_pr2 q)).
    - apply nat_iso_to_invertible_2cell.
      apply bindelta_pair_pr1_iso.
    - apply nat_iso_to_invertible_2cell.
      apply bindelta_pair_pr2_iso.
  Defined.

  Definition binprod_ump_2_cell_univ_cat
    : has_binprod_ump_2_cell (univ_cat_binprod_cone C₁ C₂).
  Proof.
    intros q F₁ F₂ α β ; cbn -[functor_composite] in *.
    use make_nat_trans.
    - exact (λ x, α x ,, β x).
    - intros x y f.
      use pathsdirprod.
      + apply (nat_trans_ax α).
      + apply (nat_trans_ax β).
  Defined.

  Definition binprod_ump_2_cell_pr1_univ_cat
    : has_binprod_ump_2_cell_pr1
        (univ_cat_binprod_cone C₁ C₂)
        binprod_ump_2_cell_univ_cat.
  Proof.
    intros q F₁ F₂ α β.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x ; cbn.
    apply idpath.
  Qed.

  Definition binprod_ump_2_cell_pr2_univ_cat
    : has_binprod_ump_2_cell_pr2
        (univ_cat_binprod_cone C₁ C₂)
        binprod_ump_2_cell_univ_cat.
  Proof.
    intros q F₁ F₂ α β.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x ; cbn.
    apply idpath.
  Qed.

  Definition binprod_ump_2_cell_unique_univ_cat
    : has_binprod_ump_2_cell_unique (univ_cat_binprod_cone C₁ C₂).
  Proof.
    intros q F₁ F₂ α β γ δ p₁ p₂ p₃ p₄.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use pathsdirprod.
    - exact (nat_trans_eq_pointwise p₁ x @ !(nat_trans_eq_pointwise p₃ x)).
    - exact (nat_trans_eq_pointwise p₂ x @ !(nat_trans_eq_pointwise p₄ x)).
  Qed.

  Definition has_binprod_ump_univ_cats
    : has_binprod_ump (univ_cat_binprod_cone C₁ C₂).
  Proof.
    use make_binprod_ump.
    - exact binprod_ump_1_univ_cat.
    - exact binprod_ump_2_cell_univ_cat.
    - exact binprod_ump_2_cell_pr1_univ_cat.
    - exact binprod_ump_2_cell_pr2_univ_cat.
    - exact binprod_ump_2_cell_unique_univ_cat.
  Defined.
End CatsBinprodUMP.

Definition has_pb_bicat_of_univ_cats
  : has_binprod bicat_of_univ_cats.
Proof.
  intros C₁ C₂.
  simple refine (_ ,, _).
  - exact (univ_cat_binprod_cone C₁ C₂).
  - exact (has_binprod_ump_univ_cats C₁ C₂).
Defined.

Module Notations.
  Notation "b₁ ⊗ b₂" := (binprod _ b₁ b₂).
  Notation "'π₁'" := (binprod_pr1 _ _ _).
  Notation "'π₂'" := (binprod_pr2 _ _ _).
  Notation "⟨ f , g ⟩" := (prod_1cell _ f g).
  Notation "f '⊗₁' g" := (pair_1cell _ f g) (at level 40).
  Notation "⟪ α , β ⟫" := (prod_2cell _ α β).
  Notation "α '⊗₂' β" := (pair_2cell _ α β) (at level 40).
End Notations.
