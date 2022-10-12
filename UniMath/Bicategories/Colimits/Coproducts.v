(****************************************************************

 Coproducts in bicategories

 In this file we define the notion of coproduct diagram in arbitrary
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
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.

Local Open Scope cat.

Section Coproduct.
  Context {B : bicat}
          {b₁ b₂ : B}.

  (** Cones on the diagram *)
  Definition bincoprod_cocone
    : UU
    := ∑ (p : B), b₁ --> p × b₂ --> p.

  Coercion bincoprod_cocone_obj
           (p : bincoprod_cocone)
    : B
    := pr1 p.

  Definition bincoprod_cocone_inl
             (p : bincoprod_cocone)
    : b₁ --> p
    := pr12 p.

  Definition bincoprod_cocone_inr
             (p : bincoprod_cocone)
    : b₂ --> p
    := pr22 p.

  Definition make_bincoprod_cocone
             (p : B)
             (π₁ : b₁ --> p)
             (π₂ : b₂ --> p)
    : bincoprod_cocone
    := (p ,, π₁ ,, π₂).

  (** 1-cells between cocones *)
  Definition bincoprod_1cell
             (p q : bincoprod_cocone)
    : UU
    := ∑ (φ : p --> q),
       invertible_2cell
         (bincoprod_cocone_inl p · φ)
         (bincoprod_cocone_inl q)
       ×
       invertible_2cell
         (bincoprod_cocone_inr p · φ)
         (bincoprod_cocone_inr q).

  Coercion bincoprod_1cell_1cell
           {p q : bincoprod_cocone}
           (φ : bincoprod_1cell p q)
    : p --> q
    := pr1 φ.

  Definition bincoprod_1cell_inl
             {p q : bincoprod_cocone}
             (φ : bincoprod_1cell p q)
    : invertible_2cell
        (bincoprod_cocone_inl p · φ)
        (bincoprod_cocone_inl q)
    := pr12 φ.

  Definition bincoprod_1cell_inr
             {p q : bincoprod_cocone}
             (φ : bincoprod_1cell p q)
    : invertible_2cell
        (bincoprod_cocone_inr p · φ)
        (bincoprod_cocone_inr q)
    := pr22 φ.

  Definition make_bincoprod_1cell
             {p q : bincoprod_cocone}
             (φ : p --> q)
             (τ : invertible_2cell
                    (bincoprod_cocone_inl p · φ)
                    (bincoprod_cocone_inl q))
             (θ : invertible_2cell
                    (bincoprod_cocone_inr p · φ)
                    (bincoprod_cocone_inr q))
    : bincoprod_1cell p q
    := (φ ,, τ ,, θ).

  Definition eq_bincoprod_1cell
             {p q : bincoprod_cocone}
             (φ ψ : bincoprod_1cell p q)
             (r₁ : pr1 φ = pr1 ψ)
             (r₂ : pr1 (bincoprod_1cell_inl φ)
                   =
                   (bincoprod_cocone_inl p ◃ idtoiso_2_1 _ _ r₁) • pr1 (bincoprod_1cell_inl ψ))
             (r₃ : pr1 (bincoprod_1cell_inr φ)
                   =
                   (bincoprod_cocone_inr p ◃ idtoiso_2_1 _ _ r₁) • pr1 (bincoprod_1cell_inr ψ))
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
      rewrite lwhisker_id2, id2_left in r₂.
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
    rewrite lwhisker_id2, id2_left in r₃.
    exact r₃.
  Qed.

  (** Statements of universal mapping properties of coproducts *)
  Section UniversalMappingPropertyStatements.
    Variable (p : bincoprod_cocone).

    Definition bincoprod_ump_1
      : UU
      := ∏ (q : bincoprod_cocone), bincoprod_1cell p q.

    Definition bincoprod_ump_2
      : UU
      := ∏ (a : B)
           (φ ψ : p --> a)
           (α : bincoprod_cocone_inl p · φ
                ==>
                bincoprod_cocone_inl p · ψ)
           (β : bincoprod_cocone_inr p · φ
                ==>
                bincoprod_cocone_inr p · ψ),
         ∃! (γ : φ ==> ψ),
         (bincoprod_cocone_inl p ◃ γ = α)
         ×
         (bincoprod_cocone_inr p ◃ γ = β).

    Definition has_bincoprod_ump
      : UU
      := bincoprod_ump_1 × bincoprod_ump_2.

    Definition has_bincoprod_ump_1
               (H : has_bincoprod_ump)
      : bincoprod_ump_1
      := pr1 H.

    Definition has_bincoprod_ump_2
               (H : has_bincoprod_ump)
      : bincoprod_ump_2
      := pr2 H.

    Definition has_bincoprod_ump_2_cell
      : UU
      := ∏ (a : B)
           (φ ψ : p --> a)
           (α : bincoprod_cocone_inl p · φ
                ==>
                bincoprod_cocone_inl p · ψ)
           (β : bincoprod_cocone_inr p · φ
                ==>
                bincoprod_cocone_inr p · ψ),
         φ ==> ψ.

    Definition has_bincoprod_ump_2_cell_pr1
               (υ : has_bincoprod_ump_2_cell)
      := ∏ (a : B)
           (φ ψ : p --> a)
           (α : bincoprod_cocone_inl p · φ
                ==>
                bincoprod_cocone_inl p · ψ)
           (β : bincoprod_cocone_inr p · φ
                ==>
                bincoprod_cocone_inr p · ψ),
         bincoprod_cocone_inl p ◃ υ a φ ψ α β = α.

    Definition has_bincoprod_ump_2_cell_pr2
               (υ : has_bincoprod_ump_2_cell)
      := ∏ (a : B)
           (φ ψ : p --> a)
           (α : bincoprod_cocone_inl p · φ
                ==>
                bincoprod_cocone_inl p · ψ)
           (β : bincoprod_cocone_inr p · φ
                ==>
                bincoprod_cocone_inr p · ψ),
         bincoprod_cocone_inr p ◃ υ a φ ψ α β = β.

    Definition has_bincoprod_ump_2_cell_unique
      : UU
      := ∏ (a : B)
           (φ ψ : p --> a)
           (α : bincoprod_cocone_inl p · φ
                ==>
                bincoprod_cocone_inl p · ψ)
           (β : bincoprod_cocone_inr p · φ
                ==>
                bincoprod_cocone_inr p · ψ)
           (γ δ : φ ==> ψ)
           (γinl : bincoprod_cocone_inl p ◃ γ = α)
           (γinr : bincoprod_cocone_inr p ◃ γ = β)
           (δinl : bincoprod_cocone_inl p ◃ δ = α)
           (δinr : bincoprod_cocone_inr p ◃ δ = β),
         γ = δ.

    Definition make_bincoprod_ump
               (υ₁ : bincoprod_ump_1)
               (υ₂ : has_bincoprod_ump_2_cell)
               (υ₂pr1 : has_bincoprod_ump_2_cell_pr1 υ₂)
               (υ₂pr2 : has_bincoprod_ump_2_cell_pr2 υ₂)
               (υ₃ : has_bincoprod_ump_2_cell_unique)
      : has_bincoprod_ump.
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
    Context {p : bincoprod_cocone}
            (H : has_bincoprod_ump p).

    Definition bincoprod_ump_1cell
               {a : B}
               (ainl : b₁ --> a)
               (ainr : b₂ --> a)
      : p --> a
      := has_bincoprod_ump_1 _ H (make_bincoprod_cocone a ainl ainr).

    Definition bincoprod_ump_1cell_inl
               (a : B)
               (ainl : b₁ --> a)
               (ainr : b₂ --> a)
      : invertible_2cell
          (bincoprod_cocone_inl p · bincoprod_ump_1cell ainl ainr)
          ainl
      := bincoprod_1cell_inl
           (has_bincoprod_ump_1 _ H (make_bincoprod_cocone a ainl ainr)).

    Definition bincoprod_ump_1cell_inr
               (a : B)
               (ainl : b₁ --> a)
               (ainr : b₂ --> a)
      : invertible_2cell
          (bincoprod_cocone_inr p · bincoprod_ump_1cell ainl ainr)
          ainr
      := bincoprod_1cell_inr
           (has_bincoprod_ump_1 _ H (make_bincoprod_cocone a ainl ainr)).

    Definition bincoprod_ump_2cell
               {a : B}
               {φ ψ : p --> a}
               (α : bincoprod_cocone_inl p · φ
                    ==>
                    bincoprod_cocone_inl p · ψ)
               (β : bincoprod_cocone_inr p · φ
                    ==>
                    bincoprod_cocone_inr p · ψ)
      : φ ==> ψ
      := pr11 (has_bincoprod_ump_2 _ H a φ ψ α β).

    Definition bincoprod_ump_2cell_inl
               {a : B}
               {φ ψ : p --> a}
               (α : bincoprod_cocone_inl p · φ
                    ==>
                    bincoprod_cocone_inl p · ψ)
               (β : bincoprod_cocone_inr p · φ
                    ==>
                    bincoprod_cocone_inr p · ψ)
      : bincoprod_cocone_inl p ◃ bincoprod_ump_2cell α β = α
      := pr121 (has_bincoprod_ump_2 _ H a φ ψ α β).

    Definition bincoprod_ump_2cell_inr
               {a : B}
               {φ ψ : p --> a}
               (α : bincoprod_cocone_inl p · φ
                    ==>
                    bincoprod_cocone_inl p · ψ)
               (β : bincoprod_cocone_inr p · φ
                    ==>
                    bincoprod_cocone_inr p · ψ)
      : bincoprod_cocone_inr p ◃ bincoprod_ump_2cell α β = β
      := pr221 (has_bincoprod_ump_2 _ H a φ ψ α β).

    Definition bincoprod_ump_2cell_unique
               {a : B}
               {φ ψ : p --> a}
               (α : bincoprod_cocone_inl p · φ
                    ==>
                    bincoprod_cocone_inl p · ψ)
               (β : bincoprod_cocone_inr p · φ
                    ==>
                    bincoprod_cocone_inr p · ψ)
               (γ δ : φ ==> ψ)
               (γinl : bincoprod_cocone_inl p ◃ γ = α)
               (γinr : bincoprod_cocone_inr p ◃ γ = β)
               (δinl : bincoprod_cocone_inl p ◃ δ = α)
               (δinr : bincoprod_cocone_inr p ◃ δ = β)
      : γ = δ.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (has_bincoprod_ump_2 _ H a φ ψ α β))
                  (γ ,, (γinl ,, γinr))
                  (δ ,, (δinl ,, δinr)))).
    Qed.

    Definition bincoprod_ump_2cell_unique_alt
               {a : B}
               {φ ψ : p --> a}
               (γ δ : φ ==> ψ)
               (pinl : bincoprod_cocone_inl p ◃ γ = bincoprod_cocone_inl p ◃ δ)
               (pinr : bincoprod_cocone_inr p ◃ γ = bincoprod_cocone_inr p ◃ δ)
      : γ = δ.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr
                     (has_bincoprod_ump_2
                        _
                        H a φ ψ
                        _ _))
                  (γ ,, (idpath _ ,, idpath _))
                  (δ ,, (!pinl ,, !pinr)))).
    Qed.

    Definition bincoprod_ump_2cell_invertible
               {a : B}
               {φ ψ : p --> a}
               (α : bincoprod_cocone_inl p · φ
                    ==>
                    bincoprod_cocone_inl p · ψ)
               (β : bincoprod_cocone_inr p · φ
                    ==>
                    bincoprod_cocone_inr p · ψ)
               (Hα : is_invertible_2cell α)
               (Hβ : is_invertible_2cell β)
      : is_invertible_2cell (bincoprod_ump_2cell α β).
    Proof.
      use make_is_invertible_2cell.
      - exact (bincoprod_ump_2cell (Hα^-1) (Hβ^-1)).
      - use (bincoprod_ump_2cell_unique (id2 _) (id2 _)).
        + abstract
            (rewrite <- !lwhisker_vcomp ;
             rewrite !bincoprod_ump_2cell_inl ;
             rewrite vcomp_rinv ;
             apply idpath).
        + abstract
            (rewrite <- !lwhisker_vcomp ;
             rewrite !bincoprod_ump_2cell_inr ;
             rewrite vcomp_rinv ;
             apply idpath).
        + abstract (apply lwhisker_id2).
        + abstract (apply lwhisker_id2).
      - use (bincoprod_ump_2cell_unique (id2 _) (id2 _)).
        + abstract
            (rewrite <- !lwhisker_vcomp ;
             rewrite !bincoprod_ump_2cell_inl ;
             rewrite vcomp_linv ;
             apply idpath).
        + abstract
            (rewrite <- !lwhisker_vcomp ;
             rewrite !bincoprod_ump_2cell_inr ;
             rewrite vcomp_linv ;
             apply idpath).
        + abstract (apply lwhisker_id2).
        + abstract (apply lwhisker_id2).
    Defined.
  End Projections.

  Definition isaprop_has_bincoprod_ump
             (p : bincoprod_cocone)
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop (has_bincoprod_ump p).
  Proof.
    use invproofirrelevance.
    intros χ₁ χ₂.
    use pathsdirprod.
    - use funextsec ; intro q.
      use eq_bincoprod_1cell.
      + use (isotoid_2_1 HB_2_1).
        use make_invertible_2cell.
        * use (bincoprod_ump_2cell χ₂).
          ** exact (comp_of_invertible_2cell
                      (bincoprod_1cell_inl (pr1 χ₁ q))
                      (inv_of_invertible_2cell
                         (bincoprod_1cell_inl (pr1 χ₂ q)))).
          ** exact (comp_of_invertible_2cell
                      (bincoprod_1cell_inr (pr1 χ₁ q))
                      (inv_of_invertible_2cell
                         (bincoprod_1cell_inr (pr1 χ₂ q)))).
        * use bincoprod_ump_2cell_invertible.
          ** apply property_from_invertible_2cell.
          ** apply property_from_invertible_2cell.
      + rewrite idtoiso_2_1_isotoid_2_1.
        cbn.
        rewrite bincoprod_ump_2cell_inl.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      + rewrite idtoiso_2_1_isotoid_2_1.
        cbn.
        rewrite bincoprod_ump_2cell_inr.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
    - repeat (use funextsec ; intro).
      apply isapropiscontr.
  Qed.

  (**
   Formulation via hom-categories
   *)
  Definition universal_coprod_functor_data
             (p : bincoprod_cocone)
             (x : B)
    : functor_data
        (hom p x)
        (category_binproduct (hom b₁ x) (hom b₂ x)).
  Proof.
    use make_functor_data.
    - exact (λ f,
             bincoprod_cocone_inl p · f
             ,,
             bincoprod_cocone_inr p · f).
    - exact (λ f₁ f₂ α,
             _ ◃ α
             ,,
             _ ◃ α).
  Defined.

  Definition universal_coprod_is_functor
             (p : bincoprod_cocone)
             (x : B)
    : is_functor (universal_coprod_functor_data p x).
  Proof.
    split.
    - intro f.
      use pathsdirprod ; cbn.
      + apply lwhisker_id2.
      + apply lwhisker_id2.
    - intros f₁ f₂ f₃ α β.
      use pathsdirprod ; cbn.
      + refine (!_).
        apply lwhisker_vcomp.
      + refine (!_).
        apply lwhisker_vcomp.
  Qed.

  Definition universal_coprod_functor
             (p : bincoprod_cocone)
             (x : B)
    : hom p x ⟶ category_binproduct (hom b₁ x) (hom b₂ x).
  Proof.
    use make_functor.
    - exact (universal_coprod_functor_data p x).
    - exact (universal_coprod_is_functor p x).
  Defined.

  Definition is_universal_coprod_cocone
             (p : bincoprod_cocone)
    : UU
    := ∏ (x : B),
       adj_equivalence_of_cats
         (universal_coprod_functor p x).

  (**
   Equivalence of the two formulations
   *)
  Section UniversalFromUMP.
    Context {p : bincoprod_cocone}
            (Hp : has_bincoprod_ump p)
            (x : B).

    Definition make_is_universal_coprod_cocone_full
      : full (universal_coprod_functor p x).
    Proof.
      intros u₁ u₂ α.
      apply hinhpr.
      simple refine (_ ,, _).
      - use (bincoprod_ump_2cell Hp).
        + exact (pr1 α).
        + exact (pr2 α).
      - use pathsdirprod.
        + apply bincoprod_ump_2cell_inl.
        + apply bincoprod_ump_2cell_inr.
    Defined.

    Definition make_is_universal_coprod_cocone_faithful
      : faithful (universal_coprod_functor p x).
    Proof.
      intros u₁ u₂ α.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (bincoprod_ump_2cell_unique Hp).
      - exact (pr1 α).
      - exact (pr2 α).
      - exact (maponpaths pr1 (pr2 φ₁)).
      - exact (maponpaths dirprod_pr2 (pr2 φ₁)).
      - exact (maponpaths pr1 (pr2 φ₂)).
      - exact (maponpaths dirprod_pr2 (pr2 φ₂)).
    Qed.

    Definition make_is_universal_coprod_cocone_essentially_surjective
      : essentially_surjective (universal_coprod_functor p x).
    Proof.
      intros f.
      use hinhpr.
      simple refine (_ ,, _).
      - exact (bincoprod_ump_1cell Hp (pr1 f) (pr2 f)).
      - use category_binproduct_z_iso_map.
        refine (_ ,, _).
        + use inv2cell_to_z_iso ; cbn.
          apply bincoprod_ump_1cell_inl.
        + use inv2cell_to_z_iso ; cbn.
          apply bincoprod_ump_1cell_inr.
    Defined.
  End UniversalFromUMP.

  Definition make_is_universal_coprod_cocone
             (HB_2_1 : is_univalent_2_1 B)
             (p : bincoprod_cocone)
             (Hp : has_bincoprod_ump p)
    : is_universal_coprod_cocone p.
  Proof.
    intro x.
    use rad_equivalence_of_cats.
    - apply is_univ_hom.
      exact HB_2_1.
    - use full_and_faithful_implies_fully_faithful.
      split.
      + apply make_is_universal_coprod_cocone_full.
        apply Hp.
      + apply make_is_universal_coprod_cocone_faithful.
        apply Hp.
    - apply make_is_universal_coprod_cocone_essentially_surjective.
      apply Hp.
  Defined.

  Section UniversalCoprodHasUMP.
    Context (p : bincoprod_cocone)
            (Hp : is_universal_coprod_cocone p).

    Definition universal_coprod_cocone_has_ump_1
      : bincoprod_ump_1 p.
    Proof.
      intro q.
      use make_bincoprod_1cell.
      - exact (right_adjoint
                 (Hp q)
                 (bincoprod_cocone_inl q ,, bincoprod_cocone_inr q)).
      - apply z_iso_to_inv2cell.
        exact (pr1 (category_binproduct_z_iso_inv
                      _ _
                      (nat_z_iso_pointwise_z_iso
                         (counit_nat_z_iso_from_adj_equivalence_of_cats (Hp q))
                         (bincoprod_cocone_inl q ,, bincoprod_cocone_inr q)))).
      - apply z_iso_to_inv2cell.
        exact (pr2 (category_binproduct_z_iso_inv
                      _ _
                      (nat_z_iso_pointwise_z_iso
                         (counit_nat_z_iso_from_adj_equivalence_of_cats (Hp q))
                         (bincoprod_cocone_inl q ,, bincoprod_cocone_inr q)))).
    Defined.

    Definition universal_coprod_cocone_has_ump_2_unique
               {x : B}
               {u₁ u₂ : p --> x}
               (ζ₁ : bincoprod_cocone_inl p · u₁
                     ==>
                     bincoprod_cocone_inl p · u₂)
               (ζ₂ : bincoprod_cocone_inr p · u₁
                     ==>
                     bincoprod_cocone_inr p · u₂)
      : isaprop
          (∑ (γ : u₁ ==> u₂),
           bincoprod_cocone_inl p ◃ γ = ζ₁
           ×
           bincoprod_cocone_inr p ◃ γ = ζ₂).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      use (invmaponpathsweq
             (make_weq
                _
                (fully_faithful_from_equivalence _ _ _ (Hp x) u₁ u₂))) ; cbn.
      apply pathsdirprod.
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - exact (pr22 φ₁ @ !(pr22 φ₂)).
    Qed.

    Definition universal_coprod_cocone_has_ump_2
      : bincoprod_ump_2 p.
    Proof.
      intros x u₁ u₂ ζ₁ ζ₂.
      use iscontraprop1.
      - exact (universal_coprod_cocone_has_ump_2_unique ζ₁ ζ₂).
      - simple refine (_ ,, _ ,, _).
        + exact (invmap
                   (make_weq
                      _
                      (fully_faithful_from_equivalence _ _ _ (Hp x) u₁ u₂))
                   (ζ₁ ,, ζ₂)).
        + abstract
            (exact (maponpaths
                      pr1
                      (homotweqinvweq
                         (make_weq
                            _
                            (fully_faithful_from_equivalence _ _ _ (Hp x) u₁ u₂))
                         (ζ₁ ,, ζ₂)))).
        + abstract
            (exact (maponpaths
                      dirprod_pr2
                      (homotweqinvweq
                         (make_weq
                            _
                            (fully_faithful_from_equivalence _ _ _ (Hp x) u₁ u₂))
                         (ζ₁ ,, ζ₂)))).
    Defined.
  End UniversalCoprodHasUMP.

  Definition universal_coprod_cocone_has_ump
             (p : bincoprod_cocone)
             (Hp : is_universal_coprod_cocone p)
    : has_bincoprod_ump p.
  Proof.
    refine (_ ,, _).
    - exact (universal_coprod_cocone_has_ump_1 p Hp).
    - exact (universal_coprod_cocone_has_ump_2 p Hp).
  Defined.

  Definition isaprop_is_universal_inserter_cone
             (HB_2_1 : is_univalent_2_1 B)
             (p : bincoprod_cocone)
    : isaprop (is_universal_coprod_cocone p).
  Proof.
    use impred ; intro x.
    use isofhlevelweqf.
    - exact (@left_adjoint_equivalence
               bicat_of_univ_cats
               (univ_hom HB_2_1 _ _)
               (univalent_category_binproduct
                  (univ_hom HB_2_1 _ _)
                  (univ_hom HB_2_1 _ _))
               (universal_coprod_functor p x)).
    - exact (@adj_equiv_is_equiv_cat
               (univ_hom HB_2_1 _ _)
               (univalent_category_binproduct
                  (univ_hom HB_2_1 _ _)
                  (univ_hom HB_2_1 _ _))
               (universal_coprod_functor p x)).
    - apply isaprop_left_adjoint_equivalence.
      exact univalent_cat_is_univalent_2_1.
  Qed.

  Definition has_binprod_ump_weq_universal
             (HB_2_1 : is_univalent_2_1 B)
             (p : bincoprod_cocone)
    : has_bincoprod_ump p ≃ is_universal_coprod_cocone p.
  Proof.
    use weqimplimpl.
    - exact (make_is_universal_coprod_cocone HB_2_1 p).
    - exact (universal_coprod_cocone_has_ump p).
    - apply isaprop_has_bincoprod_ump.
      exact HB_2_1.
    - apply isaprop_is_universal_inserter_cone.
      exact HB_2_1.
  Defined.
End Coproduct.

Arguments bincoprod_cocone {_} _ _.

Definition has_bincoprod
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ : B),
     ∑ (p : bincoprod_cocone b₁ b₂),
     has_bincoprod_ump p.

Definition bicat_with_bincoprod
  : UU
  := ∑ (B : bicat), has_bincoprod B.

Coercion bicat_with_bincoprod_to_bicat
         (B : bicat_with_bincoprod)
  : bicat
  := pr1 B.

Definition bincoprod_of
           (B : bicat_with_bincoprod)
  : has_bincoprod B
  := pr2 B.

(**
 Some useful functions
 *)
Section StandardFunctions.
  Context (B : bicat_with_bincoprod).

  Definition bincoprod
             (b₁ b₂ : B)
    : B
    := pr1 (bincoprod_of B b₁ b₂).

  Local Notation "b₁ ⊕ b₂" := (bincoprod b₁ b₂).

  Definition bincoprod_inl
             (b₁ b₂ : B)
    : b₁ --> b₁ ⊕ b₂
    := bincoprod_cocone_inl (pr1 (bincoprod_of B b₁ b₂)).

  Definition bincoprod_inr
             (b₁ b₂ : B)
    : b₂ --> b₁ ⊕ b₂
    := bincoprod_cocone_inr (pr1 (bincoprod_of B b₁ b₂)).

  Local Notation "'ι₁'" := (bincoprod_inl _ _).
  Local Notation "'ι₂'" := (bincoprod_inr _ _).

  Definition coprod_1cell
             {b₁ b₂ c : B}
             (f : b₁ --> c)
             (g : b₂ --> c)
    : b₁ ⊕ b₂ --> c
    := bincoprod_ump_1cell (pr2 (bincoprod_of B b₁ b₂)) f g.

  Local Notation "[ f , g ]" := (coprod_1cell f g).

  Definition coprod_1cell_inl
             {b₁ b₂ c : B}
             (f : b₁ --> c)
             (g : b₂ --> c)
    : invertible_2cell (ι₁ · [ f , g ]) f
    := bincoprod_ump_1cell_inl (pr2 (bincoprod_of B b₁ b₂)) _ f g.

  Definition coprod_1cell_inr
             {b₁ b₂ c : B}
             (f : b₁ --> c)
             (g : b₂ --> c)
    : invertible_2cell (ι₂ · [ f , g ]) g
    := bincoprod_ump_1cell_inr (pr2 (bincoprod_of B b₁ b₂)) _ f g.

  Definition sum_1cell
             {a₁ a₂ b₁ b₂ : B}
             (f : a₁ --> b₁)
             (g : a₂ --> b₂)
    : a₁ ⊕ a₂ --> b₁ ⊕ b₂
    := [ f · ι₁ , g · ι₂ ].

  Local Notation "f '⊕₁' g" := (sum_1cell f g) (at level 34, left associativity).

  Definition sum_1cell_inl
             {a₁ a₂ b₁ b₂ : B}
             (f : a₁ --> b₁)
             (g : a₂ --> b₂)
    : invertible_2cell (ι₁ · f ⊕₁ g) (f · ι₁)
    := coprod_1cell_inl (f · ι₁) (g · ι₂).

  Definition sum_1cell_inr
             {a₁ a₂ b₁ b₂ : B}
             (f : a₁ --> b₁)
             (g : a₂ --> b₂)
    : invertible_2cell (ι₂ · f ⊕₁ g) (g · ι₂)
    := coprod_1cell_inr (f · ι₁) (g · ι₂).

  Definition coprod_2cell
             {b₁ b₂ c : B}
             {f₁ f₂ : b₁ --> c}
             {g₁ g₂ : b₂ --> c}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : [ f₁ , g₁ ] ==> [ f₂ , g₂ ].
  Proof.
    use (bincoprod_ump_2cell (pr2 (bincoprod_of B b₁ b₂))).
    - exact (coprod_1cell_inl f₁ g₁ • α • (coprod_1cell_inl f₂ g₂)^-1).
    - exact (coprod_1cell_inr f₁ g₁ • β • (coprod_1cell_inr f₂ g₂)^-1).
  Defined.

  Local Notation "[[ α , β ]]" := (coprod_2cell α β).

  Definition coprod_2cell_is_invertible
             {b₁ b₂ c : B}
             {f₁ f₂ : b₁ --> c}
             {g₁ g₂ : b₂ --> c}
             {α : f₁ ==> f₂}
             {β : g₁ ==> g₂}
             (Hα : is_invertible_2cell α)
             (Hβ : is_invertible_2cell β)
    : is_invertible_2cell [[ α , β ]].
  Proof.
    use bincoprod_ump_2cell_invertible.
    - is_iso.
      apply property_from_invertible_2cell.
    - is_iso.
      apply property_from_invertible_2cell.
  Defined.

  Definition coprod_2cell_inl
             {b₁ b₂ c : B}
             {f₁ f₂ : b₁ --> c}
             {g₁ g₂ : b₂ --> c}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ι₁ ◃ [[ α , β ]]
      =
      coprod_1cell_inl f₁ g₁ • α • (coprod_1cell_inl f₂ g₂)^-1
    := bincoprod_ump_2cell_inl _ _ _.

  Definition coprod_2cell_inr
             {b₁ b₂ c : B}
             {f₁ f₂ : b₁ --> c}
             {g₁ g₂ : b₂ --> c}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ι₂ ◃ [[ α , β ]]
      =
      coprod_1cell_inr f₁ g₁ • β • (coprod_1cell_inr f₂ g₂)^-1
    := bincoprod_ump_2cell_inr _ _ _.

  Definition sum_2cell
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ : a₁ --> b₁}
             {g₁ g₂ : a₂ --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : f₁ ⊕₁ g₁ ==> f₂ ⊕₁ g₂
    := [[ α ▹ ι₁ , β ▹ ι₂ ]].

  Local Notation "α '⊕₂' β" := (sum_2cell α β) (at level 34, left associativity).

  Definition sum_2cell_inl
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ : a₁ --> b₁}
             {g₁ g₂ : a₂ --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ι₁ ◃ (α ⊕₂ β)
      =
      sum_1cell_inl f₁ g₁
      • (α ▹ ι₁)
      • (sum_1cell_inl f₂ g₂)^-1
    := coprod_2cell_inl (α ▹ ι₁) (β ▹ ι₂).

  Definition sum_2cell_inr
             {a₁ a₂ b₁ b₂ : B}
             {f₁ f₂ : a₁ --> b₁}
             {g₁ g₂ : a₂ --> b₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==> g₂)
    : ι₂ ◃ (α ⊕₂ β)
      =
      sum_1cell_inr f₁ g₁
      • (β ▹ ι₂)
      • (sum_1cell_inr f₂ g₂)^-1
    := coprod_2cell_inr (α ▹ ι₁) (β ▹ ι₂).
End StandardFunctions.

Module Notations.
  Notation "b₁ ⊕ b₂" := (bincoprod _ b₁ b₂).
  Notation "'ι₁'" := (bincoprod_inl _ _ _).
  Notation "'ι₂'" := (bincoprod_inr _ _ _).
  Notation "[ f , g ]" := (coprod_1cell _ f g).
  Notation "[[ α , β ]]" := (coprod_2cell _ α β).
  Notation "f '⊕₁' g" := (sum_1cell _ f g) (at level 34, left associativity).
  Notation "α '⊕₂' β" := (sum_2cell _ α β) (at level 34, left associativity).
End Notations.
