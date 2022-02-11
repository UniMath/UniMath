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
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.

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
