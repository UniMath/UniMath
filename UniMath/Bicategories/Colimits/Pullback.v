(****************************************************************
 Pullbacks in bicategories

 In this file we define the notion of pullback square in arbitrary
 bicategories. This definition is expressed using universal
 properties.

 Content
 1. Cones
 2. 1-cells and 2-cells of cones
 3. Statements of universal mapping properties of pullbacks
 4. Being a pullback is a property (requires local univalence)
 5. Bicategories with pullbacks
 6. 1-Types has pullbacks
 7. The bicategory of univalent categories has pullbacks
 8. The bicategory of univalent groupoids has pullbacks
 9. Pullbacks from reindexing
 10. Mirroring pullbacks
 11. Pullbacks in op2

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.

Local Open Scope cat.

Section Pullback.
  Context {B : bicat}
          {b₁ b₂ b₃ : B}
          {f : b₁ --> b₃}
          {g : b₂ --> b₃}.

  (**
    1. Cones
   *)
  Definition pb_cone
    : UU
    := ∑ (p : B)
         (π₁ : p --> b₁)
         (π₂ : p --> b₂),
       invertible_2cell (π₁ · f) (π₂ · g).

  Coercion pb_cone_obj
           (p : pb_cone)
    : B
    := pr1 p.

  Definition pb_cone_pr1
             (p : pb_cone)
    : p --> b₁
    := pr12 p.

  Definition pb_cone_pr2
             (p : pb_cone)
    : p --> b₂
    := pr122 p.

  Definition pb_cone_cell
             (p : pb_cone)
    : invertible_2cell
        (pb_cone_pr1 p · f)
        (pb_cone_pr2 p · g)
    := pr222 p.

  Definition make_pb_cone
             (p : B)
             (π₁ : p --> b₁)
             (π₂ : p --> b₂)
             (η : invertible_2cell (π₁ · f) (π₂ · g))
    : pb_cone
    := (p ,, π₁ ,, π₂ ,, η).

  (**
   2. 1-cells and 2-cells of cones
   *)
  Definition pb_1cell
             (p q : pb_cone)
    : UU
    := ∑ (φ : p --> q)
         (τ : invertible_2cell
                (φ · pb_cone_pr1 q)
                (pb_cone_pr1 p))
         (θ : invertible_2cell
                (φ · pb_cone_pr2 q)
                (pb_cone_pr2 p)),
       φ ◃ pb_cone_cell q
       =
       lassociator _ _ _
       • (τ ▹ f)
       • pb_cone_cell p
       • (θ^-1 ▹ g)
       • rassociator _ _ _.

  Coercion pb_1cell_1cell
           {p q : pb_cone}
           (φ : pb_1cell p q)
    : p --> q
    := pr1 φ.

  Definition pb_1cell_pr1
             {p q : pb_cone}
             (φ : pb_1cell p q)
    : invertible_2cell
        (φ · pb_cone_pr1 q)
        (pb_cone_pr1 p)
    := pr12 φ.

  Definition pb_1cell_pr2
             {p q : pb_cone}
             (φ : pb_1cell p q)
    : invertible_2cell
        (φ · pb_cone_pr2 q)
        (pb_cone_pr2 p)
    := pr122 φ.

  Definition pb_1cell_eq
             {p q : pb_cone}
             (φ : pb_1cell p q)
    : φ ◃ pb_cone_cell q
      =
      lassociator _ _ _
      • (pb_1cell_pr1 φ ▹ f)
      • pb_cone_cell p
      • ((pb_1cell_pr2 φ)^-1 ▹ g)
      • rassociator _ _ _
    := pr222 φ.

  Definition make_pb_1cell
             {p q : pb_cone}
             (φ : p --> q)
             (τ : invertible_2cell
                    (φ · pb_cone_pr1 q)
                    (pb_cone_pr1 p))
             (θ : invertible_2cell
                    (φ · pb_cone_pr2 q)
                    (pb_cone_pr2 p))
             (H : φ ◃ pb_cone_cell q
                  =
                  lassociator _ _ _
                  • (τ ▹ f)
                  • pb_cone_cell p
                  • (θ^-1 ▹ g)
                  • rassociator _ _ _)
    : pb_1cell p q
    := (φ ,, τ ,, θ ,, H).

  Definition eq_pb_1cell
             {p q : pb_cone}
             (φ ψ : pb_1cell p q)
             (r₁ : pr1 φ = pr1 ψ)
             (r₂ : pr1 (pb_1cell_pr1 φ)
                   =
                   (idtoiso_2_1 _ _ r₁ ▹ pb_cone_pr1 q) • pr1 (pb_1cell_pr1 ψ))
             (r₃ : pr1 (pb_1cell_pr2 φ)
                   =
                   (idtoiso_2_1 _ _ r₁ ▹ pb_cone_pr2 q) • pr1 (pb_1cell_pr2 ψ))
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
      intro ; apply cellset_property.
    }
    cbn.
    cbn in r₃.
    rewrite id2_rwhisker, id2_left in r₃.
    use subtypePath.
    {
      intro ; apply isaprop_is_invertible_2cell.
    }
    exact r₃.
  Qed.

  Definition pb_2cell
             {p q : pb_cone}
             (φ ψ : pb_1cell p q)
    : UU
    := ∑ (η : φ ==> ψ),
       ((η ▹ pb_cone_pr1 q) • pb_1cell_pr1 ψ = pb_1cell_pr1 φ)
       ×
       ((η ▹ pb_cone_pr2 q) • pb_1cell_pr2 ψ = pb_1cell_pr2 φ).

  Coercion pb_2cell_2cell
           {p q : pb_cone}
           {φ ψ : pb_1cell p q}
           (η : pb_2cell φ ψ)
    : φ ==> ψ
    := pr1 η.

  Definition pb_2cell_pr1
             {p q : pb_cone}
             {φ ψ : pb_1cell p q}
             (η : pb_2cell φ ψ)
    : (η ▹ pb_cone_pr1 q) • pb_1cell_pr1 ψ = pb_1cell_pr1 φ
    := pr12 η.

  Definition pb_2cell_pr2
             {p q : pb_cone}
             {φ ψ : pb_1cell p q}
             (η : pb_2cell φ ψ)
    : (η ▹ pb_cone_pr2 q) • pb_1cell_pr2 ψ = pb_1cell_pr2 φ
    := pr22 η.

  Definition make_pb_2cell
             {p q : pb_cone}
             {φ ψ : pb_1cell p q}
             (η : φ ==> ψ)
             (H₁ : (η ▹ pb_cone_pr1 q) • pb_1cell_pr1 ψ = pb_1cell_pr1 φ)
             (H₂ : (η ▹ pb_cone_pr2 q) • pb_1cell_pr2 ψ = pb_1cell_pr2 φ)
    : pb_2cell φ ψ
    := (η ,, H₁ ,, H₂).

  Definition isaset_pb_2cell
             {p q : pb_cone}
             (φ ψ : pb_1cell p q)
    : isaset (pb_2cell φ ψ).
  Proof.
    use isaset_total2.
    - apply cellset_property.
    - intro.
      apply isasetdirprod ; apply isasetaprop ; apply cellset_property.
  Qed.

  Definition id2_pb_2cell
             {p q : pb_cone}
             (φ : pb_1cell p q)
    : pb_2cell φ φ.
  Proof.
    use make_pb_2cell.
    - exact (id2 φ).
    - abstract
        (rewrite id2_rwhisker, id2_left ;
         apply idpath).
    - abstract
        (rewrite id2_rwhisker, id2_left ;
         apply idpath).
  Defined.

  Definition comp_pb_2cell
             {p q : pb_cone}
             {φ ψ χ : pb_1cell p q}
             (η₁ : pb_2cell φ ψ)
             (η₂ : pb_2cell ψ χ)
    : pb_2cell φ χ.
  Proof.
    use make_pb_2cell.
    - exact (η₁ • η₂).
    - abstract
        (rewrite <- rwhisker_vcomp ;
         rewrite vassocl ;
         rewrite !pb_2cell_pr1 ;
         apply idpath).
    - abstract
        (rewrite <- rwhisker_vcomp ;
         rewrite vassocl ;
         rewrite !pb_2cell_pr2 ;
         apply idpath).
  Defined.

  (**
   3. Statements of universal mapping properties of pullbacks
   *)
  Section UniversalMappingPropertyStatements.
    Variable (p : pb_cone).

    Definition pb_ump_1
      : UU
      := ∏ (q : pb_cone), pb_1cell q p.

    Definition pb_ump_2
      : UU
      := ∏ (q : B)
           (φ ψ : q --> p)
           (α : φ · pb_cone_pr1 p ==> ψ · pb_cone_pr1 p)
           (β : φ · pb_cone_pr2 p ==> ψ · pb_cone_pr2 p)
           (r : (φ ◃ pb_cone_cell p)
                • lassociator _ _ _
                • (β ▹ g)
                • rassociator _ _ _
                =
                lassociator _ _ _
                • (α ▹ f)
                • rassociator _ _ _
                • (ψ ◃ pb_cone_cell p)),
         ∃! (γ : φ ==> ψ),
         (γ ▹ pb_cone_pr1 p = α)
         ×
         (γ ▹ pb_cone_pr2 p = β).

    Definition has_pb_ump
      : UU
      := pb_ump_1 × pb_ump_2.
  End UniversalMappingPropertyStatements.

  Definition has_pb_ump_1
             {p : pb_cone}
             (H : has_pb_ump p)
    : pb_ump_1 p
    := pr1 H.

  Definition has_pb_ump_2
             {p : pb_cone}
             (H : has_pb_ump p)
    : pb_ump_2 p
    := pr2 H.

  Section Projections.
    Context {p : pb_cone}
            (Hp : has_pb_ump p).

    Definition pb_ump_mor
               (q : pb_cone)
      : q --> p
      := pr1 Hp q.

    Definition pb_ump_mor_pr1
               (q : pb_cone)
      : invertible_2cell
          (pb_ump_mor q · pb_cone_pr1 p)
          (pb_cone_pr1 q)
      := pb_1cell_pr1 (pr1 Hp q).

    Definition pb_ump_mor_pr2
               (q : pb_cone)
      : invertible_2cell
          (pb_ump_mor q · pb_cone_pr2 p)
          (pb_cone_pr2 q)
      := pb_1cell_pr2 (pr1 Hp q).

    Definition pb_ump_mor_cell
               (q : pb_cone)
      : pr1 Hp q ◃ pb_cone_cell p
        =
        lassociator (pr1 Hp q) (pb_cone_pr1 p) f
        • (pb_1cell_pr1 (pr1 Hp q) ▹ f)
        • pb_cone_cell q
        • ((pb_1cell_pr2 (pr1 Hp q)) ^-1 ▹ g)
        • rassociator (pr1 Hp q) (pb_cone_pr2 p) g
      := pb_1cell_eq (pr1 Hp q).

    Section CellProperty.
      Context {q : B}
              (φ ψ : q --> p)
              (α : φ · pb_cone_pr1 p ==> ψ · pb_cone_pr1 p)
              (β : φ · pb_cone_pr2 p ==> ψ · pb_cone_pr2 p)
              (r : (φ ◃ pb_cone_cell p)
                   • lassociator _ _ _
                   • (β ▹ g)
                   • rassociator _ _ _
                   =
                   lassociator _ _ _
                   • (α ▹ f)
                   • rassociator _ _ _
                   • (ψ ◃ pb_cone_cell p)).

      Definition pb_ump_cell
        : φ ==> ψ
        := pr11 (pr2 Hp q φ ψ α β r).

      Definition pb_ump_cell_pr1
        : pb_ump_cell ▹ pb_cone_pr1 p = α
        := pr121 (pr2 Hp q φ ψ α β r).

      Definition pb_ump_cell_pr2
        : pb_ump_cell ▹ pb_cone_pr2 p = β
        := pr221 (pr2 Hp q φ ψ α β r).

      Definition pb_ump_eq
                 (τ₁ τ₂ : φ ==> ψ)
                 (τ₁_pr1 : τ₁ ▹ pb_cone_pr1 p = α)
                 (τ₁_pr2 : τ₁ ▹ pb_cone_pr2 p = β)
                 (τ₂_pr1 : τ₂ ▹ pb_cone_pr1 p = α)
                 (τ₂_pr2 : τ₂ ▹ pb_cone_pr2 p = β)
        : τ₁ = τ₂
        := maponpaths
             pr1
             (proofirrelevance
                _
                (isapropifcontr (pr2 Hp q φ ψ α β r))
                (τ₁ ,, τ₁_pr1 ,, τ₁_pr2)
                (τ₂ ,, τ₂_pr1 ,, τ₂_pr2)).
      End CellProperty.
  End Projections.

  Section InvertiblePBUmpCell.
    Context {p : pb_cone}
            (Hp : has_pb_ump p)
            {q : B}
            {φ ψ : q --> p}
            {α : φ · pb_cone_pr1 p ==> ψ · pb_cone_pr1 p}
            {β : φ · pb_cone_pr2 p ==> ψ · pb_cone_pr2 p}
            (r : (φ ◃ pb_cone_cell p)
                   • lassociator _ _ _
                   • (β ▹ g)
                   • rassociator _ _ _
                 =
                 lassociator _ _ _
                             • (α ▹ f)
                             • rassociator _ _ _
                             • (ψ ◃ pb_cone_cell p))
            (Hα : is_invertible_2cell α)
            (Hβ : is_invertible_2cell β).

    Definition is_invertible_2cell_pb_ump_cell_inv : ψ ==> φ.
    Proof.
      use (pb_ump_cell Hp _ _ (Hα^-1) (Hβ^-1)).
      abstract
        (do 3 (use vcomp_move_R_Mp ; [ is_iso | ]) ;
         rewrite !vassocl ;
         do 3 (use vcomp_move_L_pM ; [ is_iso | ]) ;
         cbn ;
         rewrite !vassocr ;
         exact (!r)).
    Defined.

    Lemma is_invertible_2cell_pb_ump_cell_left
      : pb_ump_cell Hp φ ψ α β r • is_invertible_2cell_pb_ump_cell_inv
        =
        id₂ φ.
    Proof.
      use (pb_ump_eq Hp).
      - apply id2.
      - apply id2.
      - rewrite !id2_rwhisker, !id2_right.
        rewrite lassociator_rassociator, id2_left.
        rewrite vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      - unfold is_invertible_2cell_pb_ump_cell_inv.
        rewrite <- rwhisker_vcomp.
        rewrite !pb_ump_cell_pr1.
        apply vcomp_rinv.
      - unfold is_invertible_2cell_pb_ump_cell_inv.
        rewrite <- rwhisker_vcomp.
        rewrite !pb_ump_cell_pr2.
        apply vcomp_rinv.
      - apply id2_rwhisker.
      - apply id2_rwhisker.
    Qed.

    Lemma is_invertible_2cell_pb_ump_cell_right
      : is_invertible_2cell_pb_ump_cell_inv • pb_ump_cell Hp φ ψ α β r
        =
        id₂ _.
    Proof.
      use (pb_ump_eq Hp).
      - apply id2.
      - apply id2.
      - rewrite !id2_rwhisker, !id2_right.
        rewrite lassociator_rassociator, id2_left.
        rewrite vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      - unfold is_invertible_2cell_pb_ump_cell_inv.
        rewrite <- rwhisker_vcomp.
        rewrite !pb_ump_cell_pr1.
        apply vcomp_linv.
      - unfold is_invertible_2cell_pb_ump_cell_inv.
        rewrite <- rwhisker_vcomp.
        rewrite !pb_ump_cell_pr2.
        apply vcomp_linv.
      - apply id2_rwhisker.
      - apply id2_rwhisker.
    Qed.

    Definition is_invertible_2cell_pb_ump_cell
      : is_invertible_2cell (pb_ump_cell Hp φ ψ α β r).
    Proof.
      use make_is_invertible_2cell.
      - exact is_invertible_2cell_pb_ump_cell_inv.
      - exact is_invertible_2cell_pb_ump_cell_left.
      - exact is_invertible_2cell_pb_ump_cell_right.
    Defined.
  End InvertiblePBUmpCell.

  (**
   4. Being a pullback is a property (requires local univalence)
   *)
  Definition isaprop_has_pb_ump
             (HB_2_1 : is_univalent_2_1 B)
             (p : pb_cone)
    : isaprop (has_pb_ump p).
  Proof.
    use invproofirrelevance.
    intros χ₁ χ₂.
    use subtypePath.
    {
      intro.
      do 6 (use impred ; intro).
      apply isapropiscontr.
    }
    use funextsec ; intro q.
    use eq_pb_1cell ; cbn.
    - use (isotoid_2_1 HB_2_1).
      use make_invertible_2cell.
      + use (pb_ump_cell χ₁).
        * exact (pb_ump_mor_pr1 χ₁ q • (pb_ump_mor_pr1 χ₂ q)^-1).
        * exact (pb_ump_mor_pr2 χ₁ q • (pb_ump_mor_pr2 χ₂ q)^-1).
        * abstract
            (refine (!_) ;
             refine (maponpaths (λ z, _ • z) (pb_ump_mor_cell χ₂ q) @ _) ;
             rewrite !vassocl ;
             refine (!_) ;
             refine (maponpaths (λ z, z • _) (pb_ump_mor_cell χ₁ q) @ _) ;
             rewrite <- !rwhisker_vcomp ;
             rewrite !vassocl ;
             do 2 apply maponpaths ;
             rewrite !vassocr ;
             do 2 apply maponpaths_2 ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite rwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite id2_rwhisker ;
             rewrite id2_right ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite rassociator_lassociator ;
             rewrite id2_left ;
             rewrite !vassocr ;
             rewrite rwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite id2_rwhisker ;
             rewrite id2_left ;
             apply idpath).
      + use make_is_invertible_2cell.
        * use (pb_ump_cell χ₁).
          ** exact (pb_ump_mor_pr1 χ₂ q • (pb_ump_mor_pr1 χ₁ q)^-1).
          ** exact (pb_ump_mor_pr2 χ₂ q • (pb_ump_mor_pr2 χ₁ q)^-1).
          ** abstract
               (refine (!_) ;
                refine (maponpaths (λ z, _ • z) (pb_ump_mor_cell χ₁ q) @ _) ;
                rewrite !vassocl ;
                refine (!_) ;
                refine (maponpaths (λ z, z • _) (pb_ump_mor_cell χ₂ q) @ _) ;
                rewrite <- !rwhisker_vcomp ;
                rewrite !vassocl ;
                do 2 apply maponpaths ;
                rewrite !vassocr ;
                do 2 apply maponpaths_2 ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
                rewrite rassociator_lassociator ;
                rewrite id2_left ;
                rewrite rwhisker_vcomp ;
                rewrite vcomp_linv ;
                rewrite id2_rwhisker ;
                rewrite id2_right ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
                rewrite rassociator_lassociator ;
                rewrite id2_left ;
                rewrite !vassocr ;
                rewrite rwhisker_vcomp ;
                rewrite vcomp_linv ;
                rewrite id2_rwhisker ;
                rewrite id2_left ;
                apply idpath).
        * use (pb_ump_eq χ₁ _ _ (id₂ _) (id₂ _)).
          ** abstract
               (rewrite !id2_rwhisker ;
                rewrite !id2_right ;
                rewrite lassociator_rassociator ;
                rewrite !vassocl ;
                rewrite lassociator_rassociator ;
                rewrite id2_left, id2_right ;
                apply idpath).
          ** abstract
               (rewrite <- rwhisker_vcomp ;
                rewrite !pb_ump_cell_pr1 ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
                rewrite vcomp_linv ;
                rewrite id2_left ;
                rewrite vcomp_rinv ;
                apply idpath).
          ** abstract
               (rewrite <- rwhisker_vcomp ;
                rewrite !pb_ump_cell_pr2 ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
                rewrite vcomp_linv ;
                rewrite id2_left ;
                rewrite vcomp_rinv ;
                apply idpath).
          ** apply id2_rwhisker.
          ** apply id2_rwhisker.
        * use (pb_ump_eq χ₁ _ _ (id₂ _) (id₂ _)).
          ** abstract
               (rewrite !id2_rwhisker ;
                rewrite !id2_right ;
                rewrite lassociator_rassociator ;
                rewrite !vassocl ;
                rewrite lassociator_rassociator ;
                rewrite id2_left, id2_right ;
                apply idpath).
          ** abstract
               (rewrite <- rwhisker_vcomp ;
                rewrite !pb_ump_cell_pr1 ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
                rewrite vcomp_linv ;
                rewrite id2_left ;
                rewrite vcomp_rinv ;
                apply idpath).
          ** abstract
               (rewrite <- rwhisker_vcomp ;
                rewrite !pb_ump_cell_pr2 ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
                rewrite vcomp_linv ;
                rewrite id2_left ;
                rewrite vcomp_rinv ;
                apply idpath).
          ** apply id2_rwhisker.
          ** apply id2_rwhisker.
    - abstract
        (rewrite idtoiso_2_1_isotoid_2_1 ; cbn ;
         refine (!_) ;
         rewrite pb_ump_cell_pr1 ;
         rewrite !vassocl ;
         rewrite vcomp_linv ;
         apply id2_right).
    - abstract
        (rewrite idtoiso_2_1_isotoid_2_1 ; cbn ;
         refine (!_) ;
         rewrite pb_ump_cell_pr2 ;
         rewrite !vassocl ;
         rewrite vcomp_linv ;
         apply id2_right).
    Qed.
End Pullback.

Arguments pb_cone {_ _ _ _} _ _.

(**
 5. Bicategories with pullbacks
 *)
Definition has_pb
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ b₃ : B)
       (f : b₁ --> b₃)
       (g : b₂ --> b₃),
     ∑ (p : pb_cone f g),
     has_pb_ump p.

Definition bicat_with_pb
  : UU
  := ∑ (B : bicat), has_pb B.

Coercion bicat_with_pb_to_bicat
         (B : bicat_with_pb)
  : bicat
  := pr1 B.

(**
 6. 1-Types has pullbacks
 *)
Definition one_types_pb_cone
           {X Y Z : one_types}
           (f : X --> Z)
           (g : Y --> Z)
  : pb_cone f g.
Proof.
  use make_pb_cone.
  - exact (hfp_HLevel 3 f g).
  - exact (hfpg f g).
  - exact (hfpg' f g).
  - use make_invertible_2cell.
    + exact (λ x, !(commhfp f g x)).
    + apply one_type_2cell_iso.
Defined.

Section OneTypesPb.
  Context {X Y Z : one_types}
          (f : X --> Z)
          (g : Y --> Z).

  Definition one_types_pb_ump_1
    : pb_ump_1 (one_types_pb_cone f g).
  Proof.
    intro q.
    use make_pb_1cell.
    - exact (λ x, (pb_cone_pr1 q x ,, pb_cone_pr2 q x) ,, !(pr1 (pb_cone_cell q) x)).
    - use make_invertible_2cell.
      + intro x ; cbn.
        apply idpath.
      + apply one_type_2cell_iso.
    - use make_invertible_2cell.
      + intro x ; cbn.
        apply idpath.
      + apply one_type_2cell_iso.
    - abstract
        (use funextsec ;
         intro x ; cbn ;
         unfold homotcomp, homotfun, invhomot ;
         cbn ;
         rewrite !pathscomp0rid ;
         apply pathsinv0inv0).
  Defined.

  Definition one_types_pb_ump_2
    : pb_ump_2 (one_types_pb_cone f g).
  Proof.
    intros W φ ψ α β r.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use funextsec ; intro x ;
         use homot_hfp_one_type ;
         [ apply Z
         | exact (eqtohomot (pr12 τ₁) x @ !(eqtohomot (pr12 τ₂) x))
         | exact (eqtohomot (pr22 τ₁) x @ !(eqtohomot (pr22 τ₂) x)) ]).
    - simple refine (_ ,, _).
      + intro x.
        use path_hfp.
        * exact (α x).
        * exact (β x).
        * abstract
            (pose (eqtohomot r x) as p ;
             cbn in p ;
             unfold homotcomp, funhomotsec, homotfun in p ;
             cbn in p ;
             rewrite !pathscomp0rid in p ;
             use hornRotation_lr ;
             rewrite !path_assoc ;
             refine (_ @ maponpaths (λ z, z @ _) (!p)) ;
             rewrite <- !path_assoc ;
             rewrite pathsinv0l ;
             rewrite pathscomp0rid ;
             apply idpath).
      + split.
        * abstract
            (use funextsec ; intro x ;
             apply maponpaths_hfpg_path_hfp).
        * abstract
            (use funextsec ; intro x ;
             apply maponpaths_hfpg'_path_hfp).
  Defined.
End OneTypesPb.

Definition one_types_has_pb
  : has_pb one_types.
Proof.
  intros X Y Z f g.
  simple refine (_ ,, _ ,, _).
  - exact (one_types_pb_cone f g).
  - exact (one_types_pb_ump_1 f g).
  - exact (one_types_pb_ump_2 f g).
Defined.

(**
 7. The bicategory of univalent categories has pullbacks
 *)
Definition iso_comma_pb_cone
           {C₁ C₂ C₃ : bicat_of_univ_cats}
           (F : C₁ --> C₃)
           (G : C₂ --> C₃)
  : pb_cone F G.
Proof.
  use make_pb_cone.
  - exact (univalent_iso_comma F G).
  - exact (iso_comma_pr1 F G).
  - exact (iso_comma_pr2 F G).
  - apply nat_iso_to_invertible_2cell.
    exact (iso_comma_commute F G).
Defined.

Section IsoCommaUMP.
  Context {C₁ C₂ C₃ : bicat_of_univ_cats}
          (F : C₁ --> C₃)
          (G : C₂ --> C₃).

  Definition pb_ump_1_iso_comma
    : pb_ump_1 (iso_comma_pb_cone F G).
  Proof.
    intro q.
    use make_pb_1cell.
    - use iso_comma_ump1.
      + exact (pb_cone_pr1 q).
      + exact (pb_cone_pr2 q).
      + apply invertible_2cell_to_nat_iso.
        exact (pb_cone_cell q).
    - apply nat_iso_to_invertible_2cell.
      apply iso_comma_ump1_pr1.
    - apply nat_iso_to_invertible_2cell.
      apply iso_comma_ump1_pr2.
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ; unfold pb_cone_cell ;
         rewrite (functor_id F), (functor_id G) ;
         rewrite !id_left, !id_right ;
         apply idpath).
  Defined.

  Section CellUMP.
    Let p := iso_comma_pb_cone F G.

    Context {q : bicat_of_univ_cats}
            (φ ψ : q --> p)
            (α : φ · pb_cone_pr1 p ==> ψ · pb_cone_pr1 p)
            (β : φ · pb_cone_pr2 p ==> ψ · pb_cone_pr2 p)
            (r : (φ ◃ pb_cone_cell p)
                 • lassociator _ _ _
                 • (β ▹ G)
                 • rassociator _ _ _
                 =
                 lassociator _ _ _
                 • (α ▹ F)
                 • rassociator _ _ _
                 • (ψ ◃ pb_cone_cell p)).

    Definition pb_ump_2_nat_trans
      : φ ==> ψ.
    Proof.
      use (iso_comma_ump2 _ _ _ _ α β).
      abstract
        (intros x ;
         pose (nat_trans_eq_pointwise r x) as z ;
         cbn in z ;
         unfold iso_comma_commute_nat_trans_data in z ;
         rewrite !id_left, !id_right in z ;
         exact z).
    Defined.

    Definition pb_ump_2_nat_trans_pr1
      : pb_ump_2_nat_trans ▹ pb_cone_pr1 (iso_comma_pb_cone F G) = α.
    Proof.
      apply iso_comma_ump2_pr1.
    Qed.

    Definition pb_ump_2_nat_trans_pr2
      : pb_ump_2_nat_trans ▹ pb_cone_pr2 (iso_comma_pb_cone F G) = β.
    Proof.
      apply iso_comma_ump2_pr2.
    Qed.
  End CellUMP.

  Definition pb_ump_2_iso_comma
    : pb_ump_2 (iso_comma_pb_cone F G).
  Proof.
    intros C φ ψ α β r.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         exact (iso_comma_ump_eq _ _ _ _ α β (pr12 τ₁) (pr22 τ₁) (pr12 τ₂) (pr22 τ₂))).
    - simple refine (_ ,, _).
      + exact (pb_ump_2_nat_trans φ ψ α β r).
      + split.
        * exact (pb_ump_2_nat_trans_pr1 φ ψ α β r).
        * exact (pb_ump_2_nat_trans_pr2 φ ψ α β r).
  Defined.

  Definition iso_comma_has_pb_ump
    : has_pb_ump (iso_comma_pb_cone F G).
  Proof.
    split.
    - exact pb_ump_1_iso_comma.
    - exact pb_ump_2_iso_comma.
  Defined.
End IsoCommaUMP.

Definition has_pb_bicat_of_univ_cats
  : has_pb bicat_of_univ_cats.
Proof.
  intros C₁ C₂ C₃ F G.
  simple refine (_ ,, _).
  - exact (iso_comma_pb_cone F G).
  - exact (iso_comma_has_pb_ump F G).
Defined.

(** 8. The bicategory of univalent groupoids has pullbacks *)
Definition grpds_iso_comma_pb_cone
           {C₁ C₂ C₃ : grpds}
           (F : C₁ --> C₃)
           (G : C₂ --> C₃)
  : pb_cone F G.
Proof.
  use make_pb_cone.
  - exact (univalent_iso_comma (pr1 F) (pr1 G)
           ,,
           is_pregroupoid_iso_comma _ _ (pr2 C₁) (pr2 C₂)).
  - refine (_ ,, tt).
    apply iso_comma_pr1.
  - refine (_ ,, tt).
    apply iso_comma_pr2.
  - use make_invertible_2cell.
    + refine (_ ,, tt).
      apply iso_comma_commute.
    + apply locally_groupoid_grpds.
Defined.

Section IsoCommaUMP.
  Context {C₁ C₂ C₃ : grpds}
          (F : C₁ --> C₃)
          (G : C₂ --> C₃).

  Definition pb_ump_1_grpds_iso_comma
    : pb_ump_1 (grpds_iso_comma_pb_cone F G).
  Proof.
    intro q.
    use make_pb_1cell.
    - refine (_ ,, tt).
      use iso_comma_ump1.
      + exact (pr1 (pb_cone_pr1 q)).
      + exact (pr1 (pb_cone_pr2 q)).
      + exact (grpds_2cell_to_nat_iso (pr1 (pb_cone_cell q))).
    - use make_invertible_2cell.
      + refine (_ ,, tt).
        apply iso_comma_ump1_pr1.
      + apply locally_groupoid_grpds.
    - use make_invertible_2cell.
      + refine (_ ,, tt).
        apply iso_comma_ump1_pr2.
      + apply locally_groupoid_grpds.
    - abstract
        (use subtypePath ; [ intro ; apply isapropunit | ] ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intros x ; cbn ; unfold pb_cone_cell ;
         rewrite (functor_on_inv_from_iso (pr1 G)) ;
         rewrite (functor_id (pr1 F)) ;
         rewrite !id_left, id_right ;
         refine (!(id_right _) @ _) ;
         apply maponpaths ;
         use inv_iso_unique' ;
         unfold precomp_with ;
         cbn ;
         rewrite id_right ;
         apply functor_id).
  Defined.

  Section CellUMP.
    Let p := grpds_iso_comma_pb_cone F G.

    Context {q : grpds}
            (φ ψ : q --> p)
            (α : φ · pb_cone_pr1 p ==> ψ · pb_cone_pr1 p)
            (β : φ · pb_cone_pr2 p ==> ψ · pb_cone_pr2 p)
            (r : (φ ◃ pb_cone_cell p)
                 • lassociator _ _ _
                 • (β ▹ G)
                 • rassociator _ _ _
                 =
                 lassociator _ _ _
                 • (α ▹ F)
                 • rassociator _ _ _
                 • (ψ ◃ pb_cone_cell p)).

    Definition pb_ump_2_grpds_nat_trans
      : φ ==> ψ.
    Proof.
      refine (_ ,, tt).
      use (iso_comma_ump2 _ _ _ _ (pr1 α) (pr1 β)).
      abstract
        (intros x ;
         pose (nat_trans_eq_pointwise (maponpaths pr1 r) x) as z ;
         cbn in z ;
         unfold iso_comma_commute_nat_trans_data in z ;
         rewrite !id_left, !id_right in z ;
         exact z).
    Defined.

    Definition pb_ump_2_grpds_nat_trans_pr1
      : pb_ump_2_grpds_nat_trans ▹ pb_cone_pr1 _ = α.
    Proof.
      use subtypePath ; [ intro ; apply isapropunit | ].
      apply iso_comma_ump2_pr1.
    Qed.

    Definition pb_ump_2_grpds_nat_trans_pr2
      : pb_ump_2_grpds_nat_trans ▹ _ = β.
    Proof.
      use subtypePath ; [ intro ; apply isapropunit | ].
      apply iso_comma_ump2_pr2.
    Qed.
  End CellUMP.

  Definition pb_ump_2_grpds_iso_comma
    : pb_ump_2 (grpds_iso_comma_pb_cone F G).
  Proof.
    intros C φ ψ α β r.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use subtypePath ; [ intro ; apply isapropunit | ] ;
         exact (iso_comma_ump_eq
                  _ _ _ _ _ _
                  (maponpaths pr1 (pr12 τ₁))
                  (maponpaths pr1 (pr22 τ₁))
                  (maponpaths pr1 (pr12 τ₂))
                  (maponpaths pr1 (pr22 τ₂)))).
    - simple refine (_ ,, _).
      + exact (pb_ump_2_grpds_nat_trans φ ψ α β r).
      + split.
        * exact (pb_ump_2_grpds_nat_trans_pr1 φ ψ α β r).
        * exact (pb_ump_2_grpds_nat_trans_pr2 φ ψ α β r).
  Defined.

  Definition grpds_iso_comma_has_pb_ump
    : has_pb_ump (grpds_iso_comma_pb_cone F G).
  Proof.
    split.
    - exact pb_ump_1_grpds_iso_comma.
    - exact pb_ump_2_grpds_iso_comma.
  Defined.
End IsoCommaUMP.

Definition has_pb_grpds
  : has_pb grpds.
Proof.
  intros C₁ C₂ C₃ F G.
  simple refine (_ ,, _).
  - exact (grpds_iso_comma_pb_cone F G).
  - exact (grpds_iso_comma_has_pb_ump F G).
Defined.

(**
  9. Pullbacks from reindexing
 *)
Section ReindexingPullback.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (F : C₁ --> C₂)
          (D₂ : disp_univalent_category (pr1 C₂))
          (HD₂ : iso_cleaving (pr1 D₂)).

  Let tot_D₂ : bicat_of_univ_cats
    := total_univalent_category D₂.
  Let pb : bicat_of_univ_cats
    := univalent_reindex_cat F D₂.
  Let π₁ : pb --> _
    := pr1_category _.
  Let π₂ : pb --> tot_D₂
    := total_functor (reindex_disp_cat_disp_functor F D₂).
  Let γ : invertible_2cell (π₁ · F) (π₂ · pr1_category D₂)
    := nat_iso_to_invertible_2cell
         (π₁ · F)
         (π₂ · pr1_category D₂)
         (total_functor_commute_iso (reindex_disp_cat_disp_functor F (pr1 D₂))).
  Let cone : pb_cone F (pr1_category _ : tot_D₂ --> C₂)
    := make_pb_cone pb π₁ π₂ γ.

  Definition reindexing_has_pb_ump_1_cell
             (q : pb_cone F (pr1_category _ : tot_D₂ --> C₂))
    : q --> cone.
  Proof.
    use reindex_pb_ump_1.
    - exact HD₂.
    - exact (pb_cone_pr2 q).
    - exact (pb_cone_pr1 q).
    - apply invertible_2cell_to_nat_iso.
      exact (pb_cone_cell q).
  Defined.

  Definition reindexing_has_pb_ump_1_pr1
             (q : pb_cone F (pr1_category _ : tot_D₂ --> C₂))
    : invertible_2cell
        (reindexing_has_pb_ump_1_cell q · pb_cone_pr1 cone)
        (pb_cone_pr1 q).
  Proof.
    use nat_iso_to_invertible_2cell.
    exact (reindex_pb_ump_1_pr1_nat_iso
             F D₂ HD₂
             (pb_cone_pr2 q)
             (pb_cone_pr1 q)
             (invertible_2cell_to_nat_iso
                _ _
                (pb_cone_cell q))).
  Defined.

  Definition reindexing_has_pb_ump_1_pr2
             (q : pb_cone F (pr1_category _ : tot_D₂ --> C₂))
    : invertible_2cell
        (reindexing_has_pb_ump_1_cell q · pb_cone_pr2 cone)
        (pb_cone_pr2 q).
  Proof.
    use nat_iso_to_invertible_2cell.
    exact (reindex_pb_ump_1_pr2_nat_iso
             F D₂ HD₂
             (pb_cone_pr2 q)
             (pb_cone_pr1 q)
             (invertible_2cell_to_nat_iso
                _ _
                (pb_cone_cell q))).
  Defined.

  Definition reindexing_has_pb_ump_1_pb_cell
             (q : pb_cone F (pr1_category _ : tot_D₂ --> C₂))
    : reindexing_has_pb_ump_1_cell q ◃ pb_cone_cell cone
      =
      lassociator _ _ _
      • (reindexing_has_pb_ump_1_pr1 q ▹ F)
      • pb_cone_cell q
      • ((reindexing_has_pb_ump_1_pr2 q)^-1 ▹ _)
      • rassociator _ _ _.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    refine (!_).
    refine (id_right _ @ _).
    etrans.
    {
      do 2 refine (maponpaths (λ z, z · _) _).
      apply id_left.
    }
    etrans.
    {
      do 2 refine (maponpaths (λ z, z · _) _).
      exact (functor_id F _).
    }
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).
      apply id_left.
    }
    etrans.
    {
      apply maponpaths.
      exact (inv_from_iso_in_total
               (is_invertible_2cell_to_is_nat_iso _ (pr2 (pb_cone_cell q)) x)
               _).
    }
    etrans.
    {
      apply maponpaths.
      apply id_right.
    }
    exact (nat_trans_eq_pointwise
             (vcomp_rinv
                (pb_cone_cell q))
             x).
  Qed.

  Definition reindexing_has_pb_ump_1
    : pb_ump_1 cone.
  Proof.
    intro q.
    use make_pb_1cell.
    - exact (reindexing_has_pb_ump_1_cell q).
    - exact (reindexing_has_pb_ump_1_pr1 q).
    - exact (reindexing_has_pb_ump_1_pr2 q).
    - exact (reindexing_has_pb_ump_1_pb_cell q).
  Defined.

  Definition reindexing_has_pb_ump_2
    : pb_ump_2 cone.
  Proof.
    intros C₀ G₁ G₂ τ₁ τ₂ p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         exact (reindex_pb_ump_eq
                  _ _ _ _
                  τ₁ τ₂
                  _ _
                  (pr12 φ₁)
                  (pr22 φ₁)
                  (pr12 φ₂)
                  (pr22 φ₂))).
    - simple refine (_ ,, _ ,, _).
      + use reindex_pb_ump_2.
        * exact τ₁.
        * exact τ₂.
        * abstract
            (intro x ;
             pose (nat_trans_eq_pointwise p x) as q ;
             cbn in q ;
             rewrite !id_left, !id_right in q ;
             exact q).
      + apply reindex_pb_ump_2_pr1.
      + apply reindex_pb_ump_2_pr2.
  Defined.

  Definition reindexing_has_pb_ump
    : has_pb_ump cone.
  Proof.
    split.
    - exact reindexing_has_pb_ump_1.
    - exact reindexing_has_pb_ump_2.
  Defined.
End ReindexingPullback.

(**
 10. Mirroring pullbacks
 *)
Definition mirror_cone
           {B : bicat}
           {x y z : B}
           {f : x --> z}
           {g : y --> z}
           (p : pb_cone f g)
  : pb_cone g f
  := make_pb_cone
       p
       (pb_cone_pr2 p) (pb_cone_pr1 p)
       (inv_of_invertible_2cell (pb_cone_cell p)).

Section Mirroring.
  Context {B : bicat}
          {pb x y z : B}
          {f : x --> z}
          {g : y --> z}
          {p₁ : pb --> x}
          {p₂ : pb --> y}
          {γ : invertible_2cell (p₁ · f) (p₂ · g)}
          (cone := make_pb_cone pb p₁ p₂ γ)
          (pb_sqr : has_pb_ump cone).

  Definition mirror_has_pb_ump
    : has_pb_ump (mirror_cone cone).
  Proof.
    split.
    - intros q.
      use make_pb_1cell.
      + exact (pb_ump_mor pb_sqr (mirror_cone q)).
      + exact (pb_ump_mor_pr2 pb_sqr (mirror_cone q)).
      + exact (pb_ump_mor_pr1 pb_sqr (mirror_cone q)).
      + abstract
          (pose (r := pb_ump_mor_cell pb_sqr (mirror_cone q)) ;
           cbn in r ;
           cbn ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           do 2 (use vcomp_move_L_pM ; [ is_iso | ] ; cbn) ;
           rewrite !vassocl in r ;
           exact (!r)).
    - intros w φ ψ α β q.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros ζ₁ ζ₂ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
           refine (pb_ump_eq
                     pb_sqr
                     φ ψ β α
                     _ _ _
                     (pr22 ζ₁) (pr12 ζ₁)
                     (pr22 ζ₂) (pr12 ζ₂)) ;
           rewrite !vassocl ;
           cbn in q ;
           use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite q ;
           rewrite !vassocl ;
           rewrite lwhisker_vcomp ;
           rewrite vcomp_linv ;
           rewrite lwhisker_id2 ;
           rewrite id2_right ;
           apply idpath).
      + simple refine (_ ,, _ ,, _).
        * use (pb_ump_cell pb_sqr φ ψ β α).
          abstract
            (rewrite !vassocl ;
             cbn in q ;
             use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
             cbn ;
             rewrite !vassocr ;
             rewrite q ;
             rewrite !vassocl ;
             rewrite lwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite lwhisker_id2 ;
             rewrite id2_right ;
             apply idpath).
        * exact (pb_ump_cell_pr2 pb_sqr φ ψ β α _).
        * exact (pb_ump_cell_pr1 pb_sqr φ ψ β α _).
  Defined.
End Mirroring.

(**
 11. Pullbacks in op2
 *)
Definition to_op2_pb_cone
           {B : bicat}
           {pb x y z : B}
           {f : x --> z}
           {g : y --> z}
           {p₁ : pb --> x}
           {p₂ : pb --> y}
           (γ : invertible_2cell (p₁ · f) (p₂ · g))
           (cone := make_pb_cone pb p₁ p₂ γ)
  : @pb_cone (op2_bicat B) _ _ _ f g.
Proof.
  use make_pb_cone.
  - exact pb.
  - exact p₁.
  - exact p₂.
  - apply bicat_invertible_2cell_is_op2_bicat_invertible_2cell.
    exact (inv_of_invertible_2cell γ).
Defined.

Definition from_op2_pb_cone
           {B : bicat}
           {x y z : B}
           {f : x --> z}
           {g : y --> z}
           (cone : @pb_cone (op2_bicat B) _ _ _ f g)
  : pb_cone f g.
Proof.
  use make_pb_cone.
  - exact cone.
  - exact (pb_cone_pr1 cone).
  - exact (pb_cone_pr2 cone).
  - exact (inv_of_invertible_2cell
             (invmap
                (bicat_invertible_2cell_is_op2_bicat_invertible_2cell _ _)
                (pb_cone_cell cone))).
Defined.

Section ToOp2Pullback.
  Context {B : bicat}
          {pb x y z : B}
          {f : x --> z}
          {g : y --> z}
          {p₁ : pb --> x}
          {p₂ : pb --> y}
          (γ : invertible_2cell (p₁ · f) (p₂ · g))
          (cone := make_pb_cone pb p₁ p₂ γ)
          (H : has_pb_ump cone).

  Definition to_op2_pb_ump_1
    : pb_ump_1 (to_op2_pb_cone γ).
  Proof.
    intro q.
    use make_pb_1cell ; cbn.
    - exact (pb_ump_mor H (from_op2_pb_cone q)).
    - apply bicat_invertible_2cell_is_op2_bicat_invertible_2cell.
      exact (inv_of_invertible_2cell
               (pb_ump_mor_pr1 H (from_op2_pb_cone q))).
    - apply bicat_invertible_2cell_is_op2_bicat_invertible_2cell.
      exact (inv_of_invertible_2cell
               (pb_ump_mor_pr2 H (from_op2_pb_cone q))).
    - abstract
        (cbn ;
         pose (pb_ump_mor_cell H (from_op2_pb_cone q)) as p ; cbn in p ;
         use vcomp_move_L_pM ; [ is_iso | ] ;
         use vcomp_move_R_Mp ; [ is_iso | ] ;
         cbn ;
         rewrite !vassocl ;
         use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         use vcomp_move_L_pM ;
         [ apply op2_bicat_is_invertible_2cell_to_bicat_is_invertible_2cell ;
           apply property_from_invertible_2cell
         | ] ;
         cbn ;
         use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         use vcomp_move_L_pM ; [ is_iso | ] ;
         cbn ;
         refine (_ @ !p) ;
         rewrite !vassocl ;
         apply idpath).
  Defined.

  Definition to_op2_pb_ump_2
    : pb_ump_2 (to_op2_pb_cone γ).
  Proof.
    intros w φ ψ α β p ; cbn in p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros ζ₁ ζ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use (pb_ump_eq H _ _ α β _ _ _ (pr12 ζ₁) (pr22 ζ₁) (pr12 ζ₂) (pr22 ζ₂)) ;
         cbn ; cbn in p ;
         rewrite !vassocl ;
         use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         cbn ;
         rewrite !vassocr ;
         use vcomp_move_L_Mp ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         cbn ;
         rewrite !vassocl ;
         exact p).
    - simple refine (_ ,, _).
      + use (pb_ump_cell H ψ φ α β).
        abstract
          (cbn ; cbn in p ;
           rewrite !vassocl ;
           use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocr ;
           use vcomp_move_L_Mp ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocl ;
           exact p).
      + split.
        * apply (pb_ump_cell_pr1 H ψ φ α β).
        * apply (pb_ump_cell_pr2 H ψ φ α β).
  Defined.

  Definition to_op2_has_pb_ump
    : has_pb_ump (to_op2_pb_cone γ).
  Proof.
    split.
    - exact to_op2_pb_ump_1.
    - exact to_op2_pb_ump_2.
  Defined.
End ToOp2Pullback.
