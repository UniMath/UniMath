(****************************************************************
 Comma objects in bicategories

 In this file we define the notion of comma squares in arbitrary
 bicategories. This definition is expressed using universal
 properties.

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.

Section CommaObject.
  Context {B : bicat}
          {b₁ b₂ b₃ : B}
          {f : b₁ --> b₃}
          {g : b₂ --> b₃}.

  (**
    1. Cones
   *)
  Definition comma_cone
    : UU
    := ∑ (p : B)
         (π₁ : p --> b₁)
         (π₂ : p --> b₂),
       π₁ · f ==> π₂ · g.

  Coercion comma_cone_obj
           (p : comma_cone)
    : B
    := pr1 p.

  Definition comma_cone_pr1
             (p : comma_cone)
    : p --> b₁
    := pr12 p.

  Definition comma_cone_pr2
             (p : comma_cone)
    : p --> b₂
    := pr122 p.

  Definition comma_cone_cell
             (p : comma_cone)
    : comma_cone_pr1 p · f ==> comma_cone_pr2 p · g
    := pr222 p.

  Definition make_comma_cone
             (p : B)
             (π₁ : p --> b₁)
             (π₂ : p --> b₂)
             (η : π₁ · f ==> π₂ · g)
    : comma_cone
    := (p ,, π₁ ,, π₂ ,, η).

  (**
   2. 1-cells and 2-cells of cones
   *)
  Definition comma_1cell
             (p q : comma_cone)
    : UU
    := ∑ (φ : p --> q)
         (τ : invertible_2cell
                (φ · comma_cone_pr1 q)
                (comma_cone_pr1 p))
         (θ : invertible_2cell
                (φ · comma_cone_pr2 q)
                (comma_cone_pr2 p)),
       φ ◃ comma_cone_cell q
       =
       lassociator _ _ _
       • (τ ▹ f)
       • comma_cone_cell p
       • (θ^-1 ▹ g)
       • rassociator _ _ _.

  Coercion comma_1cell_1cell
           {p q : comma_cone}
           (φ : comma_1cell p q)
    : p --> q
    := pr1 φ.

  Definition comma_1cell_pr1
             {p q : comma_cone}
             (φ : comma_1cell p q)
    : invertible_2cell
        (φ · comma_cone_pr1 q)
        (comma_cone_pr1 p)
    := pr12 φ.

  Definition comma_1cell_pr2
             {p q : comma_cone}
             (φ : comma_1cell p q)
    : invertible_2cell
        (φ · comma_cone_pr2 q)
        (comma_cone_pr2 p)
    := pr122 φ.

  Definition comma_1cell_eq
             {p q : comma_cone}
             (φ : comma_1cell p q)
    : φ ◃ comma_cone_cell q
      =
      lassociator _ _ _
      • (comma_1cell_pr1 φ ▹ f)
      • comma_cone_cell p
      • ((comma_1cell_pr2 φ)^-1 ▹ g)
      • rassociator _ _ _
    := pr222 φ.

  Definition make_comma_1cell
             {p q : comma_cone}
             (φ : p --> q)
             (τ : invertible_2cell
                    (φ · comma_cone_pr1 q)
                    (comma_cone_pr1 p))
             (θ : invertible_2cell
                    (φ · comma_cone_pr2 q)
                    (comma_cone_pr2 p))
             (H : φ ◃ comma_cone_cell q
                  =
                  lassociator _ _ _
                  • (τ ▹ f)
                  • comma_cone_cell p
                  • (θ^-1 ▹ g)
                  • rassociator _ _ _)
    : comma_1cell p q
    := (φ ,, τ ,, θ ,, H).

  Definition eq_comma_1cell
             {p q : comma_cone}
             (φ ψ : comma_1cell p q)
             (r₁ : pr1 φ = pr1 ψ)
             (r₂ : pr1 (comma_1cell_pr1 φ)
                   =
                   (idtoiso_2_1 _ _ r₁ ▹ comma_cone_pr1 q) • pr1 (comma_1cell_pr1 ψ))
             (r₃ : pr1 (comma_1cell_pr2 φ)
                   =
                   (idtoiso_2_1 _ _ r₁ ▹ comma_cone_pr2 q) • pr1 (comma_1cell_pr2 ψ))
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

  (**
   3. Statements of universal mapping properties of pullbacks
   *)
  Section UniversalMappingPropertyStatements.
    Variable (p : comma_cone).

    Definition comma_ump_1
      : UU
      := ∏ (q : comma_cone), comma_1cell q p.

    Definition comma_ump_2
      : UU
      := ∏ (q : B)
           (φ ψ : q --> p)
           (α : φ · comma_cone_pr1 p ==> ψ · comma_cone_pr1 p)
           (β : φ · comma_cone_pr2 p ==> ψ · comma_cone_pr2 p)
           (r : (φ ◃ comma_cone_cell p)
                • lassociator _ _ _
                • (β ▹ g)
                • rassociator _ _ _
                =
                lassociator _ _ _
                • (α ▹ f)
                • rassociator _ _ _
                • (ψ ◃ comma_cone_cell p)),
         ∃! (γ : φ ==> ψ),
         (γ ▹ comma_cone_pr1 p = α)
         ×
         (γ ▹ comma_cone_pr2 p = β).

    Definition has_comma_ump
      : UU
      := comma_ump_1 × comma_ump_2.
  End UniversalMappingPropertyStatements.

  Definition has_comma_ump_1
             {p : comma_cone}
             (H : has_comma_ump p)
    : comma_ump_1 p
    := pr1 H.

  Definition has_comma_ump_2
             {p : comma_cone}
             (H : has_comma_ump p)
    : comma_ump_2 p
    := pr2 H.

  Section Projections.
    Context {p : comma_cone}
            (Hp : has_comma_ump p).

    Definition comma_ump_mor
               (q : comma_cone)
      : q --> p
      := pr1 Hp q.

    Definition comma_ump_mor_pr1
               (q : comma_cone)
      : invertible_2cell
          (comma_ump_mor q · comma_cone_pr1 p)
          (comma_cone_pr1 q)
      := comma_1cell_pr1 (pr1 Hp q).

    Definition comma_ump_mor_pr2
               (q : comma_cone)
      : invertible_2cell
          (comma_ump_mor q · comma_cone_pr2 p)
          (comma_cone_pr2 q)
      := comma_1cell_pr2 (pr1 Hp q).

    Definition comma_ump_mor_cell
               (q : comma_cone)
      : pr1 Hp q ◃ comma_cone_cell p
        =
        lassociator (pr1 Hp q) (comma_cone_pr1 p) f
        • (comma_1cell_pr1 (pr1 Hp q) ▹ f)
        • comma_cone_cell q
        • ((comma_1cell_pr2 (pr1 Hp q)) ^-1 ▹ g)
        • rassociator (pr1 Hp q) (comma_cone_pr2 p) g
      := comma_1cell_eq (pr1 Hp q).

    Section CellProperty.
      Context {q : B}
              (φ ψ : q --> p)
              (α : φ · comma_cone_pr1 p ==> ψ · comma_cone_pr1 p)
              (β : φ · comma_cone_pr2 p ==> ψ · comma_cone_pr2 p)
              (r : (φ ◃ comma_cone_cell p)
                   • lassociator _ _ _
                   • (β ▹ g)
                   • rassociator _ _ _
                   =
                   lassociator _ _ _
                   • (α ▹ f)
                   • rassociator _ _ _
                   • (ψ ◃ comma_cone_cell p)).

      Definition comma_ump_cell
        : φ ==> ψ
        := pr11 (pr2 Hp q φ ψ α β r).

      Definition comma_ump_cell_pr1
        : comma_ump_cell ▹ comma_cone_pr1 p = α
        := pr121 (pr2 Hp q φ ψ α β r).

      Definition comma_ump_cell_pr2
        : comma_ump_cell ▹ comma_cone_pr2 p = β
        := pr221 (pr2 Hp q φ ψ α β r).

      Definition comma_ump_eq
                 (τ₁ τ₂ : φ ==> ψ)
                 (τ₁_pr1 : τ₁ ▹ comma_cone_pr1 p = α)
                 (τ₁_pr2 : τ₁ ▹ comma_cone_pr2 p = β)
                 (τ₂_pr1 : τ₂ ▹ comma_cone_pr1 p = α)
                 (τ₂_pr2 : τ₂ ▹ comma_cone_pr2 p = β)
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

  Section InvertibleCommaUmpCell.
    Context {p : comma_cone}
            (Hp : has_comma_ump p)
            {q : B}
            {φ ψ : q --> p}
            {α : φ · comma_cone_pr1 p ==> ψ · comma_cone_pr1 p}
            {β : φ · comma_cone_pr2 p ==> ψ · comma_cone_pr2 p}
            (r : (φ ◃ comma_cone_cell p)
                   • lassociator _ _ _
                   • (β ▹ g)
                   • rassociator _ _ _
                 =
                 lassociator _ _ _
                             • (α ▹ f)
                             • rassociator _ _ _
                             • (ψ ◃ comma_cone_cell p))
            (Hα : is_invertible_2cell α)
            (Hβ : is_invertible_2cell β).

    Definition is_invertible_2cell_comma_ump_cell_inv : ψ ==> φ.
    Proof.
      use (comma_ump_cell Hp _ _ (Hα^-1) (Hβ^-1)).
      abstract
        (do 3 (use vcomp_move_R_Mp ; [ is_iso | ]) ;
         rewrite !vassocl ;
         do 3 (use vcomp_move_L_pM ; [ is_iso | ]) ;
         cbn ;
         rewrite !vassocr ;
         exact (!r)).
    Defined.

    Lemma is_invertible_2cell_comma_ump_cell_left
      : comma_ump_cell Hp φ ψ α β r • is_invertible_2cell_comma_ump_cell_inv
        =
        id₂ φ.
    Proof.
      use (comma_ump_eq Hp).
      - apply id2.
      - apply id2.
      - rewrite !id2_rwhisker, !id2_right.
        rewrite lassociator_rassociator, id2_left.
        rewrite vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      - unfold is_invertible_2cell_comma_ump_cell_inv.
        rewrite <- rwhisker_vcomp.
        rewrite !comma_ump_cell_pr1.
        apply vcomp_rinv.
      - unfold is_invertible_2cell_comma_ump_cell_inv.
        rewrite <- rwhisker_vcomp.
        rewrite !comma_ump_cell_pr2.
        apply vcomp_rinv.
      - apply id2_rwhisker.
      - apply id2_rwhisker.
    Qed.

    Lemma is_invertible_2cell_comma_ump_cell_right
      : is_invertible_2cell_comma_ump_cell_inv • comma_ump_cell Hp φ ψ α β r
        =
        id₂ _.
    Proof.
      use (comma_ump_eq Hp).
      - apply id2.
      - apply id2.
      - rewrite !id2_rwhisker, !id2_right.
        rewrite lassociator_rassociator, id2_left.
        rewrite vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      - unfold is_invertible_2cell_comma_ump_cell_inv.
        rewrite <- rwhisker_vcomp.
        rewrite !comma_ump_cell_pr1.
        apply vcomp_linv.
      - unfold is_invertible_2cell_comma_ump_cell_inv.
        rewrite <- rwhisker_vcomp.
        rewrite !comma_ump_cell_pr2.
        apply vcomp_linv.
      - apply id2_rwhisker.
      - apply id2_rwhisker.
    Qed.

    Definition is_invertible_2cell_comma_ump_cell
      : is_invertible_2cell (comma_ump_cell Hp φ ψ α β r).
    Proof.
      use make_is_invertible_2cell.
      - exact is_invertible_2cell_comma_ump_cell_inv.
      - exact is_invertible_2cell_comma_ump_cell_left.
      - exact is_invertible_2cell_comma_ump_cell_right.
    Defined.
  End InvertibleCommaUmpCell.

  (**
   4. Being a pullback is a property (requires local univalence)
   *)
  Definition isaprop_has_comma_ump
             (HB_2_1 : is_univalent_2_1 B)
             (p : comma_cone)
    : isaprop (has_comma_ump p).
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
    use eq_comma_1cell ; cbn.
    - use (isotoid_2_1 HB_2_1).
      use make_invertible_2cell.
      + use (comma_ump_cell χ₁).
        * exact (comma_ump_mor_pr1 χ₁ q • (comma_ump_mor_pr1 χ₂ q)^-1).
        * exact (comma_ump_mor_pr2 χ₁ q • (comma_ump_mor_pr2 χ₂ q)^-1).
        * abstract
            (refine (!_) ;
             refine (maponpaths (λ z, _ • z) (comma_ump_mor_cell χ₂ q) @ _) ;
             rewrite !vassocl ;
             refine (!_) ;
             refine (maponpaths (λ z, z • _) (comma_ump_mor_cell χ₁ q) @ _) ;
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
        * use (comma_ump_cell χ₁).
          ** exact (comma_ump_mor_pr1 χ₂ q • (comma_ump_mor_pr1 χ₁ q)^-1).
          ** exact (comma_ump_mor_pr2 χ₂ q • (comma_ump_mor_pr2 χ₁ q)^-1).
          ** abstract
               (refine (!_) ;
                refine (maponpaths (λ z, _ • z) (comma_ump_mor_cell χ₁ q) @ _) ;
                rewrite !vassocl ;
                refine (!_) ;
                refine (maponpaths (λ z, z • _) (comma_ump_mor_cell χ₂ q) @ _) ;
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
        * use (comma_ump_eq χ₁ _ _ (id₂ _) (id₂ _)).
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
                rewrite !comma_ump_cell_pr1 ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
                rewrite vcomp_linv ;
                rewrite id2_left ;
                rewrite vcomp_rinv ;
                apply idpath).
          ** abstract
               (rewrite <- rwhisker_vcomp ;
                rewrite !comma_ump_cell_pr2 ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
                rewrite vcomp_linv ;
                rewrite id2_left ;
                rewrite vcomp_rinv ;
                apply idpath).
          ** apply id2_rwhisker.
          ** apply id2_rwhisker.
        * use (comma_ump_eq χ₁ _ _ (id₂ _) (id₂ _)).
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
                rewrite !comma_ump_cell_pr1 ;
                rewrite !vassocl ;
                rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
                rewrite vcomp_linv ;
                rewrite id2_left ;
                rewrite vcomp_rinv ;
                apply idpath).
          ** abstract
               (rewrite <- rwhisker_vcomp ;
                rewrite !comma_ump_cell_pr2 ;
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
         rewrite comma_ump_cell_pr1 ;
         rewrite !vassocl ;
         rewrite vcomp_linv ;
         apply id2_right).
    - abstract
        (rewrite idtoiso_2_1_isotoid_2_1 ; cbn ;
         refine (!_) ;
         rewrite comma_ump_cell_pr2 ;
         rewrite !vassocl ;
         rewrite vcomp_linv ;
         apply id2_right).
    Qed.
End CommaObject.

Arguments comma_cone {_ _ _ _} _ _.

(**
 5. Bicategories with comma objects
 *)
Definition has_comma
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ b₃ : B)
       (f : b₁ --> b₃)
       (g : b₂ --> b₃),
     ∑ (p : comma_cone f g),
     has_comma_ump p.

Definition bicat_with_comma
  : UU
  := ∑ (B : bicat), has_comma B.

Coercion bicat_with_comma_to_bicat
         (B : bicat_with_comma)
  : bicat
  := pr1 B.
