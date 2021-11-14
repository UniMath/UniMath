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


(** MOVE *)
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
(** END MOVE *)


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

  (** 2-cells of cones *)
  Definition binprod_2cell
             {p q : binprod_cone}
             (φ ψ : binprod_1cell p q)
    : UU
    := ∑ (η : φ ==> ψ),
       ((η ▹ binprod_cone_pr1 q) • binprod_1cell_pr1 ψ = binprod_1cell_pr1 φ)
       ×
       ((η ▹ binprod_cone_pr2 q) • binprod_1cell_pr2 ψ = binprod_1cell_pr2 φ).

  Coercion binprod_2cell_2cell
           {p q : binprod_cone}
           {φ ψ : binprod_1cell p q}
           (η : binprod_2cell φ ψ)
    : φ ==> ψ
    := pr1 η.

  Definition binprod_2cell_pr1
             {p q : binprod_cone}
             {φ ψ : binprod_1cell p q}
             (η : binprod_2cell φ ψ)
    : (η ▹ binprod_cone_pr1 q) • binprod_1cell_pr1 ψ
      =
      binprod_1cell_pr1 φ
    := pr12 η.

  Definition binprod_2cell_pr2
             {p q : binprod_cone}
             {φ ψ : binprod_1cell p q}
             (η : binprod_2cell φ ψ)
    : (η ▹ binprod_cone_pr2 q) • binprod_1cell_pr2 ψ
      =
      binprod_1cell_pr2 φ
    := pr22 η.

  Definition make_binprod_2cell
             {p q : binprod_cone}
             {φ ψ : binprod_1cell p q}
             (η : φ ==> ψ)
             (H₁ : (η ▹ binprod_cone_pr1 q) • binprod_1cell_pr1 ψ
                   =
                   binprod_1cell_pr1 φ)
             (H₂ : (η ▹ binprod_cone_pr2 q) • binprod_1cell_pr2 ψ
                   =
                   binprod_1cell_pr2 φ)
    : binprod_2cell φ ψ
    := (η ,, H₁ ,, H₂).

  Definition isaset_binprod_2cell
             {p q : binprod_cone}
             (φ ψ : binprod_1cell p q)
    : isaset (binprod_2cell φ ψ).
  Proof.
    use isaset_total2.
    - apply cellset_property.
    - intro.
      apply isasetdirprod ; apply isasetaprop ; apply cellset_property.
  Qed.

  Definition id2_binprod_2cell
             {p q : binprod_cone}
             (φ : binprod_1cell p q)
    : binprod_2cell φ φ.
  Proof.
    use make_binprod_2cell.
    - exact (id2 φ).
    - abstract
        (rewrite id2_rwhisker, id2_left ;
         apply idpath).
    - abstract
        (rewrite id2_rwhisker, id2_left ;
         apply idpath).
  Defined.

  Definition comp_binprod_2cell
             {p q : binprod_cone}
             {φ ψ χ : binprod_1cell p q}
             (η₁ : binprod_2cell φ ψ)
             (η₂ : binprod_2cell ψ χ)
    : binprod_2cell φ χ.
  Proof.
    use make_binprod_2cell.
    - exact (η₁ • η₂).
    - abstract
        (rewrite <- rwhisker_vcomp ;
         rewrite vassocl ;
         rewrite !binprod_2cell_pr1 ;
         apply idpath).
    - abstract
        (rewrite <- rwhisker_vcomp ;
         rewrite vassocl ;
         rewrite !binprod_2cell_pr2 ;
         apply idpath).
  Defined.

  (** Statements of universal mapping properties of products *)
  Section UniversalMappingPropertyStatements.
    Variable (p : binprod_cone).

    Definition binprod_ump_1
      : UU
      := ∏ (q : binprod_cone), binprod_1cell q p.

    Definition binprod_ump_2
      : UU
      := ∏ (q : binprod_cone)
           (φ ψ : binprod_1cell q p),
         binprod_2cell φ ψ.

    Definition binprod_ump_eq
      : UU
      := ∏ (q : binprod_cone)
           (φ ψ : binprod_1cell q p)
           (η₁ η₂ : binprod_2cell φ ψ),
         η₁ = η₂.

    Definition has_binprod_ump
      : UU
      := binprod_ump_1 × binprod_ump_2 × binprod_ump_eq.

    Definition has_binprod_ump_1
               (H : has_binprod_ump)
      : binprod_ump_1
      := pr1 H.

    Definition has_binprod_ump_2
               (H : has_binprod_ump)
      : binprod_ump_2
      := pr12 H.

    Definition has_binprod_ump_eq
               (H : has_binprod_ump)
      : binprod_ump_eq
      := pr22 H.

    Definition make_has_binprod_ump
               (H₁ : binprod_ump_1)
               (H₂ : binprod_ump_2)
               (Heq : binprod_ump_eq)
      : has_binprod_ump
      := H₁ ,, H₂ ,, Heq.

    Definition binprod_ump_1_1cell
               (H : has_binprod_ump)
               (q : B)
               (π₁ : q --> b₁)
               (π₂ : q --> b₂)
      : q --> p
      := has_binprod_ump_1 H (make_binprod_cone q π₁ π₂).

    Definition binprod_ump_1_1cell_pr1
               (H : has_binprod_ump)
               (q : B)
               (π₁ : q --> b₁)
               (π₂ : q --> b₂)
      : invertible_2cell
          (binprod_ump_1_1cell H q π₁ π₂ · binprod_cone_pr1 p)
          π₁
      := binprod_1cell_pr1 (has_binprod_ump_1 H (make_binprod_cone q π₁ π₂)).

    Definition binprod_ump_1_1cell_pr2
               (H : has_binprod_ump)
               (q : B)
               (π₁ : q --> b₁)
               (π₂ : q --> b₂)
      : invertible_2cell
          (binprod_ump_1_1cell H q π₁ π₂ · binprod_cone_pr2 p)
          π₂
      := binprod_1cell_pr2 (has_binprod_ump_1 H (make_binprod_cone q π₁ π₂)).

    Definition binprod_ump_2_cell
               (H : has_binprod_ump)
               {q : B}
               {π₁ : q --> b₁}
               {π₂ : q --> b₂}
               {f₁ f₂ : q --> p}
               {f₁π₁ : invertible_2cell (f₁ · binprod_cone_pr1 p) π₁}
               {f₁π₂ : invertible_2cell (f₁ · binprod_cone_pr2 p) π₂}
               {f₂π₁ : invertible_2cell (f₂ · binprod_cone_pr1 p) π₁}
               {f₂π₂ : invertible_2cell (f₂ · binprod_cone_pr2 p) π₂}
               (q_cone := make_binprod_cone q π₁ π₂)
      : f₁ ==> f₂
      := has_binprod_ump_2
           H
           q_cone
           (@make_binprod_1cell q_cone _ f₁ f₁π₁ f₁π₂)
           (@make_binprod_1cell q_cone _ f₂ f₂π₁ f₂π₂).

    Definition binprod_ump_2_cell_pr1
               (H : has_binprod_ump)
               {q : B}
               {π₁ : q --> b₁}
               {π₂ : q --> b₂}
               (f₁ f₂ : q --> p)
               (f₁π₁ : invertible_2cell (f₁ · binprod_cone_pr1 p) π₁)
               (f₁π₂ : invertible_2cell (f₁ · binprod_cone_pr2 p) π₂)
               (f₂π₁ : invertible_2cell (f₂ · binprod_cone_pr1 p) π₁)
               (f₂π₂ : invertible_2cell (f₂ · binprod_cone_pr2 p) π₂)
               (q_cone := make_binprod_cone q π₁ π₂)
      : (binprod_ump_2_cell H ▹ binprod_cone_pr1 p) • f₂π₁
        =
        f₁π₁
      := binprod_2cell_pr1
           (has_binprod_ump_2
              H
              q_cone
              (@make_binprod_1cell q_cone _ f₁ f₁π₁ f₁π₂)
              (@make_binprod_1cell q_cone _ f₂ f₂π₁ f₂π₂)).

    Definition pb_ump_2_cell_pr2
               (H : has_binprod_ump)
               {q : B}
               {π₁ : q --> b₁}
               {π₂ : q --> b₂}
               (f₁ f₂ : q --> p)
               (f₁π₁ : invertible_2cell (f₁ · binprod_cone_pr1 p) π₁)
               (f₁π₂ : invertible_2cell (f₁ · binprod_cone_pr2 p) π₂)
               (f₂π₁ : invertible_2cell (f₂ · binprod_cone_pr1 p) π₁)
               (f₂π₂ : invertible_2cell (f₂ · binprod_cone_pr2 p) π₂)
               (q_cone := make_binprod_cone q π₁ π₂)
      : (binprod_ump_2_cell H ▹ binprod_cone_pr2 p) • f₂π₂
        =
        f₁π₂
      := binprod_2cell_pr2
           (has_binprod_ump_2
              H
              q_cone
              (@make_binprod_1cell q_cone _ f₁ f₁π₁ f₁π₂)
              (@make_binprod_1cell q_cone _ f₂ f₂π₁ f₂π₂)).

    (** In locally univalent bicateogires, being a product is a proposition *)
    Definition isaprop_has_binprod_ump
               (HB_2_1 : is_univalent_2_1 B)
      : isaprop has_binprod_ump.
    Proof.
      use invproofirrelevance.
      intros χ₁ χ₂.
      repeat use pathsdirprod.
      - use funextsec ; intro q.
        use eq_binprod_1cell.
        + use (isotoid_2_1 HB_2_1).
          use make_invertible_2cell.
          * apply (has_binprod_ump_2 χ₁).
          * use make_is_invertible_2cell.
            ** apply (has_binprod_ump_2 χ₁).
            ** abstract
                 (exact (maponpaths
                           pr1
                           (has_binprod_ump_eq
                              χ₁ _
                              (pr1 χ₁ q)
                              (pr1 χ₁ q)
                              (comp_binprod_2cell
                                 (has_binprod_ump_2 χ₁ q (pr1 χ₁ q) (pr1 χ₂ q))
                                 (has_binprod_ump_2 χ₁ q (pr1 χ₂ q) (pr1 χ₁ q)))
                              (id2_binprod_2cell _)))).
            ** abstract
                 (exact (maponpaths
                           pr1
                           (has_binprod_ump_eq
                              χ₁ _
                              (pr1 χ₂ q)
                              (pr1 χ₂ q)
                              (comp_binprod_2cell
                                 (has_binprod_ump_2 χ₁ q (pr1 χ₂ q) (pr1 χ₁ q))
                                 (has_binprod_ump_2 χ₁ q (pr1 χ₁ q) (pr1 χ₂ q)))
                              (id2_binprod_2cell _)))).
        + rewrite idtoiso_2_1_isotoid_2_1 ; cbn.
          refine (!_).
          apply binprod_2cell_pr1.
        + rewrite idtoiso_2_1_isotoid_2_1.
          refine (!_).
          apply binprod_2cell_pr2.
      - use funextsec ; intro q.
        use funextsec ; intro φ.
        use funextsec ; intro ψ.
        exact (has_binprod_ump_eq
                 χ₁ q φ ψ
                 (has_binprod_ump_2 χ₁ q φ ψ)
                 (has_binprod_ump_2 χ₂ q φ ψ)).
      - repeat (use funextsec ; intro).
        apply isaset_binprod_2cell.
    Qed.
  End UniversalMappingPropertyStatements.
End Product.

Arguments binprod_cone {_} _ _.

Definition has_binprod
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ : B),
     ∑ (p : binprod_cone b₁ b₂),
     has_binprod_ump p.

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

  Definition binprod_ump_2_one_types
    : binprod_ump_2 (one_types_binprod_cone X Y).
  Proof.
    intros q φ ψ.
    use make_binprod_2cell.
    - intro x.
      use pathsdirprod.
      + exact (pr1 (binprod_1cell_pr1 φ) x @ !(pr1 (binprod_1cell_pr1 ψ) x)).
      + exact (pr1 (binprod_1cell_pr2 φ) x @ !(pr1 (binprod_1cell_pr2 ψ) x)).
    - abstract
        (use funextsec ;
         intro x ; cbn ; unfold homotcomp, homotfun ;
         refine (maponpaths (λ z, z @ _) (maponpaths_pr1_pathsdirprod _ _) @ _) ;
         rewrite <- path_assoc ;
         rewrite pathsinv0l ;
         apply pathscomp0rid).
    - abstract
        (use funextsec ;
         intro x ; cbn ; unfold homotcomp, homotfun ;
         refine (maponpaths (λ z, z @ _) (maponpaths_pr2_pathsdirprod _ _) @ _) ;
         rewrite <- path_assoc ;
         rewrite pathsinv0l ;
         apply pathscomp0rid).
  Defined.

  Definition binprod_ump_eq_one_types
    : binprod_ump_eq (one_types_binprod_cone X Y).
  Proof.
    intros q φ ψ η₁ η₂.
    use subtypePath.
    {
      intro ; apply isapropdirprod ; apply cellset_property.
    }
    use funextsec ; intro x.
    refine (pathsdirprod_eta _ @ _ @ !(pathsdirprod_eta _)).
    pose (eqtohomot (binprod_2cell_pr1 η₁) x @ !(eqtohomot (binprod_2cell_pr1 η₂) x)) as p₁.
    cbn in p₁.
    unfold homotcomp, homotfun in p₁.
    etrans.
    {
      apply maponpaths_2.
      exact (pathscomp_cancel_right _ _ _ p₁).
    }
    apply maponpaths.
    pose (eqtohomot (binprod_2cell_pr2 η₁) x @ !(eqtohomot (binprod_2cell_pr2 η₂) x)) as p₂.
    cbn in p₂.
    unfold homotcomp, homotfun in p₂.
    exact (pathscomp_cancel_right _ _ _ p₂).
  Qed.

  Definition has_binprod_ump_one_types
    : has_binprod_ump (one_types_binprod_cone X Y).
  Proof.
    use make_has_binprod_ump.
    - exact binprod_ump_1_one_types.
    - exact binprod_ump_2_one_types.
    - exact binprod_ump_eq_one_types.
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

(** Products in the bicategory of univalent categories. *)
Definition cat_binprod_cone
           (C₁ C₂ : bicat_of_univ_cats)
  : binprod_cone C₁ C₂.
Proof.
  use make_binprod_cone.
  - use make_univalent_category.
    + exact (category_binproduct (pr1 C₁) (pr1 C₂)).
    + use is_unvialent_category_binproduct.
      * apply C₁.
      * apply C₂.
  - apply pr1_functor.
  - apply pr2_functor.
Defined.


(** MOVE *)
Definition bindelta_pair_pr1_data
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_trans_data (bindelta_pair_functor F G ∙ pr1_functor _ _) F
  := λ _, identity _.

Definition bindelta_pair_pr1_is_nat_trans
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : is_nat_trans _ _ (bindelta_pair_pr1_data F G).
Proof.
  intros x y f ; cbn ; unfold bindelta_pair_pr1_data.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition bindelta_pair_pr1
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : bindelta_pair_functor F G ∙ pr1_functor _ _ ⟹ F.
Proof.
  use make_nat_trans.
  - exact (bindelta_pair_pr1_data F G).
  - exact (bindelta_pair_pr1_is_nat_trans F G).
Defined.

Definition bindelta_pair_pr1_iso
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_iso
      (bindelta_pair_functor F G ∙ pr1_functor _ _)
      F.
Proof.
  use make_nat_iso.
  - exact (bindelta_pair_pr1 F G).
  - intro.
    apply identity_is_iso.
Defined.

Definition bindelta_pair_pr2_data
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_trans_data (bindelta_pair_functor F G ∙ pr2_functor _ _) G
  := λ _, identity _.

Definition bindelta_pair_pr2_is_nat_trans
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : is_nat_trans _ _ (bindelta_pair_pr2_data F G).
Proof.
  intros x y f ; cbn ; unfold bindelta_pair_pr1_data.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition bindelta_pair_pr2
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : bindelta_pair_functor F G ∙ pr2_functor _ _ ⟹ G.
Proof.
  use make_nat_trans.
  - exact (bindelta_pair_pr2_data F G).
  - exact (bindelta_pair_pr2_is_nat_trans F G).
Defined.

Definition bindelta_pair_pr2_iso
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_iso
      (bindelta_pair_functor F G ∙ pr2_functor _ _)
      G.
Proof.
  use make_nat_iso.
  - exact (bindelta_pair_pr2 F G).
  - intro.
    apply identity_is_iso.
Defined.
(** END MOVE *)


Section CatBinprodUMP.
  Context (C₁ C₂ : bicat_of_univ_cats).

  Definition cat_binprod_ump_1
    : binprod_ump_1 (cat_binprod_cone C₁ C₂).
  Proof.
    intro q.
    use make_binprod_1cell.
    - use bindelta_pair_functor.
      + exact (binprod_cone_pr1 q).
      + exact (binprod_cone_pr2 q).
    - apply nat_iso_to_invertible_2cell.
      apply bindelta_pair_pr1_iso.
    - apply nat_iso_to_invertible_2cell.
      apply bindelta_pair_pr2_iso.
  Defined.

  Definition cat_binprod_ump_2_nat_trans_data
             {q : binprod_cone C₁ C₂}
             (φ ψ : binprod_1cell q (cat_binprod_cone C₁ C₂))
    : nat_trans_data (pr11 φ) (pr11 ψ).
  Proof.
    intro x.
    simple refine (_ ,, _).
    - exact (pr11 (binprod_1cell_pr1 φ) x
             · inv_from_iso
                 (nat_iso_pointwise_iso
                    (invertible_2cell_to_nat_iso
                       _ _
                       (binprod_1cell_pr1 ψ))
                    x)).
    - exact (pr11 (binprod_1cell_pr2 φ) x
             · inv_from_iso
                 (nat_iso_pointwise_iso
                    (invertible_2cell_to_nat_iso
                       _ _
                       (binprod_1cell_pr2 ψ))
                    x)).
  Defined.

  Definition cat_binprod_ump_2_is_nat_trans
             {q : binprod_cone C₁ C₂}
             (φ ψ : binprod_1cell q (cat_binprod_cone C₁ C₂))
    : is_nat_trans _ _ (cat_binprod_ump_2_nat_trans_data φ ψ).
  Proof.
    intros x y f.
    use pathsdirprod.
    - simpl.
      rewrite assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax (pr1 (binprod_1cell_pr1 φ))).
      }
      rewrite !assoc'.
      apply maponpaths.
      cbn ; unfold precomp_with.
      rewrite !id_right.
      exact (nat_trans_ax (pr2 (binprod_1cell_pr1 ψ)^-1) _ _ f).
    - simpl.
      rewrite assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax (pr1 (binprod_1cell_pr2 φ))).
      }
      rewrite !assoc'.
      apply maponpaths.
      cbn ; unfold precomp_with.
      rewrite !id_right.
      exact (nat_trans_ax (pr2 (binprod_1cell_pr2 ψ)^-1) _ _ f).
  Qed.

  Definition cat_binprod_ump_2_nat_trans
             {q : binprod_cone C₁ C₂}
             (φ ψ : binprod_1cell q (cat_binprod_cone C₁ C₂))
    : φ ==> ψ.
  Proof.
    use make_nat_trans.
    - exact (cat_binprod_ump_2_nat_trans_data φ ψ).
    - exact (cat_binprod_ump_2_is_nat_trans φ ψ).
  Defined.

  Definition cat_binprod_ump_2
    : binprod_ump_2 (cat_binprod_cone C₁ C₂).
  Proof.
    intros q φ ψ.
    use make_binprod_2cell.
    - exact (cat_binprod_ump_2_nat_trans φ ψ).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         unfold precomp_with ;
         rewrite id_right ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         exact (nat_trans_eq_pointwise (vcomp_linv (binprod_1cell_pr1 ψ)) x)).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         unfold precomp_with ;
         rewrite id_right ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         exact (nat_trans_eq_pointwise (vcomp_linv (binprod_1cell_pr2 ψ)) x)).
  Defined.

  Definition cat_binprod_ump_eq
    : binprod_ump_eq (cat_binprod_cone C₁ C₂).
  Proof.
    intros q φ ψ η₁ η₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use pathsdirprod.
    - pose (nat_trans_eq_pointwise
              (binprod_2cell_pr1 η₁)
              x)
        as m.
      pose (nat_trans_eq_pointwise
              (binprod_2cell_pr1 η₂)
              x)
        as n.
      pose (r := m @ !n).
      cbn in r.
      exact (cancel_postcomposition_iso
               (nat_iso_pointwise_iso
                  (invertible_2cell_to_nat_iso
                     _ _
                     (binprod_1cell_pr1 ψ))
                  x)
               _ _
               r).
    - pose (nat_trans_eq_pointwise
              (binprod_2cell_pr2 η₁)
              x)
        as m.
      pose (nat_trans_eq_pointwise
              (binprod_2cell_pr2 η₂)
              x)
        as n.
      pose (r := m @ !n).
      cbn in r.
      exact (cancel_postcomposition_iso
               (nat_iso_pointwise_iso
                  (invertible_2cell_to_nat_iso
                     _ _
                     (binprod_1cell_pr2 ψ))
                  x)
               _ _
               r).
  Qed.

  Definition cat_binprod_ump
    : has_binprod_ump (cat_binprod_cone C₁ C₂).
  Proof.
    use make_has_binprod_ump.
    - exact cat_binprod_ump_1.
    - exact cat_binprod_ump_2.
    - exact cat_binprod_ump_eq.
  Defined.
End CatBinprodUMP.

Definition has_pb_bicat_of_univ_cats
  : has_binprod bicat_of_univ_cats.
Proof.
  intros C₁ C₂.
  simple refine (_ ,, _).
  - exact (cat_binprod_cone C₁ C₂).
  - exact (cat_binprod_ump C₁ C₂).
Defined.
