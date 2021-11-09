(****************************************************************

 Pullbacks in bicategories

 In this file we define the notion of pullback square in arbitrary
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
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Local Open Scope cat.

Section Pullback.
  Context {B : bicat}
          {b₁ b₂ b₃ : B}
          {f : b₁ --> b₃}
          {g : b₂ --> b₃}.

  (** Cones on the diagram *)
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

  (** 1-cells between cones *)
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

  (** 2-cells of cones *)
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

  (** Statements of universal mapping properties of pullbacks *)
  Section UniversalMappingPropertyStatements.
    Variable (p : pb_cone).

    Definition pb_ump_1
      : UU
      := ∏ (q : pb_cone), pb_1cell q p.

    Definition pb_ump_2
      : UU
      := ∏ (q : pb_cone)
           (φ ψ : pb_1cell q p),
         pb_2cell φ ψ.

    Definition pb_ump_eq
      : UU
      := ∏ (q : pb_cone)
           (φ ψ : pb_1cell q p)
           (η₁ η₂ : pb_2cell φ ψ),
         η₁ = η₂.

    Definition has_pb_ump
      : UU
      := pb_ump_1 × pb_ump_2 × pb_ump_eq.

    Definition has_pb_ump_1
               (H : has_pb_ump)
      : pb_ump_1
      := pr1 H.

    Definition has_pb_ump_2
               (H : has_pb_ump)
      : pb_ump_2
      := pr12 H.

    Definition has_pb_ump_eq
               (H : has_pb_ump)
      : pb_ump_eq
      := pr22 H.

    Definition make_has_pb_ump
               (H₁ : pb_ump_1)
               (H₂ : pb_ump_2)
               (Heq : pb_ump_eq)
      : has_pb_ump
      := H₁ ,, H₂ ,, Heq.

    Definition pb_ump_1_1cell
               (H : has_pb_ump)
               (q : B)
               (π₁ : q --> b₁)
               (π₂ : q --> b₂)
               (comm : invertible_2cell (π₁ · f) (π₂ · g))
      : q --> p
      := has_pb_ump_1 H (make_pb_cone q π₁ π₂ comm).

    Definition pb_ump_1_1cell_pr1
               (H : has_pb_ump)
               (q : B)
               (π₁ : q --> b₁)
               (π₂ : q --> b₂)
               (comm : invertible_2cell (π₁ · f) (π₂ · g))
      : invertible_2cell
          (pb_ump_1_1cell H q π₁ π₂ comm · pb_cone_pr1 p)
          π₁
      := pb_1cell_pr1 (has_pb_ump_1 H (make_pb_cone q π₁ π₂ comm)).

    Definition pb_ump_1_1cell_pr2
               (H : has_pb_ump)
               (q : B)
               (π₁ : q --> b₁)
               (π₂ : q --> b₂)
               (comm : invertible_2cell (π₁ · f) (π₂ · g))
      : invertible_2cell
          (pb_ump_1_1cell H q π₁ π₂ comm · pb_cone_pr2 p)
          π₂
      := pb_1cell_pr2 (has_pb_ump_1 H (make_pb_cone q π₁ π₂ comm)).

    Definition pb_ump_1_1cell_eq
               (H : has_pb_ump)
               (q : B)
               (π₁ : q --> b₁)
               (π₂ : q --> b₂)
               (comm : invertible_2cell (π₁ · f) (π₂ · g))
      : has_pb_ump_1 H (make_pb_cone q π₁ π₂ comm) ◃ pb_cone_cell p
        =
        lassociator _ _ _
        • (pb_ump_1_1cell_pr1 H q π₁ π₂ comm ▹ f)
        • comm
        • ((pb_ump_1_1cell_pr2 H q π₁ π₂ comm)^-1 ▹ g)
        • rassociator _ _ _
      := pb_1cell_eq (has_pb_ump_1 H (make_pb_cone q π₁ π₂ comm)).

    Definition pb_ump_2_cell
               (H : has_pb_ump)
               {q : B}
               {π₁ : q --> b₁}
               {π₂ : q --> b₂}
               {comm : invertible_2cell (π₁ · f) (π₂ · g)}
               {f₁ f₂ : q --> p}
               {f₁π₁ : invertible_2cell (f₁ · pb_cone_pr1 p) π₁}
               {f₁π₂ : invertible_2cell (f₁ · pb_cone_pr2 p) π₂}
               {f₂π₁ : invertible_2cell (f₂ · pb_cone_pr1 p) π₁}
               {f₂π₂ : invertible_2cell (f₂ · pb_cone_pr2 p) π₂}
               (f₁comm : f₁ ◃ pb_cone_cell p
                         =
                         lassociator _ _ _
                         • (f₁π₁ ▹ f)
                         • comm
                         • (f₁π₂ ^-1 ▹ g)
                         • rassociator _ _ _)
               (f₂comm : f₂ ◃ pb_cone_cell p
                         =
                         lassociator _ _ _
                         • (f₂π₁ ▹ f)
                         • comm
                         • (f₂π₂ ^-1 ▹ g)
                         • rassociator _ _ _)
               (q_cone := make_pb_cone q π₁ π₂ comm)
      : f₁ ==> f₂
      := has_pb_ump_2
           H
           q_cone
           (@make_pb_1cell q_cone _ f₁ f₁π₁ f₁π₂ f₁comm)
           (@make_pb_1cell q_cone _ f₂ f₂π₁ f₂π₂ f₂comm).

    Definition pb_ump_2_cell_pr1
               (H : has_pb_ump)
               {q : B}
               {π₁ : q --> b₁}
               {π₂ : q --> b₂}
               {comm : invertible_2cell (π₁ · f) (π₂ · g)}
               (f₁ f₂ : q --> p)
               (f₁π₁ : invertible_2cell (f₁ · pb_cone_pr1 p) π₁)
               (f₁π₂ : invertible_2cell (f₁ · pb_cone_pr2 p) π₂)
               (f₂π₁ : invertible_2cell (f₂ · pb_cone_pr1 p) π₁)
               (f₂π₂ : invertible_2cell (f₂ · pb_cone_pr2 p) π₂)
               (f₁comm : f₁ ◃ pb_cone_cell p
                         =
                         lassociator _ _ _
                         • (f₁π₁ ▹ f)
                         • comm
                         • (f₁π₂ ^-1 ▹ g)
                         • rassociator _ _ _)
               (f₂comm : f₂ ◃ pb_cone_cell p
                         =
                         lassociator _ _ _
                         • (f₂π₁ ▹ f)
                         • comm
                         • (f₂π₂ ^-1 ▹ g)
                         • rassociator _ _ _)
               (q_cone := make_pb_cone q π₁ π₂ comm)
      : (pb_ump_2_cell H f₁comm f₂comm ▹ pb_cone_pr1 p) • f₂π₁
        =
        f₁π₁
      := pb_2cell_pr1
           (has_pb_ump_2
              H
              q_cone
              (@make_pb_1cell q_cone _ f₁ f₁π₁ f₁π₂ f₁comm)
              (@make_pb_1cell q_cone _ f₂ f₂π₁ f₂π₂ f₂comm)).

    Definition pb_ump_2_cell_pr2
               (H : has_pb_ump)
               {q : B}
               {π₁ : q --> b₁}
               {π₂ : q --> b₂}
               {comm : invertible_2cell (π₁ · f) (π₂ · g)}
               (f₁ f₂ : q --> p)
               (f₁π₁ : invertible_2cell (f₁ · pb_cone_pr1 p) π₁)
               (f₁π₂ : invertible_2cell (f₁ · pb_cone_pr2 p) π₂)
               (f₂π₁ : invertible_2cell (f₂ · pb_cone_pr1 p) π₁)
               (f₂π₂ : invertible_2cell (f₂ · pb_cone_pr2 p) π₂)
               (f₁comm : f₁ ◃ pb_cone_cell p
                         =
                         lassociator _ _ _
                         • (f₁π₁ ▹ f)
                         • comm
                         • (f₁π₂ ^-1 ▹ g)
                         • rassociator _ _ _)
               (f₂comm : f₂ ◃ pb_cone_cell p
                         =
                         lassociator _ _ _
                         • (f₂π₁ ▹ f)
                         • comm
                         • (f₂π₂ ^-1 ▹ g)
                         • rassociator _ _ _)
               (q_cone := make_pb_cone q π₁ π₂ comm)
      : (pb_ump_2_cell H f₁comm f₂comm ▹ pb_cone_pr2 p) • f₂π₂
        =
        f₁π₂
      := pb_2cell_pr2
           (has_pb_ump_2
              H
              q_cone
              (@make_pb_1cell q_cone _ f₁ f₁π₁ f₁π₂ f₁comm)
              (@make_pb_1cell q_cone _ f₂ f₂π₁ f₂π₂ f₂comm)).

    (** In locally univalent bicateogires, being a pullback is a proposition *)
    Definition isaprop_has_pb_ump
               (HB_2_1 : is_univalent_2_1 B)
      : isaprop has_pb_ump.
    Proof.
      use invproofirrelevance.
      intros χ₁ χ₂.
      repeat use pathsdirprod.
      - use funextsec ; intro q.
        use eq_pb_1cell ; cbn.
        + use (isotoid_2_1 HB_2_1).
          use make_invertible_2cell.
          * apply (has_pb_ump_2 χ₁).
          * use make_is_invertible_2cell.
            ** apply (has_pb_ump_2 χ₁).
            ** abstract
                 (exact (maponpaths
                           pr1
                           (has_pb_ump_eq
                              χ₁
                              _
                              (pr1 χ₁ q)
                              (pr1 χ₁ q)
                              (comp_pb_2cell
                                 (has_pb_ump_2 χ₁ q (pr1 χ₁ q) (pr1 χ₂ q))
                                 (has_pb_ump_2 χ₁ q (pr1 χ₂ q) (pr1 χ₁ q)))
                              (id2_pb_2cell _)))).
            ** abstract
                 (exact (maponpaths
                           pr1
                           (has_pb_ump_eq
                              χ₁
                              _
                              (pr1 χ₂ q)
                              (pr1 χ₂ q)
                              (comp_pb_2cell
                                 (has_pb_ump_2 χ₁ q (pr1 χ₂ q) (pr1 χ₁ q))
                                 (has_pb_ump_2 χ₁ q (pr1 χ₁ q) (pr1 χ₂ q)))
                              (id2_pb_2cell _)))).
        + rewrite idtoiso_2_1_isotoid_2_1 ; cbn.
          refine (!_).
          apply pb_2cell_pr1.
        + rewrite idtoiso_2_1_isotoid_2_1.
          refine (!_).
          apply pb_2cell_pr2.
      - use funextsec ; intro q.
        use funextsec ; intro φ.
        use funextsec ; intro ψ.
        exact (has_pb_ump_eq
                 χ₁ q φ ψ
                 (has_pb_ump_2 χ₁ q φ ψ)
                 (has_pb_ump_2 χ₂ q φ ψ)).
      - repeat (use funextsec ; intro).
        apply isaset_pb_2cell.
    Qed.
  End UniversalMappingPropertyStatements.
End Pullback.

Arguments pb_cone {_ _ _ _} _ _.

Definition has_pb
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ b₃ : B)
       (f : b₁ --> b₃)
       (g : b₂ --> b₃),
     ∑ (p : pb_cone f g),
     has_pb_ump p.


(** MOVE ??!??!???!??? *)
Definition pb_type
           {X Y Z : UU}
           (f : X → Z)
           (g : Y → Z)
  : UU
  := ∑ (x : X × Y), f (pr1 x) = g (pr2 x).

Definition pb_type_pr1
           {X Y Z : UU}
           {f : X → Z}
           {g : Y → Z}
  : pb_type f g → X
  := λ x, pr11 x.

Definition pb_type_pr2
           {X Y Z : UU}
           {f : X → Z}
           {g : Y → Z}
  : pb_type f g → Y
  := λ x, pr21 x.

Definition pb_type_eq
           {X Y Z : UU}
           {f : X → Z}
           {g : Y → Z}
           (x : pb_type f g)
  : f (pb_type_pr1 x) = g (pb_type_pr2 x)
  := pr2 x.

Definition path_pb_type
           {X Y Z : UU}
           {f : X → Z}
           {g : Y → Z}
           {x y : pb_type f g}
           (p₁ : pb_type_pr1 x = pb_type_pr1 y)
           (p₂ : pb_type_pr2 x = pb_type_pr2 y)
           (p₃ : pb_type_eq x @ maponpaths g p₂
                 =
                 maponpaths f p₁ @ pb_type_eq y)
  : x = y.
Proof.
  induction x as [ [ x₁ x₂ ] px ].
  induction y as [ [ y₁ y₂ ] py ].
  cbn in p₁, p₂.
  induction p₁, p₂.
  cbn in p₃.
  apply maponpaths.
  exact (!(pathscomp0rid _) @ p₃).
Defined.

Definition maponpaths_pr1_path_pb_type
           {X Y Z : UU}
           {f : X → Z}
           {g : Y → Z}
           {x y : pb_type f g}
           (p₁ : pb_type_pr1 x = pb_type_pr1 y)
           (p₂ : pb_type_pr2 x = pb_type_pr2 y)
           (p₃ : pb_type_eq x @ maponpaths g p₂
                 =
                 maponpaths f p₁ @ pb_type_eq y)
  : maponpaths
      pb_type_pr1
      (path_pb_type p₁ p₂ p₃)
    =
    p₁.
Proof.
  induction x as [ [ x₁ x₂ ] px ].
  induction y as [ [ y₁ y₂ ] py ].
  cbn in p₁, p₂.
  induction p₁, p₂.
  cbn in p₃.
  induction p₃ ; cbn.
  etrans.
  {
    apply (maponpathscomp
             (tpair (λ x : X × Y, f (pr1 x) = g (pr2 x)) (x₁,, x₂))
             pb_type_pr1).
  }
  apply maponpaths_for_constant_function.
Qed.

Definition maponpaths_pr2_path_pb_type
           {X Y Z : UU}
           {f : X → Z}
           {g : Y → Z}
           {x y : pb_type f g}
           (p₁ : pb_type_pr1 x = pb_type_pr1 y)
           (p₂ : pb_type_pr2 x = pb_type_pr2 y)
           (p₃ : pb_type_eq x @ maponpaths g p₂
                 =
                 maponpaths f p₁ @ pb_type_eq y)
  : maponpaths
      pb_type_pr2
      (path_pb_type p₁ p₂ p₃)
    =
    p₂.
Proof.
  induction x as [ [ x₁ x₂ ] px ].
  induction y as [ [ y₁ y₂ ] py ].
  cbn in p₁, p₂.
  induction p₁, p₂.
  cbn in p₃.
  induction p₃ ; cbn.
  etrans.
  {
    apply (maponpathscomp
             (tpair (λ x : X × Y, f (pr1 x) = g (pr2 x)) (x₁,, x₂))
             pb_type_pr2).
  }
  apply maponpaths_for_constant_function.
Qed.

Definition homot_pb_type_eta
           {X Y Z : UU}
           {f : X → Z}
           {g : Y → Z}
           {x y : pb_type f g}
           (p : x = y)
  : p
    =
    path_pb_type
      (maponpaths pb_type_pr1 p)
      (maponpaths pb_type_pr2 p)
      (maponpaths (λ z, _ @ z) (maponpathscomp pb_type_pr2 g p)
       @ !(homotsec_natural pb_type_eq p)
       @ maponpaths (λ z, z @ _) (!(maponpathscomp pb_type_pr1 f p))).
Proof.
  induction p.
  cbn -[path_pb_type].
  rewrite pathscomp0rid.
  simpl.
  rewrite pathsinv0r.
  apply idpath.
Qed.

Definition homot_pb
           {X Y Z : UU}
           {f : X → Z} {g : Y → Z}
           {x y : pb_type f g}
           {h₁ h₁' : pb_type_pr1 x = pb_type_pr1 y} (e₁ : h₁ = h₁')
           {h₂ h₂' : pb_type_pr2 x = pb_type_pr2 y} (e₂ : h₂ = h₂')
           (h₃ : pb_type_eq x @ maponpaths g h₂ = maponpaths f h₁ @ pb_type_eq y)
  : path_pb_type h₁ h₂ h₃
    =
    path_pb_type
      h₁' h₂'
      (maponpaths
         (λ z, _ @ maponpaths g z)
         (!e₂)
       @ h₃
       @ maponpaths
           (λ z, maponpaths f z @ _)
           e₁).
Proof.
  induction e₁ ; induction e₂.
  simpl.
  apply maponpaths.
  exact (!(pathscomp0rid _)).
Qed.

Definition homot_pb_one_type
           {X Y Z : UU}
           (HZ : isofhlevel 3 Z)
           {f : X → Z}
           {g : Y → Z}
           {x y : pb_type f g}
           (p q : x = y)
           (r₁ : maponpaths pb_type_pr1 p
                 =
                 maponpaths pb_type_pr1 q)
           (r₂ : maponpaths pb_type_pr2 p
                 =
                 maponpaths pb_type_pr2 q)
  : p = q.
Proof.
  refine (homot_pb_type_eta p @ _ @ !(homot_pb_type_eta q)).
  etrans.
  {
    exact (homot_pb r₁ r₂ _).
  }
  apply maponpaths.
  apply HZ.
Qed.

Definition pb_is_of_hlevel
           (n : nat)
           {X Y Z : UU}
           (HX : isofhlevel n X)
           (HY : isofhlevel n Y)
           (HZ : isofhlevel n Z)
           (f : X → Z)
           (g : Y → Z)
  : isofhlevel n (pb_type f g).
Proof.
  use isofhleveltotal2.
  - use isofhleveldirprod.
    + exact HX.
    + exact HY.
  - simpl.
    intro x.
    apply (hlevelntosn n _ HZ).
Qed.

Definition pb_HLevel
           (n : nat)
           {X Y Z : HLevel n}
           (f : pr1 X → pr1 Z)
           (g : pr1 Y → pr1 Z)
  : HLevel n.
Proof.
  simple refine (pb_type f g ,, _).
  apply pb_is_of_hlevel.
  - exact (pr2 X).
  - exact (pr2 Y).
  - exact (pr2 Z).
Defined.

(** END MOVE ??!??!???!??? *)


(** Pullbacks of 1-types *)
Definition one_types_pb_cone
           {X Y Z : one_types}
           (f : X --> Z)
           (g : Y --> Z)
  : pb_cone f g.
Proof.
  use make_pb_cone.
  - exact (pb_HLevel 3 f g).
  - exact pb_type_pr1.
  - exact pb_type_pr2.
  - use make_invertible_2cell.
    + exact pb_type_eq.
    + apply one_type_2cell_iso.
Defined.

Section OneTypesPullbackUMP.
  Context {X Y Z : one_types}
          (f : X --> Z)
          (g : Y --> Z).

  Definition pb_ump_1_one_types
    : pb_ump_1 (one_types_pb_cone f g).
  Proof.
    intro q.
    use make_pb_1cell.
    - exact (λ x, (pb_cone_pr1 q x ,, pb_cone_pr2 q x) ,, pr1 (pb_cone_cell q) x).
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
         apply idpath).
  Defined.

  Definition pb_ump_2_one_types
    : pb_ump_2 (one_types_pb_cone f g).
  Proof.
    intros q φ ψ.
    use make_pb_2cell.
    - intro x.
      use path_pb_type.
      + exact (pr1 (pb_1cell_pr1 φ) x @ !(pr1 (pb_1cell_pr1 ψ) x)).
      + exact (pr1 (pb_1cell_pr2 φ) x @ !(pr1 (pb_1cell_pr2 ψ) x)).
      + abstract
          (pose (eqtohomot (pb_1cell_eq φ) x) as p ;
           cbn in p ; unfold homotcomp, homotfun in p ; cbn in p ;
           rewrite pathscomp0rid in p ;
           rewrite p ; clear p ;
           rewrite !maponpathscomp0 ;
           rewrite <- !path_assoc ;
           apply maponpaths ;
           pose (eqtohomot (pb_1cell_eq ψ) x) as p ;
           cbn in p ; unfold homotcomp, homotfun in p ; cbn in p ;
           rewrite pathscomp0rid in p ;
           rewrite p ; clear p ;
           rewrite !path_assoc ;
           rewrite <- !maponpathscomp0 ;
           rewrite pathsinv0l ;
           cbn ;
           rewrite <- !path_assoc ;
           apply maponpaths ;
           rewrite <- !maponpathscomp0 ;
           apply maponpaths ;
           rewrite !path_assoc ;
           refine (maponpaths
                     (λ z, z @ _)
                     (eqtohomot
                        (vcomp_linv
                           (pb_1cell_pr2 φ))
                        x)
                   @ _) ;
           cbn ;
           use pathsinv0_to_right' ;
           refine (!_) ;
           exact (eqtohomot
                    (vcomp_rinv
                       (pb_1cell_pr2 ψ))
                    x)).
    - abstract
        (use funextsec ;
         intro x ; cbn ; unfold homotcomp, homotfun ;
         refine (maponpaths (λ z, z @ _) (maponpaths_pr1_path_pb_type _ _ _) @ _) ;
         rewrite <- path_assoc ;
         rewrite pathsinv0l ;
         apply pathscomp0rid).
    - abstract
        (use funextsec ;
         intro x ; cbn ; unfold homotcomp, homotfun ;
         refine (maponpaths (λ z, z @ _) (maponpaths_pr2_path_pb_type _ _ _) @ _) ;
         rewrite <- path_assoc ;
         rewrite pathsinv0l ;
         apply pathscomp0rid).
  Defined.

  Definition pb_ump_eq_one_types
    : pb_ump_eq (one_types_pb_cone f g).
  Proof.
    intros q φ ψ η₁ η₂.
    use subtypePath.
    {
      intro ; apply isapropdirprod ; apply cellset_property.
    }
    use funextsec ; intro x.
    use homot_pb_one_type.
    - apply Z.
    - pose (eqtohomot (pb_2cell_pr1 η₁) x) as m.
      cbn in m.
      unfold homotcomp, homotfun in m.
      pose (eqtohomot (pb_2cell_pr1 η₂) x) as n.
      cbn in n.
      unfold homotcomp, homotfun in n.
      pose (r := m @ !n).
      apply (pathscomp_cancel_right _ _ (pr1 (pb_1cell_pr1 ψ) x)).
      exact r.
    - pose (eqtohomot (pb_2cell_pr2 η₁) x) as m.
      cbn in m.
      unfold homotcomp, homotfun in m.
      pose (eqtohomot (pb_2cell_pr2 η₂) x) as n.
      cbn in n.
      unfold homotcomp, homotfun in n.
      pose (r := m @ !n).
      apply (pathscomp_cancel_right _ _ (pr1 (pb_1cell_pr2 ψ) x)).
      exact r.
  Qed.

  Definition has_pb_ump_one_types
    : has_pb_ump (one_types_pb_cone f g).
  Proof.
    use make_has_pb_ump.
    - exact pb_ump_1_one_types.
    - exact pb_ump_2_one_types.
    - exact pb_ump_eq_one_types.
  Defined.
End OneTypesPullbackUMP.

Definition has_pb_one_types
  : has_pb one_types.
Proof.
  intros X Y Z f g ; cbn in *.
  simple refine (_ ,, _).
  - exact (one_types_pb_cone f g).
  - exact (has_pb_ump_one_types f g).
Defined.

(** Pullbacks in the bicategory of univalent categories.
    Here, we use the iso-comma category.
 *)
Definition iso_comma_pb_cone
           {C₁ C₂ C₃ : bicat_of_cats}
           (F : C₁ --> C₃)
           (G : C₂ --> C₃)
  : pb_cone F G.
Proof.
  use make_pb_cone.
  - use make_univalent_category.
    + exact (iso_comma F G).
    + apply is_univalent_iso_comma.
      * apply C₁.
      * apply C₂.
      * apply C₃.
  - apply iso_comma_pr1.
  - apply iso_comma_pr2.
  - apply nat_iso_to_invertible_2cell.
    apply iso_comma_commute.
Defined.

Section IsoCommaUMP.
  Context {C₁ C₂ C₃ : bicat_of_cats}
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

  Definition pb_ump_2_iso_comma
    : pb_ump_2 (iso_comma_pb_cone F G).
  Proof.
    intros q φ ψ.
    use make_pb_2cell.
    - use (iso_comma_ump2).
      + exact (pb_cone_pr1 q).
      + exact (pb_cone_pr2 q).
      + apply invertible_2cell_to_nat_iso.
        exact (pb_cone_cell q).
      + apply invertible_2cell_to_nat_iso.
        exact (pb_1cell_pr1 φ).
      + apply invertible_2cell_to_nat_iso.
        exact (pb_1cell_pr1 ψ).
      + apply invertible_2cell_to_nat_iso.
        exact (pb_1cell_pr2 φ).
      + apply invertible_2cell_to_nat_iso.
        exact (pb_1cell_pr2 ψ).
      + abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ; cbn ;
           pose (nat_trans_eq_pointwise (pb_1cell_eq φ) x) as m ;
           cbn in m ;
           rewrite m ;
           rewrite !assoc ;
           unfold precomp_with ;
           rewrite !id_left, !id_right ;
           apply idpath).
      + abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intro x ; cbn ;
           pose (nat_trans_eq_pointwise (pb_1cell_eq ψ) x) as m ;
           cbn in m ;
           rewrite m ;
           rewrite !assoc ;
           unfold precomp_with ;
           rewrite !id_left, !id_right ;
           apply idpath).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ; unfold precomp_with ;
         rewrite id_right ;
         refine (_ @ id_right _) ;
         rewrite !assoc' ;
         apply maponpaths ;
         exact (nat_trans_eq_pointwise
                  (vcomp_linv (pr2 (pb_1cell_pr1 ψ)))
                  x)).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ; unfold precomp_with ;
         rewrite id_right ;
         refine (_ @ id_right _) ;
         rewrite !assoc' ;
         apply maponpaths ;
         exact (nat_trans_eq_pointwise
                  (vcomp_linv (pr2 (pb_1cell_pr2 ψ)))
                  x)).
  Defined.

  Definition pb_ump_eq_iso_comma
    : pb_ump_eq (iso_comma_pb_cone F G).
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
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use pathsdirprod.
    - pose (nat_trans_eq_pointwise
              (pb_2cell_pr1 η₁)
              x)
        as m.
      pose (nat_trans_eq_pointwise
              (pb_2cell_pr1 η₂)
              x)
        as n.
      pose (r := m @ !n).
      cbn in r.
      exact (cancel_postcomposition_iso
               (nat_iso_pointwise_iso
                  (invertible_2cell_to_nat_iso
                     _ _
                     (pb_1cell_pr1 ψ))
                  x)
               _ _
               r).
    - pose (nat_trans_eq_pointwise
              (pb_2cell_pr2 η₁)
              x)
        as m.
      pose (nat_trans_eq_pointwise
              (pb_2cell_pr2 η₂)
              x)
        as n.
      pose (r := m @ !n).
      cbn in r.
      exact (cancel_postcomposition_iso
               (nat_iso_pointwise_iso
                  (invertible_2cell_to_nat_iso
                     _ _
                     (pb_1cell_pr2 ψ))
                  x)
               _ _
               r).
  Qed.

  Definition has_pb_ump_iso_comma
    : has_pb_ump (iso_comma_pb_cone F G).
  Proof.
    use make_has_pb_ump.
    - exact pb_ump_1_iso_comma.
    - exact pb_ump_2_iso_comma.
    - exact pb_ump_eq_iso_comma.
  Defined.
End IsoCommaUMP.

Definition has_pb_bicat_of_cats
  : has_pb bicat_of_cats.
Proof.
  intros C₁ C₂ C₃ F G.
  simple refine (_ ,, _).
  - exact (iso_comma_pb_cone F G).
  - exact (has_pb_ump_iso_comma F G).
Defined.
