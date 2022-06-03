(****************************************************************************

 Equifiers in bicategories

 Contents
 1. Cones
 2. The universal mapping property
 3. Alternative formulation of equifier via universal cones
 4. Bicategories with equifiers
 5. Equifiers are fully faithful

 ****************************************************************************)
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
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.

Local Open Scope cat.

Section Equifiers.
  Context {B : bicat}
          {b₁ b₂ : B}
          {f g : b₁ --> b₂}
          {α β : f ==> g}.

  (**
   1. Cones
   *)
  Definition equifier_cone
    : UU
    := ∑ (i : B)
         (m : i --> b₁),
       m ◃ α = m ◃ β.

  Definition make_equifier_cone
             (i : B)
             (m : i --> b₁)
             (α : m ◃ α = m ◃ β)
    : equifier_cone
    := i ,, m ,, α.

  Coercion equifier_cone_ob
           (cone : equifier_cone)
    : B
    := pr1 cone.

  Definition equifier_cone_pr1
             (cone : equifier_cone)
    : cone --> b₁
    := pr12 cone.

  Definition equifier_cone_eq
             (cone : equifier_cone)
    : equifier_cone_pr1 cone ◃ α = equifier_cone_pr1 cone ◃ β
    := pr22 cone.

  Definition equifier_1cell
             (cone₁ cone₂ : equifier_cone)
    : UU
    := ∑ (k : cone₁ --> cone₂),
       invertible_2cell
         (k · equifier_cone_pr1 cone₂)
         (equifier_cone_pr1 cone₁).

  Definition make_equifier_1cell
             {cone₁ cone₂ : equifier_cone}
             (k : cone₁ --> cone₂)
             (α : invertible_2cell
                    (k · equifier_cone_pr1 cone₂)
                    (equifier_cone_pr1 cone₁))
    : equifier_1cell cone₁ cone₂
    := k ,, α.

  Coercion equifier_1cell_mor
           {cone₁ cone₂ : equifier_cone}
           (u : equifier_1cell cone₁ cone₂)
    : cone₁ --> cone₂
    := pr1 u.

  Definition equifier_1cell_pr1
             {cone₁ cone₂ : equifier_cone}
             (u : equifier_1cell cone₁ cone₂)
    : invertible_2cell
        (u · equifier_cone_pr1 cone₂)
        (equifier_cone_pr1 cone₁)
    := pr2 u.

  Definition path_equifier_1cell
             {cone₁ cone₂ : equifier_cone}
             (φ ψ : equifier_1cell cone₁ cone₂)
             (p₁ : pr1 φ = pr1 ψ)
             (p₂ : pr12 φ = (idtoiso_2_1 _ _ p₁ ▹ _) • pr12 ψ)
    : φ = ψ.
  Proof.
    induction φ as [ φ₁ [ φ₂ φ₃ ]].
    induction ψ as [ ψ₁ [ ψ₂ ψ₃ ]].
    cbn in *.
    induction p₁.
    apply maponpaths.
    use subtypePath.
    {
      intro.
      apply isaprop_is_invertible_2cell.
    }
    cbn in p₂.
    rewrite id2_rwhisker, id2_left in p₂.
    exact p₂.
  Qed.

  (**
   2. The universal mapping property
   *)
  Section UniversalMappingProperty.
    Context (cone : equifier_cone).

    Definition has_equifier_ump_1
      : UU
      := ∏ (other_cone : equifier_cone),
         equifier_1cell other_cone cone.

    Definition has_equifier_ump_2
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (α : u₁ · equifier_cone_pr1 cone
                ==>
                u₂ · equifier_cone_pr1 cone),
         ∑ (ζ : u₁ ==> u₂),
         ζ ▹ equifier_cone_pr1 cone = α.

    Definition has_equifier_ump_eq
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (α : u₁ · equifier_cone_pr1 cone
                ==>
                u₂ · equifier_cone_pr1 cone)
           (φ₁ φ₂ : u₁ ==> u₂)
           (q₁ : φ₁ ▹ equifier_cone_pr1 cone = α)
           (q₂ : φ₂ ▹ equifier_cone_pr1 cone = α),
         φ₁ = φ₂.

    Definition has_equifier_ump
      : UU
      := has_equifier_ump_1 × has_equifier_ump_2 × has_equifier_ump_eq.
  End UniversalMappingProperty.

  Section Projections.
    Context {cone : equifier_cone}
            (H : has_equifier_ump cone).

    Definition equifier_ump_mor
               {i : B}
               (m : i --> b₁)
               (p : m ◃ α = m ◃ β)
      : i --> cone
      := pr1 H (make_equifier_cone i m p).

    Definition equifier_ump_mor_pr1
               {i : B}
               (m : i --> b₁)
               (p : m ◃ α = m ◃ β)
      : invertible_2cell
          (equifier_ump_mor m p · equifier_cone_pr1 cone)
          m
      := equifier_1cell_pr1 (pr1 H (make_equifier_cone i m p)).

    Definition equifier_ump_cell
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
      : u₁ ==> u₂
      := pr1 (pr12 H x u₁ u₂ ζ).

    Definition equifier_ump_cell_pr1
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
      : equifier_ump_cell ζ ▹ equifier_cone_pr1 cone = ζ
      := pr2 (pr12 H x u₁ u₂ ζ).

    Definition equifier_ump_eq
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
               (φ₁ φ₂ : u₁ ==> u₂)
               (q₁ : φ₁ ▹ equifier_cone_pr1 cone = ζ)
               (q₂ : φ₂ ▹ equifier_cone_pr1 cone = ζ)
      : φ₁ = φ₂
      := pr22 H x u₁ u₂ ζ φ₁ φ₂ q₁ q₂.

    Definition equifier_ump_eq_alt
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
               (φ₁ φ₂ : u₁ ==> u₂)
               (q : φ₁ ▹ equifier_cone_pr1 cone
                    =
                    φ₂ ▹ equifier_cone_pr1 cone)
      : φ₁ = φ₂.
    Proof.
      use equifier_ump_eq.
      - exact (φ₁ ▹ equifier_cone_pr1 cone).
      - apply idpath.
      - exact (!q).
    Qed.

    Definition is_invertible_equifier_ump_cell
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
               (Hζ : is_invertible_2cell ζ)
      : is_invertible_2cell (equifier_ump_cell ζ).
    Proof.
      use make_is_invertible_2cell.
      - exact (equifier_ump_cell (Hζ^-1)).
      - abstract
          (use (equifier_ump_eq_alt (id2 _)) ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !equifier_ump_cell_pr1 ;
           rewrite vcomp_rinv ;
           rewrite id2_rwhisker ;
           apply idpath).
      - abstract
          (use (equifier_ump_eq_alt (id2 _)) ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !equifier_ump_cell_pr1 ;
           rewrite vcomp_linv ;
           rewrite id2_rwhisker ;
           apply idpath).
    Defined.
  End Projections.

  (**
   3. Alternative formulation of equifier via universal cones
   *)
  Definition universal_equifier_cat
             (x : B)
    : category.
  Proof.
    refine (full_sub_category
              (hom x b₁)
              (λ h,
               make_hProp
                 (h ◃ α = h ◃ β)
                 _)).
    apply cellset_property.
  Defined.

  Definition univalent_universal_equifier_cat
             (HB_2_1 : is_univalent_2_1 B)
             (x : B)
    : univalent_category.
  Proof.
    use make_univalent_category.
    - exact (universal_equifier_cat x).
    - use is_univalent_full_subcat.
      use is_univ_hom.
      exact HB_2_1.
  Defined.

  Definition to_universal_equifier_cat_data
             (cone : equifier_cone)
             (x : B)
    : functor_data
        (hom x cone)
        (universal_equifier_cat x).
  Proof.
    use make_functor_data.
    - refine (λ h, h · equifier_cone_pr1 cone ,, _) ; cbn.
      abstract
        (use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ] ;
         rewrite <- !lwhisker_lwhisker ;
         apply maponpaths_2 ;
         apply maponpaths ;
         exact (equifier_cone_eq cone)).
    - exact (λ h₁ h₂ ζ, ζ ▹ _ ,, tt).
  Defined.

  Definition to_universal_equifier_cat_is_functor
             (cone : equifier_cone)
             (x : B)
    : is_functor (to_universal_equifier_cat_data cone x).
  Proof.
    split.
    - intro h ; cbn.
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      cbn.
      apply id2_rwhisker.
    - intros h₁ h₂ h₃ ζ₁ ζ₂ ; cbn.
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      cbn.
      refine (!_).
      apply rwhisker_vcomp.
  Qed.

  Definition to_universal_equifier_cat
             (cone : equifier_cone)
             (x : B)
    : hom x cone ⟶ universal_equifier_cat x.
  Proof.
    use make_functor.
    - exact (to_universal_equifier_cat_data cone x).
    - exact (to_universal_equifier_cat_is_functor cone x).
  Defined.

  Definition is_univeral_equifier_cone
             (cone : equifier_cone)
    : UU
    := ∏ (x : B),
       adj_equivalence_of_cats
         (to_universal_equifier_cat cone x).

  Section MakeUniversalEquifierCone.
    Context (cone : equifier_cone)
            (H : has_equifier_ump cone)
            (x : B).

    Definition make_is_universal_equifier_cone_full
      : full (to_universal_equifier_cat cone x).
    Proof.
      intros u₁ u₂ ζ.
      apply hinhpr.
      simple refine (_ ,, _).
      - use (equifier_ump_cell H).
        exact (pr1 ζ).
      - abstract
          (use subtypePath ; [ intro  ; apply isapropunit | ] ;
           apply (equifier_ump_cell_pr1 H)).
    Defined.

    Definition make_is_universal_equifier_cone_faithful
      : faithful (to_universal_equifier_cat cone x).
    Proof.
      intros u₁ u₂ ζ₁.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (equifier_ump_eq_alt H).
      - exact (pr1 ζ₁).
      - exact (maponpaths pr1 (pr2 φ₁ @ !(pr2 φ₂))).
    Qed.

    Definition make_is_universal_equifier_cone_essentially_surjective
      : essentially_surjective (to_universal_equifier_cat cone x).
    Proof.
      intros h.
      apply hinhpr.
      simple refine (_ ,, _).
      - use (equifier_ump_mor H).
        + exact (pr1 h).
        + exact (pr2 h).
      - cbn.
        use iso_in_sub_from_iso ; cbn.
        use inv2cell_to_z_iso.
        apply equifier_ump_mor_pr1.
    Defined.
  End MakeUniversalEquifierCone.

  Definition make_is_universal_equifier_cone
             (HB_2_1 : is_univalent_2_1 B)
             (cone : equifier_cone)
             (H : has_equifier_ump cone)
    : is_univeral_equifier_cone cone.
  Proof.
    intro x.
    use rad_equivalence_of_cats.
    - apply is_univ_hom.
      exact HB_2_1.
    - use full_and_faithful_implies_fully_faithful.
      split.
      + apply make_is_universal_equifier_cone_full.
        exact H.
      + apply make_is_universal_equifier_cone_faithful.
        exact H.
    - apply make_is_universal_equifier_cone_essentially_surjective.
      exact H.
  Defined.

  Section UniversalConeHasUMP.
    Context (cone : equifier_cone)
            (H : is_univeral_equifier_cone cone).

    Section UMP1.
      Context (q : equifier_cone).

      Let q' : universal_equifier_cat q
        := equifier_cone_pr1 q ,, equifier_cone_eq q.

      Definition universal_equifier_cone_has_ump_1_mor
        : q --> cone
        := right_adjoint (H q) q'.

      Definition universal_equifier_cone_has_ump_1_pr1
        : invertible_2cell
            (universal_equifier_cone_has_ump_1_mor · equifier_cone_pr1 cone)
            (equifier_cone_pr1 q).
      Proof.
        use z_iso_to_inv2cell.
        exact (iso_from_iso_in_sub
                 _ _ _ _
                 (nat_z_iso_pointwise_z_iso
                    (counit_nat_z_iso_from_adj_equivalence_of_cats (H q))
                    q')).
      Defined.
    End UMP1.

    Definition universal_equifier_cone_has_ump_1
      : has_equifier_ump_1 cone.
    Proof.
      intro q.
      use make_equifier_1cell.
      - exact (universal_equifier_cone_has_ump_1_mor q).
      - exact (universal_equifier_cone_has_ump_1_pr1 q).
    Defined.
  End UniversalConeHasUMP.

  Section UMP2.
    Context (cone : equifier_cone)
            (H : is_univeral_equifier_cone cone)
            {x : B}
            {u₁ u₂ : x --> cone}
            (ζ : u₁ · equifier_cone_pr1 cone
                 ==>
                 u₂ · equifier_cone_pr1 cone).

    Definition universal_equifier_cone_has_ump_2_cell
      : u₁ ==> u₂.
    Proof.
      apply (invmap (make_weq _ (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))).
      simple refine (_ ,, _).
      - exact ζ.
      - exact tt.
    Defined.

    Definition universal_equifier_cone_has_ump_2_pr1
      : universal_equifier_cone_has_ump_2_cell ▹ equifier_cone_pr1 cone
        =
        ζ.
    Proof.
      exact (maponpaths
               pr1
               (homotweqinvweq
                  (make_weq _ (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))
                  _)).
    Qed.
  End UMP2.

  Definition universal_equifier_cone_has_ump_2
             (cone : equifier_cone)
             (H : is_univeral_equifier_cone cone)
    : has_equifier_ump_2 cone.
  Proof.
    intros x u₁ u₂ ζ.
    simple refine (_ ,, _).
    - exact (universal_equifier_cone_has_ump_2_cell cone H ζ).
    - exact (universal_equifier_cone_has_ump_2_pr1 cone H ζ).
  Defined.

  Definition universal_equifier_cone_has_ump_eq
             (cone : equifier_cone)
             (H : is_univeral_equifier_cone cone)
    : has_equifier_ump_eq cone.
  Proof.
    intros x u₁ u₂ ζ φ₁ φ₂ p q.
    use (invmaponpathsweq
           (make_weq
              _
              (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))) ; cbn.
    use subtypePath.
    {
      intro.
      apply isapropunit.
    }
    cbn.
    exact (p @ !q).
  Qed.

  Definition universal_equifier_cone_has_ump
             (cone : equifier_cone)
             (H : is_univeral_equifier_cone cone)
    : has_equifier_ump cone.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (universal_equifier_cone_has_ump_1 cone H).
    - exact (universal_equifier_cone_has_ump_2 cone H).
    - exact (universal_equifier_cone_has_ump_eq cone H).
  Defined.

  Definition isaprop_has_equifier_ump
             (HB_2_1 : is_univalent_2_1 B)
             (cone : equifier_cone)
    : isaprop (has_equifier_ump cone).
  Proof.
    use invproofirrelevance.
    intros χ₁ χ₂.
    use pathsdirprod.
    - use funextsec.
      intro q.
      use path_equifier_1cell.
      + apply (isotoid_2_1 HB_2_1).
        use make_invertible_2cell.
        * use (equifier_ump_cell χ₁).
          exact (equifier_1cell_pr1 (pr1 χ₁ q) • (equifier_1cell_pr1 (pr1 χ₂ q))^-1).
        * use is_invertible_equifier_ump_cell.
          is_iso.
          apply property_from_invertible_2cell.
      + rewrite idtoiso_2_1_isotoid_2_1.
        cbn.
        rewrite equifier_ump_cell_pr1.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
    - use pathsdirprod.
      + use funextsec ; intro x.
        use funextsec ; intro u₁.
        use funextsec ; intro u₂.
        use funextsec ; intro φ.
        use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        use (equifier_ump_eq χ₁).
        * exact φ.
        * exact (pr2 ((pr12 χ₁) x u₁ u₂ φ)).
        * exact (pr2 ((pr12 χ₂) x u₁ u₂ φ)).
      + do 8 (use funextsec ; intro).
        apply cellset_property.
  Qed.

  Definition isaprop_is_universal_equifier_cone
             (HB_2_1 : is_univalent_2_1 B)
             (cone : equifier_cone)
    : isaprop (is_univeral_equifier_cone cone).
  Proof.
    use impred.
    intro x.
    use isofhlevelweqf.
    - exact (@left_adjoint_equivalence
               bicat_of_univ_cats
               (univ_hom HB_2_1 x cone)
               (univalent_universal_equifier_cat HB_2_1 x)
               (to_universal_equifier_cat cone x)).
    - exact (@adj_equiv_is_equiv_cat
               (univ_hom HB_2_1 x cone)
               (univalent_universal_equifier_cat HB_2_1 x)
               (to_universal_equifier_cat cone x)).
    - apply isaprop_left_adjoint_equivalence.
      exact univalent_cat_is_univalent_2_1.
  Defined.

  Definition equifier_ump_weq_is_universal
             (HB_2_1 : is_univalent_2_1 B)
             (cone : equifier_cone)
    : has_equifier_ump cone ≃ is_univeral_equifier_cone cone.
  Proof.
    use weqimplimpl.
    - exact (make_is_universal_equifier_cone HB_2_1 cone).
    - exact (universal_equifier_cone_has_ump cone).
    - exact (isaprop_has_equifier_ump HB_2_1 cone).
    - exact (isaprop_is_universal_equifier_cone HB_2_1 cone).
  Defined.
End Equifiers.

Arguments equifier_cone {_ _ _} _ _.

(**
 4. Bicategories with equifiers
 *)
Definition has_equifiers
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ : B)
       (f g : b₁ --> b₂)
       (α β : f ==> g),
     ∑ (i : B)
       (m : i --> b₁)
       (p : m ◃ α = m ◃ β),
     has_equifier_ump (make_equifier_cone i m p).

(**
 5. Equifiers are fully faithful
 *)
Definition equifier_faithful
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {α β : f ==> g}
           {i : B}
           (m : i --> b₁)
           (p :  m ◃ α = m ◃ β)
           (H : has_equifier_ump (make_equifier_cone i m p))
  : faithful_1cell m.
Proof.
  intros x g₁ g₂ β₁ β₂ q.
  use (equifier_ump_eq_alt H) ; cbn.
  - exact (β₁ ▹ m).
  - exact q.
Defined.

Definition equifier_fully_faithful
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {α β : f ==> g}
           {i : B}
           (m : i --> b₁)
           (p :  m ◃ α = m ◃ β)
           (H : has_equifier_ump (make_equifier_cone i m p))
  : fully_faithful_1cell m.
Proof.
  use make_fully_faithful.
  - exact (equifier_faithful m p H).
  - intros z g₁ g₂ βf.
    simple refine (_ ,, _).
    + exact (equifier_ump_cell H βf).
    + exact (equifier_ump_cell_pr1 H βf).
Defined.
