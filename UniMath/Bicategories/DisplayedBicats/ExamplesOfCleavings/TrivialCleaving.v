Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Cartesians.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.

Local Open Scope cat.

(**
The trivial bicategory has a cleaving
 *)
Section ConstantCleaving.
  Variable (B₁ B₂ : bicat).

  (** Characterisation of cartesian 2-cells *)
  Definition trivial_invertible_is_cartesian_2cell
             {x₁ x₂ : B₁}
             {y₁ : trivial_displayed_bicat B₁ B₂ x₁}
             {y₂ : trivial_displayed_bicat B₁ B₂ x₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ : y₁ -->[ f₁ ] y₂}
             {g₂ : y₁ -->[ f₂ ] y₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==>[ α ] g₂)
             (Hβ : is_invertible_2cell β)
    : is_cartesian_2cell (trivial_displayed_bicat B₁ B₂) β.
  Proof.
    intros h h' γ ββ ; cbn in *.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         use (vcomp_rcancel _ Hβ) ;
         exact (pr2 τ₁ @ !(pr2 τ₂))).
    - refine (ββ • Hβ^-1 ,, _).
      abstract
        (rewrite !vassocl ;
         rewrite vcomp_linv ;
         apply id2_right).
  Defined.

  Definition trivial_cartesian_2cell_is_invertible
             {x₁ x₂ : B₁}
             {y₁ : trivial_displayed_bicat B₁ B₂ x₁}
             {y₂ : trivial_displayed_bicat B₁ B₂ x₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ : y₁ -->[ f₁ ] y₂}
             {g₂ : y₁ -->[ f₂ ] y₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==>[ α ] g₂)
             (Hβ : is_cartesian_2cell (trivial_displayed_bicat B₁ B₂) β)
    : is_invertible_2cell β.
  Proof.
    cbn in *.
    unfold is_cartesian_2cell in Hβ.
    pose (Hβ f₁ g₂ (id2 _) (id2 _)) as lift.
    pose (inv := iscontrpr1 lift).
    cbn in lift, inv.
    use make_is_invertible_2cell.
    - exact (pr1 inv).
    - abstract
        (pose (Hβ f₁ g₁ (id2 _) β) as m ;
         cbn in m ;
         pose (proofirrelevance _ (isapropifcontr m)) as i ;
         simple refine (maponpaths pr1 (i (β • pr1 inv ,, _) (id₂ g₁ ,, _))) ; cbn ;
         [ cbn ;
           rewrite vassocl ;
           rewrite (pr2 inv) ;
           apply id2_right
         | apply id2_left ]).
    - abstract
        (exact (pr2 inv)).
  Defined.

    (** Characterisation of cartesian 2-cells *)
  Definition trivial_invertible_is_opcartesian_2cell
             {x₁ x₂ : B₁}
             {y₁ : trivial_displayed_bicat B₁ B₂ x₁}
             {y₂ : trivial_displayed_bicat B₁ B₂ x₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ : y₁ -->[ f₁ ] y₂}
             {g₂ : y₁ -->[ f₂ ] y₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==>[ α ] g₂)
             (Hβ : is_invertible_2cell β)
    : is_opcartesian_2cell (trivial_displayed_bicat B₁ B₂) β.
  Proof.
    intros h h' γ ββ ; cbn in *.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         use (vcomp_lcancel _ Hβ) ;
         exact (pr2 τ₁ @ !(pr2 τ₂))).
    - refine (Hβ^-1 • ββ,, _).
      abstract
        (rewrite !vassocr ;
         rewrite vcomp_rinv ;
         apply id2_left).
  Defined.

  Definition trivial_opcartesian_2cell_is_invertible
             {x₁ x₂ : B₁}
             {y₁ : trivial_displayed_bicat B₁ B₂ x₁}
             {y₂ : trivial_displayed_bicat B₁ B₂ x₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ : y₁ -->[ f₁ ] y₂}
             {g₂ : y₁ -->[ f₂ ] y₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==>[ α ] g₂)
             (Hβ : is_opcartesian_2cell (trivial_displayed_bicat B₁ B₂) β)
    : is_invertible_2cell β.
  Proof.
    cbn in *.
    unfold is_cartesian_2cell in Hβ.
    pose (Hβ f₂ g₁ (id2 _) (id2 _)) as lift.
    pose (inv := iscontrpr1 lift).
    cbn in lift, inv.
    use make_is_invertible_2cell.
    - exact (pr1 inv).
    - abstract
        (exact (pr2 inv)).
    - abstract
        (pose (Hβ f₂ g₂ (id2 _) β) as m ;
         cbn in m ;
         pose (proofirrelevance _ (isapropifcontr m)) as i ;
         simple refine (maponpaths pr1 (i (pr1 inv • β,, _) (id₂ g₂ ,, _))) ; cbn ;
         [ cbn ;
           rewrite vassocr ;
           rewrite (pr2 inv) ;
           apply id2_left
         | apply id2_right ]).
  Defined.

  Definition trivial_local_cleaving
    : local_cleaving (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros x₁ x₂ y₁ y₂ f₁ f₂ f α.
    simple refine (f ,, id2 _ ,, _) ; cbn.
    apply trivial_invertible_is_cartesian_2cell.
    is_iso.
  Defined.

  Definition trivial_local_opcleaving
    : local_opcleaving (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros x₁ x₂ y₁ y₂ f₁ f₂ f α.
    simple refine (f ,, id2 _ ,, _) ; cbn.
    apply trivial_invertible_is_opcartesian_2cell.
    is_iso.
  Defined.

  Section TrivialCartesianOneCell.
    Context {x₁ x₂ : B₁}
            {y₁ : trivial_displayed_bicat B₁ B₂ x₁}
            {y₂ : trivial_displayed_bicat B₁ B₂ x₂}
            (f : x₁ --> x₂)
            (g : y₁ -->[ f ] y₂)
            (Hg : left_adjoint_equivalence g).

    Definition trivial_lift_1cell
               {x₃ : B₁}
               {y₃ : trivial_displayed_bicat B₁ B₂ x₃}
               (h : x₃ --> x₁)
               (k : y₃ -->[ h · f] y₂)
      : lift_1cell_factor (trivial_displayed_bicat B₁ B₂) g k.
    Proof.
      simple refine (_ ,, _) ; cbn in *.
      - exact (k · left_adjoint_right_adjoint Hg).
      - simple refine (_ ,, _) ; cbn.
        + refine (rassociator _ _ _ • (k ◃ _) • runitor _).
          exact (left_adjoint_counit Hg).
        + cbn.
          use trivial_is_invertible_2cell_to_is_disp_invertible.
          is_iso.
          apply (left_equivalence_counit_iso Hg).
    Defined.

    Definition trivial_lift_2cell
               {w : B₁}
               {z : B₂}
               {h h' : w --> x₁}
               {k k' : z --> y₂}
               (γ : h ==> h')
               (δ : k ==> k')
               (Lh : lift_1cell_factor (trivial_displayed_bicat B₁ B₂) g k)
               (Lh' : lift_1cell_factor (trivial_displayed_bicat B₁ B₂) g k')
      : lift_2cell_factor (trivial_displayed_bicat B₁ B₂) g (δ := γ) δ Lh Lh'.
    Proof.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           induction φ₁ as [ φ₁ ψ₁ ] ;
           induction φ₂ as [ φ₂ ψ₂ ] ;
           use subtypePath ; [ intro ; apply cellset_property | ] ;
           cbn in * ;
           rewrite transportf_const in ψ₁, ψ₂ ;
           cbn in * ;
           apply (fully_faithful_1cell_faithful (adj_equiv_fully_faithful Hg)) ;
           pose (p₂ := trivial_disp_invertible_to_invertible_2cell (pr2 Lh')) ;
           use (vcomp_rcancel p₂) ; [ apply p₂ | ] ;
           exact (ψ₁ @ !ψ₂)).
      - simple refine (_ ,, _) ; cbn.
        + exact (fully_faithful_1cell_inv_map
                   (adj_equiv_fully_faithful Hg)
                   (pr12 Lh
                    • δ
                    • trivial_disp_invertible_to_invertible_2cell (pr2 Lh')^-1)).
        + abstract
            (rewrite transportf_const ; cbn ;
             etrans ;
             [ apply maponpaths_2 ;
               apply (fully_faithful_1cell_inv_map_eq (adj_equiv_fully_faithful Hg))
             | ] ;
             cbn in * ;
             rewrite !vassocl ;
             apply maponpaths ;
             refine (_ @ id2_right _) ;
             apply maponpaths ;
             apply (vcomp_linv
                      (trivial_disp_invertible_to_invertible_2cell (pr2 Lh')))).
    Defined.

    Definition trivial_cartesian_1cell
      : cartesian_1cell (trivial_displayed_bicat B₁ B₂) g.
    Proof.
      split.
      - exact @trivial_lift_1cell.
      - exact @trivial_lift_2cell.
    Defined.
  End TrivialCartesianOneCell.

  Section Cartesian1CellToAdjEquiv.
    Context {x₁ x₂ : B₁}
            {y₁ : trivial_displayed_bicat B₁ B₂ x₁}
            {y₂ : trivial_displayed_bicat B₁ B₂ x₂}
            (f : x₁ --> x₂)
            (g : y₁ -->[ f ] y₂)
            (Hg : cartesian_1cell (trivial_displayed_bicat B₁ B₂) g).

    Let inv : y₂ --> y₁ := pr1 (pr1 Hg x₁ y₂ (id₁ _) (id₁ _)).
    Let ε : inv · g ==> id₁ y₂ := pr12 (pr1 Hg x₁ y₂ (id₁ _) (id₁ _)).
    Let εinv
      : is_invertible_2cell ε
      := trivial_disp_invertible_to_invertible_2cell
           (pr2 (pr1 Hg x₁ y₂ (id₁ _) (id₁ _))).

    Local Definition unit_help_lift₁
      : lift_1cell_factor (trivial_displayed_bicat B₁ B₂) (h := id₁ _) g g.
    Proof.
      simple refine (_ ,, _ ,, _) ; cbn.
      - apply id₁.
      - apply lunitor.
      - use trivial_is_invertible_2cell_to_is_disp_invertible.
        is_iso.
    Defined.

    Local Definition unit_help_lift₂
      : lift_1cell_factor (trivial_displayed_bicat B₁ B₂) (h := id₁ _) g g.
    Proof.
      simple refine (_ ,, _ ,, _) ; cbn.
      - exact (g · inv).
      - exact (rassociator _ _ _ • (g ◃ ε) • runitor _).
      - use trivial_is_invertible_2cell_to_is_disp_invertible.
        is_iso.
    Defined.

    Local Definition unit
      : id₁ y₁ ==> g · inv
      := cartesian_1cell_lift_2cell
           _ _
           Hg
           (δ := id2 _) (id2 _)
           unit_help_lift₁ unit_help_lift₂.

    Definition trivial_cartesian_1cell_left_adj_data
      : left_adjoint_data g
      := (inv ,, unit ,, ε).

    Definition trivial_cartesian_1cell_left_equiv_axioms
      : left_equivalence_axioms trivial_cartesian_1cell_left_adj_data.
    Proof.
      split.
      - use (trivial_is_disp_invertible_to_is_invertible_2cell (α := id2 (id₁ _))).
        + is_iso.
        + refine (cartesian_1cell_lift_2cell_invertible
                   _ Hg _ _
                   unit_help_lift₁
                   unit_help_lift₂).
          use trivial_is_invertible_2cell_to_is_disp_invertible.
          is_iso.
      - exact εinv.
    Defined.

    Definition trivial_cartesian_1cell_is_adj_equiv
      : left_adjoint_equivalence g.
    Proof.
      use equiv_to_adjequiv.
      simple refine (_ ,, _).
      - exact trivial_cartesian_1cell_left_adj_data.
      - exact trivial_cartesian_1cell_left_equiv_axioms.
    Defined.
  End Cartesian1CellToAdjEquiv.

  Definition trivial_global_cleaving
    : global_cleaving (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros x₁ x₂ y₁ y₂.
    simple refine (y₁ ,, id₁ _ ,, _) ; cbn.
    apply trivial_cartesian_1cell.
    apply (internal_adjoint_equivalence_identity y₁).
  Defined.

  Definition trivial_lwhisker_cartesian
    : lwhisker_cartesian (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hαα.
    apply trivial_invertible_is_cartesian_2cell.
    cbn.
    is_iso.
    apply trivial_cartesian_2cell_is_invertible.
    apply Hαα.
  Qed.

  Definition trivial_rwhisker_cartesian
    : rwhisker_cartesian (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hαα.
    apply trivial_invertible_is_cartesian_2cell.
    cbn.
    is_iso.
    apply trivial_cartesian_2cell_is_invertible.
    apply Hαα.
  Qed.

  Definition trivial_lwhisker_opcartesian
    : lwhisker_opcartesian (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hαα.
    apply trivial_invertible_is_opcartesian_2cell.
    cbn.
    is_iso.
    apply trivial_opcartesian_2cell_is_invertible.
    apply Hαα.
  Qed.

  Definition trivial_rwhisker_opcartesian
    : rwhisker_opcartesian (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hαα.
    apply trivial_invertible_is_opcartesian_2cell.
    cbn.
    is_iso.
    apply trivial_opcartesian_2cell_is_invertible.
    apply Hαα.
  Qed.

  Definition trivial_cleaving_of_bicats
    : cleaving_of_bicats (trivial_displayed_bicat B₁ B₂).
  Proof.
    repeat split.
    - exact trivial_local_cleaving.
    - exact trivial_global_cleaving.
    - exact trivial_lwhisker_cartesian.
    - exact trivial_rwhisker_cartesian.
  Defined.
End ConstantCleaving.
