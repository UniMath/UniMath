(*****************************************************************************************


 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.

Local Open Scope cat.
Local Open Scope double_bicat.

Section CompanionPairs.
  Context {B : verity_double_bicat}.

  Definition are_companions
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
    : UU
    := ∑ (φ : square_double_bicat h (id₁ _) v (id₁ _))
         (ψ : square_double_bicat (id₁ _) h (id₁ _) v),
       (runitor _ ▹s (linvunitor _ ◃s ψ ⋆v φ) = id_h_square_bicat _)
       ×
       (runitor _ ▿s (linvunitor _ ▵s ψ ⋆h φ) = id_v_square_bicat _).

  Definition make_are_companions
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
             (φ : square_double_bicat h (id₁ _) v (id₁ _))
             (ψ : square_double_bicat (id₁ _) h (id₁ _) v)
             (p : runitor _ ▹s (linvunitor _ ◃s ψ ⋆v φ) = id_h_square_bicat _)
             (q : runitor _ ▿s (linvunitor _ ▵s ψ ⋆h φ) = id_v_square_bicat _)
    : are_companions h v
    := φ ,, ψ ,, p ,, q.

  Definition unit_are_companions
             {x y : B}
             {h : x --> y}
             {v : x -|-> y}
             (c : are_companions h v)
    : square_double_bicat h (id₁ _) v (id₁ _)
    := pr1 c.

  Definition counit_are_companions
             {x y : B}
             {h : x --> y}
             {v : x -|-> y}
             (c : are_companions h v)
    : square_double_bicat (id₁ _) h (id₁ _) v
    := pr12 c.

  Proposition are_companions_left
              {x y : B}
              {h : x --> y}
              {v : x -|-> y}
              (c : are_companions h v)
    : runitor _ ▹s (linvunitor _ ◃s counit_are_companions c ⋆v unit_are_companions c)
      =
      id_h_square_bicat _.
  Proof.
    exact (pr122 c).
  Defined.

  Proposition are_companions_left'
              {x y : B}
              {h : x --> y}
              {v : x -|-> y}
              (c : are_companions h v)
    : counit_are_companions c ⋆v unit_are_companions c
      =
      rinvunitor _ ▹s (lunitor _ ◃s id_h_square_bicat _).
  Proof.
    rewrite <- (are_companions_left c).
    rewrite !rwhisker_lwhisker_square.
    rewrite <- lwhisker_square_comp.
    rewrite lunitor_linvunitor.
    rewrite lwhisker_square_id.
    rewrite <- rwhisker_square_comp.
    rewrite runitor_rinvunitor.
    rewrite rwhisker_square_id.
    apply idpath.
  Qed.

  Proposition are_companions_right
              {x y : B}
              {h : x --> y}
              {v : x -|-> y}
              (c : are_companions h v)
    : runitor _ ▿s (linvunitor _ ▵s counit_are_companions c ⋆h unit_are_companions c)
      =
      id_v_square_bicat _.
  Proof.
    exact (pr222 c).
  Defined.

  Proposition are_companions_right'
              {x y : B}
              {h : x --> y}
              {v : x -|-> y}
              (c : are_companions h v)
    : counit_are_companions c ⋆h unit_are_companions c
      =
      rinvunitor _ ▿s (lunitor _ ▵s id_v_square_bicat _).
  Proof.
    rewrite <- (are_companions_right c).
    rewrite !dwhisker_uwhisker_square.
    rewrite <- uwhisker_square_comp.
    rewrite lunitor_linvunitor.
    rewrite uwhisker_square_id.
    rewrite <- dwhisker_square_comp.
    rewrite runitor_rinvunitor.
    rewrite dwhisker_square_id.
    apply idpath.
  Qed.

  Proposition eq_are_companions
              {x y : B}
              {h : x --> y}
              {v : x -|-> y}
              {c₁ c₂ : are_companions h v}
              (p : unit_are_companions c₁ = unit_are_companions c₂)
              (q : counit_are_companions c₁ = counit_are_companions c₂)
    : c₁ = c₂.
  Proof.
    use total2_paths_f.
    - exact p.
    - use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply isaset_square_double_bicat.
      }
      rewrite pr1_transportf.
      rewrite transportf_const.
      exact q.
  Qed.

  Definition id_are_companions
             (x : B)
    : are_companions (id₁ x) (id₁ _).
  Proof.
    use make_are_companions.
    - apply id_v_square_bicat.
    - apply id_v_square_bicat.
    - abstract
        (refine (_ @ rwhisker_square_id _ _) ;
         rewrite <- rinvunitor_runitor ;
         rewrite rwhisker_square_comp ;
         apply maponpaths ;
         rewrite id_h_square_bicat_id ;
         rewrite lunitor_v_comp_square' ;
         rewrite rwhisker_lwhisker_square ;
         rewrite <- lwhisker_square_comp ;
         rewrite linvunitor_lunitor ;
         rewrite lwhisker_square_id ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         apply idpath).
    - abstract
        (refine (_ @ dwhisker_square_id _ _) ;
         rewrite <- rinvunitor_runitor ;
         rewrite dwhisker_square_comp ;
         apply maponpaths ;
         rewrite <- !id_h_square_bicat_id ;
         rewrite lunitor_h_comp_square' ;
         rewrite dwhisker_uwhisker_square ;
         rewrite <- uwhisker_square_comp ;
         rewrite linvunitor_lunitor ;
         rewrite uwhisker_square_id ;
         rewrite lunitor_V_id_is_left_unit_V_id ;
         apply idpath).
  Defined.

  Section CompCompanions.
    Context {x y z : B}
            {h₁ : x --> y}
            {h₂ : y --> z}
            {v₁ : x -|-> y}
            {v₂ : y -|-> z}
            (c₁ : are_companions h₁ v₁)
            (c₂ : are_companions h₂ v₂).

    Let φ₁ : square_double_bicat h₁ (id₁ y) v₁ (id₁ _) := unit_are_companions c₁.
    Let ψ₁ : square_double_bicat (id₁ x) h₁ (id₁ _) v₁ := counit_are_companions c₁.
    Let φ₂ : square_double_bicat h₂ (id₁ z) v₂ (id₁ _) := unit_are_companions c₂.
    Let ψ₂ : square_double_bicat (id₁ y) h₂ (id₁ _) v₂ := counit_are_companions c₂.

    Definition comp_are_companions_unit
      : square_double_bicat (h₁ · h₂) (id₁ z) (v₁ · v₂) (id₁ _)
      := lunitor _ ▹s (lunitor _ ▿s ((φ₁ ⋆h id_v_square_bicat h₂)
                                     ⋆v
                                     (id_h_square_bicat v₂ ⋆h φ₂))).

    Let φ : square_double_bicat (h₁ · h₂) (id₁ z) (v₁ · v₂) (id₁ _)
      := comp_are_companions_unit.

    Definition comp_are_companions_counit
      : square_double_bicat (id₁ x) (h₁ · h₂) (id₁ _) (v₁ · v₂)
      := linvunitor _ ◃s (linvunitor _ ▵s ((ψ₁ ⋆h id_h_square_bicat _)
                                           ⋆v
                                           (id_v_square_bicat h₁ ⋆h ψ₂))).

    Let ψ : square_double_bicat (id₁ x) (h₁ · h₂) (id₁ _) (v₁ · v₂)
      := comp_are_companions_counit.

    Proposition comp_are_companions_left
      : runitor (v₁ · v₂) ▹s (linvunitor (v₁ · v₂) ◃s ψ ⋆v φ)
        =
        id_h_square_bicat (v₁ · v₂).
    Proof.
    Admitted.

    Proposition comp_are_companions_right
      : runitor (h₁ · h₂) ▿s (linvunitor (h₁ · h₂) ▵s ψ ⋆h φ)
        =
        id_v_square_bicat (h₁ · h₂).
    Proof.
    Admitted.

    Definition comp_are_companions
      : are_companions (h₁ · h₂) (v₁ · v₂).
    Proof.
      use make_are_companions.
      - exact φ.
      - exact ψ.
      - exact comp_are_companions_left.
      - exact comp_are_companions_right.
    Defined.
  End CompCompanions.

  Definition cell_are_companions
             (H : vertical_cells_are_squares B)
             {x y : B}
             {h₁ h₂ : x --> y}
             (τ : h₂ ==> h₁)
             {v₁ v₂ : x -|-> y}
             (c₁ : are_companions h₁ v₁)
             (c₂ : are_companions h₂ v₂)
    : v₁ ==> v₂
    := let φ₁ := unit_are_companions c₁ in
       let ψ₂ := τ ▿s counit_are_companions c₂ in
       square_to_vertical_cell H (linvunitor _ ◃s (runitor _ ▹s ψ₂ ⋆v φ₁)).

  Proposition cell_are_companions_id
              (H : vertical_cells_are_squares B)
              {x y : B}
              {h : x --> y}
              {v : x -|-> y}
              (c : are_companions h v)
    : cell_are_companions H (id2 h) c c = id2 v.
  Proof.
    unfold cell_are_companions.
    rewrite <- (square_to_vertical_cell_id H).
    apply maponpaths.
    rewrite dwhisker_square_id.
    rewrite are_companions_left'.
    rewrite <- rwhisker_square_comp.
    rewrite rinvunitor_runitor.
    rewrite rwhisker_square_id.
    rewrite <- lwhisker_square_comp.
    rewrite linvunitor_lunitor.
    rewrite lwhisker_square_id.
    apply idpath.
  Qed.

  Proposition cell_are_companions_comp
              (H : vertical_cells_are_squares B)
              {x y : B}
              {h₁ h₂ h₃ : x --> y}
              (τ₁ : h₂ ==> h₁)
              (τ₂ : h₃ ==> h₂)
              {v₁ v₂ v₃ : x -|-> y}
              (c₁ : are_companions h₁ v₁)
              (c₂ : are_companions h₂ v₂)
              (c₃ : are_companions h₃ v₃)
    : cell_are_companions H (τ₂ • τ₁) c₁ c₃
      =
      cell_are_companions H τ₁ c₁ c₂ • cell_are_companions H τ₂ c₂ c₃.
  Proof.
    unfold cell_are_companions.
    rewrite <- square_to_vertical_cell_comp.
    apply maponpaths.
    unfold comp_ver_globular_square.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite <- lwhisker_hcomp_square.
      apply maponpaths.
      rewrite <- rwhisker_lwhisker_square.
      rewrite <- rwhisker_hcomp_square.
      apply idpath.
    }
    rewrite <- lwhisker_dwhisker_square.
    rewrite <- lwhisker_uwhisker_square.
    apply maponpaths.
    rewrite <- rwhisker_dwhisker_square.
    rewrite <- rwhisker_uwhisker_square.
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite lrwhisker_hcomp_square.
      rewrite <- rwhisker_square_comp.
      apply idpath.
    }
  Admitted.

  Definition inv2cell_are_companions
             (H : vertical_cells_are_squares B)
             {x y : B}
             {h₁ h₂ : x --> y}
             (τ : invertible_2cell h₁ h₂)
             {v₁ v₂ : x -|-> y}
             (c₁ : are_companions h₁ v₁)
             (c₂ : are_companions h₂ v₂)
    : invertible_2cell v₁ v₂.
  Proof.
    use make_invertible_2cell.
    - exact (cell_are_companions H (τ^-1) c₁ c₂).
    - use make_is_invertible_2cell.
      + exact (cell_are_companions H τ c₂ c₁).
      + abstract
          (rewrite <- cell_are_companions_comp ;
           rewrite vcomp_rinv ;
           apply cell_are_companions_id).
      + abstract
          (rewrite <- cell_are_companions_comp ;
           rewrite vcomp_linv ;
           apply cell_are_companions_id).
  Defined.

  Section CompanionOfAdjequiv.
    Context (H : vertical_cells_are_squares B)
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            (c : are_companions h v)
            (Hh : left_adjoint_equivalence h)
            {v' : y -|-> x}
            (c' : are_companions (left_adjoint_right_adjoint Hh) v').

    Let h' : y --> x := left_adjoint_right_adjoint Hh.
    Let η : invertible_2cell (id₁ x) (h · h')
      := left_equivalence_unit_iso Hh.
    Let ε : invertible_2cell (h' · h) (id₁ y)
      := left_equivalence_counit_iso Hh.

    Definition companion_of_adjequiv_equiv
      : left_equivalence v.
    Proof.
      simple refine ((v' ,, (_ ,, _)) ,, (_ ,, _)).
      - exact (inv2cell_are_companions
                 H
                 η
                 (id_are_companions x)
                 (comp_are_companions c c')).
      - exact (inv2cell_are_companions
                 H
                 ε
                 (comp_are_companions c' c)
                 (id_are_companions y)).
      - apply property_from_invertible_2cell.
      - apply property_from_invertible_2cell.
    Defined.

    Definition companion_of_adjequiv
      : left_adjoint_equivalence v.
    Proof.
      use equiv_to_adjequiv.
      exact companion_of_adjequiv_equiv.
    Defined.
  End CompanionOfAdjequiv.

  Definition square_between_companions
             {x y : B}
             {h : x --> y}
             {v₁ v₂ : x -|-> y}
             (c₁ : are_companions h v₁)
             (c₂ : are_companions h v₂)
    : square_double_bicat (id₁ _) (id₁ _) v₁ v₂
    := linvunitor _ ◃s (runitor _ ▹s counit_are_companions c₂ ⋆v unit_are_companions c₁).

  (*
  Section ComparionPairUnique.
    Context {x y : B}
            {h : x --> y}
            {v₁ v₂ : x -|-> y}
            (c₁ : are_companions h v₁)
            (c₂ : are_companions h v₂).

    Let γ₁ : square_double_bicat (id₁ _) (id₁ _) v₁ v₂
      := square_between_companions c₁ c₂.

    Let γ₂ : square_double_bicat (id₁ _) (id₁ _) v₂ v₁
      := square_between_companions c₂ c₁.

    Definition test
      : lunitor _ ▿s (rinvunitor _ ▵s γ₁ ⋆h γ₂) = id_h_square_bicat v₁.
    Proof.
      unfold γ₁, γ₂, square_between_companions.
      pose (p₁ := are_companions_left c₁).
      refine (_ @ p₁).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- lwhisker_hcomp_square.
        apply maponpaths.
        rewrite lrwhisker_hcomp_square.
        rewrite <- rwhisker_hcomp_square.
        apply idpath.
      }
      rewrite <- rwhisker_lwhisker_square.
      rewrite <- rwhisker_uwhisker_square.
      rewrite <- rwhisker_dwhisker_square.
      apply maponpaths.
      rewrite <- lwhisker_uwhisker_square.
      rewrite <- lwhisker_dwhisker_square.
      apply maponpaths.
      refine (!_).

      pose (q₂ := are_companions_right c₂).
      rewrite <-


        Check double_bicat_interchange.

        assert UU.
        {
          refine ((counit_are_companions c₂ ⋆v unit_are_companions c₁)
                  ⋆h
                  (counit_are_companions c₁ ⋆v unit_are_companions c₂)
                  =
                 _).
          Search comp_h_square_bicat.

        rewrite lrwhisker_hcomp_square.
        rewrite rwhisker_square_comp.
        rewrite double_bicat_interchange.
      cbn.
      refine ().
      Check γ₂ ⋆h γ₁.
      Check γ₁ ⋆h γ₂.
  End ComparionPairUnique.
   *)
End CompanionPairs.

Definition all_companions
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y),
     ∑ (v : x -|-> y), are_companions h v.

Definition all_equivs_companions
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B)
       (h : x --> y)
       (Hh : left_adjoint_equivalence h),
     ∑ (v : x -|-> y), are_companions h v.

Definition all_companions_to_all_equivs_companions
           (B : verity_double_bicat)
           (H : all_companions B)
  : all_equivs_companions B
  := λ x y h _, H x y h.

Definition all_equivs_companions_adjequiv
           {B : verity_double_bicat}
           (H : vertical_cells_are_squares B)
           (H' : all_equivs_companions B)
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
           (Hh : left_adjoint_equivalence h)
  : left_adjoint_equivalence v.
Proof.
  use companion_of_adjequiv.
  - exact H.
  - exact h.
  - exact c.
  - exact Hh.
  - exact (pr1 (H' _ _ _ (inv_left_adjoint_equivalence Hh))).
  - exact (pr2 (H' _ _ _ (inv_left_adjoint_equivalence Hh))).
Defined.

Definition all_companions_adjequiv
           {B : verity_double_bicat}
           (H : vertical_cells_are_squares B)
           (H' : all_companions B)
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
           (Hh : left_adjoint_equivalence h)
  : left_adjoint_equivalence v.
Proof.
  use all_equivs_companions_adjequiv.
  - exact H.
  - use all_companions_to_all_equivs_companions.
    exact H'.
  - exact h.
  - exact c.
  - exact Hh.
Defined.

Definition univalent_2_0_all_equivs_companions
           (B : verity_double_bicat)
           (H : is_univalent_2_0 (hor_bicat_of_verity_double_bicat B))
  : all_equivs_companions B.
Proof.
  assert (∏ (x y : B)
            (h : adjoint_equivalence x y),
          ∑ (v : x -|-> y), are_companions h v)
    as H'.
  {
    use (J_2_0 H) ; cbn.
    intros x.
    exact (_ ,, id_are_companions x).
  }
  intros x y h Hh.
  exact (H' x y (h ,, Hh)).
Defined.
