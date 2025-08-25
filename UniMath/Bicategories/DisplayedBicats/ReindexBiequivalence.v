(**

 Reindexing a displayed bicategory along a biequivalence

 Given a pseudofunctor `F` from `B₁` to `B₂`, every displayed bicategory `D` over `B₂`
 can be reindexed to obtain a displayed bicategory over `B₁`. If `F` happens to be part
 of a biequivalence, then the reindexed displayed bicategory is biequivalent to `D`. In
 this file, we construct the displayed biequivalence witnessing that biequivalence.

 To construct the reindexed displayed bicategory, we made several simplifying assumptions,
 namely that all displayed 2-cells with the same source and target are equal. Here we make
 further simplifying assumptions, namely that the type of displayed 2-cells from `f` to `g`
 is contractible. The reason is purely to simplify the involved computations.

 There are a couple of interesting aspects in the construction of the desired displayed
 biequivalence. To understand them, let us look at the construction. We denote the reindexed
 displayed bicategory by `reindex_disp_bicat F D`. Note that we have a displayed pseudofunctor
 from `reindex_disp_bicat F D` to `D`, which sends every `xx : (reindex_disp_bicat F D) x`
 (which is the same as `xx : D(F x)`) to `xx : D(F x)`. This pseudofunctor can be constructed
 without any problem. Now if `G` is the inverse of `F` given by the biequivalence, then we
 must also construct a displayed functor from `D` to `reindex_disp_bicat F D` over `G`. Given
 an object `xx : D x`, we must construct an object `(reindex_disp_bicat F D) (G x)`, which
 entails to construct an object `D(G(F x))`. This is where the first interesting aspect
 arises, because, in essence, we must assume that `D` is an isocleaving. Specifically,
 we have an adjoint equivalence between `x` and `G(F x)` (because `F` and `G` form a
 biequivalence), and we use this lifting operation to lift objects over `x` to objects over
 `G(F x)`. In this file, we construct this lifting operation by assuming that the involved
 bicategories are univalent.

 Another interesting aspect arises in the invertible 2-cells that are necessary to construct
 the unit of the displayed biequivalence. Writing `η` and `ε` for the unit and counit of
 the biequivalence between the base categories `B₁` and `B₂`, we need to construct an
 invertible 2-cell between `#F(ε x)` and `η(F x)` in order to construct the unit of the
 displayed biequivalence. This invertible 2-cell is an instance of the triangle coherences
 of a biequivalence. Since we use the incoherent notion of biequivalence in this file,
 we postulate the existence of the desired invertible 2-cell separately.

 Finally, we apply this construction to incoherent biequivalences. The main idea here is
 that every biequivalence can be refined into a coherent biequivalence, which allows us
 to apply this construction.

 Contents
 1. Invertible 2-cells that are necessary
 2. Lifts along adjoint equivalences
 3. The reindexing pseudofunctor
 4. The pseudotransformations
 5. The biequivalence
 6. The construction applied to incoherent biequivalences

                                                                                      *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Reindex.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudoNaturalAdjequiv.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.PseudoFunctors.BiequivalenceCoherent.

Local Open Scope cat.

Section ReindexBiequivalence.
  Context {B₁ B₂ : bicat}
          (univ_2_B₁ : is_univalent_2 B₁)
          (univ_2_B₂ : is_univalent_2 B₂)
          {F : psfunctor B₁ B₂}
          {G : psfunctor B₂ B₁}
          {e : is_biequivalence_unit_counit G F}
          (a : is_biequivalence_adjoints e)
          {D : disp_bicat B₂}
          (HD : local_iso_cleaving D)
          (Dcontr : disp_2cells_iscontr D)
          (θ : ∏ (x : B₁),
               invertible_2cell
                 (identity _)
                 (unit_of_is_biequivalence e (F x)
                  · #F (invcounit_of_is_biequivalence a x))).

  Let Dprop : disp_2cells_isaprop D
    := disp_2cells_isaprop_from_disp_2cells_iscontr _ Dcontr.

  Let Dgrpd : disp_locally_groupoid D
    := disp_2cells_isgroupoid_from_disp_2cells_iscontr _ Dcontr.

  Let η (x : B₂) : adjoint_equivalence (F(G x)) x
    := unit_of_is_biequivalence e x
       ,,
       pointwise_adjequiv
         (unit_of_is_biequivalence e)
         (is_biequivalence_adjoint_unit a) x.

  Let ε (x : B₁) : adjoint_equivalence (G(F x)) x
    := counit_of_is_biequivalence e x
       ,,
       pointwise_adjequiv
         (counit_of_is_biequivalence e)
         (is_biequivalence_adjoint_counit a) x.

  (** * 1. Invertible 2-cells that are necessary *)
  Definition counit_unit_invertible_2cell
             (x : B₁)
    : invertible_2cell (#F (ε x)) (η (F x)).
  Proof.
    refine (comp_of_invertible_2cell
              (linvunitor_invertible_2cell _)
              _).
    refine (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell _ (θ x))
              _).
    refine (comp_of_invertible_2cell
              (rassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell _ (psfunctor_comp F _ _))
              _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (psfunctor_inv2cell F (left_equivalence_counit_iso (ε x))))
              _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell (psfunctor_id F _)))
              _).
    exact (runitor_invertible_2cell _).
  Defined.

  Definition counit_unit_invertible_2cell_inv
             (x : B₁)
    : invertible_2cell
        (#F (left_adjoint_right_adjoint (ε x)))
        (left_adjoint_right_adjoint (η (F x))).
  Proof.
    assert (psfunctor_preserve_adj_equiv F _ _ (ε x) = η(F x))
      as X.
    {
      use path_internal_adjoint_equivalence.
      {
        exact (pr2 univ_2_B₂).
      }
      use isotoid_2_1.
      {
        exact (pr2 univ_2_B₂).
      }
      exact (counit_unit_invertible_2cell x).
    }
    induction X.
    apply id2_invertible_2cell.
  Qed.

  Definition reindex_disp_psfunctor_inv_inv2cell
             {x y : B₂}
             (f : x --> y)
    : invertible_2cell
        (#F(#G f))
        (η x · f · left_adjoint_right_adjoint (η y)).
  Proof.
    refine (comp_of_invertible_2cell
              (rinvunitor_invertible_2cell _)
              _).
    refine (comp_of_invertible_2cell
              _
              (inv_of_invertible_2cell
                 (rwhisker_of_invertible_2cell
                    _
                    (psnaturality_of (unit_of_is_biequivalence e) f)))).
    refine (comp_of_invertible_2cell
              _
              (lassociator_invertible_2cell _ _ _)).
    refine (lwhisker_of_invertible_2cell _ _).
    exact (left_equivalence_unit_iso (η y)).
  Defined.

  Let reindex_grpd : disp_locally_groupoid (reindex_disp_bicat F D HD Dprop).
  Proof.
    use disp_locally_groupoid_reindex.
    - exact Dgrpd.
    - exact (pr2 univ_2_B₁).
  Defined.

  (** * 2. Lifts along adjoint equivalences *)
  Definition lift_adjequiv_ob_disp_adjequiv
             {x y : B₂}
             (f : adjoint_equivalence x y)
             (yy : D y)
    : ∑ (xx : D x), disp_adjoint_equivalence f xx yy.
  Proof.
    revert x y f yy.
    use J_2_0.
    {
      exact (pr1 univ_2_B₂).
    }
    intros x xx.
    refine (xx ,, _).
    apply disp_identity_adjoint_equivalence.
  Defined.

  Definition lift_adjequiv_ob
             {x y : B₂}
             (f : adjoint_equivalence x y)
             (yy : D y)
    : D x
    := pr1 (lift_adjequiv_ob_disp_adjequiv f yy).

  Definition lift_adjequiv_disp_adjequiv
             {x y : B₂}
             (f : adjoint_equivalence x y)
             (yy : D y)
    : disp_adjoint_equivalence f (lift_adjequiv_ob f yy) yy
    := pr2 (lift_adjequiv_ob_disp_adjequiv f yy).

  (** * 3. The reindexing pseudofunctor *)
  Definition reindex_disp_psfunctor
    : disp_psfunctor (reindex_disp_bicat F D HD Dprop) D F.
  Proof.
    use make_disp_psfunctor_contr.
    - exact Dcontr.
    - exact (λ x xx, xx).
    - exact (λ x y f xx yy ff, ff).
  Defined.

  Definition reindex_disp_psfunctor_inv
    : disp_psfunctor D (reindex_disp_bicat F D HD Dprop) G.
  Proof.
    use make_disp_psfunctor_contr.
    - intro ; intros ; apply Dcontr.
    - exact (λ (x : B₂) (xx : D x), lift_adjequiv_ob (η x) xx).
    - exact (λ (x y : B₂)
               (f : x --> y)
               (xx : D x) (yy : D y)
               (ff : xx -->[ f ] yy),
             local_iso_cleaving_1cell
               HD
               (lift_adjequiv_disp_adjequiv (η x) xx
                ;; ff
                ;; pr112 (lift_adjequiv_disp_adjequiv (η y) yy))%mor_disp
               (reindex_disp_psfunctor_inv_inv2cell _)).
  Defined.

  (** * 4. The pseudotransformations *)
  Definition reindex_disp_psfunctor_unit
    : disp_pstrans
        (disp_pseudo_comp
           G F
           D (reindex_disp_bicat F D HD Dprop) D
           reindex_disp_psfunctor_inv
           reindex_disp_psfunctor)
        (disp_pseudo_id D)
        (unit_of_is_biequivalence e).
  Proof.
    use make_disp_pstrans_contr.
    - intro ; intros ; apply Dcontr.
    - exact (λ (x : B₂) (xx : D x), lift_adjequiv_disp_adjequiv (η x) xx).
  Qed.

  Proposition reindex_disp_psfunctor_unit_adjequiv
              (x : B₂)
              (xx : D x)
    : disp_left_adjoint_equivalence
        (pointwise_adjequiv
           (unit_of_is_biequivalence e)
           (is_biequivalence_adjoint_unit a) x)
        (reindex_disp_psfunctor_unit x xx).
  Proof.
    use make_disp_adjequiv_contr.
    - apply Dcontr.
    - exact (pr112 (lift_adjequiv_disp_adjequiv (η x) xx)).
  Qed.

  Definition reindex_disp_psfunctor_counit
    : disp_pstrans
        (disp_pseudo_id (reindex_disp_bicat F D HD Dprop))
        (disp_pseudo_comp
           F G
           (reindex_disp_bicat F D HD Dprop) D (reindex_disp_bicat F D HD Dprop)
           reindex_disp_psfunctor reindex_disp_psfunctor_inv)
        (invcounit_of_is_biequivalence a).
  Proof.
    use make_disp_pstrans_contr.
    - intro ; intros ; apply Dcontr.
    - refine (λ (x : B₁) (xx : D(F x)), _).
      refine (local_iso_cleaving_1cell
                HD
                (pr112 (lift_adjequiv_disp_adjequiv (η(F x)) xx))
                _).
      apply counit_unit_invertible_2cell_inv.
  Defined.

  Proposition reindex_disp_psfunctor_counit_adjequiv
              (x : B₁)
              (xx : D(F x))
    : disp_left_adjoint_equivalence
        (pointwise_adjequiv
           (invcounit_of_is_biequivalence a)
           (inv_left_adjoint_equivalence (is_biequivalence_adjoint_counit a)) x)
        (reindex_disp_psfunctor_counit x xx).
  Proof.
    use make_disp_adjequiv_contr.
    - intro ; intros ; apply Dcontr.
    - exact (local_iso_cleaving_1cell
               HD
               (pr1 (lift_adjequiv_disp_adjequiv (η(F x)) xx))
               (counit_unit_invertible_2cell x)).
  Qed.

  (** * 5. The biequivalence *)
  Definition reindex_is_disp_biequivalence_unit_counit
    : is_disp_biequivalence_unit_counit
        _ _
        e
        reindex_disp_psfunctor_inv
        reindex_disp_psfunctor.
  Proof.
    use make_disp_biequiv_unit_counit_pointwise_adjequiv_alt.
    - exact univ_2_B₁.
    - exact a.
    - intro ; intros ; apply Dprop.
    - exact reindex_grpd.
    - exact reindex_disp_psfunctor_unit.
    - exact reindex_disp_psfunctor_counit.
    - exact reindex_disp_psfunctor_counit_adjequiv.
  Defined.

  Definition reindex_disp_is_biequivalence
    : disp_is_biequivalence_data
        D (reindex_disp_bicat F D HD Dprop)
        a
        reindex_is_disp_biequivalence_unit_counit.
  Proof.
    use (make_disp_biequiv_pointwise_adjequiv_alt _ _).
    - exact univ_2_B₂.
    - apply Dprop.
    - exact Dgrpd.
    - exact reindex_disp_psfunctor_unit_adjequiv.
  Defined.
End ReindexBiequivalence.

Arguments reindex_disp_psfunctor {B₁ B₂} F {D} HD Dcontr.

Definition reindex_disp_psfunctor_univ
           {B₁ B₂ : bicat}
           (univ_2_B₂ : is_univalent_2 B₂)
           (F : psfunctor B₁ B₂)
           {D : disp_bicat B₂}
           (HD := univalent_2_1_to_local_iso_cleaving (pr2 univ_2_B₂) D)
           (Dcontr : disp_2cells_iscontr D)
  : disp_psfunctor
      (reindex_disp_bicat
         F D HD
         (disp_2cells_isaprop_from_disp_2cells_iscontr D Dcontr))
      D
      F
  := reindex_disp_psfunctor F HD Dcontr.

Definition reindex_disp_psfunctor_inv_univ
           {B₁ B₂ : bicat}
           (univ_2_B₂ : is_univalent_2 B₂)
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit G F}
           (a : is_biequivalence_adjoints e)
           {D : disp_bicat B₂}
           (HD := univalent_2_1_to_local_iso_cleaving (pr2 univ_2_B₂) D)
           (Dcontr : disp_2cells_iscontr D)
  : disp_psfunctor
      D
      (reindex_disp_bicat
         F D HD
         (disp_2cells_isaprop_from_disp_2cells_iscontr D Dcontr))
      G
  := reindex_disp_psfunctor_inv univ_2_B₂ a HD Dcontr.

Definition reindex_is_disp_biequivalence_unit_counit_univ
           {B₁ B₂ : bicat}
           (univ_2_B₁ : is_univalent_2 B₁)
           (univ_2_B₂ : is_univalent_2 B₂)
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit G F}
           (a : is_biequivalence_adjoints e)
           {D : disp_bicat B₂}
           (HD := univalent_2_1_to_local_iso_cleaving (pr2 univ_2_B₂) D)
           (Dcontr : disp_2cells_iscontr D)
           (θ : ∏ (x : B₁),
                invertible_2cell
                  (identity _)
                  (unit_of_is_biequivalence e (F x)
                   · #F (invcounit_of_is_biequivalence a x)))
  : is_disp_biequivalence_unit_counit
      _ _
      e
      (reindex_disp_psfunctor_inv univ_2_B₂ a HD Dcontr)
      (reindex_disp_psfunctor_univ univ_2_B₂ F Dcontr).
Proof.
  use reindex_is_disp_biequivalence_unit_counit.
  - exact univ_2_B₁.
  - exact θ.
Defined.

Definition reindex_disp_is_biequivalence_univ
           {B₁ B₂ : bicat}
           (univ_2_B₁ : is_univalent_2 B₁)
           (univ_2_B₂ : is_univalent_2 B₂)
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit G F}
           (a : is_biequivalence_adjoints e)
           {D : disp_bicat B₂}
           (HD := univalent_2_1_to_local_iso_cleaving (pr2 univ_2_B₂) D)
           (Dcontr : disp_2cells_iscontr D)
           (θ : ∏ (x : B₁),
                invertible_2cell
                  (identity _)
                  (unit_of_is_biequivalence e (F x)
                   · #F (invcounit_of_is_biequivalence a x)))
  : disp_is_biequivalence_data
      D (reindex_disp_bicat F D HD _)
      a
      (reindex_is_disp_biequivalence_unit_counit_univ
         univ_2_B₁ univ_2_B₂
         a
         Dcontr
         θ).
Proof.
  apply reindex_disp_is_biequivalence.
Defined.

(** * *)
Definition reindex_is_disp_biequivalence_unit_counit_univ_coh
           {B₁ B₂ : bicat}
           (univ_2_B₁ : is_univalent_2 B₁)
           (univ_2_B₂ : is_univalent_2 B₂)
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit G F}
           (a : is_biequivalence_adjoints e)
           {D : disp_bicat B₂}
           (HD := univalent_2_1_to_local_iso_cleaving (pr2 univ_2_B₂) D)
           (Dcontr : disp_2cells_iscontr D)
  : is_disp_biequivalence_unit_counit
      _ _
      (coherent_is_biequivalence_adjoints univ_2_B₁ a)
      (reindex_disp_psfunctor_inv univ_2_B₂ a HD Dcontr)
      (reindex_disp_psfunctor_univ univ_2_B₂ F Dcontr).
Proof.
  refine (reindex_is_disp_biequivalence_unit_counit
            univ_2_B₁ univ_2_B₂
            (coherent_is_biequivalence_adjoints univ_2_B₁ a)
            HD
            Dcontr
            _).
  apply coherent_is_biequivalence_adjoints_triangle_2_alt.
Defined.

Definition reindex_disp_is_biequivalence_univ_coh
           {B₁ B₂ : bicat}
           (univ_2_B₁ : is_univalent_2 B₁)
           (univ_2_B₂ : is_univalent_2 B₂)
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit G F}
           (a : is_biequivalence_adjoints e)
           {D : disp_bicat B₂}
           (HD := univalent_2_1_to_local_iso_cleaving (pr2 univ_2_B₂) D)
           (Dcontr : disp_2cells_iscontr D)
  : disp_is_biequivalence_data
      D (reindex_disp_bicat F D HD _)
      (coherent_is_biequivalence_adjoints univ_2_B₁ a)
      (reindex_is_disp_biequivalence_unit_counit_univ_coh
         univ_2_B₁ univ_2_B₂
         a
         Dcontr).
Proof.
  exact (reindex_disp_is_biequivalence_univ
           univ_2_B₁ univ_2_B₂
           (coherent_is_biequivalence_adjoints univ_2_B₁ a)
           Dcontr
           _).
Defined.
