(*******************************************************************************************

 Preservation of isomorphic functors

 In this file, we show that two functors that are equivalent in the arrow bicategory, share
 the same preservation properties regarding finite limits. More specifically, we show two
 statements.

 First, we show that whenever we have a natural isomorphism from `F` to `G`, then `G`
 preserves terminal objects/binary products/equalizers whenever `F` does. Using this, we show
 that whenever a functor `G : D₁ ⟶ D₂` is equivalent to some functor `F : C₁ ⟶ C₂` in the
 arrow bicategory, then `G` preserves terminal objects/binary products/equalizers if `F` does.
 An equivalence between `F` and `G` in the arrow bicategory amounts to adjoint equivalences
 `C₁ ≃ D₁` and `C₂ ≃ D₂` such that the resulting square commutes.

 We also compare preservation of pullbacks and preservation of products and equalizers.

 Contents
 1. Preservation and natural isomorphisms
 2. Preservation and equivalences in the arrow bicategory
 3. Preservation of binary products and equalizers from pullbacks
 4. Preservation of pullbacks via binary products and equalizers

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.PullbackConstructions.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.EquivalencePreservation.
Require Import UniMath.CategoryTheory.Limits.LimitIso.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** * 1. Preservation and natural isomorphisms *)
Section PreservationNatIso.
  Context {C D : category}
          {F G : C ⟶ D}
          (τ : nat_z_iso F G).

  Definition preserves_terminal_nat_z_iso_f
             (HF : preserves_terminal F)
    : preserves_terminal G.
  Proof.
    intros x Hx.
    use (iso_to_Terminal (make_Terminal _ (HF _ Hx))).
    cbn.
    exact (nat_z_iso_pointwise_z_iso τ x).
  Defined.

  Definition preserves_binproduct_nat_z_iso_f
             (HF : preserves_binproduct F)
    : preserves_binproduct G.
  Proof.
    intros x y p π₁ π₂ H.
    pose (prod := make_BinProduct _ _ _ _ _ _ (HF _ _ _ _ _ H)).
    use (isBinProduct_z_iso
           (isBinProduct_BinProduct _ (BinProduct_z_iso_lr prod _ _))).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ x)).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ y)).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ p)).
    - abstract
        (cbn ;
         rewrite nat_trans_ax ;
         refine (!(id_left _) @ !_) ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply z_iso_after_z_iso_inv).
    - abstract
        (cbn ;
         rewrite nat_trans_ax ;
         refine (!(id_left _) @ !_) ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply z_iso_after_z_iso_inv).
  Defined.

  Definition preserves_equalizer_nat_z_iso_f
             (HF : preserves_equalizer F)
    : preserves_equalizer G.
  Proof.
    intros x y e f g h p Fp H.
    assert (q : # F h · # F f = # F h · # F g).
    {
      abstract
        (rewrite <- !functor_comp ;
         exact (maponpaths #F p)).
    }
    pose (eq := make_Equalizer _ _ _ q (HF _ _ _ _ _ _ _ _ H)).
    use (isEqualizer_z_iso
           (isEqualizer_Equalizer (Equalizer_z_iso_lr eq _ _ _ _))).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ x)).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ y)).
    - abstract
        (cbn ;
         use z_iso_inv_on_left ;
         rewrite !assoc' ;
         cbn ;
         refine (!_) ;
         use z_iso_inv_on_right ;
         apply nat_trans_ax).
    - abstract
        (cbn ;
         use z_iso_inv_on_left ;
         rewrite !assoc' ;
         cbn ;
         refine (!_) ;
         use z_iso_inv_on_right ;
         apply nat_trans_ax).
    - exact (z_iso_inv (nat_z_iso_pointwise_z_iso τ e)).
    - abstract
        (cbn ;
         rewrite nat_trans_ax ;
         refine (!(id_left _) @ !_) ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply z_iso_after_z_iso_inv).
  Defined.

  Definition preserves_initial_nat_z_iso_f
             (HF : preserves_initial F)
    : preserves_initial G.
  Proof.
    intros x Hx.
    use (iso_to_Initial (make_Initial _ (HF _ Hx))).
    cbn.
    exact (nat_z_iso_pointwise_z_iso τ x).
  Defined.

  Definition preserves_bincoproduct_nat_z_iso_f
             (HF : preserves_bincoproduct F)
    : preserves_bincoproduct G.
  Proof.
    intros x y p π₁ π₂ H.
    pose (coprod := make_BinCoproduct _ _ _ _ _ _ (HF _ _ _ _ _ H)).
    use (isBinCoproduct_z_iso
           (isBinCoproduct_BinCoproduct _ (BinCoproduct_z_iso_lr coprod _ _))).
    - exact (nat_z_iso_pointwise_z_iso τ x).
    - exact (nat_z_iso_pointwise_z_iso τ y).
    - exact (nat_z_iso_pointwise_z_iso τ p).
    - abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite nat_trans_ax ;
         refine (!(id_left _) @ !_) ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply z_iso_after_z_iso_inv).
    - abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite nat_trans_ax ;
         refine (!(id_left _) @ !_) ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply z_iso_after_z_iso_inv).
  Defined.
End PreservationNatIso.

Definition preserves_terminal_nat_z_iso_b
           {C D : category}
           {F G : C ⟶ D}
           (τ : nat_z_iso F G)
           (HF : preserves_terminal G)
  : preserves_terminal F.
Proof.
  exact (preserves_terminal_nat_z_iso_f (nat_z_iso_inv τ) HF).
Defined.

Definition preserves_binproduct_nat_z_iso_b
           {C D : category}
           {F G : C ⟶ D}
           (τ : nat_z_iso F G)
           (HF : preserves_binproduct G)
  : preserves_binproduct F.
Proof.
  exact (preserves_binproduct_nat_z_iso_f (nat_z_iso_inv τ) HF).
Defined.

Definition preserves_equalizer_nat_z_iso_b
           {C D : category}
           {F G : C ⟶ D}
           (τ : nat_z_iso F G)
           (HF : preserves_equalizer G)
  : preserves_equalizer F.
Proof.
  exact (preserves_equalizer_nat_z_iso_f (nat_z_iso_inv τ) HF).
Defined.

Definition preserves_initial_nat_z_iso_b
           {C D : category}
           {F G : C ⟶ D}
           (τ : nat_z_iso F G)
           (HF : preserves_initial G)
  : preserves_initial F.
Proof.
  exact (preserves_initial_nat_z_iso_f (nat_z_iso_inv τ) HF).
Defined.

Definition preserves_bincoproduct_nat_z_iso_b
           {C D : category}
           {F G : C ⟶ D}
           (τ : nat_z_iso F G)
           (HF : preserves_bincoproduct G)
  : preserves_bincoproduct F.
Proof.
  exact (preserves_bincoproduct_nat_z_iso_f (nat_z_iso_inv τ) HF).
Defined.

(** *  2. Preservation and equivalences in the arrow bicategory *)
Section EquivalencePreservation.
  Context {C₁ C₂ D₁ D₂ : category}
          (EC : C₁ ⟶ C₂)
          (ED : D₁ ⟶ D₂)
          (HEC : adj_equivalence_of_cats EC)
          (HED : adj_equivalence_of_cats ED)
          (F : C₁ ⟶ D₁)
          (G : C₂ ⟶ D₂)
          (τ : nat_z_iso (F ∙ ED) (EC ∙ G)).

  Let R : C₂ ⟶ C₁ := right_adjoint HEC.

  Let θ : nat_z_iso (R ∙ F ∙ ED) G
    := nat_z_iso_comp
         (pre_whisker_nat_z_iso R τ)
         (post_whisker_nat_z_iso (counit_nat_z_iso_from_adj_equivalence_of_cats HEC) G).

  Definition preserves_terminal_equivalence_f
             (HF : preserves_terminal F)
    : preserves_terminal G.
  Proof.
    use (preserves_terminal_nat_z_iso_f θ).
    use composition_preserves_terminal.
    - use composition_preserves_terminal.
      + exact (right_adjoint_preserves_terminal _ HEC).
      + exact HF.
    - exact (right_adjoint_preserves_terminal _ (adj_equivalence_of_cats_inv HED)).
  Defined.

  Definition preserves_binproduct_equivalence_f
             (HF : preserves_binproduct F)
    : preserves_binproduct G.
  Proof.
    use (preserves_binproduct_nat_z_iso_f θ).
    use composition_preserves_binproduct.
    - use composition_preserves_binproduct.
      + exact (right_adjoint_preserves_binproduct _ HEC).
      + exact HF.
    - exact (right_adjoint_preserves_binproduct _ (adj_equivalence_of_cats_inv HED)).
  Defined.

  Definition preserves_equalizer_equivalence_f
             (HF : preserves_equalizer F)
    : preserves_equalizer G.
  Proof.
    use (preserves_equalizer_nat_z_iso_f θ).
    use composition_preserves_equalizer.
    - use composition_preserves_equalizer.
      + exact (right_adjoint_preserves_equalizer _ HEC).
      + exact HF.
    - exact (right_adjoint_preserves_equalizer _ (adj_equivalence_of_cats_inv HED)).
  Defined.

  Definition preserves_initial_equivalence_f
             (HF : preserves_initial F)
    : preserves_initial G.
  Proof.
    use (preserves_initial_nat_z_iso_f θ).
    use composition_preserves_initial.
    - use composition_preserves_initial.
      + exact (left_adjoint_preserves_initial _ (adj_equivalence_of_cats_inv HEC)).
      + exact HF.
    - exact (left_adjoint_preserves_initial _ HED).
  Defined.

  Definition preserves_bincoproduct_equivalence_f
             (HF : preserves_bincoproduct F)
    : preserves_bincoproduct G.
  Proof.
    use (preserves_bincoproduct_nat_z_iso_f θ).
    use composition_preserves_bincoproduct.
    - use composition_preserves_bincoproduct.
      + exact (left_adjoint_preserves_bincoproduct _ (adj_equivalence_of_cats_inv HEC)).
      + exact HF.
    - exact (left_adjoint_preserves_bincoproduct _ HED).
  Defined.
End EquivalencePreservation.

Section EquivalencePreservation.
  Context {C₁ C₂ D₁ D₂ : category}
          (EC : C₁ ⟶ C₂)
          (ED : D₁ ⟶ D₂)
          (HEC : adj_equivalence_of_cats EC)
          (HED : adj_equivalence_of_cats ED)
          (F : C₁ ⟶ D₁)
          (G : C₂ ⟶ D₂)
          (τ : nat_z_iso (F ∙ ED) (EC ∙ G)).

  Let RC : C₂ ⟶ C₁ := right_adjoint HEC.
  Let RD : D₂ ⟶ D₁ := right_adjoint HED.

  Let θ : nat_z_iso (G ∙ RD) (RC ∙ F)
    := nat_z_iso_comp
         (post_whisker_nat_z_iso
            (nat_z_iso_inv
               (counit_nat_z_iso_from_adj_equivalence_of_cats HEC))
            (G ∙ RD))
         (nat_z_iso_comp
            (post_whisker_nat_z_iso
               (pre_whisker_nat_z_iso
                  RC
                  (nat_z_iso_inv τ))
               RD)
            (pre_whisker_nat_z_iso
               (RC ∙ F)
               (nat_z_iso_inv (unit_nat_z_iso_from_adj_equivalence_of_cats HED)))).

  Definition preserves_terminal_equivalence_b
             (HG : preserves_terminal G)
    : preserves_terminal F
    := preserves_terminal_equivalence_f
         _ _
         (adj_equivalence_of_cats_inv HEC)
         (adj_equivalence_of_cats_inv HED)
         _ _
         θ
         HG.

  Definition preserves_binproduct_equivalence_b
             (HG : preserves_binproduct G)
    : preserves_binproduct F
    := preserves_binproduct_equivalence_f
         _ _
         (adj_equivalence_of_cats_inv HEC)
         (adj_equivalence_of_cats_inv HED)
         _ _
         θ
         HG.

  Definition preserves_equalizer_equivalence_b
             (HG : preserves_equalizer G)
    : preserves_equalizer F
    := preserves_equalizer_equivalence_f
         _ _
         (adj_equivalence_of_cats_inv HEC)
         (adj_equivalence_of_cats_inv HED)
         _ _
         θ
         HG.

  Definition preserves_initial_equivalence_b
             (HG : preserves_initial G)
    : preserves_initial F
    := preserves_initial_equivalence_f
         _ _
         (adj_equivalence_of_cats_inv HEC)
         (adj_equivalence_of_cats_inv HED)
         _ _
         θ
         HG.

  Definition preserves_bincoproduct_equivalence_b
             (HG : preserves_bincoproduct G)
    : preserves_bincoproduct F
    := preserves_bincoproduct_equivalence_f
         _ _
         (adj_equivalence_of_cats_inv HEC)
         (adj_equivalence_of_cats_inv HED)
         _ _
         θ
         HG.
End EquivalencePreservation.

(** * 3. Preservation of binary products and equalizers from pullbacks *)
Section BinProductEqualizerPreservation.
  Context {C D : category}
          (F : C ⟶ D)
          (TC : Terminal C)
          (PBC : Pullbacks C)
          (HF₁ : preserves_pullback F)
          (HF₂ : preserves_terminal F).

  Let prodC : BinProducts C := BinProductsFromPullbacks PBC TC.

  Section PreservesProd.
    Context (x y : C).

    Let p : BinProduct C x y := prodC x y.
    Let π₁ : p --> x := BinProductPr1 _ p.
    Let π₂ : p --> y := BinProductPr2 _ p.
    Let H : isPullback
              (PullbackSqrCommutes
                 (PBC TC x y (TerminalArrow TC x) (TerminalArrow TC y)))
      := isPullback_Pullback (PBC TC x y (TerminalArrow _ _) (TerminalArrow _ _)).

    Section UMP.
      Context {w : D}
              (f : w --> F x)
              (g : w --> F y).

      Let FT : Terminal D
        := make_Terminal _ (HF₂ TC (pr2 TC)).

      Local Lemma pullback_sqr_comm
        : # F π₁ · # F (TerminalArrow TC x)
          =
          # F π₂ · # F (TerminalArrow TC y).
      Proof.
        rewrite <- !functor_comp.
        apply maponpaths.
        apply TerminalArrowEq.
      Qed.

      Let P : Pullback (# F (TerminalArrow TC x)) (# F (TerminalArrow TC y))
        := make_Pullback _ (HF₁ _ _ _ _ _ _ _ _ _ pullback_sqr_comm H).

      Proposition preserves_binproduct_from_pullback_terminal_unique
        : isaprop (∑ fg, fg · # F π₁ = f × fg · # F π₂ = g).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
        - exact (pr12 φ₁ @ !(pr12 φ₂)).
        - exact (pr22 φ₁ @ !(pr22 φ₂)).
      Qed.

      Definition preserves_binproduct_from_pullback_terminal_map
        : w --> F p.
      Proof.
        use (PullbackArrow P).
        - exact f.
        - exact g.
        - abstract
            (use (TerminalArrowEq (T := FT))).
      Defined.

      Proposition preserves_binproduct_from_pullback_terminal_pr1
        : preserves_binproduct_from_pullback_terminal_map · # F π₁ = f.
      Proof.
        exact (PullbackArrow_PullbackPr1 P _ _ _ _).
      Qed.

      Proposition preserves_binproduct_from_pullback_terminal_pr2
        : preserves_binproduct_from_pullback_terminal_map · # F π₂ = g.
      Proof.
        exact (PullbackArrow_PullbackPr2 P _ _ _ _).
      Qed.
    End UMP.

    Definition preserves_binproduct_from_pullback_terminal_is_prod
      : isBinProduct D (F x) (F y) (F p) (# F π₁) (# F π₂).
    Proof.
      intros w f g.
      use iscontraprop1.
      - exact (preserves_binproduct_from_pullback_terminal_unique f g).
      - simple refine (_ ,, _ ,, _).
        + exact (preserves_binproduct_from_pullback_terminal_map f g).
        + exact (preserves_binproduct_from_pullback_terminal_pr1 f g).
        + exact (preserves_binproduct_from_pullback_terminal_pr2 f g).
    Defined.
  End PreservesProd.

  Definition preserves_binproduct_from_pullback_terminal
    : preserves_binproduct F.
  Proof.
    use (preserves_binproduct_if_preserves_chosen prodC).
    intros x y.
    exact (preserves_binproduct_from_pullback_terminal_is_prod x y).
  Defined.

  Let eqC : Equalizers C := equalizers_from_pullbacks_prods PBC prodC.

  Section PreservesEq.
    Context {x y : C}
            (f g : x --> y)
            (p : # F (EqualizerArrow (eqC x y f g)) · # F f
                 =
                 # F (EqualizerArrow (eqC x y f g)) · # F g).

    Let yy : BinProduct C y y := prodC y y.
    Let Δ : y --> prodC y y := diagonalMap' prodC y.
    Let fg : x --> prodC y y := BinProductArrow C yy f g.
    Let P : Pullback Δ fg := PBC (prodC y y) y x Δ fg.
    Let H : isPullback (PullbackSqrCommutes P)
      := isPullback_Pullback P.
    Let e : P --> x := PullbackPr2 P.

    Section UMP.
      Context {w : D}
              (h : w --> F x)
              (q : h · # F f = h · # F g).

      Local Lemma pullback_sqr_comm_eq
        : # F (PullbackPr1 P) · # F Δ = # F (PullbackPr2 P) · # F fg.
      Proof.
        rewrite <- !functor_comp.
        apply maponpaths.
        apply PullbackSqrCommutes.
      Qed.

      Let r : # F (PullbackPr1 P) · # F Δ = # F (PullbackPr2 P) · # F fg
        := pullback_sqr_comm_eq.

      Let Fyy : BinProduct D (F y) (F y)
        := make_BinProduct
             _ _ _ _ _ _
             (preserves_binproduct_from_pullback_terminal
                _ _ _ _ _
                (isBinProduct_BinProduct _ yy)).

      Let FH : isPullback r := HF₁ _ _ _ _ _ _ _ _ _ r H.
      Let FP : Pullback (#F Δ) (#F fg) := make_Pullback _ FH.

      Local Lemma preserves_equalizer_from_pullback_terminal_map_eq
        : h · # F g · # F Δ = h · # F fg.
      Proof.
        use (BinProductArrowsEq _ _ _ Fyy) ; cbn.
        - rewrite !assoc'.
          rewrite <- !functor_comp.
          rewrite !PullbackArrow_PullbackPr1.
          rewrite id_right.
          rewrite q.
          apply idpath.
        - rewrite !assoc'.
          rewrite <- !functor_comp.
          rewrite !PullbackArrow_PullbackPr2.
          rewrite id_right.
          apply idpath.
      Qed.

      Proposition preserves_equalizer_from_pullback_terminal_map_unique
        : isaprop (∑ φ, φ · # F (EqualizerArrow (eqC x y f g)) = h).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback FP)).
        - cbn.
          enough (pr1 φ₁ · # F (PullbackPr1 P) · #F Δ
                  =
                  pr1 φ₂ · # F (PullbackPr1 P) · #F Δ)
            as help_mono.
          {
            pose (maponpaths (λ z, z · BinProductPr1 D Fyy) help_mono) as lem.
            cbn in lem.
            rewrite !assoc' in lem.
            rewrite <- !functor_comp in lem.
            rewrite !PullbackArrow_PullbackPr1 in lem.
            rewrite !id_right in lem.
            exact lem.
          }
          rewrite !assoc'.
          rewrite <- !functor_comp.
          rewrite (PullbackSqrCommutes P).
          rewrite !functor_comp.
          rewrite !assoc.
          apply maponpaths_2.
          exact (pr2 φ₁ @ !(pr2 φ₂)).
        - exact (pr2 φ₁ @ !(pr2 φ₂)).
      Qed.

      Definition preserves_equalizer_from_pullback_terminal_map
        : w --> F (eqC x y f g).
      Proof.
        use (PullbackArrow FP).
        - exact (h · #F g).
        - exact h.
        - exact preserves_equalizer_from_pullback_terminal_map_eq.
      Defined.

      Proposition preserves_equalizer_from_pullback_terminal_comm
        : preserves_equalizer_from_pullback_terminal_map · # F (EqualizerArrow (eqC x y f g))
          =
          h.
      Proof.
        apply (PullbackArrow_PullbackPr2 FP).
      Qed.
    End UMP.

    Definition preserves_equalizer_from_pullback_terminal_is_equalizer
      : isEqualizer (# F f) (# F g) (# F (EqualizerArrow (eqC x y f g))) p.
    Proof.
      intros w h q.
      use iscontraprop1.
      - exact (preserves_equalizer_from_pullback_terminal_map_unique h).
      - simple refine (_ ,, _).
        + exact (preserves_equalizer_from_pullback_terminal_map h q).
        + exact (preserves_equalizer_from_pullback_terminal_comm h q).
    Defined.
  End PreservesEq.

  Definition preserves_equalizer_from_pullback_terminal
    : preserves_equalizer F.
  Proof.
    use (preserves_equalizer_if_preserves_chosen eqC).
    intros x y f g p.
    exact (preserves_equalizer_from_pullback_terminal_is_equalizer f g p).
  Defined.
End BinProductEqualizerPreservation.

(** * 4. Preservation of pullbacks via binary products and equalizers *)
Section PullbackPreservation.
  Context {C D : category}
          (PC : BinProducts C)
          (EC : Equalizers C)
          (F : C ⟶ D)
          (HF₁ : preserves_binproduct F)
          (HF₂ : preserves_equalizer F).

  Let PBC : Pullbacks C := Pullbacks_from_Equalizers_BinProducts C PC EC.

  Section PreservesPB.
    Context {x y z : C}
            (f : x --> z)
            (g : y --> z).

    Let P : Pullback f g := PBC z x y f g.

    Context (q : # F (PullbackPr1 (PBC z x y f g)) · # F f
                 =
                 # F (PullbackPr2 (PBC z x y f g)) · # F g).

    Let xy : BinProduct C x y := PC x y.
    Let π₁ : xy --> x := BinProductPr1 _ xy.
    Let π₂ : xy --> y := BinProductPr2 _ xy.

    Let fp : xy --> z := π₁ · f.
    Let gp : xy --> z := π₂ · g.

    Let E : Equalizer fp gp := EC _ _ fp gp.

    Section UMP.
      Context {w : D}
              (h : w --> F x)
              (k : w --> F y)
              (r : h · # F f = k · # F g).

      Local Lemma equalizer_eq_help
        : # F (EqualizerArrow E) · # F fp = # F (EqualizerArrow E) · # F gp.
      Proof.
        rewrite <- !functor_comp.
        apply maponpaths.
        apply EqualizerEqAr.
      Qed.

      Let path : # F (EqualizerArrow E) · # F fp = # F (EqualizerArrow E) · # F gp
        := equalizer_eq_help.

      Let FE : Equalizer (#F fp) (#F gp)
        := make_Equalizer _ _ _ _ (HF₂ _ _ _ _ _ _ _ path (isEqualizer_Equalizer E)).

      Let Fxy : BinProduct _ (F x) (F y)
        := make_BinProduct _ _ _ _ _ _ (HF₁ _ _ _ _ _ (isBinProduct_BinProduct _ xy)).

      Proposition preserves_pullback_from_binproduct_equalizer_map_eq
        : BinProductArrow D Fxy h k · #F fp
          =
          BinProductArrow D Fxy h k · #F gp.
      Proof.
        unfold fp, gp.
        rewrite !functor_comp.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (BinProductPr1Commutes _ _ _ Fxy).
        }
        refine (r @ _).
        refine (!_).
        apply maponpaths_2.
        apply (BinProductPr2Commutes _ _ _ Fxy).
      Qed.

      Proposition preserves_pullback_from_binproduct_equalizer_unique
        : isaprop
            (∑ hk,
             (hk · # F (PullbackPr1 (PBC z x y f g)) = h)
             ×
             (hk · # F (PullbackPr2 (PBC z x y f g)) = k)).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (EqualizerInsEq FE).
        use (BinProductArrowsEq _ _ _ Fxy) ; cbn.
        - rewrite !assoc'.
          rewrite <- !functor_comp.
          exact (pr12 φ₁ @ !(pr12 φ₂)).
        - rewrite !assoc'.
          rewrite <- !functor_comp.
          exact (pr22 φ₁ @ !(pr22 φ₂)).
      Qed.

      Definition preserves_pullback_from_binproduct_equalizer_map
        : w --> F P.
      Proof.
        use (EqualizerIn FE).
        - exact (BinProductArrow _ Fxy h k).
        - exact preserves_pullback_from_binproduct_equalizer_map_eq.
      Defined.

      Proposition preserves_pullback_from_binproduct_equalizer_pr1
        : preserves_pullback_from_binproduct_equalizer_map
          · #F (PullbackPr1 (PBC z x y f g))
          =
          h.
      Proof.
        cbn.
        rewrite functor_comp.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (EqualizerCommutes FE).
        }
        apply (BinProductPr1Commutes _ _ _ Fxy).
      Qed.

      Proposition preserves_pullback_from_binproduct_equalizer_pr2
        : preserves_pullback_from_binproduct_equalizer_map
          · #F (PullbackPr2 (PBC z x y f g))
          =
          k.
      Proof.
        cbn.
        rewrite functor_comp.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (EqualizerCommutes FE).
        }
        apply (BinProductPr2Commutes _ _ _ Fxy).
      Qed.
    End UMP.

    Definition preserves_pullback_from_binproduct_equalizer_is_pb
      : isPullback q.
    Proof.
      intros w h k r.
      use iscontraprop1.
      - exact (preserves_pullback_from_binproduct_equalizer_unique h k).
      - simple refine (_ ,, _ ,, _).
        + exact (preserves_pullback_from_binproduct_equalizer_map h k r).
        + exact (preserves_pullback_from_binproduct_equalizer_pr1 h k r).
        + exact (preserves_pullback_from_binproduct_equalizer_pr2 h k r).
    Defined.
  End PreservesPB.

  Definition preserves_pullback_from_binproduct_equalizer
    : preserves_pullback F.
  Proof.
    use (preserves_pullback_if_preserves_chosen PBC).
    intros x y z f g.
    apply (preserves_pullback_from_binproduct_equalizer_is_pb f g).
  Defined.
End PullbackPreservation.
