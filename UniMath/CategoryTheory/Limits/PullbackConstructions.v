(***************************************************************************************

 Constructions using pullbacks

 In this file, we collect various constructions with pullbacks.

 Contents
 1. Equalizers from pullbacks and products
 2. Equalizers from pullbacks and a terminal object
 3. Pullback of a product

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Local Open Scope cat.

(** * 1. Equalizers from pullbacks and products *)
Section EqualizersFromPullbackProducts.
  Context {C : category}
          (PB : Pullbacks C)
          (P : BinProducts C).

  Section EqualizerConstruction.
    Context {x y : C}
            (f g : x --> y).

    Let Δ : y --> P y y := diagonalMap' P y.
    Let φ : x --> P y y := BinProductArrow _ (P y y) f g.

    Let e : Pullback Δ φ := PB _ _ _ Δ φ.
    Let i : e --> x := PullbackPr2 e.

    Proposition equalizer_from_pb_prod_eq
      : i · f = i · g.
    Proof.
      pose (maponpaths (λ z, z · BinProductPr1 _ _) (PullbackSqrCommutes e)) as p.
      cbn in p.
      rewrite !assoc' in p.
      unfold Δ, φ, diagonalMap' in p.
      rewrite !BinProductPr1Commutes in p.
      rewrite id_right in p.
      refine (!p @ _).
      clear p.
      pose (maponpaths (λ z, z · BinProductPr2 _ _) (PullbackSqrCommutes e)) as p.
      cbn in p.
      rewrite !assoc' in p.
      unfold Δ, φ, diagonalMap' in p.
      rewrite !BinProductPr2Commutes in p.
      rewrite id_right in p.
      exact p.
    Qed.

    Section UMP.
      Context {w : C}
              {h : w --> x}
              (p : h · f = h · g).

      Proposition equalizer_from_pb_prod_map_eq
        : h · f · Δ = h · φ.
      Proof.
        unfold Δ, diagonalMap', φ.
        use BinProductArrowsEq.
        - rewrite !assoc'.
          rewrite !BinProductPr1Commutes.
          rewrite id_right.
          apply idpath.
        - rewrite !assoc'.
          rewrite !BinProductPr2Commutes.
          rewrite id_right.
          exact p.
      Qed.

      Proposition equalizer_from_pb_prod_unique
        : isaprop (∑ (ζ : w --> e), ζ · i = h).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback e)).
        - use (diagonalMap_isMonic P y).
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact (PullbackSqrCommutes e).
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (pr2 ζ₁).
          }
          rewrite !assoc'.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            exact (PullbackSqrCommutes e).
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (pr2 ζ₂).
          }
          apply idpath.
        - exact (pr2 ζ₁ @ !(pr2 ζ₂)).
      Qed.

      Definition equalizer_from_pb_prod_map
        : w --> e.
      Proof.
        use (PullbackArrow e _ (h · f) h).
        apply equalizer_from_pb_prod_map_eq.
      Defined.

      Proposition equalizer_from_pb_prod_comm
        : equalizer_from_pb_prod_map · i = h.
      Proof.
        exact (PullbackArrow_PullbackPr2 e _ (h · f) h equalizer_from_pb_prod_map_eq).
      Qed.
    End UMP.

    Definition equalizer_from_pb_prod
      : Equalizer f g.
    Proof.
      use make_Equalizer.
      - exact e.
      - exact i.
      - exact equalizer_from_pb_prod_eq.
      - intros w h p.
        use iscontraprop1.
        + apply equalizer_from_pb_prod_unique.
        + refine (equalizer_from_pb_prod_map p ,, _).
          exact (equalizer_from_pb_prod_comm p).
    Defined.
  End EqualizerConstruction.

  Definition equalizers_from_pullbacks_prods
    : Equalizers C.
  Proof.
    intros x y f g.
    apply equalizer_from_pb_prod.
  Defined.
End EqualizersFromPullbackProducts.

(** * 2. Equalizers from pullbacks and a terminal object *)
Definition equalizers_from_pullbacks_terminal
           {C : category}
           (PB : Pullbacks C)
           (T : Terminal C)
  : Equalizers C.
Proof.
  use equalizers_from_pullbacks_prods.
  - exact PB.
  - exact (BinProductsFromPullbacks PB T).
Defined.

(** * 3. Pullback of a product *)
Section PullbackProduct.
  Context {C : category}
          (PC : BinProducts C)
          (PB : Pullbacks C)
          {x₁ x₂ : C}
          (f : x₁ --> x₂)
          (y : C).

  Let xy₁ : BinProduct C x₁ y := PC x₁ y.
  Let π₁ : xy₁ --> x₁ := BinProductPr1 _ _.
  Let π₂ : xy₁ --> y := BinProductPr2 _ _.

  Let xy₂ : BinProduct C x₂ y := PC x₂ y.
  Let ρ₁ : xy₂ --> x₂ := BinProductPr1 _ _.
  Let ρ₂ : xy₂ --> y := BinProductPr2 _ _.

  Let pb : Pullback ρ₁ f := PB _ _ _ ρ₁ f.

  Definition map_from_pb_prod
    : pb --> xy₁.
  Proof.
    use BinProductArrow.
    - exact (PullbackPr2 pb).
    - exact (PullbackPr1 pb · ρ₂).
  Defined.

  Definition map_to_pb_prod
    : xy₁ --> pb.
  Proof.
    use PullbackArrow.
    - use BinProductArrow.
      + exact (π₁ · f).
      + exact π₂.
    - exact π₁.
    - abstract
        (exact (BinProductPr1Commutes _ _ _ _ _ _ _)).
  Defined.

  Proposition pb_prod_is_inverse
    : is_inverse_in_precat
        map_from_pb_prod
        map_to_pb_prod.
  Proof.
    unfold map_from_pb_prod, map_to_pb_prod.
    split.
    - use (MorphismsIntoPullbackEqual (isPullback_Pullback pb)).
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite id_left.
        use BinProductArrowsEq.
        * rewrite !assoc'.
          rewrite BinProductPr1Commutes.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply BinProductPr1Commutes.
          }
          refine (!_).
          apply PullbackSqrCommutes.
        * rewrite !assoc'.
          rewrite BinProductPr2Commutes.
          apply BinProductPr2Commutes.
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite id_left.
        apply BinProductPr1Commutes.
    - use BinProductArrowsEq.
      + rewrite !assoc'.
        rewrite BinProductPr1Commutes.
        rewrite PullbackArrow_PullbackPr2.
        rewrite id_left.
        apply idpath.
      + rewrite !assoc'.
        rewrite BinProductPr2Commutes.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr1.
        rewrite id_left.
        apply BinProductPr2Commutes.
  Qed.

  Definition pb_prod_z_iso
    : z_iso pb xy₁.
  Proof.
    use make_z_iso.
    - exact map_from_pb_prod.
    - exact map_to_pb_prod.
    - exact pb_prod_is_inverse.
  Defined.
End PullbackProduct.
