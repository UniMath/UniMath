(*******************************************************************************************

 Disjoint and stable binary coproducts

 In this file, we define several properties that binary coproducts could satisfy. These are
 - Disjointness
 - Stability under pullback.
 These properties are used when defining extensive categories. An extensive category is a
 category with finite coproducts such that coproducts are disjoint and stable under pullback,
 and such that pullbacks exist of coproduct injections.

 Disjointness is easy to formulate. The requirements are that the coproduct injections are
 monomorphic and that their intersection is given by the initial object.

 However, more subtleties come up when defining stability under pullback of coproducts. The
 main challenge here lies in the requirements that you put on the category. If you require
 that all pullbacks exist, then it suffices to require that the pullback functor between
 slice categories preserves binary coproducts. In certain cases, however, one does not want
 to rely the assumption that the category has all pullbacks. In fact, to define extensiveness,
 one usually does not assume all pullbacks (see, e.g., Definition 2.1 in "Introduction to
 extensive and distributive categories" by Carboni, Lack, and Walters).

 For this reason, we define stability of binary coproducts without assuming the existence
 of all pullbacks. The full definition is given in ([stable_bincoproducts]), and basically,
 it says that whenever we have pullbacks of objects `a` and `b`, then the canonical square
 involving the binary coproduct is also a pullback. In diagrams: if we have pullbacks

<<
 ap -----> a
 |         |
 |         |
 V         V
 x ------> y
>>

 and

<<
 bp -----> b
 |         |
 |         |
 V         V
 x ------> y
>>

 then we also have a pullback

<<
 ap + bp -----> a + b
    |             |
    |             |
    V             V
    x ----------> y
>>

 where the involved maps are defined via the universal property.

 We also show that this definition of stability is equivalent to the pullback functors
 preserving binary coprduct if the involved category has pullbacks. This proof is a tedious
 verification of facts.

 Referenes
 - "Introduction to extensive and distributive categories" by Carboni, Lack, and Walters

 Contents
 1. Disjoint binary coproducts
 2. Stable binary coproducts
 3. Characterization of stable binary coproducts

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

(** * 1. Disjoint binary coproducts *)
Proposition bincoproduct_intersection
            {C : category}
            (BC : BinCoproducts C)
            (I : Initial C)
            (x y : C)
  : InitialArrow I x · BinCoproductIn1 (BC x y)
    =
    InitialArrow I y · BinCoproductIn2 (BC x y).
Proof.
  apply InitialArrowEq.
Qed.

Definition disjoint_bincoproducts
           {C : category}
           (BC : BinCoproducts C)
           (I : Initial C)
  : UU
  := ∏ (x y : C),
     isMonic (BinCoproductIn1 (BC x y))
     ×
     isMonic (BinCoproductIn2 (BC x y))
     ×
     isPullback (bincoproduct_intersection BC I x y).

Proposition isaprop_disjoint_bincoproducts
            {C : category}
            (BC : BinCoproducts C)
            (I : Initial C)
  : isaprop (disjoint_bincoproducts BC I).
Proof.
  do 2 (use impred ; intro).
  repeat (use isapropdirprod).
  - apply isapropisMonic.
  - apply isapropisMonic.
  - apply isaprop_isPullback.
Qed.

(** * 2. Stable binary coproducts *)
Section StableBinCoproducts.
  Context {C : category}
          (BC : BinCoproducts C).

  Section Diagram.
    Context {a b x y ap bp : C}
            (f : x --> y)
            (g₁ : a --> y)
            (g₂ : b --> y)
            (π₁ : ap --> a)
            (π₂ : ap --> x)
            (ρ₁ : bp --> b)
            (ρ₂ : bp --> x).

    Let ab : BinCoproduct a b := BC a b.

    Let apbp : BinCoproduct ap bp := BC ap bp.

    Definition bincoproduct_slice_mor
      : ab --> y
      := BinCoproductArrow ab g₁ g₂.

    Definition bincoproduct_pb_slice_mor
      : apbp --> x
      := BinCoproductArrow apbp π₂ ρ₂.

    Definition pb_bincoproduct_mor
      : apbp --> ab
      := BinCoproductArrow apbp (π₁ · BinCoproductIn1 ab) (ρ₁ · BinCoproductIn2 ab).
  End Diagram.

  Proposition bincoproduct_pb_diag
              {a b x y ap bp : C}
              {f : x --> y}
              {g₁ : a --> y}
              {g₂ : b --> y}
              {π₁ : ap --> a}
              {π₂ : ap --> x}
              {ρ₁ : bp --> b}
              {ρ₂ : bp --> x}
              (p : π₁ · g₁ = π₂ · f)
              (q : ρ₁ · g₂ = ρ₂ · f)
    : pb_bincoproduct_mor π₁ ρ₁ · bincoproduct_slice_mor g₁ g₂
      =
      bincoproduct_pb_slice_mor π₂ ρ₂ · f.
  Proof.
    unfold bincoproduct_slice_mor, bincoproduct_pb_slice_mor, pb_bincoproduct_mor.
    use BinCoproductArrowsEq ; cbn.
    - rewrite !assoc.
      rewrite !BinCoproductIn1Commutes.
      rewrite !assoc'.
      rewrite BinCoproductIn1Commutes.
      rewrite p.
      apply idpath.
    - rewrite !assoc.
      rewrite !BinCoproductIn2Commutes.
      rewrite !assoc'.
      rewrite BinCoproductIn2Commutes.
      rewrite q.
      apply idpath.
  Qed.

  Definition stable_bincoproducts
    : UU
    := ∏ (a b x y ap bp : C)
         (f : x --> y)
         (g₁ : a --> y)
         (g₂ : b --> y)
         (π₁ : ap --> a)
         (π₂ : ap --> x)
         (ρ₁ : bp --> b)
         (ρ₂ : bp --> x)
         (p : π₁ · g₁ = π₂ · f)
         (q : ρ₁ · g₂ = ρ₂ · f)
         (H₁ : isPullback p)
         (H₂ : isPullback q),
       isPullback (bincoproduct_pb_diag p q).

  Proposition isaprop_stable_bincoproducts
    : isaprop stable_bincoproducts.
  Proof.
    do 17 (use impred ; intro) ; cbn -[isofhlevel].
    apply isaprop_isPullback.
  Qed.
End StableBinCoproducts.

(** * 3. Characterization of stable binary coproducts *)
Section StableBinCoproductsCharacterization.
  Context {C : category}
          (BC : BinCoproducts C)
          (PB : Pullbacks C).

  Section ToStable.
    Context (H : ∏ (x y : C)
                   (f : x --> y),
                 preserves_bincoproduct (cod_pb PB f))
            {a b x y ap bp : C}
            (f : x --> y)
            (g₁ : a --> y)
            (g₂ : b --> y)
            (π₁ : ap --> a)
            (π₂ : ap --> x)
            (ρ₁ : bp --> b)
            (ρ₂ : bp --> x)
            (p : π₁ · g₁ = π₂ · f)
            (q : ρ₁ · g₂ = ρ₂ · f)
            (H₁ : isPullback p)
            (H₂ : isPullback q).

    Let ab : BinCoproduct a b := BC a b.
    Let apbp : BinCoproduct ap bp := BC ap bp.
    Let ζ : C/x := make_cod_fib_ob (bincoproduct_pb_slice_mor BC π₂ ρ₂).
    Let Hab : isBinCoproduct _ _ _ _ _ _ := isBinCoproduct_BinCoproduct _ ab.
    Let ag₁ : C/y := make_cod_fib_ob g₁.
    Let bg₂ : C/y := make_cod_fib_ob g₂.
    Let sum : C/y := make_cod_fib_ob (bincoproduct_slice_mor BC g₁ g₂).

    Local Definition stable_from_pb_preserves_bincoproduct_in1
      : ag₁ --> sum.
    Proof.
      use make_cod_fib_mor.
      - apply BinCoproductIn1.
      - abstract
          (apply BinCoproductIn1Commutes).
    Defined.

    Let ι₁ : ag₁ --> sum := stable_from_pb_preserves_bincoproduct_in1.

    Local Definition stable_from_pb_preserves_bincoproduct_in2
      : bg₂ --> sum.
    Proof.
      use make_cod_fib_mor.
      - apply BinCoproductIn2.
      - abstract
          (apply BinCoproductIn2Commutes).
    Defined.

    Let ι₂ : bg₂ --> sum := stable_from_pb_preserves_bincoproduct_in2.

    Let pb : Pullback (bincoproduct_slice_mor BC g₁ g₂) f
      := PB y (BC a b) x (bincoproduct_slice_mor BC g₁ g₂) f.

    Let pb_sum : BinCoproduct (cod_pb PB f ag₁) (cod_pb PB f bg₂)
      := make_BinCoproduct
           _ _ _ _ _ _
           (H x y f
              _ _ _ _ _
              (to_bincoproduct_slice ι₁ ι₂ (isBinCoproduct_BinCoproduct _ (BC a b)))).

    Let φa : z_iso ap (PB y a x g₁ f)
      := z_iso_from_Pullback_to_Pullback (make_Pullback _ H₁) (PB y a x g₁ f).

    Let φb : z_iso bp (PB y b x g₂ f)
      := z_iso_from_Pullback_to_Pullback (make_Pullback _ H₂) (PB y b x g₂ f).

    Definition stable_from_pb_preserves_bincoproduct_mor_help
      : pb_sum --> ζ.
    Proof.
      use (BinCoproductArrow pb_sum (c := ζ)).
      - use make_cod_fib_mor.
        + exact (inv_from_z_iso φa · BinCoproductIn1 _).
        + abstract
            (cbn ;
             unfold bincoproduct_pb_slice_mor ;
             rewrite !assoc' ;
             rewrite BinCoproductIn1Commutes ;
             apply (PullbackArrow_PullbackPr2 (make_Pullback p H₁))).
      - use make_cod_fib_mor.
        + exact (inv_from_z_iso φb · BinCoproductIn2 _).
        + abstract
            (cbn ;
             unfold bincoproduct_pb_slice_mor ;
             rewrite !assoc' ;
             rewrite BinCoproductIn2Commutes ;
             apply (PullbackArrow_PullbackPr2 (make_Pullback q H₂))).
    Defined.

    Let hp : pb_sum --> ζ
      := stable_from_pb_preserves_bincoproduct_mor_help.

    Definition stable_from_pb_preserves_bincoproduct_mor
      : pb --> BC ap bp
      := dom_mor stable_from_pb_preserves_bincoproduct_mor_help.

    Definition stable_from_pb_preserves_bincoproduct_inv
      : BC ap bp --> pb.
    Proof.
      use BinCoproductArrow.
      - exact (φa · dom_mor (BinCoproductIn1 pb_sum)).
      - exact (φb · dom_mor (BinCoproductIn2 pb_sum)).
    Defined.

    Proposition stable_from_pb_preserves_bincoproduct_inv_eq
      : stable_from_pb_preserves_bincoproduct_inv · cod_mor pb_sum = cod_mor ζ.
    Proof.
      cbn.
      unfold stable_from_pb_preserves_bincoproduct_inv.
      unfold bincoproduct_pb_slice_mor.
      use BinCoproductArrowsEq.
      - rewrite !assoc.
        rewrite !BinCoproductIn1Commutes.
        rewrite !assoc'.
        assert (dom_mor (BinCoproductIn1 pb_sum) = dom_mor (#(cod_pb PB f) ι₁))
          as r.
        {
          apply idpath.
        }
        rewrite r.
        rewrite cod_fiber_functor_on_mor.
        cbn.
        rewrite PullbackArrow_PullbackPr2.
        unfold from_Pullback_to_Pullback.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
      - rewrite !assoc.
        rewrite !BinCoproductIn2Commutes.
        rewrite !assoc'.
        assert (dom_mor (BinCoproductIn2 pb_sum) = dom_mor (#(cod_pb PB f) ι₂))
          as r.
        {
          apply idpath.
        }
        rewrite r.
        rewrite cod_fiber_functor_on_mor.
        cbn.
        rewrite PullbackArrow_PullbackPr2.
        unfold from_Pullback_to_Pullback.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
    Qed.

    Definition stable_from_pb_preserves_bincoproduct_inv_slice
      : ζ --> pb_sum.
    Proof.
      use make_cod_fib_mor.
      - exact stable_from_pb_preserves_bincoproduct_inv.
      - exact stable_from_pb_preserves_bincoproduct_inv_eq.
    Defined.

    Let hp_inv : ζ --> pb_sum
      := stable_from_pb_preserves_bincoproduct_inv_slice.

    Proposition stable_from_pb_preserves_bincoproduct_inverses
      : is_inverse_in_precat
          stable_from_pb_preserves_bincoproduct_mor
          stable_from_pb_preserves_bincoproduct_inv.
    Proof.
      unfold stable_from_pb_preserves_bincoproduct_inv.
      split.
      - refine (_ @ maponpaths
                      dom_mor
                      (BinCoproductArrowsEq
                         _ _ _
                         pb_sum _
                         (hp · hp_inv) (identity _)
                         _ _)).
        + rewrite comp_in_cod_fib.
          apply idpath.
        + rewrite !assoc.
          unfold hp, hp_inv, stable_from_pb_preserves_bincoproduct_mor_help.
          rewrite BinCoproductIn1Commutes.
          use eq_mor_cod_fib.
          rewrite comp_in_cod_fib.
          simpl.
          unfold stable_from_pb_preserves_bincoproduct_inv.
          rewrite !assoc'.
          rewrite BinCoproductIn1Commutes.
          rewrite !assoc.
          rewrite z_iso_after_z_iso_inv.
          rewrite id_left.
          apply maponpaths.
          exact (!(id_right _)).
        + rewrite !assoc.
          unfold hp, hp_inv, stable_from_pb_preserves_bincoproduct_mor_help.
          rewrite BinCoproductIn2Commutes.
          use eq_mor_cod_fib.
          rewrite comp_in_cod_fib.
          simpl.
          unfold stable_from_pb_preserves_bincoproduct_inv.
          rewrite !assoc'.
          rewrite BinCoproductIn2Commutes.
          rewrite !assoc.
          rewrite z_iso_after_z_iso_inv.
          rewrite id_left.
          apply maponpaths.
          exact (!(id_right _)).
      - use BinCoproductArrowsEq.
        + rewrite !assoc.
          rewrite BinCoproductIn1Commutes.
          unfold stable_from_pb_preserves_bincoproduct_mor.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            exact (comp_in_cod_fib
                     (BinCoproductIn1 pb_sum)
                     stable_from_pb_preserves_bincoproduct_mor_help).
          }
          etrans.
          {
            do 2 apply maponpaths.
            apply BinCoproductIn1Commutes.
          }
          cbn.
          rewrite id_right.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (z_iso_inv_after_z_iso φa).
          }
          apply id_left.
        + rewrite !assoc.
          rewrite BinCoproductIn2Commutes.
          unfold stable_from_pb_preserves_bincoproduct_mor.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            exact (comp_in_cod_fib
                     (BinCoproductIn2 pb_sum)
                     stable_from_pb_preserves_bincoproduct_mor_help).
          }
          etrans.
          {
            do 2 apply maponpaths.
            apply BinCoproductIn2Commutes.
          }
          cbn.
          rewrite id_right.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (z_iso_inv_after_z_iso φb).
          }
          apply id_left.
    Qed.

    Definition stable_from_pb_preserves_bincoproduct_z_iso
      : z_iso pb (BC ap bp).
    Proof.
      use make_z_iso.
      - exact stable_from_pb_preserves_bincoproduct_mor.
      - exact stable_from_pb_preserves_bincoproduct_inv.
      - exact stable_from_pb_preserves_bincoproduct_inverses.
    Defined.

    Proposition stable_from_pb_preserves_bincoproduct_left
      : stable_from_pb_preserves_bincoproduct_mor
        · pb_bincoproduct_mor BC π₁ ρ₁
        =
        PullbackPr1 pb.
    Proof.
      refine (!_).
      use (z_iso_inv_to_left _ _ _ stable_from_pb_preserves_bincoproduct_z_iso).
      cbn.
      use BinCoproductArrowsEq.
      - rewrite !assoc.
        unfold stable_from_pb_preserves_bincoproduct_inv.
        unfold pb_bincoproduct_mor.
        rewrite !BinCoproductIn1Commutes.
        assert (dom_mor (BinCoproductIn1 pb_sum) = dom_mor (#(cod_pb PB f) ι₁))
          as r.
        {
          apply idpath.
        }
        rewrite r.
        rewrite cod_fiber_functor_on_mor.
        cbn.
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite !assoc.
        unfold from_Pullback_to_Pullback.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      - rewrite !assoc.
        unfold stable_from_pb_preserves_bincoproduct_inv.
        unfold pb_bincoproduct_mor.
        rewrite !BinCoproductIn2Commutes.
        assert (dom_mor (BinCoproductIn2 pb_sum) = dom_mor (#(cod_pb PB f) ι₂))
          as r.
        {
          apply idpath.
        }
        rewrite r.
        rewrite cod_fiber_functor_on_mor.
        cbn.
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite !assoc.
        unfold from_Pullback_to_Pullback.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
    Qed.

    Proposition stable_from_pb_preserves_bincoproduct_right
      : stable_from_pb_preserves_bincoproduct_mor
        · bincoproduct_pb_slice_mor BC π₂ ρ₂
        =
        PullbackPr2 pb.
    Proof.
      refine (!_).
      use (z_iso_inv_to_left _ _ _ stable_from_pb_preserves_bincoproduct_z_iso).
      cbn.
      use BinCoproductArrowsEq.
      - rewrite !assoc.
        unfold stable_from_pb_preserves_bincoproduct_inv.
        unfold bincoproduct_pb_slice_mor.
        rewrite !BinCoproductIn1Commutes.
        assert (dom_mor (BinCoproductIn1 pb_sum) = dom_mor (#(cod_pb PB f) ι₁))
          as r.
        {
          apply idpath.
        }
        rewrite r.
        rewrite cod_fiber_functor_on_mor.
        cbn.
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        unfold from_Pullback_to_Pullback.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
      - rewrite !assoc.
        unfold stable_from_pb_preserves_bincoproduct_inv.
        unfold bincoproduct_pb_slice_mor.
        rewrite !BinCoproductIn2Commutes.
        assert (dom_mor (BinCoproductIn2 pb_sum) = dom_mor (#(cod_pb PB f) ι₂))
          as r.
        {
          apply idpath.
        }
        rewrite r.
        rewrite cod_fiber_functor_on_mor.
        cbn.
        rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        unfold from_Pullback_to_Pullback.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
    Qed.

    Proposition stable_from_pb_preserves_bincoproduct
      : isPullback (bincoproduct_pb_diag BC p q).
    Proof.
      simple refine (isPullback_z_iso
                       _ _
                       (isPullback_Pullback pb)
                       _ _ _).
      - exact stable_from_pb_preserves_bincoproduct_z_iso.
      - exact stable_from_pb_preserves_bincoproduct_left.
      - exact stable_from_pb_preserves_bincoproduct_right.
    Defined.
  End ToStable.

  Proposition stable_bincoproducts_from_pb_preserves_bincoproduct
              (H : ∏ (x y : C)
                     (f : x --> y),
                   preserves_bincoproduct (cod_pb PB f))
    : stable_bincoproducts BC.
  Proof.
    intros a b x y ab bp f g₁ g₂ π₁ π₂ ρ₁ ρ₂ p q H₁ H₂.
    exact (stable_from_pb_preserves_bincoproduct H _ _ _ _ _ _ _ _ _ H₁ H₂).
  Defined.

  Section FromStable.
    Context (H : stable_bincoproducts BC)
            {x y : C}
            (f : x --> y)
            (ag₁ bg₂ : C / y).

    Let a : C := cod_dom ag₁.
    Let g₁ : a --> y := cod_mor ag₁.

    Let b : C := cod_dom bg₂.
    Let g₂ : b --> y := cod_mor bg₂.

    Let ap : Pullback g₁ f := PB _ _ _ g₁ f.
    Let π₁ : ap --> a := PullbackPr1 ap.
    Let π₂ : ap --> x := PullbackPr2 ap.

    Let bp : Pullback g₂ f := PB _ _ _ g₂ f.
    Let ρ₁ : bp --> b := PullbackPr1 bp.
    Let ρ₂ : bp --> x := PullbackPr2 bp.

    Let p : π₁ · g₁ = π₂ · f := PullbackSqrCommutes ap.
    Let q : ρ₁ · g₂ = ρ₂ · f := PullbackSqrCommutes bp.

    Let Hap : isPullback p := isPullback_Pullback ap.
    Let Hbp : isPullback q := isPullback_Pullback bp.

    Let Hpb : Pullback (bincoproduct_slice_mor BC g₁ g₂) f
      := make_Pullback _ (H a b x y ap bp f g₁ g₂ π₁ π₂ ρ₁ ρ₂ p q Hap Hbp).

    Let ab : BinCoproduct a b := BC a b.

    Let apbp : BinCoproduct ap bp := BC ap bp.

    Definition from_stable_mor
      : apbp
        -->
        PB y (BC a b) x (cod_fib_coproduct_ob_mor ag₁ bg₂ (BC a b)) f.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 Hpb).
      - exact (PullbackPr2 Hpb).
      - abstract
          (apply (PullbackSqrCommutes Hpb)).
    Defined.

    Definition from_stable_inv
      : PB y (BC a b) x (cod_fib_coproduct_ob_mor ag₁ bg₂ (BC a b)) f
        -->
        apbp.
    Proof.
      use (PullbackArrow Hpb).
      - apply PullbackPr1.
      - apply PullbackPr2.
      - abstract
          (apply PullbackSqrCommutes).
    Defined.

    Proposition from_stable_inverses
      : is_inverse_in_precat from_stable_mor from_stable_inv.
    Proof.
      unfold from_stable_mor, from_stable_inv.
      split.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback Hpb)).
        + rewrite !assoc'.
          rewrite (PullbackArrow_PullbackPr1 Hpb).
          rewrite PullbackArrow_PullbackPr1.
          rewrite id_left.
          apply idpath.
        + rewrite !assoc'.
          rewrite (PullbackArrow_PullbackPr2 Hpb).
          rewrite PullbackArrow_PullbackPr2.
          rewrite id_left.
          apply idpath.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite (PullbackArrow_PullbackPr1 Hpb).
          rewrite id_left.
          apply idpath.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          rewrite (PullbackArrow_PullbackPr2 Hpb).
          rewrite id_left.
          apply idpath.
    Qed.

    Proposition from_stable_in1
      : dom_mor (cod_fiber_functor_pb
                   PB
                   f
                   (BinCoproductIn1 (bincoproducts_cod_fib y BC ag₁ bg₂)))
        =
        BinCoproductIn1 apbp · from_stable_mor.
    Proof.
      unfold from_stable_mor ; cbn.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      - rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr1.
        unfold pb_bincoproduct_mor.
        rewrite BinCoproductIn1Commutes.
        apply idpath.
      - rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr2.
        unfold bincoproduct_pb_slice_mor.
        rewrite BinCoproductIn1Commutes.
        apply idpath.
    Qed.

    Proposition from_stable_in2
      : dom_mor (cod_fiber_functor_pb
                   PB
                   f
                   (BinCoproductIn2 (bincoproducts_cod_fib y BC ag₁ bg₂)))
        =
        BinCoproductIn2 apbp · from_stable_mor.
    Proof.
      unfold from_stable_mor ; cbn.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      - rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr1.
        unfold pb_bincoproduct_mor.
        rewrite BinCoproductIn2Commutes.
        apply idpath.
      - rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr2.
        unfold bincoproduct_pb_slice_mor.
        rewrite BinCoproductIn2Commutes.
        apply idpath.
    Qed.

    Proposition from_stable
      : isBinCoproduct
          (C/x)
          (cod_pb PB f ag₁)
          (cod_pb PB f bg₂)
          (cod_pb PB f (bincoproducts_cod_fib y BC ag₁ bg₂))
          (#(cod_pb PB f) (BinCoproductIn1 (bincoproducts_cod_fib y BC ag₁ bg₂)))
          (#(cod_pb PB f) (BinCoproductIn2 (bincoproducts_cod_fib y BC ag₁ bg₂))).
    Proof.
      use to_bincoproduct_slice.
      rewrite !cod_fiber_functor_on_mor.
      use (isBinCoproduct_z_iso (isBinCoproduct_BinCoproduct _ apbp)).
      - use make_z_iso.
        + exact from_stable_mor.
        + exact from_stable_inv.
        + exact from_stable_inverses.
      - exact from_stable_in1.
      - exact from_stable_in2.
    Defined.
  End FromStable.

  Proposition pb_preserves_bincoproduct_from_stable_bincoproducts
              (H : stable_bincoproducts BC)
              {x y : C}
              (f : x --> y)
    : preserves_bincoproduct (cod_pb PB f).
  Proof.
    use preserves_bincoproduct_if_preserves_chosen.
    {
      use bincoproducts_cod_fib.
      exact BC.
    }
    intros ag₁ bg₂.
    apply from_stable.
    exact H.
  Defined.

  Definition pb_preserves_bincoproduct_weq_stable
    : stable_bincoproducts BC
      ≃
      (∏ (x y : C)
         (f : x --> y),
       preserves_bincoproduct (cod_pb PB f)).
  Proof.
    use weqimplimpl.
    - exact @pb_preserves_bincoproduct_from_stable_bincoproducts.
    - exact stable_bincoproducts_from_pb_preserves_bincoproduct.
    - abstract
        (apply isaprop_stable_bincoproducts).
    - abstract
        (do 3 (use impred ; intro) ;
         apply isaprop_preserves_bincoproduct).
  Defined.
End StableBinCoproductsCharacterization.
