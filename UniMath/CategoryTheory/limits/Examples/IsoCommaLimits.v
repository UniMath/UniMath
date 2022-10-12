(************************************************************************

 Limits and colimits in the iso-comma category

 Contents
 1. Terminal objects
 2. Products
 3. Pullbacks
 4. Initial objects
 5. Coproducts

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.

Local Open Scope cat.

Section IsoCommaLimits.
  Context {C₁ C₂ C₃ : category}
          (F : C₁ ⟶ C₃)
          (G : C₂ ⟶ C₃).

  (**
   1. Terminal objects
   *)
  Section TerminalObject.
    Context (HF : preserves_terminal F)
            (HG : preserves_terminal G).

    Definition isTerminal_iso_comma
               (x : iso_comma F G)
               (H₁ : isTerminal C₁ (pr11 x))
               (H₂ : isTerminal C₂ (pr21 x))
      : isTerminal (iso_comma F G) x.
    Proof.
      intros w.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use eq_iso_comma_mor ;
           [ apply (@TerminalArrowEq _ (make_Terminal _ H₁))
           | apply (@TerminalArrowEq _ (make_Terminal _ H₂)) ]).
      - refine ((TerminalArrow (_ ,, H₁) (pr11 w)
                   ,,
                   TerminalArrow (_ ,, H₂) (pr21 w))
                  ,,
                  _).
        apply (@TerminalArrowEq _ (make_Terminal _ (HG _ H₂))).
    Defined.

    Definition terminal_category_iso_comma
               (T₁ : Terminal C₁)
               (T₂ : Terminal C₂)
      : Terminal (iso_comma F G).
    Proof.
      simple refine (_ ,, _).
      - refine ((pr1 T₁ ,, pr1 T₂) ,, _) ; cbn.
        exact (z_iso_Terminals
                 (make_Terminal _ (HF _ (pr2 T₁)))
                 (make_Terminal _ (HG _ (pr2 T₂)))).
      - apply isTerminal_iso_comma.
        + exact (pr2 T₁).
        + exact (pr2 T₂).
    Defined.

    Definition iso_comma_pr1_preserves_terminal
               (T₁ : Terminal C₁)
               (T₂ : Terminal C₂)
      : preserves_terminal (iso_comma_pr1 F G).
    Proof.
      apply (preserves_terminal_if_preserves_chosen
               (terminal_category_iso_comma T₁ T₂)
               (iso_comma_pr1 F G)).
      exact (pr2 T₁).
    Defined.

    Definition iso_comma_pr2_preserves_terminal
               (T₁ : Terminal C₁)
               (T₂ : Terminal C₂)
      : preserves_terminal (iso_comma_pr2 F G).
    Proof.
      apply (preserves_terminal_if_preserves_chosen
               (terminal_category_iso_comma T₁ T₂)
               (iso_comma_pr2 F G)).
      exact (pr2 T₂).
    Defined.

    Definition iso_comma_ump1_preserves_terminal
               {C₀ : category}
               (H₁ : C₀ ⟶ C₁)
               (HH₁ : preserves_terminal H₁)
               (H₂ : C₀ ⟶ C₂)
               (HH₂ : preserves_terminal H₂)
               (α : nat_z_iso (H₁ ∙ F) (H₂ ∙ G))
      : preserves_terminal (iso_comma_ump1 F G H₁ H₂ α).
    Proof.
      intros x Hx.
      apply isTerminal_iso_comma.
      - apply HH₁.
        exact Hx.
      - apply HH₂.
        exact Hx.
    Defined.
  End TerminalObject.

  (**
   2. Products
   *)
  Section Product.
    Context (HF : preserves_binproduct F)
            (HG : preserves_binproduct G).

    Section IsProductInIsoComma.
      Context {x y z : iso_comma F G}
              (p₁ : z --> x)
              (p₂ : z --> y)
              (H₁ : isBinProduct _ (pr11 x) (pr11 y) (pr11 z) (pr11 p₁) (pr11 p₂))
              (H₂ : isBinProduct _ (pr21 x) (pr21 y) (pr21 z) (pr21 p₁) (pr21 p₂)).

      Let P₁ : BinProduct C₁ (pr11 x) (pr11 y) := make_BinProduct _ _ _ _ _ _ H₁.
      Let P₂ : BinProduct C₂ (pr21 x) (pr21 y) := make_BinProduct _ _ _ _ _ _ H₂.

      Section UMP.
        Context {w : iso_comma F G}
                (f : w --> x)
                (g : w --> y).

        Definition isBinProduct_in_iso_comma_unique
          : isaprop (∑ (fg : w --> z), fg · p₁ = f × fg · p₂ = g).
        Proof.
          use invproofirrelevance.
          intros φ₁ φ₂.
          use subtypePath.
          {
            intro.
            apply isapropdirprod ; apply homset_property.
          }
          use eq_iso_comma_mor.
          - use (BinProductArrowsEq _ _ _ P₁).
            + exact (maponpaths (λ z, pr11 z) (pr12 φ₁)
                     @ !(maponpaths (λ z, pr11 z) (pr12 φ₂))).
            + exact (maponpaths (λ z, pr11 z) (pr22 φ₁)
                     @ !(maponpaths (λ z, pr11 z) (pr22 φ₂))).
          - use (BinProductArrowsEq _ _ _ P₂).
            + exact (maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr12 φ₁)
                     @ !(maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr12 φ₂))).
            + exact (maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr22 φ₁)
                     @ !(maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr22 φ₂))).
        Qed.

        Definition isBinProduct_in_iso_comma_ump
          : w --> z.
        Proof.
          simple refine ((_ ,, _) ,, _) ; cbn.
          - exact (BinProductArrow _ P₁ (pr11 f) (pr11 g)).
          - exact (BinProductArrow _ P₂ (pr21 f) (pr21 g)).
          - use (BinProductArrowsEq
                   _ _ _
                   (make_BinProduct _ _ _ _ _ _ (HG _ _ _ _ _ (pr2 P₂)))) ; cbn.
            + abstract
                (rewrite !assoc' ;
                 rewrite <- functor_comp ;
                 rewrite (BinProductPr1Commutes _ _ _ P₂) ;
                 refine (_ @ pr2 f) ;
                 refine (!(maponpaths (λ z, _ · z) (pr2 p₁)) @ _) ;
                 rewrite !assoc ;
                 rewrite <- functor_comp ;
                 rewrite (BinProductPr1Commutes _ _ _ P₁) ;
                 apply idpath).
            + abstract
                (rewrite !assoc' ;
                 rewrite <- functor_comp ;
                 rewrite (BinProductPr2Commutes _ _ _ P₂) ;
                 refine (_ @ pr2 g) ;
                 refine (!(maponpaths (λ z, _ · z) (pr2 p₂)) @ _) ;
                 rewrite !assoc ;
                 rewrite <- functor_comp ;
                 rewrite (BinProductPr2Commutes _ _ _ P₁) ;
                 apply idpath).
        Defined.

        Definition isBinProduct_in_iso_comma_ump_pr1
          : isBinProduct_in_iso_comma_ump · p₁ = f.
        Proof.
          use eq_iso_comma_mor ; cbn.
          - apply (BinProductPr1Commutes _ _ _ P₁).
          - apply (BinProductPr1Commutes _ _ _ P₂).
        Qed.

        Definition isBinProduct_in_iso_comma_ump_pr2
          : isBinProduct_in_iso_comma_ump · p₂ = g.
        Proof.
          use eq_iso_comma_mor ; cbn.
          - apply (BinProductPr2Commutes _ _ _ P₁).
          - apply (BinProductPr2Commutes _ _ _ P₂).
        Qed.
      End UMP.

      Definition isBinProduct_in_iso_comma
        : isBinProduct (iso_comma F G) x y z p₁ p₂.
      Proof.
        intros w f g.
        use iscontraprop1.
        - exact (isBinProduct_in_iso_comma_unique f g).
        - simple refine (_ ,, _ ,, _).
          + exact (isBinProduct_in_iso_comma_ump f g).
          + exact (isBinProduct_in_iso_comma_ump_pr1 f g).
          + exact (isBinProduct_in_iso_comma_ump_pr2 f g).
      Defined.
    End IsProductInIsoComma.

    Definition binproducts_in_iso_comma
               (HC₁ : BinProducts C₁)
               (HC₂ : BinProducts C₂)
      : BinProducts (iso_comma F G).
    Proof.
      intros x y.
      pose (FP := make_BinProduct
                    _ _ _ _ _ _
                    (HF (pr11 x) (pr11 y)
                       _
                       (BinProductPr1 _ (HC₁ (pr11 x) (pr11 y)))
                       (BinProductPr2 _ (HC₁ (pr11 x) (pr11 y)))
                       (isBinProduct_BinProduct _ (HC₁ (pr11 x) (pr11 y))))).
      pose (GP := make_BinProduct
                    _ _ _ _ _ _
                    (HG (pr21 x) (pr21 y)
                       _
                       (BinProductPr1 _ (HC₂ (pr21 x) (pr21 y)))
                       (BinProductPr2 _ (HC₂ (pr21 x) (pr21 y)))
                       (isBinProduct_BinProduct _ (HC₂ (pr21 x) (pr21 y))))).
      use make_BinProduct.
      - simple refine ((_ ,, _) ,, _).
        + exact (BinProductObject _ (HC₁ (pr11 x) (pr11 y))).
        + exact (BinProductObject _ (HC₂ (pr21 x) (pr21 y))).
        + exact (binproduct_of_z_iso FP GP (pr2 x) (pr2 y)).
      - simple refine ((_ ,, _) ,, _).
        + exact (BinProductPr1 _ (HC₁ (pr11 x) (pr11 y))).
        + exact (BinProductPr1 _ (HC₂ (pr21 x) (pr21 y))).
        + exact (!(BinProductOfArrowsPr1 _ GP FP (pr12 x) (pr12 y))).
      - simple refine ((_ ,, _) ,, _).
        + exact (BinProductPr2 _ (HC₁ (pr11 x) (pr11 y))).
        + exact (BinProductPr2 _ (HC₂ (pr21 x) (pr21 y))).
        + exact (!(BinProductOfArrowsPr2 _ GP FP (pr12 x) (pr12 y))).
      -  use isBinProduct_in_iso_comma.
         + apply isBinProduct_BinProduct.
         + apply isBinProduct_BinProduct.
    Defined.

    Definition iso_comma_pr1_preserves_binproduct
               (HC₁ : BinProducts C₁)
               (HC₂ : BinProducts C₂)
      : preserves_binproduct (iso_comma_pr1 F G).
    Proof.
      use preserves_binproduct_if_preserves_chosen.
      - apply binproducts_in_iso_comma.
        + exact HC₁.
        + exact HC₂.
      - intros x y.
        cbn.
        apply isBinProduct_BinProduct.
    Defined.

    Definition iso_comma_pr2_preserves_binproduct
               (HC₁ : BinProducts C₁)
               (HC₂ : BinProducts C₂)
      : preserves_binproduct (iso_comma_pr2 F G).
    Proof.
      use preserves_binproduct_if_preserves_chosen.
      - apply binproducts_in_iso_comma.
        + exact HC₁.
        + exact HC₂.
      - intros x y.
        cbn.
        apply isBinProduct_BinProduct.
    Defined.

    Definition iso_comma_ump1_preserves_binproduct
               {C₀ : category}
               (H₁ : C₀ ⟶ C₁)
               (HH₁ : preserves_binproduct H₁)
               (H₂ : C₀ ⟶ C₂)
               (HH₂ : preserves_binproduct H₂)
               (α : nat_z_iso (H₁ ∙ F) (H₂ ∙ G))
      : preserves_binproduct (iso_comma_ump1 F G H₁ H₂ α).
    Proof.
      intros x y z π₁ π₂ Hx.
      apply isBinProduct_in_iso_comma.
      - apply HH₁.
        exact Hx.
      - apply HH₂.
        exact Hx.
    Defined.
  End Product.

  (**
   3. Pullbacks
   *)
  Section Pullbacks.
    Context (HF : preserves_pullback F)
            (HG : preserves_pullback G).

    Section IsPullbackIsoComma.
      Context {pb x y z : iso_comma F G}
              (f : x --> z)
              (g : y --> z)
              (π₁ : pb --> x)
              (π₂ : pb --> y)
              (sqr₁ : pr11 π₁ · pr11 f = pr11 π₂ · pr11 g)
              (H₁ : isPullback sqr₁)
              (sqr₂ : pr21 π₁ · pr21 f = pr21 π₂ · pr21 g)
              (H₂ : isPullback sqr₂)
              (sqr₃ : π₁ · f = π₂ · g).

      Let P₁ : Pullback (pr11 f) (pr11 g) := make_Pullback _ H₁.
      Let P₂ : Pullback (pr21 f) (pr21 g) := make_Pullback _ H₂.

      Section UMP.
        Context {w : iso_comma F G}
                (h₁ : w --> x)
                (h₂ : w --> y)
                (p : h₁ · f = h₂ · g).

        Definition isPullback_iso_comma_unique
          : isaprop (∑ (hk : w --> pb), hk · π₁ = h₁ × hk · π₂ = h₂).
        Proof.
          use invproofirrelevance.
          intros φ₁ φ₂.
          use subtypePath.
          {
            intro.
            apply isapropdirprod ; apply homset_property.
          }
          use eq_iso_comma_mor.
          - use (MorphismsIntoPullbackEqual H₁).
            + refine (maponpaths (λ z, pr11 z) (pr12 φ₁) @ _).
              exact (!(maponpaths (λ z, pr11 z) (pr12 φ₂))).
            + refine (maponpaths (λ z, pr11 z) (pr22 φ₁) @ _).
              exact (!(maponpaths (λ z, pr11 z) (pr22 φ₂))).
          - use (MorphismsIntoPullbackEqual H₂).
            + refine (maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr12 φ₁) @ _).
              exact (!(maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr12 φ₂))).
            + refine (maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr22 φ₁) @ _).
              exact (!(maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr22 φ₂))).
        Qed.

        Definition isPullback_iso_comma_mor
          : w --> pb.
        Proof.
          simple refine ((_ ,, _) ,, _).
          - refine (PullbackArrow P₁ _ (pr11 h₁) (pr11 h₂) _).
            abstract (exact (maponpaths (λ z, pr11 z) p)).
          - refine (PullbackArrow P₂ _ (pr21 h₁) (pr21 h₂) _).
            abstract (exact (maponpaths (λ z, dirprod_pr2 (pr1 z)) p)).
          - use (MorphismsIntoPullbackEqual (HG _ _ _ _ _ _ _ _ _ _ (pr22 P₂))).
            + abstract
                (rewrite <- !functor_comp ;
                 apply maponpaths ;
                 exact (PullbackSqrCommutes P₂)).
            + abstract
                (cbn ;
                 rewrite !assoc' ;
                 rewrite <- !functor_comp ;
                 rewrite (PullbackArrow_PullbackPr1 P₂) ;
                 refine (_ @ pr2 h₁) ;
                 rewrite <- (pr2 π₁) ;
                 rewrite !assoc ;
                 apply maponpaths_2 ;
                 rewrite <- !functor_comp ;
                 apply maponpaths ;
                 apply (PullbackArrow_PullbackPr1 P₁)).
            + abstract
                (cbn ;
                 rewrite !assoc' ;
                 rewrite <- !functor_comp ;
                 rewrite (PullbackArrow_PullbackPr2 P₂) ;
                 refine (_ @ pr2 h₂) ;
                 rewrite <- (pr2 π₂) ;
                 rewrite !assoc ;
                 apply maponpaths_2 ;
                 rewrite <- !functor_comp ;
                 apply maponpaths ;
                 apply (PullbackArrow_PullbackPr2 P₁)).
        Defined.

        Definition isPullback_iso_comma_mor_pr1
          : isPullback_iso_comma_mor · π₁ = h₁.
        Proof.
          use eq_iso_comma_mor.
          - apply (PullbackArrow_PullbackPr1 P₁).
          - apply (PullbackArrow_PullbackPr1 P₂).
        Qed.

        Definition isPullback_iso_comma_mor_pr2
          : isPullback_iso_comma_mor · π₂ = h₂.
        Proof.
          use eq_iso_comma_mor.
          - apply (PullbackArrow_PullbackPr2 P₁).
          - apply (PullbackArrow_PullbackPr2 P₂).
        Qed.
      End UMP.

      Definition isPullback_iso_comma
        : isPullback sqr₃.
      Proof.
        intros w h₁ h₂ p.
        use iscontraprop1.
        - apply isPullback_iso_comma_unique.
        - simple refine (_ ,, _ ,, _).
          + exact (isPullback_iso_comma_mor h₁ h₂ p).
          + exact (isPullback_iso_comma_mor_pr1 h₁ h₂ p).
          + exact (isPullback_iso_comma_mor_pr2 h₁ h₂ p).
      Defined.
    End IsPullbackIsoComma.

    Definition pullbacks_in_iso_comma
               (HC₁ : Pullbacks C₁)
               (HC₂ : Pullbacks C₂)
      : Pullbacks (iso_comma F G).
    Proof.
      intros z x y f g.
      simple refine ((_ ,, _ ,, _) ,, (_ ,, _)).
      - simple refine ((_ ,, _) ,, _).
        + exact (PullbackObject (HC₁ _ _ _ (pr11 f) (pr11 g))).
        + exact (PullbackObject (HC₂ _ _ _ (pr21 f) (pr21 g))).
        + use (iso_between_pullbacks
                 _ _
                 (HF _ _ _ _ _ _ _ _ _ _
                    (isPullback_Pullback (HC₁ _ _ _ (pr11 f) (pr11 g))))
                 (HG _ _ _ _ _ _ _ _ _ _
                    (isPullback_Pullback (HC₂ _ _ _ (pr21 f) (pr21 g))))).
          * abstract
              (rewrite <- !functor_comp ;
               apply maponpaths ;
               apply PullbackSqrCommutes).
          * abstract
              (rewrite <- !functor_comp ;
               apply maponpaths ;
               apply PullbackSqrCommutes).
          * exact (pr2 x).
          * exact (pr2 y).
          * exact (pr2 z).
          * exact (!(pr2 f)).
          * exact (!(pr2 g)).
      - simple refine ((_ ,, _) ,, _).
        + apply PullbackPr1.
        + apply PullbackPr1.
        + abstract
            (cbn ; unfold iso_between_pullbacks_map ;
             refine (!_) ;
             apply (PullbackArrow_PullbackPr1
                      (make_Pullback
                         _
                         (HG _ _ _ _ _ _ _ _ _ _
                            (isPullback_Pullback (HC₂ _ _ _ (pr21 f) (pr21 g))))))).
      - simple refine ((_ ,, _) ,, _).
        + apply PullbackPr2.
        + apply PullbackPr2.
        + abstract
            (cbn ; unfold iso_between_pullbacks_map ;
             refine (!_) ;
             apply (PullbackArrow_PullbackPr2
                      (make_Pullback
                         _
                         (HG _ _ _ _ _ _ _ _ _ _
                            (isPullback_Pullback (HC₂ _ _ _ (pr21 f) (pr21 g))))))).
      - abstract
          (use eq_iso_comma_mor ; cbn ;
           [ apply PullbackSqrCommutes
           | apply PullbackSqrCommutes ]).
      - use isPullback_iso_comma.
        + apply PullbackSqrCommutes.
        + apply isPullback_Pullback.
        + apply PullbackSqrCommutes.
        + apply isPullback_Pullback.
    Defined.

    Definition iso_comma_pr1_preserves_pullback
               (HC₁ : Pullbacks C₁)
               (HC₂ : Pullbacks C₂)
      : preserves_pullback (iso_comma_pr1 F G).
    Proof.
      use preserves_pullback_if_preserves_chosen.
      - apply pullbacks_in_iso_comma.
        + exact HC₁.
        + exact HC₂.
      - intros x y z f g.
        cbn.
        apply isPullback_Pullback.
    Defined.

    Definition iso_comma_pr2_preserves_pullback
               (HC₁ : Pullbacks C₁)
               (HC₂ : Pullbacks C₂)
      : preserves_pullback (iso_comma_pr2 F G).
    Proof.
      use preserves_pullback_if_preserves_chosen.
      - apply pullbacks_in_iso_comma.
        + exact HC₁.
        + exact HC₂.
      - intros x y z f g.
        cbn.
        apply isPullback_Pullback.
    Defined.

    Definition iso_comma_ump1_preserves_pullback
               {C₀ : category}
               (H₁ : C₀ ⟶ C₁)
               (HH₁ : preserves_pullback H₁)
               (H₂ : C₀ ⟶ C₂)
               (HH₂ : preserves_pullback H₂)
               (α : nat_z_iso (H₁ ∙ F) (H₂ ∙ G))
      : preserves_pullback
          (iso_comma_ump1 F G H₁ H₂ α).
    Proof.
      intros w x y z f g π₁ π₂ p₁ p₂ H.
      use isPullback_iso_comma ; cbn.
      - abstract
          (rewrite <- !functor_comp ;
           apply maponpaths ;
           exact p₁).
      - exact (HH₁ _ _ _ _ _ _ _ _ _ _ H).
      - abstract
          (rewrite <- !functor_comp ;
           apply maponpaths ;
           exact p₁).
      - exact (HH₂ _ _ _ _ _ _ _ _ _ _ H).
    Defined.
  End Pullbacks.

  (**
   4. Initial objects
   *)
  Section InitialObject.
    Context (HF : preserves_initial F)
            (HG : preserves_initial G).

    Definition isInitial_iso_comma
               (x : iso_comma F G)
               (H₁ : isInitial C₁ (pr11 x))
               (H₂ : isInitial C₂ (pr21 x))
      : isInitial (iso_comma F G) x.
    Proof.
      intros w.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use eq_iso_comma_mor ;
           [ apply (@InitialArrowEq _ (make_Initial _ H₁))
           | apply (@InitialArrowEq _ (make_Initial _ H₂)) ]).
      - refine ((InitialArrow (_ ,, H₁) (pr11 w)
                 ,,
                 InitialArrow (_ ,, H₂) (pr21 w))
                ,,
                _).
        apply (@InitialArrowEq _ (make_Initial _ (HF _ H₁))).
    Defined.

    Definition initial_category_iso_comma
               (I₁ : Initial C₁)
               (I₂ : Initial C₂)
      : Initial (iso_comma F G).
    Proof.
      simple refine (_ ,, _).
      - refine ((pr1 I₁ ,, pr1 I₂) ,, _) ; cbn.
        exact (ziso_Initials
                 (make_Initial _ (HF _ (pr2 I₁)))
                 (make_Initial _ (HG _ (pr2 I₂)))).
      - apply isInitial_iso_comma.
        + exact (pr2 I₁).
        + exact (pr2 I₂).
    Defined.

    Definition iso_comma_pr1_preserves_initial
               (I₁ : Initial C₁)
               (I₂ : Initial C₂)
      : preserves_initial (iso_comma_pr1 F G).
    Proof.
      apply (preserves_initial_if_preserves_chosen
               (initial_category_iso_comma I₁ I₂)
               (iso_comma_pr1 F G)).
      exact (pr2 I₁).
    Defined.

    Definition iso_comma_pr2_preserves_initial
               (I₁ : Initial C₁)
               (I₂ : Initial C₂)
      : preserves_initial (iso_comma_pr2 F G).
    Proof.
      apply (preserves_initial_if_preserves_chosen
               (initial_category_iso_comma I₁ I₂)
               (iso_comma_pr2 F G)).
      exact (pr2 I₂).
    Defined.

    Definition iso_comma_ump1_preserves_initial
               {C₀ : category}
               (H₁ : C₀ ⟶ C₁)
               (HH₁ : preserves_initial H₁)
               (H₂ : C₀ ⟶ C₂)
               (HH₂ : preserves_initial H₂)
               (α : nat_z_iso (H₁ ∙ F) (H₂ ∙ G))
      : preserves_initial (iso_comma_ump1 F G H₁ H₂ α).
    Proof.
      intros x Hx.
      apply isInitial_iso_comma.
      - apply HH₁.
        exact Hx.
      - apply HH₂.
        exact Hx.
    Defined.
  End InitialObject.

  (**
   5. Coproducts
   *)
  Section Coproduct.
    Context (HF : preserves_bincoproduct F)
            (HG : preserves_bincoproduct G).

    Section IsCoproductInIsoComma.
      Context {x y z : iso_comma F G}
              (i₁ : x --> z)
              (i₂ : y --> z)
              (H₁ : isBinCoproduct _ (pr11 x) (pr11 y) (pr11 z) (pr11 i₁) (pr11 i₂))
              (H₂ : isBinCoproduct _ (pr21 x) (pr21 y) (pr21 z) (pr21 i₁) (pr21 i₂)).

      Let P₁ : BinCoproduct (pr11 x) (pr11 y) := make_BinCoproduct _ _ _ _ _ _ H₁.
      Let P₂ : BinCoproduct (pr21 x) (pr21 y) := make_BinCoproduct _ _ _ _ _ _ H₂.

      Section UMP.
        Context {w : iso_comma F G}
                (f : x --> w)
                (g : y --> w).

        Definition isBinCoproduct_in_iso_comma_unique
          : isaprop (∑ (fg : z --> w), i₁ · fg = f × i₂ · fg = g).
        Proof.
          use invproofirrelevance.
          intros φ₁ φ₂.
          use subtypePath.
          {
            intro.
            apply isapropdirprod ; apply homset_property.
          }
          use eq_iso_comma_mor.
          - use (BinCoproductArrowsEq _ _ _ P₁).
            + exact (maponpaths (λ z, pr11 z) (pr12 φ₁)
                     @ !(maponpaths (λ z, pr11 z) (pr12 φ₂))).
            + exact (maponpaths (λ z, pr11 z) (pr22 φ₁)
                     @ !(maponpaths (λ z, pr11 z) (pr22 φ₂))).
          - use (BinCoproductArrowsEq _ _ _ P₂).
            + exact (maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr12 φ₁)
                     @ !(maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr12 φ₂))).
            + exact (maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr22 φ₁)
                     @ !(maponpaths (λ z, dirprod_pr2 (pr1 z)) (pr22 φ₂))).
        Qed.

        Definition isBinCoproduct_in_iso_comma_ump
          : z --> w.
        Proof.
          simple refine ((_ ,, _) ,, _) ; cbn.
          - exact (BinCoproductArrow P₁ (pr11 f) (pr11 g)).
          - exact (BinCoproductArrow P₂ (pr21 f) (pr21 g)).
          - use (BinCoproductArrowsEq
                     _ _ _
                     (make_BinCoproduct _ _ _ _ _ _ (HF _ _ _ _ _ (pr2 P₁)))) ; cbn.
            + abstract
                (rewrite !assoc ;
                 rewrite <- functor_comp ;
                 rewrite (BinCoproductIn1Commutes _ _ _ P₁) ;
                 refine (pr2 f @ _) ;
                 refine (_ @ maponpaths (λ z, z · _) (!(pr2 i₁))) ;
                 rewrite !assoc' ;
                 apply maponpaths ;
                 rewrite <- functor_comp ;
                 apply maponpaths ;
                 refine (!_) ;
                 apply (BinCoproductIn1Commutes _ _ _ P₂)).
            + abstract
                (rewrite !assoc ;
                 rewrite <- functor_comp ;
                 rewrite (BinCoproductIn2Commutes _ _ _ P₁) ;
                 refine (pr2 g @ _) ;
                 refine (_ @ maponpaths (λ z, z · _) (!(pr2 i₂))) ;
                 rewrite !assoc' ;
                 apply maponpaths ;
                 rewrite <- functor_comp ;
                 apply maponpaths ;
                 refine (!_) ;
                 apply (BinCoproductIn2Commutes _ _ _ P₂)).
        Defined.

        Definition isBinCoproduct_in_iso_comma_ump_in1
          : i₁ · isBinCoproduct_in_iso_comma_ump = f.
        Proof.
          use eq_iso_comma_mor ; cbn.
          - apply (BinCoproductIn1Commutes _ _ _ P₁).
          - apply (BinCoproductIn1Commutes _ _ _ P₂).
        Qed.

        Definition isBinCoproduct_in_iso_comma_ump_in2
          : i₂ · isBinCoproduct_in_iso_comma_ump  = g.
        Proof.
          use eq_iso_comma_mor ; cbn.
          - apply (BinCoproductIn2Commutes _ _ _ P₁).
          - apply (BinCoproductIn2Commutes _ _ _ P₂).
        Qed.
      End UMP.

      Definition isBinCoproduct_in_iso_comma
        : isBinCoproduct (iso_comma F G) x y z i₁ i₂.
      Proof.
        intros w f g.
        use iscontraprop1.
        - exact (isBinCoproduct_in_iso_comma_unique f g).
        - simple refine (_ ,, _ ,, _).
          + exact (isBinCoproduct_in_iso_comma_ump f g).
          + exact (isBinCoproduct_in_iso_comma_ump_in1 f g).
          + exact (isBinCoproduct_in_iso_comma_ump_in2 f g).
      Defined.
    End IsCoproductInIsoComma.

    Definition bincoproducts_in_iso_comma
               (HC₁ : BinCoproducts C₁)
               (HC₂ : BinCoproducts C₂)
      : BinCoproducts (iso_comma F G).
    Proof.
      intros x y.
      pose (FP := make_BinCoproduct
                    _ _ _ _ _ _
                    (HF (pr11 x) (pr11 y)
                       _
                       (BinCoproductIn1 (HC₁ (pr11 x) (pr11 y)))
                       (BinCoproductIn2 (HC₁ (pr11 x) (pr11 y)))
                       (isBinCoproduct_BinCoproduct _ (HC₁ (pr11 x) (pr11 y))))).
      pose (GP := make_BinCoproduct
                    _ _ _ _ _ _
                    (HG (pr21 x) (pr21 y)
                       _
                       (BinCoproductIn1 (HC₂ (pr21 x) (pr21 y)))
                       (BinCoproductIn2 (HC₂ (pr21 x) (pr21 y)))
                       (isBinCoproduct_BinCoproduct _ (HC₂ (pr21 x) (pr21 y))))).
      use make_BinCoproduct.
      - simple refine ((_ ,, _) ,, _).
        + exact (BinCoproductObject (HC₁ (pr11 x) (pr11 y))).
        + exact (BinCoproductObject (HC₂ (pr21 x) (pr21 y))).
        + exact (bincoproduct_of_z_iso FP GP (pr2 x) (pr2 y)).
      - simple refine ((_ ,, _) ,, _).
        + exact (BinCoproductIn1 (HC₁ (pr11 x) (pr11 y))).
        + exact (BinCoproductIn1 (HC₂ (pr21 x) (pr21 y))).
        + exact ((BinCoproductOfArrowsIn1 _ FP GP (pr12 x) (pr12 y))).
      - simple refine ((_ ,, _) ,, _).
        + exact (BinCoproductIn2 (HC₁ (pr11 x) (pr11 y))).
        + exact (BinCoproductIn2 (HC₂ (pr21 x) (pr21 y))).
        + exact ((BinCoproductOfArrowsIn2 _ FP GP (pr12 x) (pr12 y))).
      -  use isBinCoproduct_in_iso_comma.
         + apply isBinCoproduct_BinCoproduct.
         + apply isBinCoproduct_BinCoproduct.
    Defined.

    Definition iso_comma_pr1_preserves_bincoproduct
               (HC₁ : BinCoproducts C₁)
               (HC₂ : BinCoproducts C₂)
      : preserves_bincoproduct (iso_comma_pr1 F G).
    Proof.
      use preserves_bincoproduct_if_preserves_chosen.
      - apply bincoproducts_in_iso_comma.
        + exact HC₁.
        + exact HC₂.
      - intros x y.
        cbn.
        apply isBinCoproduct_BinCoproduct.
    Defined.

    Definition iso_comma_pr2_preserves_bincoproduct
               (HC₁ : BinCoproducts C₁)
               (HC₂ : BinCoproducts C₂)
      : preserves_bincoproduct (iso_comma_pr2 F G).
    Proof.
      use preserves_bincoproduct_if_preserves_chosen.
      - apply bincoproducts_in_iso_comma.
        + exact HC₁.
        + exact HC₂.
      - intros x y.
        cbn.
        apply isBinCoproduct_BinCoproduct.
    Defined.

    Definition iso_comma_ump1_preserves_bincoproduct
               {C₀ : category}
               (H₁ : C₀ ⟶ C₁)
               (HH₁ : preserves_bincoproduct H₁)
               (H₂ : C₀ ⟶ C₂)
               (HH₂ : preserves_bincoproduct H₂)
               (α : nat_z_iso (H₁ ∙ F) (H₂ ∙ G))
      : preserves_bincoproduct (iso_comma_ump1 F G H₁ H₂ α).
    Proof.
      intros x y z π₁ π₂ Hx.
      apply isBinCoproduct_in_iso_comma.
      - apply HH₁.
        exact Hx.
      - apply HH₂.
        exact Hx.
    Defined.
  End Coproduct.
End IsoCommaLimits.
