(************************************************************************

 Limits and colimits in the unit category

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
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.

Local Open Scope cat.

(**
 1. Terminal objects
 *)
Section TerminalProduct.
  Context {C₁ C₂ : category}.

  Definition isTerminal_category_binproduct
             (x : category_binproduct C₁ C₂)
             (H₁ : isTerminal C₁ (pr1 x))
             (H₂ : isTerminal C₂ (pr2 x))
    : isTerminal (category_binproduct C₁ C₂) x.
  Proof.
    intros w.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use pathsdirprod ;
         [ exact (TerminalArrowUnique (_ ,, H₁) _ _ @ !(TerminalArrowUnique (_ ,, H₁) _ _))
         | exact (TerminalArrowUnique (_ ,, H₂) _ _ @ !(TerminalArrowUnique (_ ,, H₂) _ _))
         ]).
    - exact (TerminalArrow (_ ,, H₁) (pr1 w)
             ,,
             TerminalArrow (_ ,, H₂) (pr2 w)).
  Defined.

  Definition terminal_category_binproduct
             (T₁ : Terminal C₁)
             (T₂ : Terminal C₂)
    : Terminal (category_binproduct C₁ C₂)
    := (pr1 T₁ ,, pr1 T₂) ,, isTerminal_category_binproduct (_ ,, _) (pr2 T₁) (pr2 T₂).
End TerminalProduct.

Definition pr1_preserves_terminal
           (C₁ C₂ : category)
  : preserves_terminal (pr1_functor C₁ C₂).
Proof.
  intros x Hx w.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       refine (maponpaths
                 pr1
                 (TerminalArrowUnique
                    (x ,, Hx)
                    (w ,, pr2 x)
                    (φ₁ ,, identity _))
               @ !_) ;
       exact (maponpaths
                pr1
                (TerminalArrowUnique
                   (x ,, Hx)
                   (w ,, pr2 x)
                   (φ₂ ,, identity _)))).
  - exact (pr1 (TerminalArrow (_ ,, Hx) (w ,, pr2 x))).
Defined.

Definition pr2_preserves_terminal
           (C₁ C₂ : category)
  : preserves_terminal (pr2_functor C₁ C₂).
Proof.
  intros x Hx w.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       refine (maponpaths
                 dirprod_pr2
                 (TerminalArrowUnique
                    (x ,, Hx)
                    (pr1 x ,, w)
                    (identity _ ,, φ₁))
                 @ !_) ;
       exact (maponpaths
                 dirprod_pr2
                 (TerminalArrowUnique
                    (x ,, Hx)
                    (pr1 x ,, w)
                    (identity _ ,, φ₂)))).
  - exact (pr2 (TerminalArrow (_ ,, Hx) (pr1 x ,, w))).
Defined.

Definition preserves_terminal_bindelta_pair_functor
           {C D₁ D₂ : category}
           {F : C ⟶ D₁}
           {G : C ⟶ D₂}
           (HF : preserves_terminal F)
           (HG : preserves_terminal G)
  : preserves_terminal
      (bindelta_pair_functor F G).
Proof.
  intros x Hx.
  apply isTerminal_category_binproduct.
  - apply HF.
    apply Hx.
  - apply HG.
    apply Hx.
Defined.

(**
 2. Products
 *)
Section BinProductInProduct.
  Context {C₁ C₂ : category}.

  Definition isBinProduct_in_product_category
             {x y z : category_binproduct C₁ C₂}
             (p₁ : z --> x)
             (p₂ : z --> y)
             (H₁ : isBinProduct _ (pr1 x) (pr1 y) (pr1 z) (pr1 p₁) (pr1 p₂))
             (H₂ : isBinProduct _ (pr2 x) (pr2 y) (pr2 z) (pr2 p₁) (pr2 p₂))
    : isBinProduct _ x y z p₁ p₂.
  Proof.
    pose (P₁ := make_BinProduct _ _ _ _ _ _ H₁).
    pose (P₂ := make_BinProduct _ _ _ _ _ _ H₂).
    intros w f g.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use pathsdirprod ;
         [ exact (BinProductArrowsEq
                    _ _ _
                    P₁
                    _ _ _
                    (maponpaths pr1 (pr12 φ₁)
                     @ !(maponpaths pr1 (pr12 φ₂)))
                    (maponpaths pr1 (pr22 φ₁)
                     @ !(maponpaths pr1 (pr22 φ₂))))
         | exact (BinProductArrowsEq
                    _ _ _
                    P₂
                    _ _ _
                    (maponpaths dirprod_pr2 (pr12 φ₁)
                     @ !(maponpaths dirprod_pr2 (pr12 φ₂)))
                    (maponpaths dirprod_pr2 (pr22 φ₁)
                     @ !(maponpaths dirprod_pr2 (pr22 φ₂)))) ]).
    - simple refine ((_ ,, _) ,, _ ,, _).
      + exact (BinProductArrow _ P₁ (pr1 f) (pr1 g)).
      + exact (BinProductArrow _ P₂ (pr2 f) (pr2 g)).
      + abstract
          (use pathsdirprod ;
           [ apply (BinProductPr1Commutes _ _ _ P₁)
           | apply (BinProductPr1Commutes _ _ _ P₂)]).
      + abstract
          (use pathsdirprod ;
           [ apply (BinProductPr2Commutes _ _ _ P₁)
           | apply (BinProductPr2Commutes _ _ _ P₂)]).
  Defined.

  Definition binproducts_in_product_category
             (HC₁ : BinProducts C₁)
             (HC₂ : BinProducts C₂)
    : BinProducts (category_binproduct C₁ C₂).
  Proof.
    intros x y.
    use make_BinProduct.
    - simple refine (_ ,, _).
      + exact (BinProductObject _ (HC₁ (pr1 x) (pr1 y))).
      + exact (BinProductObject _ (HC₂ (pr2 x) (pr2 y))).
    - simple refine (_ ,, _).
      + exact (BinProductPr1 _ (HC₁ (pr1 x) (pr1 y))).
      + exact (BinProductPr1 _ (HC₂ (pr2 x) (pr2 y))).
    - simple refine (_ ,, _).
      + exact (BinProductPr2 _ (HC₁ (pr1 x) (pr1 y))).
      + exact (BinProductPr2 _ (HC₂ (pr2 x) (pr2 y))).
    -  use isBinProduct_in_product_category.
       + apply isBinProduct_BinProduct.
       + apply isBinProduct_BinProduct.
  Defined.
End BinProductInProduct.

Definition pr1_preserves_binproduct
           {C₁ C₂ : category}
           (HC₁ : BinProducts C₁)
           (HC₂ : BinProducts C₂)
  : preserves_binproduct (pr1_functor C₁ C₂).
Proof.
  use preserves_binproduct_if_preserves_chosen.
  - apply binproducts_in_product_category.
    + exact HC₁.
    + exact HC₂.
  - intros x y.
    apply isBinProduct_BinProduct.
Defined.

Definition pr2_preserves_binproduct
           {C₁ C₂ : category}
           (HC₁ : BinProducts C₁)
           (HC₂ : BinProducts C₂)
  : preserves_binproduct (pr2_functor C₁ C₂).
Proof.
  use preserves_binproduct_if_preserves_chosen.
  - apply binproducts_in_product_category.
    + exact HC₁.
    + exact HC₂.
  - intros x y.
    apply isBinProduct_BinProduct.
Defined.

Definition preserves_binproduct_bindelta_pair_functor
           {C D₁ D₂ : category}
           {F : C ⟶ D₁}
           {G : C ⟶ D₂}
           (HF : preserves_binproduct F)
           (HG : preserves_binproduct G)
  : preserves_binproduct
      (bindelta_pair_functor F G).
Proof.
  intros x y z π₁ π₂ H.
  apply isBinProduct_in_product_category.
  - apply HF.
    apply H.
  - apply HG.
    apply H.
Defined.

(**
 3. Pullbacks
 *)
Section PullbackInProduct.
  Context {C₁ C₂ : category}.

  Section PullbackInProductCategoryUMP.
    Context {w x y z : category_binproduct C₁ C₂}
            {f : x --> z}
            {g : y --> z}
            (π₁ : w --> x)
            (π₂ : w --> y)
            (p : π₁ · f = π₂ · g)
            (H₁ : isPullback (maponpaths pr1 p))
            (H₂ : isPullback (maponpaths dirprod_pr2 p))
            {q : category_binproduct C₁ C₂}
            (h₁ : q --> x)
            (h₂ : q --> y)
            (r : h₁ · f = h₂ · g).

    Let P₁ : Pullback (pr1 f) (pr1 g) := make_Pullback _ H₁.
    Let P₂ : Pullback (pr2 f) (pr2 g) := make_Pullback _ H₂.

    Definition isPullback_in_product_category_unique
      : isaprop (∑ (hk : q --> w), hk · π₁ = h₁ × hk · π₂ = h₂).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use pathsdirprod.
      - use (MorphismsIntoPullbackEqual (pr22 P₁)).
        + exact (maponpaths pr1 (pr12 φ₁) @ !(maponpaths pr1 (pr12 φ₂))).
        + exact (maponpaths pr1 (pr22 φ₁) @ !(maponpaths pr1 (pr22 φ₂))).
      - use (MorphismsIntoPullbackEqual (pr22 P₂)).
        + exact (maponpaths dirprod_pr2 (pr12 φ₁)
                 @ !(maponpaths dirprod_pr2 (pr12 φ₂))).
        + exact (maponpaths dirprod_pr2 (pr22 φ₁)
                 @ !(maponpaths dirprod_pr2 (pr22 φ₂))).
    Qed.

    Definition isPullback_in_product_category_mor
      : q --> w
      := PullbackArrow P₁ _ (pr1 h₁) (pr1 h₂) (maponpaths pr1 r)
         ,,
         PullbackArrow P₂ _ (pr2 h₁) (pr2 h₂) (maponpaths dirprod_pr2 r).

    Definition isPullback_in_product_category_mor_pr1
      : isPullback_in_product_category_mor · π₁ = h₁.
    Proof.
      use pathsdirprod ; cbn.
      - apply (PullbackArrow_PullbackPr1 P₁).
      - apply (PullbackArrow_PullbackPr1 P₂).
    Qed.

    Definition isPullback_in_product_category_mor_pr2
      : isPullback_in_product_category_mor · π₂ = h₂.
    Proof.
      use pathsdirprod ; cbn.
      - apply (PullbackArrow_PullbackPr2 P₁).
      - apply (PullbackArrow_PullbackPr2 P₂).
    Qed.
  End PullbackInProductCategoryUMP.

  Definition isPullback_in_product_category
             {w x y z : category_binproduct C₁ C₂}
             {f : x --> z}
             {g : y --> z}
             (π₁ : w --> x)
             (π₂ : w --> y)
             (p : π₁ · f = π₂ · g)
             (H₁ : isPullback (maponpaths pr1 p))
             (H₂ : isPullback (maponpaths dirprod_pr2 p))
    : isPullback p.
  Proof.
    intros q h₁ h₂ r.
    use iscontraprop1.
    - exact (isPullback_in_product_category_unique π₁ π₂ p H₁ H₂ h₁ h₂).
    - simple refine (_ ,, _ ,, _).
      + exact (isPullback_in_product_category_mor π₁ π₂ p H₁ H₂ h₁ h₂ r).
      + apply isPullback_in_product_category_mor_pr1.
      + apply isPullback_in_product_category_mor_pr2.
  Defined.

  Definition pullbacks_in_product_category
             (HC₁ : Pullbacks C₁)
             (HC₂ : Pullbacks C₂)
    : Pullbacks (category_binproduct C₁ C₂).
  Proof.
    intros z x y f g.
    simple refine ((_ ,, _ ,, _) ,, (_ ,, _)).
    - refine (_ ,, _).
      + exact (PullbackObject (HC₁ _ _ _ (pr1 f) (pr1 g))).
      + exact (PullbackObject (HC₂ _ _ _ (pr2 f) (pr2 g))).
    - refine (_ ,, _).
      + apply PullbackPr1.
      + apply PullbackPr1.
    - refine (_ ,, _).
      + apply PullbackPr2.
      + apply PullbackPr2.
    - apply pathsdirprod.
      + apply PullbackSqrCommutes.
      + apply PullbackSqrCommutes.
    - use isPullback_in_product_category.
      + apply isPullback_Pullback.
      + apply isPullback_Pullback.
  Defined.
End PullbackInProduct.

Definition pr1_preserves_pullback
           {C₁ C₂ : category}
           (HC₁ : Pullbacks C₁)
           (HC₂ : Pullbacks C₂)
  : preserves_pullback (pr1_functor C₁ C₂).
Proof.
  use preserves_pullback_if_preserves_chosen.
  - apply pullbacks_in_product_category.
    + exact HC₁.
    + exact HC₂.
  - intros x y z f g.
    apply isPullback_Pullback.
Defined.

Definition pr2_preserves_pullback
           {C₁ C₂ : category}
           (HC₁ : Pullbacks C₁)
           (HC₂ : Pullbacks C₂)
  : preserves_pullback (pr2_functor C₁ C₂).
Proof.
  use preserves_pullback_if_preserves_chosen.
  - apply pullbacks_in_product_category.
    + exact HC₁.
    + exact HC₂.
  - intros x y z f g.
    apply isPullback_Pullback.
Defined.

Definition preserves_pullback_bindelta_pair_functor
           {C D₁ D₂ : category}
           {F : C ⟶ D₁}
           {G : C ⟶ D₂}
           (HF : preserves_pullback F)
           (HG : preserves_pullback G)
  : preserves_pullback
      (bindelta_pair_functor F G).
Proof.
  intros w x y z f g π₁ π₂ p₁ p₂ H.
  apply isPullback_in_product_category.
  - exact (HF _ _ _ _ _ _ _ _ _ _ H).
  - exact (HG _ _ _ _ _ _ _ _ _ _ H).
Defined.

(**
 4. Initial objects
 *)
Section InitialProduct.
  Context {C₁ C₂ : category}.

  Definition isInitial_category_binproduct
             (x : category_binproduct C₁ C₂)
             (H₁ : isInitial C₁ (pr1 x))
             (H₂ : isInitial C₂ (pr2 x))
    : isInitial (category_binproduct C₁ C₂) x.
  Proof.
    intros w.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use pathsdirprod ;
         [ exact (InitialArrowUnique (_ ,, H₁) _ _ @ !(InitialArrowUnique (_ ,, H₁) _ _))
         | exact (InitialArrowUnique (_ ,, H₂) _ _ @ !(InitialArrowUnique (_ ,, H₂) _ _))
         ]).
    - exact (InitialArrow (_ ,, H₁) (pr1 w)
             ,,
             InitialArrow (_ ,, H₂) (pr2 w)).
  Defined.

  Definition initial_category_binproduct
             (I₁ : Initial C₁)
             (I₂ : Initial C₂)
    : Initial (category_binproduct C₁ C₂)
    := (pr1 I₁ ,, pr1 I₂) ,, isInitial_category_binproduct (_ ,, _) (pr2 I₁) (pr2 I₂).
End InitialProduct.

Definition pr1_preserves_initial
           (C₁ C₂ : category)
  : preserves_initial (pr1_functor C₁ C₂).
Proof.
  intros x Hx w.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       refine (maponpaths
                 pr1
                 (InitialArrowUnique
                    (x ,, Hx)
                    (w ,, pr2 x)
                    (φ₁ ,, identity _))
               @ !_) ;
       exact (maponpaths
                pr1
                (InitialArrowUnique
                   (x ,, Hx)
                   (w ,, pr2 x)
                   (φ₂ ,, identity _)))).
  - exact (pr1 (InitialArrow (_ ,, Hx) (w ,, pr2 x))).
Defined.

Definition pr2_preserves_initial
           (C₁ C₂ : category)
  : preserves_initial (pr2_functor C₁ C₂).
Proof.
  intros x Hx w.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       refine (maponpaths
                 dirprod_pr2
                 (InitialArrowUnique
                    (x ,, Hx)
                    (pr1 x ,, w)
                    (identity _ ,, φ₁))
                 @ !_) ;
       exact (maponpaths
                 dirprod_pr2
                 (InitialArrowUnique
                    (x ,, Hx)
                    (pr1 x ,, w)
                    (identity _ ,, φ₂)))).
  - exact (pr2 (InitialArrow (_ ,, Hx) (pr1 x ,, w))).
Defined.

Definition preserves_initial_bindelta_pair_functor
           {C D₁ D₂ : category}
           {F : C ⟶ D₁}
           {G : C ⟶ D₂}
           (HF : preserves_initial F)
           (HG : preserves_initial G)
  : preserves_initial
      (bindelta_pair_functor F G).
Proof.
  intros x Hx.
  apply isInitial_category_binproduct.
  - apply HF.
    apply Hx.
  - apply HG.
    apply Hx.
Defined.

(**
 5. Coproducts
 *)
Section BinCoproductInProduct.
  Context {C₁ C₂ : category}.

  Definition isBinCoproduct_in_product_category
             {x y z : category_binproduct C₁ C₂}
             (i₁ : x --> z)
             (i₂ : y --> z)
             (H₁ : isBinCoproduct _ (pr1 x) (pr1 y) (pr1 z) (pr1 i₁) (pr1 i₂))
             (H₂ : isBinCoproduct _ (pr2 x) (pr2 y) (pr2 z) (pr2 i₁) (pr2 i₂))
    : isBinCoproduct _ x y z i₁ i₂.
  Proof.
    pose (P₁ := make_BinCoproduct _ _ _ _ _ _ H₁).
    pose (P₂ := make_BinCoproduct _ _ _ _ _ _ H₂).
    intros w f g.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use pathsdirprod ;
         [ exact (BinCoproductArrowsEq
                    _ _ _
                    P₁
                    _ _ _
                    (maponpaths pr1 (pr12 φ₁)
                     @ !(maponpaths pr1 (pr12 φ₂)))
                    (maponpaths pr1 (pr22 φ₁)
                     @ !(maponpaths pr1 (pr22 φ₂))))
         | exact (BinCoproductArrowsEq
                    _ _ _
                    P₂
                    _ _ _
                    (maponpaths dirprod_pr2 (pr12 φ₁)
                     @ !(maponpaths dirprod_pr2 (pr12 φ₂)))
                    (maponpaths dirprod_pr2 (pr22 φ₁)
                     @ !(maponpaths dirprod_pr2 (pr22 φ₂)))) ]).
    - simple refine ((_ ,, _) ,, _ ,, _).
      + exact (BinCoproductArrow P₁ (pr1 f) (pr1 g)).
      + exact (BinCoproductArrow P₂ (pr2 f) (pr2 g)).
      + abstract
          (use pathsdirprod ;
           [ apply (BinCoproductIn1Commutes _ _ _ P₁)
           | apply (BinCoproductIn1Commutes _ _ _ P₂)]).
      + abstract
          (use pathsdirprod ;
           [ apply (BinCoproductIn2Commutes _ _ _ P₁)
           | apply (BinCoproductIn2Commutes _ _ _ P₂)]).
  Defined.

  Definition bincoproducts_in_product_category
             (HC₁ : BinCoproducts C₁)
             (HC₂ : BinCoproducts C₂)
    : BinCoproducts (category_binproduct C₁ C₂).
  Proof.
    intros x y.
    use make_BinCoproduct.
    - simple refine (_ ,, _).
      + exact (BinCoproductObject (HC₁ (pr1 x) (pr1 y))).
      + exact (BinCoproductObject (HC₂ (pr2 x) (pr2 y))).
    - simple refine (_ ,, _).
      + exact (BinCoproductIn1 (HC₁ (pr1 x) (pr1 y))).
      + exact (BinCoproductIn1 (HC₂ (pr2 x) (pr2 y))).
    - simple refine (_ ,, _).
      + exact (BinCoproductIn2 (HC₁ (pr1 x) (pr1 y))).
      + exact (BinCoproductIn2 (HC₂ (pr2 x) (pr2 y))).
    -  use isBinCoproduct_in_product_category.
       + apply isBinCoproduct_BinCoproduct.
       + apply isBinCoproduct_BinCoproduct.
  Defined.
End BinCoproductInProduct.

Definition pr1_preserves_bincoproduct
           {C₁ C₂ : category}
           (HC₁ : BinCoproducts C₁)
           (HC₂ : BinCoproducts C₂)
  : preserves_bincoproduct (pr1_functor C₁ C₂).
Proof.
  use preserves_bincoproduct_if_preserves_chosen.
  - apply bincoproducts_in_product_category.
    + exact HC₁.
    + exact HC₂.
  - intros x y.
    apply isBinCoproduct_BinCoproduct.
Defined.

Definition pr2_preserves_bincoproduct
           {C₁ C₂ : category}
           (HC₁ : BinCoproducts C₁)
           (HC₂ : BinCoproducts C₂)
  : preserves_bincoproduct (pr2_functor C₁ C₂).
Proof.
  use preserves_bincoproduct_if_preserves_chosen.
  - apply bincoproducts_in_product_category.
    + exact HC₁.
    + exact HC₂.
  - intros x y.
    apply isBinCoproduct_BinCoproduct.
Defined.

Definition preserves_bincoproduct_bindelta_pair_functor
           {C D₁ D₂ : category}
           {F : C ⟶ D₁}
           {G : C ⟶ D₂}
           (HF : preserves_bincoproduct F)
           (HG : preserves_bincoproduct G)
  : preserves_bincoproduct
      (bindelta_pair_functor F G).
Proof.
  intros x y z π₁ π₂ H.
  apply isBinCoproduct_in_product_category.
  - apply HF.
    apply H.
  - apply HG.
    apply H.
Defined.
