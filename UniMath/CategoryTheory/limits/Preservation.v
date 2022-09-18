Require Import UniMath.Foundations.All.
(*********************************************************

 Preservation of (co)limits


 Content
 1. Preservation of terminal objects
 2. Preservation of binary products
 3. Preservation of pullbacks
 4. Preservation of initial objects
 5. Preservation of binary coproducts

 *********************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Local Open Scope cat.

(**
 1. Preservation of terminal objects
 *)
Definition preserves_terminal
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x : C₁), isTerminal C₁ x → isTerminal C₂ (F x).

Definition identity_preserves_terminal
           (C : category)
  : preserves_terminal (functor_identity C)
  := λ x Hx, Hx.

Definition composition_preserves_terminal
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (HF : preserves_terminal F)
           (HG : preserves_terminal G)
  : preserves_terminal (F ∙ G)
  := λ x Hx, HG _ (HF _ Hx).

Definition isaprop_preserves_terminal
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (preserves_terminal F).
Proof.
  repeat (use impred ; intro).
  use isapropiscontr.
Qed.

Definition preserves_chosen_terminal
           {C₁ C₂ : category}
           (HC₁ : Terminal C₁)
           (F : C₁ ⟶ C₂)
  : UU
  := isTerminal C₂ (F (TerminalObject HC₁)).

Definition preserves_terminal_if_preserves_chosen
           {C₁ C₂ : category}
           (HC₁ : Terminal C₁)
           (F : C₁ ⟶ C₂)
           (HF : preserves_chosen_terminal HC₁ F)
  : preserves_terminal F.
Proof.
  intros x Hx.
  exact (iso_to_Terminal
           (make_Terminal _ HF)
           _
           (functor_on_z_iso
              F
              (z_iso_Terminals HC₁ (make_Terminal _ Hx)))).
Defined.

(**
 2. Preservation of binary products
 *)
Definition preserves_binproduct
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y prod : C₁)
       (π₁ : prod --> x)
       (π₂ : prod --> y),
    isBinProduct C₁ x y prod π₁ π₂
    →
    isBinProduct C₂ (F x) (F y) (F prod) (#F π₁) (#F π₂).

Definition identity_preserves_binproduct
           (C : category)
  : preserves_binproduct (functor_identity C)
  := λ _ _ _ _ _ Hx, Hx.

Definition composition_preserves_binproduct
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (HF : preserves_binproduct F)
           (HG : preserves_binproduct G)
  : preserves_binproduct (F ∙ G).
Proof.
  intros ? ? ? ? ? Hx.
  apply HG.
  apply HF.
  exact Hx.
Defined.

Definition isaprop_preserves_binproduct
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (preserves_binproduct F).
Proof.
  repeat (use impred ; intro).
  use isapropiscontr.
Qed.

Definition preserves_chosen_binproduct
           {C₁ C₂ : category}
           (HC₁ : BinProducts C₁)
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y : C₁),
     isBinProduct
       C₂
       (F x) (F y)
       (F (BinProductObject C₁ (HC₁ x y)))
       (#F (BinProductPr1 C₁ (HC₁ x y)))
       (#F (BinProductPr2 C₁ (HC₁ x y))).

Definition preserves_binproduct_if_preserves_chosen
           {C₁ C₂ : category}
           (HC₁ : BinProducts C₁)
           (F : C₁ ⟶ C₂)
           (HF : preserves_chosen_binproduct HC₁ F)
  : preserves_binproduct F.
Proof.
  intros x y z π₁ π₂ Hxy.
  use (isBinProduct_eq_arrow
         _ _
         (pr2 (iso_to_BinProduct
                 _
                 (make_BinProduct _ _ _ _ _ _ (HF x y))
                 (z_iso_to_iso
                    (functor_on_z_iso
                       F
                       (iso_between_BinProduct
                          (make_BinProduct _ _ _ _ _ _ Hxy)
                          (HC₁ x y))))))) ; cbn.
  - abstract
      (rewrite <- functor_comp ;
       rewrite BinProductPr1Commutes ;
       apply idpath).
  - abstract
      (rewrite <- functor_comp ;
       rewrite BinProductPr2Commutes ;
       apply idpath).
Defined.

(**
 3. Preservation of pullbacks
 *)
Definition preserves_pullback
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y z pb : C₁)
       (f : x --> z)
       (g : y --> z)
       (π₁ : pb --> x)
       (π₂ : pb --> y)
       (q : π₁ · f = π₂ · g)
       (Fq : # F π₁ · # F f = # F π₂ · # F g),
    isPullback q
    →
    @isPullback C₂ _ _ _ _ (#F f) (#F g) (#F π₁) (#F π₂) Fq.

Definition identity_preserves_pullback
           (C : category)
  : preserves_pullback (functor_identity C).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  exact H.
Defined.

Definition composition_preserves_pullback
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (HF : preserves_pullback F)
           (HG : preserves_pullback G)
  : preserves_pullback (F ∙ G).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  use HG.
  - abstract
      (rewrite <- !functor_comp ;
       apply maponpaths ;
       exact q).
  - use HF.
    + exact q.
    + exact H.
Defined.

Definition isaprop_preserves_pullback
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (preserves_pullback F).
Proof.
  repeat (use impred ; intro).
  use isapropiscontr.
Qed.

Definition preserves_chosen_pullback
           {C₁ C₂ : category}
           (HC₁ : Pullbacks C₁)
           (F : C₁ ⟶ C₂)
  : UU.
Proof.
  refine (∏ (x y z : C₁)
            (f : x --> z)
            (g : y --> z),
          @isPullback
            C₂
            (F z) (F x) (F y)
            (F (PullbackObject (HC₁ _ _ _ f g)))
            (#F f)
            (#F g)
            (#F (PullbackPr1 (HC₁ _ _ _ f g)))
            (#F (PullbackPr2 (HC₁ _ _ _ f g)))
            _).
  abstract
    (rewrite <- !functor_comp ;
     apply maponpaths ;
     apply PullbackSqrCommutes).
Defined.

Definition preserves_pullback_if_preserves_chosen
           {C₁ C₂ : category}
           (HC₁ : Pullbacks C₁)
           (F : C₁ ⟶ C₂)
           (HF : preserves_chosen_pullback HC₁ F)
  : preserves_pullback F.
Proof.
  intros x y z pb f g π₁ π₂ p Hxy Hpb.
  apply (isPullback_z_iso
           _
           _
           (HF x y z f g)
           (functor_on_z_iso
              F
              (z_iso_from_Pullback_to_Pullback
                 (HC₁ _ _ _ f g)
                 (make_Pullback _ Hpb)))).
  - abstract
      (cbn ;
       rewrite <- !functor_comp ;
       apply maponpaths ;
       apply (PullbackArrow_PullbackPr1 (make_Pullback p Hpb))).
  - abstract
      (cbn ;
       rewrite <- !functor_comp ;
       apply maponpaths ;
       apply (PullbackArrow_PullbackPr2 (make_Pullback p Hpb))).
Defined.

(**
 4. Preservation of initial objects
 *)
Definition preserves_initial
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x : C₁), isInitial C₁ x → isInitial C₂ (F x).

Definition identity_preserves_initial
           (C : category)
  : preserves_initial (functor_identity C)
  := λ x Hx, Hx.

Definition composition_preserves_initial
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (HF : preserves_initial F)
           (HG : preserves_initial G)
  : preserves_initial (F ∙ G)
  := λ x Hx, HG _ (HF _ Hx).

Definition isaprop_preserves_initial
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (preserves_initial F).
Proof.
  repeat (use impred ; intro).
  use isapropiscontr.
Qed.

Definition preserves_chosen_initial
           {C₁ C₂ : category}
           (HC₁ : Initial C₁)
           (F : C₁ ⟶ C₂)
  : UU
  := isInitial C₂ (F (InitialObject HC₁)).

Definition preserves_initial_if_preserves_chosen
           {C₁ C₂ : category}
           (HC₁ : Initial C₁)
           (F : C₁ ⟶ C₂)
           (HF : preserves_chosen_initial HC₁ F)
  : preserves_initial F.
Proof.
  intros x Hx.
  exact (iso_to_Initial
           (make_Initial _ HF)
           _
           (functor_on_z_iso
              F
              (ziso_Initials HC₁ (make_Initial _ Hx)))).
Defined.

(**
 5. Preservation of binary coproducts
 *)
Definition preserves_bincoproduct
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y sum : C₁)
       (ι₁ : x --> sum)
       (ι₂ : y --> sum),
    isBinCoproduct C₁ x y sum ι₁ ι₂
    →
    isBinCoproduct C₂ (F x) (F y) (F sum) (#F ι₁) (#F ι₂).

Definition identity_preserves_bincoproduct
           (C : category)
  : preserves_bincoproduct (functor_identity C)
  := λ _ _ _ _ _ Hx, Hx.

Definition composition_preserves_bincoproduct
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (HF : preserves_bincoproduct F)
           (HG : preserves_bincoproduct G)
  : preserves_bincoproduct (F ∙ G).
Proof.
  intros ? ? ? ? ? Hx.
  apply HG.
  apply HF.
  exact Hx.
Defined.

Definition isaprop_preserves_bincoproduct
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (preserves_bincoproduct F).
Proof.
  repeat (use impred ; intro).
  use isapropiscontr.
Qed.

Definition preserves_chosen_bincoproduct
           {C₁ C₂ : category}
           (HC₁ : BinCoproducts C₁)
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y : C₁),
     isBinCoproduct
       C₂
       (F x) (F y)
       (F (BinCoproductObject (HC₁ x y)))
       (#F (BinCoproductIn1 (HC₁ x y)))
       (#F (BinCoproductIn2 (HC₁ x y))).

Definition preserves_bincoproduct_if_preserves_chosen
           {C₁ C₂ : category}
           (HC₁ : BinCoproducts C₁)
           (F : C₁ ⟶ C₂)
           (HF : preserves_chosen_bincoproduct HC₁ F)
  : preserves_bincoproduct F.
Proof.
  intros x y z ι₁ ι₂ Hxy.
  use (isBinCoproduct_eq_arrow
         _ _
         (z_iso_to_isBinCoproduct
            _
            (make_BinCoproduct _ _ _ _ _ _ (HF x y))
            (functor_on_z_iso
               F
               (z_iso_from_BinCoproduct_to_BinCoproduct
                  _
                  (make_BinCoproduct _ _ _ _ _ _ Hxy)
                  (HC₁ x y))))) ; cbn.
  - abstract
      (rewrite <- functor_comp ;
       apply maponpaths ;
       apply BinCoproductIn1Commutes).
  - abstract
      (rewrite <- functor_comp ;
       apply maponpaths ;
       apply BinCoproductIn2Commutes).
Defined.
