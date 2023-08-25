(*********************************************************

 Preservation of (co)limits

 Content
 1. Preservation of terminal objects
 2. Preservation of binary products
 3. Preservation of pullbacks
 4. Preservation of initial objects
 5. Preservation of binary coproducts
 6. Preservation of (reflexive) coequalizers
 7. Preservation of coproducts
 8. Adjunctions and preservation
 8.1 Right adjoints preserve limits
 8.2 Left adjoints preserve colimits

 *********************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

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

Definition preserves_chosen_terminal_eq
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (T₁ : Terminal C₁)
           (T₂ : Terminal C₂)
  : UU
  := ∥ F T₁ = T₂ ∥.

Proposition identity_preserves_chosen_terminal_eq
            {C : category}
            (T : Terminal C)
  : preserves_chosen_terminal_eq (functor_identity C) T T.
Proof.
  apply hinhpr.
  apply idpath.
Qed.

Proposition composition_preserves_chosen_terminal_eq
            {C₁ C₂ C₃ : category}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            {T₃ : Terminal C₃}
            (HF : preserves_chosen_terminal_eq F T₁ T₂)
            (HG : preserves_chosen_terminal_eq G T₂ T₃)
  : preserves_chosen_terminal_eq (F ∙ G) T₁ T₃.
Proof.
  revert HF.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro p.
  revert HG.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro q.
  cbn.
  apply hinhpr.
  rewrite p, q.
  apply idpath.
Qed.

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

(**
 6. Preservation of (reflexive) coequalizers
 *)
Definition preserves_coequalizer
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y c : C₁)
       (f g : x --> y)
       (h : y --> c)
       (p : f · h = g · h)
       (Fp : #F f · #F h = #F g · #F h),
     isCoequalizer f g h p
     →
     isCoequalizer (#F f) (#F g) (#F h) Fp.

Definition identity_preserves_coequalizer
           (C : category)
  : preserves_coequalizer (functor_identity C)
  := λ _ _ _ _ _ _ _ _ Hx, Hx.

Definition composition_preserves_coequalizer
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (HF : preserves_coequalizer F)
           (HG : preserves_coequalizer G)
  : preserves_coequalizer (F ∙ G).
Proof.
  intros ? ? ? ? ? ? ? ? Hx.
  use HG.
  - abstract
      (rewrite <- !functor_comp ;
       rewrite p ;
       apply idpath).
  - use HF.
    + exact p.
    + exact Hx.
Defined.

Definition isaprop_preserves_coequalizer
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (preserves_coequalizer F).
Proof.
  repeat (use impred ; intro).
  use isapropiscontr.
Qed.

Definition preserves_chosen_coequalizer
           {C₁ C₂ : category}
           (HC₁ : Coequalizers C₁)
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y : C₁)
       (f g : x --> y)
       (p : # F f · # F (CoequalizerArrow (HC₁ x y f g))
            =
            # F g · # F (CoequalizerArrow (HC₁ x y f g))),
     isCoequalizer
       (#F f)
       (#F g)
       (#F (CoequalizerArrow (HC₁ x y f g)))
       p.

Definition preserves_coequalizer_if_preserves_chosen
           {C₁ C₂ : category}
           (HC₁ : Coequalizers C₁)
           (F : C₁ ⟶ C₂)
           (HF : preserves_chosen_coequalizer HC₁ F)
  : preserves_coequalizer F.
Proof.
  intros x y c f g h p Fp Hz.
  use (Coequalizer_eq_ar
            _
            _
            _
            (pr22 (z_iso_to_Coequalizer
                     (make_Coequalizer _ _ _ _ (HF x y f g _))
                     (z_iso_inv
                        (functor_on_z_iso
                           F
                           (z_iso_between_Coequalizer
                              (make_Coequalizer _ _ _ _ Hz)
                              (HC₁ x y f g))))))) ; cbn.
  - abstract
      (rewrite <- !functor_comp ;
       rewrite CoequalizerCommutes ;
       apply idpath).
  - abstract
      (rewrite <- !functor_comp ;
       rewrite CoequalizerEqAr ;
       apply idpath).
Defined.

Definition preserves_reflexive_coequalizer
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y c : C₁)
       (f g : x --> y)
       (s : y --> x)
       (pf : s · f = identity _)
       (pg : s · g = identity _)
       (h : y --> c)
       (p : f · h = g · h)
       (Fp : #F f · #F h = #F g · #F h),
     isCoequalizer f g h p
     →
     isCoequalizer (#F f) (#F g) (#F h) Fp.

Definition identity_preserves_reflexive_coequalizer
           (C : category)
  : preserves_coequalizer (functor_identity C)
  := λ _ _ _ _ _ _ _ _ Hx, Hx.

Definition composition_preserves_reflexive_coequalizer
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (HF : preserves_reflexive_coequalizer F)
           (HG : preserves_reflexive_coequalizer G)
  : preserves_reflexive_coequalizer (F ∙ G).
Proof.
  intros x y c f g s pf pg h p Fp Hx.
  use (HG (F x) (F y) (F c) (#F f) (#F g) (#F s) _ _ (#F h)).
  - abstract
      (rewrite <- functor_comp ;
       rewrite pf ;
       apply functor_id).
  - abstract
      (rewrite <- functor_comp ;
       rewrite pg ;
       apply functor_id).
  - abstract
      (rewrite <- !functor_comp ;
       rewrite p ;
       apply idpath).
  - use (HF x y c f g s _ _ h).
    + exact pf.
    + exact pg.
    + exact p.
    + exact Hx.
Defined.

Definition isaprop_preserves_reflexive_coequalizer
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (preserves_reflexive_coequalizer F).
Proof.
  repeat (use impred ; intro).
  use isapropiscontr.
Qed.

Definition preserves_chosen_reflexive_coequalizer
           {C₁ C₂ : category}
           (HC₁ : reflexive_coequalizers C₁)
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y : C₁)
       (f g : x --> y)
       (s : y --> x)
       (pf : s · f = identity _)
       (pg : s · g = identity _)
       (p : # F f · # F (CoequalizerArrow (HC₁ x y f g s pf pg))
            =
            # F g · # F (CoequalizerArrow (HC₁ x y f g s pf pg))),
     isCoequalizer
       (#F f)
       (#F g)
       (#F (CoequalizerArrow (HC₁ x y f g s pf pg)))
       p.

Definition preserves_reflexive_coequalizers_if_chosen
           {C₁ C₂ : category}
           (HC₁ : reflexive_coequalizers C₁)
           (F : C₁ ⟶ C₂)
           (HF : preserves_chosen_reflexive_coequalizer HC₁ F)
  : preserves_reflexive_coequalizer F.
Proof.
  intros x y c f g s pf pg h p Fp Hz.
  use (Coequalizer_eq_ar
            _
            _
            _
            (pr22 (z_iso_to_Coequalizer
                     (make_Coequalizer _ _ _ _ (HF x y f g s pf pg _))
                     (z_iso_inv
                        (functor_on_z_iso
                           F
                           (z_iso_between_Coequalizer
                              (make_Coequalizer _ _ _ _ Hz)
                              (HC₁ x y f g s pf pg))))))) ; cbn.
  - abstract
      (rewrite <- !functor_comp ;
       rewrite CoequalizerCommutes ;
       apply idpath).
  - abstract
      (rewrite <- !functor_comp ;
       rewrite CoequalizerEqAr ;
       apply idpath).
Defined.

(**
 7. Preservation of coproducts
 *)
Definition preserves_coproduct
           (J : UU)
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (D : J → C₁)
       (c : C₁)
       (ι : ∏ (j : J), D j --> c),
     isCoproduct J C₁ D c ι
     →
     isCoproduct J C₂ (λ j, F (D j)) (F c) (λ j, #F (ι j)).

Definition identity_preserves_coproduct
           (C : category)
           (J : UU)
  : preserves_coproduct J (functor_identity C)
  := λ _ _ _ Hx, Hx.

Definition composition_preserves_coproduct
           (J : UU)
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           (HF : preserves_coproduct J F)
           (HG : preserves_coproduct J G)
  : preserves_coproduct J (F ∙ G).
Proof.
  intros ? ? ? Hx.
  apply HG.
  apply HF.
  exact Hx.
Defined.

Definition isaprop_preserves_coproduct
           (J : UU)
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (preserves_coproduct J F).
Proof.
  repeat (use impred ; intro).
  use isapropiscontr.
Qed.

Definition preserves_chosen_coproduct
           (J : UU)
           {C₁ C₂ : category}
           (HC₁ : Coproducts J C₁)
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (D : J → C₁),
     isCoproduct
       J
       C₂
       (λ j, F(D j))
       (F (HC₁ D))
       (λ j, #F (CoproductIn _ _ (HC₁ D) j)).

(**
 8. Adjunctions and preservation
 *)
Section AdjunctionPreservation.
  Context {C₁ C₂ : category}
          (L : C₁ ⟶ C₂)
          (HL : is_left_adjoint L).

  Let R : C₂ ⟶ C₁ := right_adjoint HL.
  Let η : functor_identity _ ⟹ L ∙ R := unit_from_left_adjoint HL.
  Let ε : R ∙ L ⟹ functor_identity _ := counit_from_left_adjoint HL.

  Local Lemma triangle_1_help
              (x : C₁)
    : #L (η x) · ε (L x) = identity (L x).
  Proof.
    exact (pr122 HL x).
  Qed.

  Local Lemma triangle_2_help
              (x : C₂)
    : η (R x) · #R (ε x) = identity (R x).
  Proof.
    exact (pr222 HL x).
  Qed.

  (**
   8.1 Right adjoints preserve limits
   *)
  Definition right_adjoint_preserves_terminal
    : preserves_terminal R.
  Proof.
    intros T HT x.
    use iscontraprop1.
    - use invproofirrelevance.
      intros g₁ g₂.
      refine (!(id_right _) @ _ @ id_right _).
      rewrite <- !triangle_2_help.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η _ _ g₁).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η _ _ g₂).
      }
      rewrite !assoc' ; cbn -[η].
      rewrite <- !functor_comp.
      do 2 apply maponpaths.
      apply (@TerminalArrowEq _ (T ,, HT)).
    - exact (η x · #R (TerminalArrow (_ ,, HT) _)).
  Qed.

  Definition right_adjoint_preserves_binproduct
    : preserves_binproduct R.
  Proof.
    intros x y p π₁ π₂ Hp c f g.
    pose (P := make_BinProduct _ _ _ _ _ _ Hp : BinProduct _ _ _).
    use iscontraprop1.
    - use invproofirrelevance.
      intros g₁ g₂.
      use subtypePath.
      {
        intro ; apply isapropdirprod ; apply homset_property.
      }
      refine (!(id_right _) @ _ @ id_right _).
      rewrite <- !triangle_2_help.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η _ _ (pr1 g₁)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η _ _ (pr1 g₂)).
      }
      rewrite !assoc' ; cbn -[η].
      rewrite <- !functor_comp.
      do 2 apply maponpaths.
      use (BinProductArrowsEq _ _ _ P).
      + cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _).
        apply maponpaths.
        exact (pr12 g₁ @ !(pr12 g₂)).
      + cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _).
        apply maponpaths.
        exact (pr22 g₁ @ !(pr22 g₂)).
    - simple refine (_ ,, _ ,, _).
      + exact (η c · #R (BinProductArrow _ P (#L f · ε x) (#L g · ε y))).
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!(functor_comp R _ _) @ _).
          apply maponpaths.
          apply BinProductPr1Commutes.
        }
        rewrite functor_comp.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (!(nat_trans_ax η _ _ f)).
        }
        rewrite !assoc'.
        rewrite triangle_2_help.
        apply id_right.
      + cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!(functor_comp R _ _) @ _).
          apply maponpaths.
          apply (BinProductPr2Commutes _ _ _ P).
        }
        rewrite functor_comp.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (!(nat_trans_ax η _ _ g)).
        }
        rewrite !assoc'.
        rewrite triangle_2_help.
        apply id_right.
  Qed.

  Definition right_adjoint_preserves_pullback
    : preserves_pullback R.
  Proof.
    intros x y z p f g π₁ π₂ q Fq Hp w h₁ h₂ r.
    pose (P := make_Pullback _ Hp).
    use iscontraprop1.
    - use invproofirrelevance.
      intros g₁ g₂.
      use subtypePath.
      {
        intro ; apply isapropdirprod ; apply homset_property.
      }
      refine (!(id_right _) @ _ @ id_right _).
      rewrite <- !triangle_2_help.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η _ _ (pr1 g₁)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η _ _ (pr1 g₂)).
      }
      rewrite !assoc' ; cbn -[η].
      rewrite <- !functor_comp.
      do 2 apply maponpaths.
      use (MorphismsIntoPullbackEqual Hp).
      + cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _).
        apply maponpaths.
        exact (pr12 g₁ @ !(pr12 g₂)).
      + cbn.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _).
        apply maponpaths.
        exact (pr22 g₁ @ !(pr22 g₂)).
    - simple refine (_ ,, _ ,, _).
      + refine (η w · #R (PullbackArrow P _ (#L h₁ · ε x) (#L h₂ · ε y) _)).
        abstract
          (rewrite !assoc' ;
           refine (maponpaths (λ z, _ · z) (!(nat_trans_ax ε _ _ f)) @ _) ;
           refine (_ @ maponpaths (λ z, _ · z) (nat_trans_ax ε _ _ g)) ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _) ;
           apply maponpaths ;
           exact r).
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!(functor_comp R _ _) @ _).
          apply maponpaths.
          apply PullbackArrow_PullbackPr1.
        }
        rewrite (functor_comp R).
        rewrite !assoc.
        refine (maponpaths (λ z, z · _) (!(nat_trans_ax η _ _ h₁)) @ _).
        refine (_ @ id_right _).
        rewrite !assoc'.
        apply maponpaths.
        apply triangle_2_help.
      + cbn -[η].
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!(functor_comp R _ _) @ _).
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 P).
        }
        rewrite (functor_comp R).
        rewrite !assoc.
        refine (maponpaths (λ z, z · _) (!(nat_trans_ax η _ _ h₂)) @ _).
        refine (_ @ id_right _).
        rewrite !assoc'.
        apply maponpaths.
        apply triangle_2_help.
  Qed.

  (**
   8.2 Left adjoints preserve colimits
   *)
  Definition left_adjoint_preserves_initial
    : preserves_initial L.
  Proof.
    intros x Hx y.
    pose (I := make_Initial x Hx).
    use iscontraprop1.
    - use invproofirrelevance.
      intros g₁ g₂.
      refine (!(id_left _) @ _ @ id_left _).
      rewrite <- !triangle_1_help.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (!(nat_trans_ax ε _ _ g₁)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (!(nat_trans_ax ε _ _ g₂)).
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(functor_comp _ _ _) @ _ @ functor_comp _ _ _).
      apply maponpaths.
      apply (@InitialArrowEq _ I).
    - exact (#L (InitialArrow I _) · ε y).
  Qed.

  Definition left_adjoint_preserves_bincoproduct
    : preserves_bincoproduct L.
  Proof.
    intros x y s ι₁ ι₂ Hs z f g.
    pose (S := make_BinCoproduct _ _ _ _ _ _ Hs).
    use iscontraprop1.
    - use invproofirrelevance.
      intros g₁ g₂.
      use subtypePath.
      {
        intro ; apply isapropdirprod ; apply homset_property.
      }
      refine (!(id_left _) @ _ @ id_left _).
      rewrite <- !triangle_1_help.
      rewrite !assoc'.
      refine (maponpaths (λ z, _ · z) (!(nat_trans_ax ε _ _ (pr1 g₁))) @ _).
      refine (_ @ maponpaths (λ z, _ · z) (nat_trans_ax ε _ _ (pr1 g₂))).
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _).
      apply maponpaths.
      use (BinCoproductArrowsEq _ _ _ S).
      + rewrite !assoc.
        refine (maponpaths (λ z, z · _) (nat_trans_ax η _ _ _) @ _).
        refine (_ @ maponpaths (λ z, z · _) (!(nat_trans_ax η _ _ _))).
        rewrite !assoc'.
        apply maponpaths.
        refine (!(functor_comp R _ _) @ _ @ functor_comp R _ _).
        apply maponpaths.
        exact (pr12 g₁ @ !(pr12 g₂)).
      + rewrite !assoc.
        refine (maponpaths (λ z, z · _) (nat_trans_ax η _ _ _) @ _).
        refine (_ @ maponpaths (λ z, z · _) (!(nat_trans_ax η _ _ _))).
        rewrite !assoc'.
        apply maponpaths.
        refine (!(functor_comp R _ _) @ _ @ functor_comp R _ _).
        apply maponpaths.
        exact (pr22 g₁ @ !(pr22 g₂)).
    - simple refine (_ ,, _ ,, _).
      + exact (#L (BinCoproductArrow S (η x · #R f) (η y · #R g)) · ε z).
      + rewrite !assoc.
        rewrite <- (functor_comp L).
        rewrite (BinCoproductIn1Commutes _ _ _  S).
        rewrite functor_comp.
        rewrite !assoc'.
        refine (maponpaths (λ z, _ · z) (nat_trans_ax ε _ _ f) @ _).
        rewrite !assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        apply triangle_1_help.
      + cbn.
        rewrite !assoc.
        rewrite <- (functor_comp L).
        rewrite (BinCoproductIn2Commutes _ _ _  S).
        rewrite functor_comp.
        rewrite !assoc'.
        refine (maponpaths (λ z, _ · z) (nat_trans_ax ε _ _ g) @ _).
        rewrite !assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        apply triangle_1_help.
  Qed.

  Definition left_adjoint_preserves_coproduct
             (J : UU)
    : preserves_coproduct J L.
  Proof.
    intros D c ι Hc x f.
    pose (S := make_Coproduct _ _ _ _ _ Hc).
    use iscontraprop1.
    - use invproofirrelevance.
      intros g₁ g₂.
      use subtypePath.
      {
        intro ; use impred ; intro ; apply homset_property.
      }
      refine (!(id_left _) @ _ @ id_left _).
      rewrite <- !triangle_1_help.
      rewrite !assoc'.
      refine (maponpaths (λ z, _ · z) (!(nat_trans_ax ε _ _ (pr1 g₁))) @ _).
      refine (_ @ maponpaths (λ z, _ · z) (nat_trans_ax ε _ _ (pr1 g₂))).
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _).
      apply maponpaths.
      use (CoproductArrow_eq _ _ _ S).
      intro j.
      rewrite !assoc.
      refine (maponpaths (λ z, z · _) (nat_trans_ax η _ _ _) @ _).
      refine (_ @ maponpaths (λ z, z · _) (!(nat_trans_ax η _ _ _))).
      rewrite !assoc'.
      apply maponpaths.
      refine (!(functor_comp R _ _) @ _ @ functor_comp R _ _).
      apply maponpaths.
      exact (pr2 g₁ j @ !(pr2 g₂ j)).
    - simple refine (_ ,, _).
      + exact (#L (CoproductArrow _ _ S (λ j, η (D j) · #R (f j))) · ε x).
      + intro j ; cbn -[η].
        rewrite !assoc.
        rewrite <- (functor_comp L).
        rewrite (CoproductInCommutes _ _ _  S).
        rewrite functor_comp.
        rewrite !assoc'.
        refine (maponpaths (λ z, _ · z) (nat_trans_ax ε _ _ (f j)) @ _).
        rewrite !assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        apply triangle_1_help.
  Qed.

  Definition left_adjoint_preserves_coequalizer
    : preserves_coequalizer L.
  Proof.
    intros x y c f g h p Fp Hc z k q.
    pose (Coeq := make_Coequalizer _ _ _ _ Hc).
    use iscontraprop1.
    - use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro ; apply homset_property.
      }
      refine (!(id_left _) @ _ @ id_left _).
      rewrite <- !triangle_1_help.
      rewrite !assoc'.
      refine (maponpaths (λ z, _ · z) (!(nat_trans_ax ε _ _ (pr1 φ₁))) @ _).
      refine (_ @ maponpaths (λ z, _ · z) (nat_trans_ax ε _ _ (pr1 φ₂))).
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(functor_comp L _ _) @ _ @ functor_comp L _ _).
      apply maponpaths.
      use (isCoequalizerOutsEq (pr22 Coeq)).
      rewrite !assoc.
      refine (maponpaths (λ z, z · _) (nat_trans_ax η _ _ _) @ _).
      refine (_ @ maponpaths (λ z, z · _) (!(nat_trans_ax η _ _ _))).
      rewrite !assoc'.
      apply maponpaths.
      refine (!(functor_comp R _ _) @ _ @ functor_comp R _ _).
      apply maponpaths.
      exact (pr2 φ₁ @ !(pr2 φ₂)).
    - simple refine (_ ,, _).
      + refine (#L _ · ε z).
        refine (CoequalizerOut Coeq _ (η y · #R k) _).
        abstract
          (rewrite !assoc ;
           etrans ;
           [ apply maponpaths_2 ;
             exact (nat_trans_ax η _ _ f)
           | ] ;
           refine (!_) ;
           etrans ;
           [ apply maponpaths_2 ;
             exact (nat_trans_ax η _ _ g)
           | ] ;
           cbn -[η] ;
           rewrite !assoc' ;
           rewrite <- !functor_comp ;
           rewrite <- q ;
           apply idpath).
      + cbn -[η].
        rewrite !assoc.
        rewrite <- functor_comp.
        rewrite (CoequalizerCommutes Coeq).
        rewrite functor_comp.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (nat_trans_ax ε _ _ k).
        }
        cbn -[η].
        rewrite !assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        exact (triangle_1_help y).
  Qed.
End AdjunctionPreservation.
