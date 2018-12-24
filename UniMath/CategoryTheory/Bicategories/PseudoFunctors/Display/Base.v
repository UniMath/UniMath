(** We construct the bicategory of pseudofunctors as a displayed bicategory.
    This is the first layer and it just consists of plain functions mapping objects to objects.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.

Local Open Scope cat.

Section BasePseudoFunctor.
  Variable (C D : bicat).

  Definition ps_base_data : prebicat_data.
  Proof.
    use build_prebicat_data.
    - exact (ob C → ob D).
    - exact (λ f g, ∏ (x : C), f x --> g x).
    - exact (λ f g α β, ∏ (x : C), α x ==> β x).
    - exact (λ f x, id₁ (f x)).
    - exact (λ f g h α β x, α x · β x).
    - exact (λ f g α x, id₂ (α x)).
    - exact (λ f g α β γ m₁ m₂ x, m₁ x • m₂ x).
    - exact (λ f g h α β γ m x, α x ◃ m x).
    - exact (λ f g h α β γ m x, m x ▹ γ x).
    - exact (λ f g α x, lunitor (α x)).
    - exact (λ f g α x, linvunitor (α x)).
    - exact (λ f g α x, runitor (α x)).
    - exact (λ f g α x, rinvunitor (α x)).
    - exact (λ f₁ f₂ f₃ f₄ α β γ x, lassociator (α x) (β x) (γ x)).
    - exact (λ f₁ f₂ f₃ f₄ α β γ x, rassociator (α x) (β x) (γ x)).
  Defined.

  Definition ps_base_laws
    : prebicat_laws ps_base_data.
  Proof.
    repeat split ; intros ; apply funextsec ; intro.
    - apply id2_left.
    - apply id2_right.
    - apply vassocr.
    - apply lwhisker_id2.
    - apply id2_rwhisker.
    - apply lwhisker_vcomp.
    - apply rwhisker_vcomp.
    - apply vcomp_lunitor.
    - apply vcomp_runitor.
    - apply lwhisker_lwhisker.
    - apply rwhisker_lwhisker.
    - apply rwhisker_rwhisker.
    - apply vcomp_whisker.
    - apply lunitor_linvunitor.
    - apply linvunitor_lunitor.
    - apply runitor_rinvunitor.
    - apply rinvunitor_runitor.
    - apply lassociator_rassociator.
    - apply rassociator_lassociator.
    - apply runitor_rwhisker.
    - apply lassociator_lassociator.
  Qed.

  Definition ps_base
    : bicat.
  Proof.
    use build_bicategory.
    - exact ps_base_data.
    - exact ps_base_laws.
    - intros ? ? ? ?.
      use impred_isaset ; intro.
      apply D.
  Defined.

  Definition all_is_invertible_to_is_invertible_2cell
             {F G : ps_base}
             {η ε : F --> G}
             (α : η ==> ε)
    : (∏ (X : C), is_invertible_2cell (α X)) → is_invertible_2cell α.
  Proof.
    intros Hα.
    use tpair ; cbn in *.
    - exact (λ x, (Hα x)^-1).
    - split ; apply funextsec ; intro X ; cbn.
      + apply vcomp_rinv.
      + apply vcomp_lid.
  Defined.

  Definition is_invertible_2cell_to_all_is_invertible
             {F G : ps_base}
             {η ε : F --> G}
             (α : η ==> ε)
    : is_invertible_2cell α → (∏ (X : C), is_invertible_2cell (α X)).
  Proof.
    intros Hα X.
    use tpair.
    - exact (Hα^-1 X).
    - split ; cbn.
      + exact (maponpaths (λ φ, φ X) (vcomp_rinv Hα)).
      + exact (maponpaths (λ φ, φ X) (vcomp_lid Hα)).
  Defined.

  Definition all_is_invertible_is_is_invertible_2cell
             {F G : ps_base}
             {η ε : F --> G}
             (α : η ==> ε)
    : (∏ (X : C), is_invertible_2cell (α X)) ≃ is_invertible_2cell α.
  Proof.
    use weqimplimpl.
    - exact (all_is_invertible_to_is_invertible_2cell α).
    - exact (is_invertible_2cell_to_all_is_invertible α).
    - apply impred ; intro.
      apply isaprop_is_invertible_2cell.
    - apply isaprop_is_invertible_2cell.
  Defined.

  Definition invertible_2cell_ps_base
             {F G : ps_base}
             (η ε : F --> G)
    : (∏ (X : C), invertible_2cell (η X) (ε X))
      →
      invertible_2cell η ε.
  Proof.
    intros α.
    use tpair.
    - intros X.
      exact (α X).
    - apply all_is_invertible_is_is_invertible_2cell.
      apply α.
  Defined.

  Definition invertible_2cell_ps_base_inv
             {F G : ps_base}
             (η ε : F --> G)
    : invertible_2cell η ε
      →
      (∏ (X : C), invertible_2cell (η X) (ε X)).
  Proof.
    intros α X.
    use tpair.
    - exact (cell_from_invertible_2cell α X).
    - apply is_invertible_2cell_to_all_is_invertible.
      apply α.
  Defined.

  Definition invertible_2cell_ps_base_weq
             {F G : ps_base}
             (η ε : F --> G)
    : (∏ (X : C), invertible_2cell (η X) (ε X))
        ≃
        invertible_2cell η ε.
  Proof.
    refine (weqpair (invertible_2cell_ps_base η ε) _).
    use isweq_iso.
    - exact (invertible_2cell_ps_base_inv η ε).
    - intros α.
      apply funextsec ; intro X.
      apply subtypeEquality.
      { intro ; apply isaprop_is_invertible_2cell. }
      reflexivity.
    - intros α.
      apply subtypeEquality.
      { intro ; apply isaprop_is_invertible_2cell. }
      apply funextsec ; intro X.
      reflexivity.
  Defined.

  Definition ps_base_is_univalent_2_1
             (HD_2_1 : is_univalent_2_1 D)
    : is_univalent_2_1 ps_base.
  Proof.
    intros F G η ε.
    use weqhomot.
    - simple refine (invertible_2cell_ps_base_weq η ε ∘ _)%weq.
      simple refine (_ ∘ weqpair _ (isweqtoforallpaths _ _ _))%weq.
      simple refine (weqonsecfibers _ _ _).
      intro X ; cbn.
      exact (weqpair (idtoiso_2_1 (η X) (ε X)) (HD_2_1 _ _ _ _)).
    - intros p.
      induction p.
      use subtypeEquality.
      { intro ; apply isaprop_is_invertible_2cell. }
      reflexivity.
  Defined.

  Definition all_is_adjequiv_to_is_adjequiv
             {F G : ps_base}
             (η : F --> G)
    : (∏ (X : C), left_adjoint_equivalence (η X)) → left_adjoint_equivalence η.
  Proof.
    intros Hη.
    use tpair.
    - use tpair.
      + intros X.
        exact (pr11 (Hη X)).
      + split ; intros X ; cbn.
        * exact (pr121 (Hη X)).
        * exact (pr221 (Hη X)).
    - split ; split ; cbn.
      + apply funextsec ; intro X.
        exact (pr112 (Hη X)).
      + apply funextsec ; intro X.
        exact (pr212 (Hη X)).
      + apply all_is_invertible_is_is_invertible_2cell.
        exact (λ X, pr122 (Hη X)).
      + apply all_is_invertible_is_is_invertible_2cell.
        exact (λ X, pr222 (Hη X)).
  Defined.

  Definition is_adjequiv_to_all_is_adjequiv
             {F G : ps_base}
             (η : F --> G)
    : left_adjoint_equivalence η → (∏ (X : C), left_adjoint_equivalence (η X)).
  Proof.
    intros Hη X.
    use tpair.
    - use tpair.
      + exact (pr11 Hη X).
      + split ; cbn.
        * exact (pr121 Hη X).
        * exact (pr221 Hη X).
    - split ; split ; cbn.
      + exact (maponpaths (λ φ, φ X) (pr112 Hη)).
      + exact (maponpaths (λ φ, φ X) (pr212 Hη)).
      + exact (is_invertible_2cell_to_all_is_invertible (pr121 Hη) (pr122 Hη) X).
      + exact (is_invertible_2cell_to_all_is_invertible (pr221 Hη) (pr222 Hη) X).
  Defined.

  Definition all_is_adjequiv_is_is_adjequiv
             {F G : ps_base}
             (η : F --> G)
    : (∏ (X : C), left_adjoint_equivalence (η X)) ≃ left_adjoint_equivalence η.
  Proof.
    refine (weqpair (all_is_adjequiv_to_is_adjequiv η) _).
    use isweq_iso.
    - exact (is_adjequiv_to_all_is_adjequiv η).
    - intros Hη.
      apply funextsec ; intro X.
      use subtypeEquality.
      {
        intro.
        do 2 apply isapropdirprod ; try (apply D)
        ; apply isaprop_is_invertible_2cell.
      }
      reflexivity.
    - intros Hη.
      use subtypeEquality.
      {
        intro.
        do 2 apply isapropdirprod ; try (apply ps_base)
        ; apply isaprop_is_invertible_2cell.
      }
      reflexivity.
  Defined.

  Definition adjequiv_ps_base
             (F G : ps_base)
    : (∏ (X : C), adjoint_equivalence (F X) (G X))
      →
      adjoint_equivalence F G.
  Proof.
    intros η.
    use tpair.
    - intros X.
      exact (η X).
    - apply all_is_adjequiv_is_is_adjequiv.
      apply η.
  Defined.

  Definition adjequiv_ps_base_inv
             (F G : ps_base)
    : adjoint_equivalence F G
      →
      (∏ (X : C), adjoint_equivalence (F X) (G X)).
  Proof.
    intros η X.
    use tpair.
    - exact (pr1 η X).
    - apply is_adjequiv_to_all_is_adjequiv.
      apply η.
  Defined.

  Definition adjequiv_ps_base_weq
             (F G : ps_base)
    : (∏ (X : C), adjoint_equivalence (F X) (G X))
      ≃
      adjoint_equivalence F G.
  Proof.
    refine (weqpair (adjequiv_ps_base F G) _).
    use isweq_iso.
    - exact (adjequiv_ps_base_inv F G).
    - intros η.
      apply funextsec ; intro X.
      use total2_paths_b.
      + reflexivity.
      + cbn ; unfold idfun.
        use subtypeEquality.
        {
          intro.
          do 2 apply isapropdirprod ; try (apply D)
          ; apply isaprop_is_invertible_2cell.
        }
        reflexivity.
    - intros η.
      use total2_paths_b.
      + reflexivity.
      + cbn ; unfold idfun.
        use subtypeEquality.
        {
          intro.
          do 2 apply isapropdirprod ; try (apply ps_base)
          ; apply isaprop_is_invertible_2cell.
        }
        reflexivity.
  Defined.

  Definition ps_base_is_univalent_2_0
             (HD_2_0 : is_univalent_2_0 D)
             (HD_2_1 : is_univalent_2_1 D)
    : is_univalent_2_0 ps_base.
  Proof.
    intros F G.
    use weqhomot.
    - simple refine (adjequiv_ps_base_weq F G ∘ _)%weq.
      simple refine (_ ∘ weqpair _ (isweqtoforallpaths _ _ _))%weq.
      simple refine (weqonsecfibers _ _ _).
      intro X ; cbn.
      exact (weqpair (idtoiso_2_0 (F X) (G X)) (HD_2_0 _ _)).
    - intros p.
      induction p.
      use subtypeEquality.
      {
        intro.
        apply isaprop_left_adjoint_equivalence.
        exact (ps_base_is_univalent_2_1 HD_2_1).
      }
      reflexivity.
  Defined.
End BasePseudoFunctor.