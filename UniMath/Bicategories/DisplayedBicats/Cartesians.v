(*********************************************************************

 Cartesian 1-cells

 In this file, we study properties of cartesian 1-cells.

 Content:

 1. Invertibility of 2-cell factorisation
 2. Being a cartesian 1-cell is a proposition
 3. Weak cartesian 1-cells
 4. Every weak cartesian 1-cell is cartesian
 5. Examples of cartesian 1-cells

 *********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.StrictToPseudo.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.

Local Open Scope cat.
Local Open Scope mor_disp.

(** 1. Invertibility of 2-cell factorisation *)
Section Lift2CellInvertible.
  Context {B : bicat}
          (D : disp_bicat B)
          {a b : B}
          {f : a --> b}
          {aa : D a}
          {bb : D b}
          {ff : aa -->[ f ] bb}
          (Hff : cartesian_1cell _ ff)
          {c : B}
          {cc : D c}
          {h h' : c --> a}
          {gg : cc -->[h · f ] bb}
          {gg' : cc -->[h' · f ] bb}
          {δ : h ==> h'}
          (Hδ : is_invertible_2cell δ)
          {σσ : gg ==>[ δ ▹ f] gg'}
          (Hσσ : is_disp_invertible_2cell (is_invertible_2cell_rwhisker f Hδ) σσ)
          (Lh : lift_1cell_factor _ ff gg)
          (Lh' : lift_1cell_factor _ ff gg').

  Let inv : Lh' ==>[ Hδ ^-1] Lh := cartesian_1cell_lift_2cell _ _ Hff (pr1 Hσσ) Lh' Lh.

  Local Lemma cartesian_1cell_lift_inv₁
    : cartesian_1cell_lift_2cell D ff Hff σσ Lh Lh' •• inv
      =
      transportb (λ α, Lh ==>[ α] Lh) (vcomp_rinv Hδ) (disp_id2 Lh).
  Proof.
    use (isaprop_lift_of_lift_2cell D ff).
    - refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_id2 _)).
      abstract
        (rewrite vcomp_rinv ;
         rewrite id2_rwhisker ;
         apply idpath).
    - use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply D | ].
        induction φ₁ as [ φ₁ p₁ ].
        induction φ₂ as [ φ₂ p₂ ].
        cbn.
        rewrite disp_mor_transportf_prewhisker in p₁, p₂.
        rewrite disp_id2_right in p₁, p₂.
        unfold transportb in *.
        rewrite transport_f_f in p₁, p₂.
        assert (r := p₁ @ !p₂).
        assert (r' : φ₁ ▹▹ ff = φ₂ ▹▹ ff).
        {
          use (disp_vcomp_rcancel _ (pr22 Lh)).
          pose (@transportb_transpose_left
                   _
                   (λ z, Lh ;; ff ==>[ z] gg)
                   _ _ _ _ _
                   r)
            as ρ.
          rewrite transportbfinv in ρ.
          exact ρ.
        }
        pose (l := pr1 Lh
                   ,,
                   disp_id2_invertible_2cell
                     (pr1 Lh ;; ff)
                 : lift_1cell_factor _ _ (Lh ;; ff)).
        apply (isaprop_lift_of_lift_2cell
                 _
                 _
                 (pr2 Hff
                      _ _ _ _ _ _ _
                      (φ₁ ▹▹ ff)
                      l
                      l)
                 φ₁
                 φ₂).
        * cbn.
          rewrite disp_id2_right, disp_id2_left.
          unfold transportb.
          rewrite transport_f_f.
          apply maponpaths_2.
          apply cellset_property.
        * cbn.
          rewrite disp_id2_right, disp_id2_left.
          unfold transportb.
          rewrite r'.
          rewrite transport_f_f.
          apply maponpaths_2.
          apply cellset_property.
      + simple refine (_ ,, _).
        * simple refine (transportf
                           (λ z, _ ==>[ z ] _)
                           _
                           (disp_id2 _)).
          abstract
            (rewrite vcomp_rinv ;
             apply idpath).
        * cbn.
          rewrite !disp_mor_transportf_prewhisker.
          rewrite disp_rwhisker_transport_left_new.
          rewrite disp_mor_transportf_postwhisker.
          rewrite transport_f_f.
          rewrite disp_id2_rwhisker.
          unfold transportb.
          rewrite disp_mor_transportf_postwhisker.
          rewrite transport_f_f.
          rewrite disp_id2_left, disp_id2_right.
          unfold transportb.
          rewrite !transport_f_f.
          apply maponpaths_2.
          apply cellset_property.
    - unfold cartesian_1cell_lift_2cell, inv.
      rewrite disp_rwhisker_vcomp_alt.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_vassocl.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply eq_lift_2cell_alt.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_vassocr.
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply eq_lift_2cell_alt.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_vassocl.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply Hσσ.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_rwhisker_transport_left_new.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_id2_rwhisker.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_id2_left, disp_id2_right.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Local Lemma cartesian_1cell_lift_inv₂
    : inv •• cartesian_1cell_lift_2cell D ff Hff σσ Lh Lh'
      =
      transportb (λ α, Lh' ==>[ α] Lh') (vcomp_linv Hδ) (disp_id2 Lh').
  Proof.
    use (isaprop_lift_of_lift_2cell D ff).
    - refine (transportf
                (λ z, _ ==>[ z ] _)
                _
                (disp_id2 _)).
      abstract
        (rewrite vcomp_linv ;
         rewrite id2_rwhisker ;
         apply idpath).
    - use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply D | ].
        induction φ₁ as [ φ₁ p₁ ].
        induction φ₂ as [ φ₂ p₂ ].
        cbn.
        rewrite disp_mor_transportf_prewhisker in p₁, p₂.
        rewrite disp_id2_right in p₁, p₂.
        unfold transportb in *.
        rewrite transport_f_f in p₁, p₂.
        assert (r := p₁ @ !p₂).
        assert (r' : φ₁ ▹▹ ff = φ₂ ▹▹ ff).
        {
          use (disp_vcomp_rcancel _ (pr22 Lh')).
          pose (@transportb_transpose_left
                  _
                  (λ z, Lh' ;; ff ==>[ z] gg')
                  _ _ _ _ _
                  r)
            as ρ.
          rewrite transportbfinv in ρ.
          exact ρ.
        }
        pose (l := pr1 Lh'
                       ,,
                       disp_id2_invertible_2cell
                       (pr1 Lh' ;; ff)
                   : lift_1cell_factor _ _ (Lh' ;; ff)).
        apply (isaprop_lift_of_lift_2cell
                 _
                 _
                 (pr2 Hff
                      _ _ _ _ _ _ _
                      (φ₁ ▹▹ ff)
                      l
                      l)
                 φ₁
                 φ₂).
        * cbn.
          rewrite disp_id2_right, disp_id2_left.
          unfold transportb.
          rewrite transport_f_f.
          apply maponpaths_2.
          apply cellset_property.
        * cbn.
          rewrite disp_id2_right, disp_id2_left.
          unfold transportb.
          rewrite r'.
          rewrite transport_f_f.
          apply maponpaths_2.
          apply cellset_property.
      + simple refine (_ ,, _).
        * simple refine (transportf
                           (λ z, _ ==>[ z ] _)
                           _
                           (disp_id2 _)).
          abstract
            (rewrite vcomp_linv ;
             apply idpath).
        * cbn.
          rewrite !disp_mor_transportf_prewhisker.
          rewrite disp_rwhisker_transport_left_new.
          rewrite disp_mor_transportf_postwhisker.
          rewrite transport_f_f.
          rewrite disp_id2_rwhisker.
          unfold transportb.
          rewrite disp_mor_transportf_postwhisker.
          rewrite transport_f_f.
          rewrite disp_id2_left, disp_id2_right.
          unfold transportb.
          rewrite !transport_f_f.
          apply maponpaths_2.
          apply cellset_property.
    - unfold cartesian_1cell_lift_2cell, inv.
      rewrite disp_rwhisker_vcomp_alt.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_vassocl.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply eq_lift_2cell_alt.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_vassocr.
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply eq_lift_2cell_alt.
      }
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_vassocl.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply Hσσ.
      }
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_rwhisker_transport_left_new.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_id2_rwhisker.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_id2_left, disp_id2_right.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Definition cartesian_1cell_lift_2cell_invertible
    : is_disp_invertible_2cell Hδ (cartesian_1cell_lift_2cell _ _ Hff σσ Lh Lh').
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact inv.
    - exact cartesian_1cell_lift_inv₁.
    - exact cartesian_1cell_lift_inv₂.
  Defined.
End Lift2CellInvertible.

(**
 2. Being a cartesian 1-cell is a proposition
 *)
Definition isaprop_cartesian_1cell
           {B : bicat}
           {D : disp_bicat B}
           (HD : disp_univalent_2_1 D)
           {b₁ b₂ : B}
           {f : b₁ --> b₂}
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           (ff : bb₁ -->[ f ] bb₂)
  : isaprop (cartesian_1cell D ff).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use subtypePath.
  {
    intro.
    do 10 (use impred ; intro).
    apply isapropiscontr.
  }
  use funextsec ; intro c.
  use funextsec ; intro cc.
  use funextsec ; intro h.
  use funextsec ; intro gg.
  use total2_paths_f.
  - use (disp_isotoid_2_1
             _
             HD
             (idpath _)).
    simple refine (_ ,, _).
    + refine (cartesian_1cell_lift_2cell _ _ φ₁ _ (pr1 φ₁ c cc h gg) (pr1 φ₂ c cc h gg)).
      exact (transportf
               (λ z, _ ==>[ z ] _)
               (!(id2_rwhisker _ _))
               (disp_id2 _)).
    + simpl.
      apply cartesian_1cell_lift_2cell_invertible.
      simple refine (_ ,, _ ,, _).
      * exact (transportf
                 (λ z, _ ==>[ z ] _)
                 (!(id2_rwhisker _ _))
                 (disp_id2 _)).
      * rewrite disp_mor_transportf_prewhisker.
        rewrite disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
      * simpl.
        rewrite disp_mor_transportf_prewhisker.
        rewrite disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
  - simpl.
    use subtypePath.
    {
      intro ; apply isaprop_is_disp_invertible_2cell.
    }
    unfold disp_invertible_2cell.
    rewrite pr1_transportf.
    cbn.
    rewrite disp_1cell_transport_rwhisker.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply disp_idtoiso_2_1_inv.
    }
    rewrite disp_idtoiso_isotoid_2_1.
    cbn.
    etrans.
    {
      apply maponpaths.
      apply eq_lift_2cell_alt.
    }
    unfold transportb.
    rewrite transport_f_f.
    rewrite disp_mor_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite disp_id2_right.
    unfold transportb.
    rewrite transport_f_f.
    use (transportf_set (λ α, pr1 φ₂ c cc h gg ;; ff ==>[ α] gg)).
    apply cellset_property.
Qed.

(**
 3. Weak cartesian 1-cells

 For a weak cartesian 1-cell, the factorisation only lives above
 the given cell up to isomorphism. We use this to show that the
 identity is cartesian.
 *)
Section WeakCartesians.
  Context {B : bicat}
          (D : disp_bicat B)
          {a b : B}
          {f : a --> b}
          {aa : D a}
          {bb : D b}
          (ff : aa -->[ f ] bb).

  Definition wk_lift_1cell_factor
             {c : B}
             {cc : D c}
             {h : c --> a}
             (gg : cc -->[ h · f ] bb)
    : UU
    := ∑ (h' : c --> a)
         (β : invertible_2cell h' h)
         (hh : cc -->[ h' ] aa),
       disp_invertible_2cell
         (rwhisker_of_invertible_2cell f β)
         (hh ;; ff)
         gg.

  Definition wk_lift_1cell_factor_over
             {c : B}
             {cc : D c}
             {h : c --> a}
             {gg : cc -->[ h · f ] bb}
             (Lh : wk_lift_1cell_factor gg)
    : c --> a
    := pr1 Lh.

  Definition wk_lift_1cell_factor_over_iso
             {c : B}
             {cc : D c}
             {h : c --> a}
             {gg : cc -->[ h · f ] bb}
             (Lh : wk_lift_1cell_factor gg)
    : invertible_2cell (wk_lift_1cell_factor_over Lh) h
    := pr12 Lh.

  Coercion disp_mor_wk_lift_1cell_factor
           {c : B}
           {cc : D c}
           {h : c --> a}
           {gg : cc -->[ h · f ] bb}
           (Lh : wk_lift_1cell_factor gg)
    : cc -->[ wk_lift_1cell_factor_over Lh ] aa
    := pr122 Lh.

  Definition disp_cell_wk_lift_1cell_factor
             {c : B}
             {cc : D c}
             {h : c --> a}
             {gg : cc -->[ h · f ] bb}
             (Lh : wk_lift_1cell_factor gg)
    : disp_invertible_2cell
        (rwhisker_of_invertible_2cell
           f
           (wk_lift_1cell_factor_over_iso Lh))
        (Lh ;; ff)
        gg
    := pr222 Lh.

  Definition wk_lift_2cell_factor_type_path
             {c : B}
             {cc : D c}
             {h h' : c --> a}
             {gg : cc -->[ h · f ] bb}
             {gg' : cc -->[ h' · f ] bb}
             {δ : h ==> h'}
             (σσ : gg ==>[ δ ▹ f] gg')
             (Lh : wk_lift_1cell_factor gg)
             (Lh' : wk_lift_1cell_factor gg')
    : (((pr12 Lh • δ) • (pr12 Lh')^-1) ▹ f)
        • (wk_lift_1cell_factor_over_iso Lh' ▹ f)
      =
      (wk_lift_1cell_factor_over_iso Lh ▹ f) • (δ ▹ f).
  Proof.
    rewrite !rwhisker_vcomp.
    rewrite !vassocl.
    rewrite vcomp_linv.
    rewrite id2_right.
    apply idpath.
  Qed.

  Definition wk_lift_2cell_factor_type
             {c : B}
             {cc : D c}
             {h h' : c --> a}
             {gg : cc -->[ h · f ] bb}
             {gg' : cc -->[ h' · f ] bb}
             {δ : h ==> h'}
             (σσ : gg ==>[ δ ▹ f] gg')
             (Lh : wk_lift_1cell_factor gg)
             (Lh' : wk_lift_1cell_factor gg')
    : UU
    := ∑ (δδ : Lh ==>[ pr12 Lh • δ • (pr12 Lh')^-1 ] Lh'),
       transportf
         (λ z, _ ==>[ z ] _)
         (wk_lift_2cell_factor_type_path σσ Lh Lh')
         (δδ ▹▹ ff •• disp_cell_wk_lift_1cell_factor Lh')
       =
       disp_cell_wk_lift_1cell_factor Lh •• σσ.

  Definition wk_lift_2cell_factor
             {c : B}
             {cc : D c}
             {h h' : c --> a}
             {gg : cc -->[h · f ] bb}
             {gg' : cc -->[h' · f ] bb}
             {δ : h ==> h'}
             (σσ : gg ==>[ δ ▹ f] gg')
             (Lh : wk_lift_1cell_factor gg)
             (Lh' : wk_lift_1cell_factor gg')
    : UU
    := iscontr (wk_lift_2cell_factor_type σσ Lh Lh').

  Coercion disp_cell_wk_lift_2cell_factor
           {c : B}
           {cc : D c}
           {h h' : c --> a}
           {gg : cc -->[h · f ] bb}
           {gg' : cc -->[h' · f ] bb}
           {δ : h ==> h'}
           {σσ : gg ==>[ δ ▹ f] gg'}
           {Lh : wk_lift_1cell_factor gg}
           {Lh' : wk_lift_1cell_factor gg'}
           (Hσσ : wk_lift_2cell_factor σσ Lh Lh')
    : Lh ==>[ pr12 Lh • δ • (pr12 Lh')^-1 ] Lh'
    := pr11 Hσσ.

  Definition eq_wk_lift_2cell
             {c : B}
             {cc : D c}
             {h h' : c --> a}
             {gg : cc -->[h · f ] bb}
             {gg' : cc -->[h' · f ] bb}
             {δ : h ==> h'}
             {σσ : gg ==>[ δ ▹ f] gg'}
             {Lh : wk_lift_1cell_factor gg}
             {Lh' : wk_lift_1cell_factor gg'}
             (Hσσ : wk_lift_2cell_factor σσ Lh Lh')
    : transportf
        (λ z, _ ==>[ z ] _)
        (wk_lift_2cell_factor_type_path σσ Lh Lh')
        (Hσσ ▹▹ ff •• disp_cell_wk_lift_1cell_factor Lh')
      =
      disp_cell_wk_lift_1cell_factor Lh •• σσ
    := pr21 Hσσ.

  Definition isaprop_wk_lift_of_lift_2cell
             {c : B}
             {cc : D c}
             {h h' : c --> a}
             {gg : cc -->[h · f ] bb}
             {gg' : cc -->[h' · f ] bb}
             {δ : h ==> h'}
             {σσ : gg ==>[ δ ▹ f] gg'}
             {Lh : wk_lift_1cell_factor gg}
             {Lh' : wk_lift_1cell_factor gg'}
             (Hσσ : wk_lift_2cell_factor σσ Lh Lh')
             (δδ₁ : Lh ==>[ pr12 Lh • δ • (pr12 Lh')^-1 ] Lh')
             (δδ₂ : Lh ==>[ pr12 Lh • δ • (pr12 Lh')^-1 ] Lh')
             (Pδδ₁ : transportf
                       (λ z, _ ==>[ z ] _)
                       (wk_lift_2cell_factor_type_path σσ Lh Lh')
                       (δδ₁ ▹▹ ff •• disp_cell_wk_lift_1cell_factor Lh')
                     =
                     disp_cell_wk_lift_1cell_factor Lh •• σσ)
             (Pδδ₂ : transportf
                       (λ z, _ ==>[ z ] _)
                       (wk_lift_2cell_factor_type_path σσ Lh Lh')
                       (δδ₂ ▹▹ ff •• disp_cell_wk_lift_1cell_factor Lh')
                     =
                     disp_cell_wk_lift_1cell_factor Lh •• σσ)
    : δδ₁ = δδ₂.
  Proof.
    pose (proofirrelevance _ (isapropifcontr Hσσ) (δδ₁ ,, Pδδ₁) (δδ₂ ,, Pδδ₂)) as p.
    exact (maponpaths pr1 p).
  Qed.

  Definition wk_cartesian_1cell
    : UU
    := (∏ (c : B)
          (cc : D c)
          (h : c --> a)
          (gg : cc -->[ h · f ] bb),
        wk_lift_1cell_factor gg)
       ×
       ∏ (c : B)
         (cc : D c)
         (h h' : c --> a)
         (gg : cc -->[h · f ] bb)
         (gg' : cc -->[h' · f ] bb)
         (δ : h ==> h')
         (σσ : gg ==>[ δ ▹ f] gg')
         (Lh : wk_lift_1cell_factor gg)
         (Lh' : wk_lift_1cell_factor gg'),
       wk_lift_2cell_factor σσ Lh Lh'.
End WeakCartesians.

(**
 4. Every weak cartesian 1-cell is cartesian
 *)
Lemma lift_1cell_factor_to_wk_lift_1cell_factor_path
      {B : bicat}
      {a b : B}
      (f : a --> b)
      {c : B}
      (h : c --> a)
  : id2_invertible_2cell (h · f)
    =
    rwhisker_of_invertible_2cell f (id2_invertible_2cell h).
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_is_invertible_2cell.
  }
  exact (!(id2_rwhisker _ _)).
Qed.

Definition lift_1cell_factor_to_wk_lift_1cell_factor
           {B : bicat}
           {D : disp_bicat B}
           {a b : B}
           {f : a --> b}
           {aa : D a}
           {bb : D b}
           {ff : aa -->[ f ] bb}
           {c : B}
           {cc : D c}
           {h : c --> a}
           {gg : cc -->[ h · f] bb}
           (ℓ : lift_1cell_factor D ff gg)
  : wk_lift_1cell_factor D ff gg.
Proof.
  refine (h ,, id2_invertible_2cell _ ,, disp_mor_lift_1cell_factor D _ ℓ ,, _).
  exact (transportf
           (λ z, disp_invertible_2cell z _ _)
           (lift_1cell_factor_to_wk_lift_1cell_factor_path f h)
           (disp_cell_lift_1cell_factor D _ ℓ)).
Defined.

Section WkLiftToLift.
  Context {B : bicat}
          {D : disp_bicat B}
          (HB : is_univalent_2_1 B)
          {a b : B}
          {f : a --> b}
          {aa : D a}
          {bb : D b}
          {ff : aa -->[ f ] bb}
          {c : B}
          {cc : D c}
          {h : B ⟦ c, a ⟧}
          {gg : cc -->[ h · f] bb}
          (ℓ : wk_lift_1cell_factor D ff gg).

  Local Definition wk_lift_1cell_factor_to_lift_1cell_factor_lift : cc -->[ h] aa
    := transport_along_inv_2cell
         HB
         (wk_lift_1cell_factor_over_iso D _ ℓ)
         (disp_mor_wk_lift_1cell_factor D _ ℓ).

  Local Definition wk_lift_1cell_factor_to_lift_1cell_factor_cell
    : wk_lift_1cell_factor_to_lift_1cell_factor_lift ;; ff
      ==>[ id₂ _ ]
      gg.
  Proof.
    refine (transportf
              (λ z, _ ==>[ z ] _)
              _
              ((transport_along_inv_2cell_disp_invertible_2cell HB _ _ ▹▹ ff)
                 •• disp_cell_wk_lift_1cell_factor D _ ℓ)).
    abstract
      (cbn ;
       rewrite rwhisker_vcomp ;
       rewrite vcomp_linv ;
       rewrite id2_rwhisker ;
       apply idpath).
  Defined.

  Definition wk_lift_1cell_factor_to_lift_1cell_factor_invertible
    : is_disp_invertible_2cell
        (is_invertible_2cell_id₂ (h · f))
        wk_lift_1cell_factor_to_lift_1cell_factor_cell.
  Proof.
    unfold wk_lift_1cell_factor_to_lift_1cell_factor_cell.
    use transportf_is_disp_invertible_2cell.
    - cbn.
      is_iso.
      apply property_from_invertible_2cell.
    - apply (vcomp_disp_is_invertible
               (disp_invertible_2cell_rwhisker
                  ff
                  (transport_along_inv_2cell_disp_invertible_2cell
                     HB
                     (wk_lift_1cell_factor_over_iso D ff ℓ) ℓ))
               (disp_cell_wk_lift_1cell_factor D ff ℓ)).
  Defined.

  Definition wk_lift_1cell_factor_to_lift_1cell_factor
    : lift_1cell_factor D ff gg.
  Proof.
    refine (wk_lift_1cell_factor_to_lift_1cell_factor_lift ,, _).
    simple refine (_ ,, _) ; cbn.
    - exact wk_lift_1cell_factor_to_lift_1cell_factor_cell.
    - exact wk_lift_1cell_factor_to_lift_1cell_factor_invertible.
  Defined.
End WkLiftToLift.

Section WkCartesianToCartesian.
  Context {B : bicat}
          {D : disp_bicat B}
          (HB : is_univalent_2_1 B)
          {a b : B}
          {f : a --> b}
          {aa : D a}
          {bb : D b}
          {ff : aa -->[ f ] bb}
          (Hff : wk_cartesian_1cell D ff).

  Section WkCartesianToCartesianTwoCell.
    Context {c : B}
            {cc : D c}
            {h h' : c --> a}
            {gg : cc -->[ h · f ] bb}
            {gg' : cc -->[ h' · f ] bb}
            {δ : h ==> h'}
            (σσ : gg ==>[ δ ▹ f ] gg')
            (Lh : lift_1cell_factor D ff gg)
            (Lh' : lift_1cell_factor D ff gg').

    Let ℓ : wk_lift_1cell_factor D ff gg
      := lift_1cell_factor_to_wk_lift_1cell_factor Lh.
    Let ℓ' : wk_lift_1cell_factor D ff gg'
      := lift_1cell_factor_to_wk_lift_1cell_factor Lh'.
    Let w : wk_lift_2cell_factor D ff σσ ℓ ℓ'
      := pr2 Hff c cc h h' gg gg' δ σσ ℓ ℓ'.

    Local Lemma help_path_wk_cartesian
      : (pr12 ℓ • δ) • (pr12 ℓ') ^-1 = δ.
    Proof.
      cbn.
      rewrite id2_left, id2_right.
      apply idpath.
    Qed.

    Local Definition wk_cartesian_1cell_to_cartesian_1cell_2cell
      : Lh ==>[ δ ] Lh'
      := transportf
           (λ z, _ ==>[ z ] _)
           help_path_wk_cartesian
           (pr11 w).

    Local Lemma wk_cartesian_1cell_to_cartesian_1cell_comm
      : transportf
          (λ z, _ ==>[ z] _)
          (id2_right (δ ▹ f) @ ! id2_left (δ ▹ f))
          ((wk_cartesian_1cell_to_cartesian_1cell_2cell ▹▹ ff)
           •• disp_cell_lift_1cell_factor D ff Lh')
        = disp_cell_lift_1cell_factor D ff Lh •• σσ.
    Proof.
      unfold wk_cartesian_1cell_to_cartesian_1cell_2cell.
      rewrite disp_rwhisker_transport_left_new.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      pose (pr21 w) as p₁.
      cbn in p₁.
      pose (q₁ := transportf_disp_invertible_2cell
                    (lift_1cell_factor_to_wk_lift_1cell_factor_path f h)
                    (disp_cell_lift_1cell_factor D ff Lh)).
      pose (p₂ := p₁ @ maponpaths (λ z, z •• _) q₁).
      rewrite disp_mor_transportf_postwhisker in p₂.
      pose (p₃ := @transportb_transpose_left
                    _
                    (λ z, _ ==>[ z ] _)
                    _ _ _ _ _
                    p₂).
      refine (_ @ p₃).
      clear p₁ q₁ p₂ p₃.
      unfold transportb.
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (transportf_disp_invertible_2cell
                 (lift_1cell_factor_to_wk_lift_1cell_factor_path f h')
                 (disp_cell_lift_1cell_factor D ff Lh')).
      }
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    Qed.

    Local Lemma wk_cartesian_1cell_to_cartesian_1cell_unique
      : isaprop (lift_2cell_factor_type D ff σσ Lh Lh').
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply disp_cellset_property.
      }
      pose (p₁ := pr2 φ₁).
      pose (p₂ := pr2 φ₂).
      cbn in p₁, p₂.
      assert (path : δ = (id₂ h • δ) • id₂ h').
      {
        rewrite id2_left, id2_right.
        apply idpath.
      }
      pose (δδ₁ := transportf
                     (λ z, _ ==>[ z ] _)
                     path
                     (pr1 φ₁)).
      pose (δδ₂ := transportf
                     (λ z, _ ==>[ z ] _)
                     path
                     (pr1 φ₂)).
      enough (δδ₁ = δδ₂) as H.
      {
        pose (r := maponpaths (transportb (λ z, _ ==>[ z ] _) path) H).
        unfold δδ₁, δδ₂ in r.
        rewrite !transportbfinv in r.
        exact r.
      }
      use (isaprop_wk_lift_of_lift_2cell D ff w δδ₁ δδ₂) ;
        cbn ;
        unfold δδ₁, δδ₂.
      - etrans.
        {
          do 2 apply maponpaths.
          apply (transportf_disp_invertible_2cell
                   (lift_1cell_factor_to_wk_lift_1cell_factor_path f h')).
        }
        rewrite disp_rwhisker_transport_left_new.
        rewrite disp_mor_transportf_prewhisker.
        rewrite disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply (transportf_disp_invertible_2cell
                   (lift_1cell_factor_to_wk_lift_1cell_factor_path f h)).
        }
        rewrite disp_mor_transportf_postwhisker.
        etrans.
        {
          apply maponpaths.
          exact (!p₁).
        }
        rewrite transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
      - etrans.
        {
          do 2 apply maponpaths.
          apply (transportf_disp_invertible_2cell
                   (lift_1cell_factor_to_wk_lift_1cell_factor_path f h')).
        }
        rewrite disp_rwhisker_transport_left_new.
        rewrite disp_mor_transportf_prewhisker.
        rewrite disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply (transportf_disp_invertible_2cell
                   (lift_1cell_factor_to_wk_lift_1cell_factor_path f h)).
        }
        rewrite disp_mor_transportf_postwhisker.
        etrans.
        {
          apply maponpaths.
          exact (!p₂).
        }
        rewrite transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
    Qed.
  End WkCartesianToCartesianTwoCell.

  Definition wk_cartesian_1cell_to_cartesian_1cell
    : cartesian_1cell D ff.
  Proof.
    split.
    - exact (λ c cc h gg, wk_lift_1cell_factor_to_lift_1cell_factor HB (pr1 Hff _ _ _ gg)).
    - intros c cc h h' gg gg' δ σσ Lh Lh'.
      use iscontraprop1.
      + exact (wk_cartesian_1cell_to_cartesian_1cell_unique σσ Lh Lh').
      + simple refine (_ ,, _).
        ** exact (wk_cartesian_1cell_to_cartesian_1cell_2cell σσ Lh Lh').
        ** exact (wk_cartesian_1cell_to_cartesian_1cell_comm σσ Lh Lh').
  Defined.
End WkCartesianToCartesian.

(**
 5. Examples of cartesian 1-cells
 *)
Section ExamplesOfCartesian1Cells.
  Context {B : bicat}
          {D : disp_bicat B}
          (HB : is_univalent_2 B).

  Section IdCartesian.
    Context {x : B}
            (xx : D x).

    Section IdCartesianOneLift.
      Context {c : B}
              {cc : D c}
              {h : c --> x}
              (gg : cc -->[ h · id₁ _ ] xx).

      Definition cartesian_1cell_id_wk_1cell_lift
        : wk_lift_1cell_factor D (id_disp xx) gg.
      Proof.
        refine (h · id₁ _
                ,,
                runitor_invertible_2cell _
                ,,
                gg
                ,,
                _).
        simple refine (_ ,, _).
        - refine (transportf
                    (λ z, _ ==>[ z ] _)
                    _
                    (disp_runitor gg)).
          abstract
            (cbn ;
             rewrite <- runitor_triangle ;
             use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
             rewrite runitor_rwhisker ;
             apply maponpaths ;
             apply runitor_lunitor_identity).
        - cbn.
          use transportf_is_disp_invertible_2cell.
          + is_iso.
          + apply is_disp_invertible_2cell_runitor.
      Defined.
    End IdCartesianOneLift.

    Section IdCartesianTwoLift.
      Context {c : B}
              {cc : D c}
              (h h' : B ⟦ c, x ⟧)
              {gg : cc -->[ h · id₁ _ ] xx}
              {gg' : cc -->[ h' · id₁ _ ] xx}
              {δ : h ==> h'}
              (σσ : gg ==>[ δ ▹ id₁ _ ] gg')
              (Lh : wk_lift_1cell_factor D (id_disp xx) gg)
              (Lh' : wk_lift_1cell_factor D (id_disp xx) gg').

      Local Definition cartesian_1cell_id_wk_2cell_lift_cell
        : Lh ==>[ (pr12 Lh • δ) • (pr12 Lh')^-1 ] Lh'.
      Proof.
        refine (transportf
                  (λ z, _ ==>[ z ] _)
                  _
                  (disp_rinvunitor _
                   •• disp_cell_wk_lift_1cell_factor D _ Lh
                   •• σσ
                   •• disp_inv_cell (disp_cell_wk_lift_1cell_factor D _ Lh')
                   •• disp_runitor _)).
        abstract
          (cbn ;
           rewrite !vassocl ;
           rewrite vcomp_runitor ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite vcomp_runitor ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite vcomp_runitor ;
           rewrite !vassocr ;
           rewrite rinvunitor_runitor ;
           apply id2_left).
      Defined.

      Local Definition cartesian_1cell_id_wk_2cell_lift_comm
        : transportf
            (λ z, Lh ;; id_disp xx ==>[ z] gg')
            (wk_lift_2cell_factor_type_path D (id_disp xx) σσ Lh Lh')
            ((cartesian_1cell_id_wk_2cell_lift_cell ▹▹ id_disp xx)
             •• disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh')
          =
          disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh •• σσ.
      Proof.
        unfold cartesian_1cell_id_wk_2cell_lift_cell.
        rewrite disp_rwhisker_transport_left_new.
        rewrite disp_mor_transportf_postwhisker.
        rewrite transport_f_f ; cbn.
        etrans.
        {
          do 2 apply maponpaths.
          apply disp_id2_left_alt.
        }
        rewrite disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpaths_2.
          exact (!(@transportf_transpose_left
                     _
                     (λ z, _ ==>[ z ] _)
                     _ _ _ _ _
                     (disp_runitor_rinvunitor Lh'))).
        }
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite !disp_vassocr.
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        rewrite disp_vcomp_runitor.
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite !disp_vassocr.
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite disp_runitor_rinvunitor.
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 5 apply maponpaths_2.
          apply disp_id2_left.
        }
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 3 (refine (disp_vassocl _ _ _ @ _) ; apply maponpaths).
          do 2 apply maponpaths.
          refine (disp_vassocr _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply disp_runitor_rinvunitor.
          }
          unfold transportb.
          etrans.
          {
            apply disp_mor_transportf_postwhisker.
          }
          apply maponpaths.
          apply disp_id2_left.
        }
        unfold transportb.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply (disp_vcomp_linv (disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh')).
        }
        unfold transportb.
        rewrite disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply disp_id2_right.
        }
        unfold transportb.
        rewrite transport_f_f.
        apply (transportf_set (λ z, _ ==>[ z ] _)).
        apply cellset_property.
      Qed.

      Local Definition cartesian_1cell_id_wk_2cell_lift_unique
        : isaprop (wk_lift_2cell_factor_type D (id_disp xx) σσ Lh Lh').
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply disp_cellset_property.
        }
        pose (p₁ := maponpaths
                      (transportb
                         (λ z, _ ==>[ z ] _)
                         (wk_lift_2cell_factor_type_path D (id_disp xx) σσ Lh Lh'))
                      (pr2 φ₁ @ !(pr2 φ₂))).
        rewrite !transportbfinv in p₁.
        pose (maponpaths
                (λ z, z •• disp_inv_cell (disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh'))
                p₁) as p₂.
        cbn in p₂.
        rewrite !disp_vassocl in p₂.
        pose (p₃ := maponpaths
                      (transportf
                         (λ z, _ ==>[ z ] _)
                         (vassocl _ _ _))
                      p₂).
        rewrite !transportfbinv in p₃.
        pose (p₄ := maponpaths
                      (λ z, _ •• z)
                      (!disp_vcomp_rinv
                        (disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh'))
                    @ p₃
                    @ maponpaths
                        (λ z, _ •• z)
                        (disp_vcomp_rinv
                           (disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh'))).
        cbn in p₄.
        unfold transportb in p₄.
        rewrite !disp_mor_transportf_prewhisker in p₄.
        pose (p₅ := !(transportbfinv _ _ _)
                    @ maponpaths _ p₄
                    @ transportbfinv _ _ _).
        rewrite !disp_id2_right in p₅.
        pose (p₆ := maponpaths
                      (transportf (λ z, _ ==>[ z ] _) (id2_right _))
                      p₅).
        rewrite !transportfbinv in p₆.
        pose (p₇ := maponpaths
                      (λ z, disp_rinvunitor _ •• (z •• disp_runitor _))
                      p₆).
        cbn in p₇.
        rewrite !disp_vcomp_runitor in p₇.
        unfold transportb in p₇.
        rewrite !disp_mor_transportf_prewhisker in p₇.
        rewrite !disp_vassocr in p₇.
        unfold transportb in p₇.
        rewrite !transport_f_f in p₇.
        rewrite !disp_rinvunitor_runitor in p₇.
        unfold transportb in p₇.
        rewrite !disp_mor_transportf_postwhisker in p₇.
        rewrite transport_f_f in p₇.
        rewrite !disp_id2_left in p₇.
        unfold transportb in p₇.
        rewrite !transport_f_f in p₇.
        pose (p := !(transportbfinv _ _ _)
                    @ maponpaths _ p₇
                    @ transportbfinv _ _ _).
        exact p.
      Qed.

      Definition cartesian_1cell_id_wk_2cell_lift
        : wk_lift_2cell_factor D (id_disp xx) σσ Lh Lh'.
      Proof.
        use iscontraprop1.
        - exact cartesian_1cell_id_wk_2cell_lift_unique.
        - exact (cartesian_1cell_id_wk_2cell_lift_cell
                 ,,
                 cartesian_1cell_id_wk_2cell_lift_comm).
      Defined.
    End IdCartesianTwoLift.

    Definition cartesian_1cell_id
      : cartesian_1cell D (id_disp xx).
    Proof.
      apply (wk_cartesian_1cell_to_cartesian_1cell (pr2 HB)).
      split.
      - exact @cartesian_1cell_id_wk_1cell_lift.
      - exact @cartesian_1cell_id_wk_2cell_lift.
    Defined.
  End IdCartesian.

  Section CompCartesian.
    Context {x y z : B}
            {f : x --> y} {g : y --> z}
            {xx : D x}
            {yy : D y}
            {zz : D z}
            {ff : xx -->[ f ] yy}
            {gg : yy -->[ g ] zz}
            (Hff : cartesian_1cell D ff)
            (Hgg : cartesian_1cell D gg).

    Section CompCartesianLiftOneCell.
      Context {c : B}
              {cc : D c}
              {h : c --> x}
              (kk : cc -->[ h · (f · g) ] zz).

      Let kk' : cc -->[ (h · f) · g ] zz
        := transport_along_inv_2cell
             (pr2 HB)
             (lassociator_invertible_2cell _ _ _)
             kk.
      Let ℓ₁ : cc -->[ h · f ] yy
        := pr1 (cartesian_1cell_lift_1cell _ _ Hgg kk').
      Let ℓ₂ : cc -->[ h ] xx
        := pr1 (cartesian_1cell_lift_1cell _ _ Hff ℓ₁).
      Let γ₁ : disp_invertible_2cell
                 (id2_invertible_2cell _)
                 (ℓ₁ ;; gg)
                 kk'
        := pr2 (cartesian_1cell_lift_1cell _ _ Hgg kk').
      Let γ₂ : disp_invertible_2cell
                 (id2_invertible_2cell _)
                 (ℓ₂ ;; ff)
                 ℓ₁
        := pr2 (cartesian_1cell_lift_1cell _ _ Hff ℓ₁).
      Let γ₃ : disp_invertible_2cell
                 (rassociator_invertible_2cell h f g)
                 kk'
                 kk
        := transport_along_inv_2cell_disp_invertible_2cell
             (pr2 HB)
             (lassociator_invertible_2cell _ _ _)
             kk.

      Definition comp_cartesian_1cell_lift_1cell_factor
        : lift_1cell_factor D (ff ;; gg) kk.
      Proof.
        refine (ℓ₂ ,, _).
        refine (transportf
                  (λ z, disp_invertible_2cell z _ _)
                  _
                  (vcomp_disp_invertible
                     (vcomp_disp_invertible
                        (vcomp_disp_invertible
                           (disp_invertible_2cell_lassociator ℓ₂ ff gg)
                           (disp_invertible_2cell_rwhisker gg γ₂))
                        γ₁)
                     γ₃)).
        abstract
          (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
           cbn ;
           rewrite id2_rwhisker, !id2_right ;
           apply lassociator_rassociator).
      Defined.
    End CompCartesianLiftOneCell.

    Section CompCartesianLiftTwoCell.
      Context {c : B}
              {cc : D c}
              {h h' : c --> x}
              {kk₁ : cc -->[ h · (f · g) ] zz}
              {kk₂ : cc -->[ h' · (f · g) ] zz}
              {δ : h ==> h'}
              (σσ : kk₁ ==>[ δ ▹ f · g] kk₂)
              (Lh : lift_1cell_factor D (ff ;; gg) kk₁)
              (Lh' : lift_1cell_factor D (ff ;; gg) kk₂).

      Let κκ₁ : cc -->[ h · f · g] zz
        := transport_along_inv_2cell
             (pr2 HB)
             (lassociator_invertible_2cell h f g)
             kk₁.
      Let γ₁ : disp_invertible_2cell
                 (rassociator_invertible_2cell h f g)
                 κκ₁
                 kk₁
        := transport_along_inv_2cell_disp_invertible_2cell
              (pr2 HB)
              (lassociator_invertible_2cell h f g)
              kk₁.
      Let κκ₂ : cc -->[ h' · f · g] zz
        := transport_along_inv_2cell
             (pr2 HB)
             (lassociator_invertible_2cell h' f g)
             kk₂.
      Let γ₂ : disp_invertible_2cell
                 (rassociator_invertible_2cell h' f g)
                 κκ₂
                 kk₂
        := transport_along_inv_2cell_disp_invertible_2cell
              (pr2 HB)
              (lassociator_invertible_2cell h' f g)
              kk₂.

      Local Lemma help_path
            {w : B}
            (q : w --> x)
        : comp_of_invertible_2cell
            (rassociator_invertible_2cell q f g)
            (comp_of_invertible_2cell
               (id2_invertible_2cell (q · (f · g)))
               (lassociator_invertible_2cell q f g))
          =
          id2_invertible_2cell (q · f · g).
      Proof.
        use subtypePath.
        {
          intro.
          apply isaprop_is_invertible_2cell.
        }
        cbn.
        rewrite id2_left.
        apply rassociator_lassociator.
      Qed.

      Let Lκ₁ : lift_1cell_factor D gg κκ₁.
      Proof.
        refine (pr1 Lh ;; ff ,, _).
        exact (transportf
                 (λ z, disp_invertible_2cell z _ _)
                 (help_path h)
                 (vcomp_disp_invertible
                    (disp_invertible_2cell_rassociator (pr1 Lh) ff gg)
                    (vcomp_disp_invertible
                       (pr2 Lh)
                       (inverse_of_disp_invertible_2cell γ₁)))).
      Defined.

      Let Lκ₂ : lift_1cell_factor D gg κκ₂.
      Proof.
        refine (pr1 Lh' ;; ff ,, _).
        exact (transportf
                 (λ z, disp_invertible_2cell z _ _)
                 (help_path h')
                 (vcomp_disp_invertible
                    (disp_invertible_2cell_rassociator (pr1 Lh') ff gg)
                    (vcomp_disp_invertible
                       (pr2 Lh')
                       (inverse_of_disp_invertible_2cell γ₂)))).
      Defined.

      Let Lq₁ : lift_1cell_factor D ff Lκ₁.
      Proof.
        simple refine (_ ,, _).
        - exact (pr1 Lh).
        - apply disp_id2_invertible_2cell.
      Defined.

      Let Lq₂ : lift_1cell_factor D ff Lκ₂.
      Proof.
        simple refine (_ ,, _).
        - exact (pr1 Lh').
        - apply disp_id2_invertible_2cell.
      Defined.

      Let σσ' : κκ₁ ==>[ δ ▹ f ▹ g ] κκ₂.
      Proof.
        refine (transportb
                  (λ z, _ ==>[ z ] _)
                  _
                  (γ₁ •• σσ •• disp_inv_cell γ₂)).
        abstract
          (cbn ;
           rewrite <- rwhisker_rwhisker_alt ;
           rewrite !vassocl ;
           rewrite rassociator_lassociator ;
           rewrite id2_right ;
           apply idpath).
      Defined.

      Definition comp_cartesian_1cell_lift_2cell_factor_unique
        : isaprop (lift_2cell_factor_type D (ff ;; gg) σσ Lh Lh').
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply disp_cellset_property.
        }
        use (isaprop_lift_of_lift_2cell
                 _ _
                 (pr2 Hff c cc h h' _ _ δ _ Lq₁ Lq₂)).
        - exact (pr2 Hgg c cc (h · f) (h' · f) κκ₁ κκ₂ (δ ▹ f) σσ' Lκ₁ Lκ₂).
        - unfold disp_cell_lift_1cell_factor.
          unfold Lq₂ ; cbn.
          rewrite disp_id2_right.
          unfold transportb.
          rewrite transport_f_f.
          rewrite disp_id2_left.
          unfold transportb.
          enough (pr1 φ₁ ▹▹ ff
                  =
                  pr11 (pr2 Hgg c cc (h · f) (h' · f) κκ₁ κκ₂ (δ ▹ f) σσ' Lκ₁ Lκ₂))
            as H.
          {
            etrans.
            {
              apply maponpaths.
              exact H.
            }
            apply maponpaths_2.
            apply cellset_property.
          }
          use (isaprop_lift_of_lift_2cell
                 _ _
                 (pr2 Hgg c cc (h · f) (h' · f) κκ₁ κκ₂ (δ ▹ f) σσ' Lκ₁ Lκ₂)).
          + unfold σσ' ; cbn.
            etrans.
            {
              do 2 apply maponpaths.
              exact (transportf_disp_invertible_2cell (help_path _) _).
            }
            cbn.
            rewrite disp_mor_transportf_prewhisker.
            rewrite transport_f_f.
            refine (!_).
            etrans.
            {
              apply maponpaths_2.
              exact (transportf_disp_invertible_2cell (help_path _) _).
            }
            cbn.
            unfold transportb.
            rewrite disp_mor_transportf_prewhisker.
            rewrite disp_mor_transportf_postwhisker.
            rewrite transport_f_f.
            etrans.
            {
              rewrite !disp_vassocl.
              unfold transportb.
              rewrite !disp_mor_transportf_prewhisker.
              rewrite !transport_f_f.
              etrans.
              {
                do 3 apply maponpaths.
                rewrite !disp_vassocr.
                unfold transportb.
                rewrite transport_f_f.
                apply maponpaths.
                do 2 apply maponpaths_2.
                exact (disp_vcomp_linv γ₁).
              }
              unfold transportb.
              rewrite !disp_mor_transportf_prewhisker.
              rewrite !disp_mor_transportf_postwhisker.
              rewrite !disp_mor_transportf_prewhisker.
              rewrite disp_id2_left.
              unfold transportb.
              rewrite !disp_mor_transportf_postwhisker.
              rewrite !disp_mor_transportf_prewhisker.
              rewrite !transport_f_f.
              apply idpath.
            }
            etrans.
            {
              do 2 apply maponpaths.
              rewrite disp_vassocr.
              apply maponpaths.
              apply maponpaths_2.
              exact (!(pr2 φ₁)).
            }
            unfold transportb.
            rewrite !disp_mor_transportf_postwhisker.
            rewrite !disp_mor_transportf_prewhisker.
            rewrite !transport_f_f.
            rewrite !disp_vassocr.
            unfold transportb.
            rewrite !disp_mor_transportf_postwhisker.
            rewrite !transport_f_f.
            rewrite <- disp_rwhisker_rwhisker_rassociator.
            unfold transportb.
            rewrite !disp_mor_transportf_postwhisker.
            rewrite !transport_f_f.
            apply maponpaths_2.
            apply cellset_property.
          + apply eq_lift_2cell.
        - unfold disp_cell_lift_1cell_factor.
          unfold Lq₂ ; cbn.
          rewrite disp_id2_right.
          unfold transportb.
          rewrite transport_f_f.
          rewrite disp_id2_left.
          unfold transportb.
          enough (pr1 φ₂ ▹▹ ff
                  =
                  pr11 (pr2 Hgg c cc (h · f) (h' · f) κκ₁ κκ₂ (δ ▹ f) σσ' Lκ₁ Lκ₂))
            as H.
          {
            etrans.
            {
              apply maponpaths.
              exact H.
            }
            apply maponpaths_2.
            apply cellset_property.
          }
          use (isaprop_lift_of_lift_2cell
                 _ _
                 (pr2 Hgg c cc (h · f) (h' · f) κκ₁ κκ₂ (δ ▹ f) σσ' Lκ₁ Lκ₂)).
          + unfold σσ' ; cbn.
            etrans.
            {
              do 2 apply maponpaths.
              exact (transportf_disp_invertible_2cell (help_path _) _).
            }
            cbn.
            rewrite disp_mor_transportf_prewhisker.
            rewrite transport_f_f.
            refine (!_).
            etrans.
            {
              apply maponpaths_2.
              exact (transportf_disp_invertible_2cell (help_path _) _).
            }
            cbn.
            unfold transportb.
            rewrite disp_mor_transportf_prewhisker.
            rewrite disp_mor_transportf_postwhisker.
            rewrite transport_f_f.
            etrans.
            {
              rewrite !disp_vassocl.
              unfold transportb.
              rewrite !disp_mor_transportf_prewhisker.
              rewrite !transport_f_f.
              etrans.
              {
                do 3 apply maponpaths.
                rewrite !disp_vassocr.
                unfold transportb.
                rewrite transport_f_f.
                apply maponpaths.
                do 2 apply maponpaths_2.
                exact (disp_vcomp_linv γ₁).
              }
              unfold transportb.
              rewrite !disp_mor_transportf_prewhisker.
              rewrite !disp_mor_transportf_postwhisker.
              rewrite !disp_mor_transportf_prewhisker.
              rewrite disp_id2_left.
              unfold transportb.
              rewrite !disp_mor_transportf_postwhisker.
              rewrite !disp_mor_transportf_prewhisker.
              rewrite !transport_f_f.
              apply idpath.
            }
            etrans.
            {
              do 2 apply maponpaths.
              rewrite disp_vassocr.
              apply maponpaths.
              apply maponpaths_2.
              exact (!(pr2 φ₂)).
            }
            unfold transportb.
            rewrite !disp_mor_transportf_postwhisker.
            rewrite !disp_mor_transportf_prewhisker.
            rewrite !transport_f_f.
            rewrite !disp_vassocr.
            unfold transportb.
            rewrite !disp_mor_transportf_postwhisker.
            rewrite !transport_f_f.
            rewrite <- disp_rwhisker_rwhisker_rassociator.
            unfold transportb.
            rewrite !disp_mor_transportf_postwhisker.
            rewrite !transport_f_f.
            apply maponpaths_2.
            apply cellset_property.
        + apply eq_lift_2cell.
      Qed.

      Let ℓ₁ : Lκ₁ ==>[ δ ▹ f] Lκ₂
        := cartesian_1cell_lift_2cell _ _ Hgg σσ' Lκ₁ Lκ₂.
      Let ℓ₂ : Lh ==>[ δ] Lh'
        := cartesian_1cell_lift_2cell _ _ Hff ℓ₁ Lq₁ Lq₂.

      Local Lemma comp_cartesian_1cell_lift_2cell_factor_commute
        : transportf
            (λ q, _ ==>[ q ] _)
            (id2_right (δ ▹ f · g) @ ! id2_left (δ ▹ f · g))
            ((ℓ₂ ▹▹ ff ;; gg) •• disp_cell_lift_1cell_factor D (ff ;; gg) Lh')
          =
          disp_cell_lift_1cell_factor D (ff ;; gg) Lh •• σσ.
      Proof.
        use (disp_vcomp_rcancel _ (pr2 (inverse_of_disp_invertible_2cell γ₂))).
        use (disp_vcomp_lcancel _ (is_disp_invertible_2cell_rassociator _ _ _)).
        rewrite !disp_mor_transportf_postwhisker.
        rewrite !disp_mor_transportf_prewhisker.
        etrans.
        {
          rewrite !disp_vassocr.
          unfold transportb.
          rewrite disp_mor_transportf_postwhisker.
          rewrite !transport_f_f.
          rewrite (@transportf_transpose_right
                     _
                     (λ z, _ ==>[ z ] _)
                     _ _ _ _ _
                     (disp_rwhisker_rwhisker_rassociator ℓ₂ ff gg)).
          rewrite !disp_mor_transportf_postwhisker.
          rewrite transport_f_f.
          apply idpath.
        }
        assert (q₁ : cartesian_1cell_lift_2cell D ff Hff ℓ₁ Lq₁ Lq₂ ▹▹ ff
                     =
                     ℓ₁).
        {
          pose (p := cartesian_1cell_lift_2cell_commutes _ _ Hff ℓ₁ Lq₁ Lq₂).
          cbn in p.
          rewrite disp_id2_left in p.
          rewrite disp_id2_right in p.
          unfold transportb in p.
          rewrite transport_f_f in p.
          etrans.
          {
            exact (@transportb_transpose_right
                     _ (λ z, _ ==>[ z ] _)
                     _ _ _ _ _
                     p).
          }
          unfold transportb.
          rewrite !transport_f_f.
          apply (transportf_set (λ z, _ ==>[ z ] _)).
          apply cellset_property.
        }
        etrans.
        {
          apply maponpaths.
          do 3 apply maponpaths_2.
          apply maponpaths.
          exact q₁.
        }
        assert (q₂ : ∑ w,
                     ℓ₁ ▹▹ gg
                     •• disp_rassociator _ _ _
                     •• pr2 Lh'
                     •• disp_inv_cell γ₂
                     =
                     transportf
                       (λ z, _ ==>[ z ] _)
                       w
                       (disp_rassociator _ _ _
                        •• pr2 Lh
                        •• disp_inv_cell γ₁
                        •• σσ')).
        {
          pose (p := cartesian_1cell_lift_2cell_commutes _ _ Hgg σσ' Lκ₁ Lκ₂).
          cbn in p.
          pose (p' := p @ maponpaths
                            (λ z, z •• _)
                            (transportf_disp_invertible_2cell
                               (help_path h)
                               _)).
          cbn in p'.
          rewrite !disp_vassocr in p'.
          unfold transportb in p'.
          rewrite transport_f_f in p'.
          rewrite disp_mor_transportf_postwhisker in p'.
          pose (p'' := @transportb_transpose_left
                         _ (λ z, _ ==>[ z ] _)
                         _ _ _ _ _
                         p').
          unfold transportb in p''.
          rewrite transport_f_f in p''.
          simple refine (_ ,, _).
          {
            abstract
              (cbn ;
               rewrite !id2_right ;
               rewrite rassociator_lassociator, id2_left ;
               rewrite !vassocl ;
               rewrite rassociator_lassociator, id2_right ;
               apply idpath).
          }
          cbn.
          refine (_ @ maponpaths _ p'').
          rewrite !transport_f_f.
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths.
            apply (transportf_disp_invertible_2cell (help_path h')).
          }
          rewrite disp_mor_transportf_prewhisker.
          rewrite transport_f_f.
          cbn.
          rewrite !disp_vassocr.
          unfold transportb.
          rewrite !transport_f_f.
          apply (transportf_set (λ z, _ ==>[ z ] _)).
          apply cellset_property.
        }
        etrans.
        {
          apply maponpaths.
          exact (pr2 q₂).
        }
        rewrite transport_f_f.
        unfold σσ'.
        unfold transportb.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite !disp_vassocl.
        unfold transportb.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 3 apply maponpaths.
          refine (disp_vassocr _ _ _ @ _) ; apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply disp_vcomp_linv.
          }
          unfold transportb.
          rewrite disp_mor_transportf_postwhisker.
          rewrite disp_id2_left.
          unfold transportb.
          rewrite transport_f_f.
          apply idpath.
        }
        unfold transportb.
        rewrite transport_f_f.
        rewrite !disp_mor_transportf_prewhisker.
        rewrite !transport_f_f.
        apply maponpaths_2.
        apply cellset_property.
      Qed.

      Definition comp_cartesian_1cell_lift_2cell_factor
        : lift_2cell_factor D (ff ;; gg) σσ Lh Lh'.
      Proof.
        use iscontraprop1.
        - exact comp_cartesian_1cell_lift_2cell_factor_unique.
        - exact (ℓ₂ ,, comp_cartesian_1cell_lift_2cell_factor_commute).
      Defined.
    End CompCartesianLiftTwoCell.

    Definition comp_cartesian_1cell
      : cartesian_1cell D (ff ;; gg).
    Proof.
      split.
      - exact @comp_cartesian_1cell_lift_1cell_factor.
      - exact @comp_cartesian_1cell_lift_2cell_factor.
    Defined.
  End CompCartesian.

  Definition cartesian_1cell_disp_adj_equiv
             (HD : disp_univalent_2_0 D)
             {x y : B}
             {f : x --> y}
             {Hf : left_adjoint_equivalence f}
             {xx : D x}
             {yy : D y}
             {ff : xx -->[ f ] yy}
             (Hff : disp_left_adjoint_equivalence Hf ff)
    : cartesian_1cell D ff.
  Proof.
    use (disp_J_2_0
           (pr1 HB) HD
           (λ x y f xx yy ff, cartesian_1cell D (pr1 ff))
           _
           ((ff ,, Hff) : disp_adjoint_equivalence (f ,, Hf) xx yy)) ; cbn.
    intros.
    apply cartesian_1cell_id.
  Defined.

  Definition invertible_2cell_from_cartesian_help
             {x y : B}
             {f g : x --> y}
             {p : f = g}
             {xx : D x}
             {yy : D y}
             {ff : xx -->[ f ] yy}
             (Hff : cartesian_1cell D ff)
             {gg : xx -->[ g ] yy}
             (pp : transportf (λ z, _ -->[ z ] _) p ff = gg)
    : cartesian_1cell D gg.
  Proof.
    induction p, pp.
    exact Hff.
  Defined.

  Definition invertible_2cell_from_cartesian
             (HD : disp_univalent_2_1 D)
             {x y : B}
             {f g : x --> y}
             {α : f ==> g}
             {Hα : is_invertible_2cell α}
             {xx : D x}
             {yy : D y}
             {ff : xx -->[ f ] yy}
             (Hff : cartesian_1cell D ff)
             {gg : xx -->[ g ] yy}
             {αα : ff ==>[ α ] gg}
             (Hαα : is_disp_invertible_2cell Hα αα)
    : cartesian_1cell D gg.
  Proof.
    use (invertible_2cell_from_cartesian_help Hff).
    - exact (isotoid_2_1 (pr2 HB) (make_invertible_2cell Hα)).
    - refine (disp_isotoid_2_1
                _
                HD
                (isotoid_2_1 (pr2 HB) (make_invertible_2cell Hα))
                ff gg
                _).
      simple refine (transportb
                       (λ z, disp_invertible_2cell z ff gg)
                       (idtoiso_2_1_isotoid_2_1 _ _)
                       (_ ,, _)).
      + exact αα.
      + exact Hαα.
  Defined.
End ExamplesOfCartesian1Cells.
