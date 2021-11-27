(*********************************************************************

 Cleavings of bicategories

 In this file, we define cleaving of bicategories

 Content:
 1. Definition of cleaving
 2. Properties of cartesian 1-cells
 3. Properties of cartesian 2-cells

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
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.Colimits.Pullback.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.StrictToPseudo.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.

Local Open Scope cat.
Local Open Scope mor_disp.

(** 1. Definition of cleaving *)

Section BicatCleaving.
  Context {B : bicat}
          (D : disp_bicat B).

  Section Cartesian1cell.
    Context {a b : B}
            {f : a --> b}
            {aa : D a}
            {bb : D b}
            (ff : aa -->[ f ] bb).

    Definition lift_1cell_factor
               {c : B}
               {cc : D c}
               {h : c --> a}
               (gg : cc -->[ h · f ] bb)
      : UU
      := ∑ (hh : cc -->[ h ] aa),
         disp_invertible_2cell
           (id2_invertible_2cell _)
           (hh ;; ff)
           gg.

    Coercion disp_mor_lift_1cell_factor
             {c : B}
             {cc : D c}
             {h : c --> a}
             {gg : cc -->[ h · f ] bb}
             (Lh : lift_1cell_factor gg)
      : cc -->[ h ] aa
      := pr1 Lh.

    Definition disp_cell_lift_1cell_factor
               {c : B}
               {cc : D c}
               {h : c --> a}
               {gg : cc -->[ h · f ] bb}
               (Lh : lift_1cell_factor gg)
      : disp_invertible_2cell _ (Lh ;; ff) gg
      := pr2 Lh.

    (** change name *)
    Definition lift_2cell_factor_type
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[ h · f ] bb}
               {gg' : cc -->[ h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell_factor gg)
               (Lh' : lift_1cell_factor gg')
      : UU
      := ∑ (δδ : Lh ==>[ δ ] Lh'),
         transportf
           (λ z, _ ==>[ z ] _)
           (id2_right _ @ ! id2_left _ )
           (δδ ▹▹ ff •• disp_cell_lift_1cell_factor Lh')
         =
         disp_cell_lift_1cell_factor Lh •• σσ.

    Definition lift_2cell_factor
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell_factor gg)
               (Lh' : lift_1cell_factor gg')
      : UU
      := iscontr (lift_2cell_factor_type σσ Lh Lh').

    Coercion disp_cell_lift_2cell_factor
             {c : B}
             {cc : D c}
             {h h' : c --> a}
             {gg : cc -->[h · f ] bb}
             {gg' : cc -->[h' · f ] bb}
             {δ : h ==> h'}
             {σσ : gg ==>[ δ ▹ f] gg'}
             {Lh : lift_1cell_factor gg}
             {Lh' : lift_1cell_factor gg'}
             (Hσσ : lift_2cell_factor σσ Lh Lh')
      : Lh ==>[ δ ] Lh'
      := pr11 Hσσ.

    Definition eq_lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell_factor gg}
               {Lh' : lift_1cell_factor gg'}
               (Hσσ : lift_2cell_factor σσ Lh Lh')
      : transportf
          (λ z, _ ==>[ z ] _)
          (id2_right _ @ ! id2_left _ )
          (Hσσ ▹▹ ff •• disp_cell_lift_1cell_factor Lh')
        =
        disp_cell_lift_1cell_factor Lh •• σσ
      := pr21 Hσσ.

    Definition eq_lift_2cell_alt
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell_factor gg}
               {Lh' : lift_1cell_factor gg'}
               (Hσσ : lift_2cell_factor σσ Lh Lh')
      : Hσσ ▹▹ ff •• disp_cell_lift_1cell_factor Lh'
        =
        transportb
          (λ z, _ ==>[ z ] _)
          (id2_right _ @ ! id2_left _ )
          (disp_cell_lift_1cell_factor Lh •• σσ).
    Proof.
      rewrite <- (eq_lift_2cell Hσσ).
      rewrite transportbfinv.
      apply idpath.
    Qed.

    Definition isaprop_lift_of_lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell_factor gg}
               {Lh' : lift_1cell_factor gg'}
               (Hσσ : lift_2cell_factor σσ Lh Lh')
               (δδ₁ : Lh ==>[ δ ] Lh')
               (δδ₂ : Lh ==>[ δ ] Lh')
               (Pδδ₁ : transportf
                         (λ z, _ ==>[ z ] _)
                         (id2_right _ @ ! id2_left _ )
                         (δδ₁ ▹▹ ff •• disp_cell_lift_1cell_factor Lh')
                       =
                       disp_cell_lift_1cell_factor Lh •• σσ)
               (Pδδ₂ : transportf
                         (λ z, _ ==>[ z ] _)
                         (id2_right _ @ ! id2_left _ )
                         (δδ₂ ▹▹ ff •• disp_cell_lift_1cell_factor Lh')
                       =
                       disp_cell_lift_1cell_factor Lh •• σσ)
      : δδ₁ = δδ₂.
    Proof.
      pose (proofirrelevance _ (isapropifcontr Hσσ) (δδ₁ ,, Pδδ₁) (δδ₂ ,, Pδδ₂)) as p.
      exact (maponpaths pr1 p).
    Qed.

    Definition cartesian_1cell
      : UU
      := (∏ (c : B)
            (cc : D c)
            (h : c --> a)
            (gg : cc -->[ h · f ] bb),
          lift_1cell_factor gg)
         ×
         ∏ (c : B)
           (cc : D c)
           (h h' : c --> a)
           (gg : cc -->[h · f ] bb)
           (gg' : cc -->[h' · f ] bb)
           (δ : h ==> h')
           (σσ : gg ==>[ δ ▹ f] gg')
           (Lh : lift_1cell_factor gg)
           (Lh' : lift_1cell_factor gg'),
         lift_2cell_factor σσ Lh Lh'.

    Definition cartesian_1cell_lift_1cell
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h : c --> a}
               (gg : cc -->[ h · f ] bb)
      : lift_1cell_factor gg
      := pr1 Hff c cc h gg.

    Definition cartesian_1cell_lift_2cell
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell_factor gg)
               (Lh' : lift_1cell_factor gg')
      : Lh ==>[ δ ] Lh'
      := pr2 Hff c cc h h' gg gg' δ σσ Lh Lh'.

    Definition cartesian_1cell_lift_2cell_commutes
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell_factor gg)
               (Lh' : lift_1cell_factor gg')
      : transportf
          (λ z, _ ==>[ z ] _)
          (id2_right _ @ ! id2_left _ )
          (cartesian_1cell_lift_2cell Hff σσ Lh Lh' ▹▹ ff
           ••
           disp_cell_lift_1cell_factor Lh')
        =
        disp_cell_lift_1cell_factor Lh •• σσ
      := eq_lift_2cell (pr2 Hff c cc h h' gg gg' δ σσ Lh Lh').
  End Cartesian1cell.

  Definition is_cartesian_2cell
             {x y : B}
             {xx : D x} {yy : D y}
             {f g : x --> y}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             {α : f ==> g}
             (αα : ff ==>[ α ] gg)
    : UU
    := ∏ (h : x --> y)
         (hh : xx -->[ h ] yy)
         (γ : h ==> f)
         (ββ : hh ==>[ γ • α ] gg),
       ∃! (γγ : hh ==>[ γ ] ff), (γγ •• αα) = ββ.

  Definition cartesian_lift_2cell
             {x y : B}
             {xx : D x}
             {yy : D y}
             {f g : x --> y}
             (gg : xx -->[ g ] yy)
             (α : f ==> g)
    : UU
    := ∑ (ff : xx -->[ f ] yy) (αα : ff ==>[ α ] gg), is_cartesian_2cell αα.

  Definition local_cleaving
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (gg : xx -->[ g ] yy)
         (α : f ==> g),
       cartesian_lift_2cell gg α.

  Definition global_cleaving
    : UU
    := ∏ (a b : B)
         (bb : D b)
         (f : a --> b),
       ∑ (aa : D a) (ff : aa -->[ f ] bb), cartesian_1cell ff.

  Definition lwhisker_cartesian
    : UU
    := ∏ (w x y : B)
         (ww : D w) (xx : D x) (yy : D y)
         (h : w --> x)
         (f g : x --> y)
         (hh : ww -->[ h ] xx)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       is_cartesian_2cell αα → is_cartesian_2cell (hh ◃◃ αα).

  Definition rwhisker_cartesian
    : UU
    := ∏ (x y z : B)
         (xx : D x) (yy : D y) (zz : D z)
         (f g : x --> y) (h : y --> z)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (hh : yy -->[ h ] zz)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       is_cartesian_2cell αα → is_cartesian_2cell (αα ▹▹ hh).

  Definition cleaving_of_bicats
    : UU
    := local_cleaving
       × global_cleaving
       × lwhisker_cartesian
       × rwhisker_cartesian.

  Coercion cleaving_of_bicats_local_cleaving
           (CD : cleaving_of_bicats)
    : local_cleaving
    := pr1 CD.

  Coercion cleaving_of_bicats_global_cleaving
           (CD : cleaving_of_bicats)
    : global_cleaving
    := pr12 CD.

  Coercion cleaving_of_bicats_lwhisker_cartesian
           (CD : cleaving_of_bicats)
    : lwhisker_cartesian
    := pr122 CD.

  Coercion cleaving_of_bicats_rwhisker_cartesian
           (CD : cleaving_of_bicats)
    : rwhisker_cartesian
    := pr222 CD.
End BicatCleaving.

(** 2. Properties of cartesian 1-cells *)
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

(** 3. Properties of cartesian 2-cells *)

Definition local_fib
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∏ (x y : B)
       (xx : D x)
       (yy : D y),
     cleaving (disp_hom xx yy).

(** Being a cartesian 2-cell is a proposition *)
Definition isaprop_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
  : isaprop (is_cartesian_2cell D αα).
Proof.
  unfold is_cartesian_2cell.
  repeat (use impred ; intro).
  apply isapropiscontr.
Qed.

(** The two definitions of local cleavings coincide *)
Definition cartesian_2cell_to_cartesian
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
           (Hαα : is_cartesian_2cell D αα)
  : @is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα.
Proof.
  intros h γ hh γα.
  exact (Hαα h hh γ γα).
Qed.

Definition cartesian_to_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
           (Hαα : @is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
  : is_cartesian_2cell D αα.
Proof.
  intros h hh γ γα.
  exact (Hαα h γ hh γα).
Qed.

Definition cartesian_2cell_weq_cartesian
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
  : (@is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
    ≃
    is_cartesian_2cell D αα.
Proof.
  use weqimplimpl.
  - apply cartesian_to_cartesian_2cell.
  - apply cartesian_2cell_to_cartesian.
  - apply isaprop_is_cartesian.
  - apply isaprop_is_cartesian_2cell.
Qed.

Definition local_cleaving_to_local_fib
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_cleaving D)
  : local_fib D.
Proof.
  intros x y xx yy g f α gg ; cbn in *.
  pose (HD x y xx yy f g gg α) as lift.
  unfold cartesian_lift.
  unfold cartesian_lift_2cell in lift.
  cbn.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply cartesian_2cell_to_cartesian.
  exact (pr22 lift).
Defined.

Definition local_fib_to_local_cleaving
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_fib D)
  : local_cleaving D.
Proof.
  intros x y xx yy g f α gg ; cbn in *.
  pose (HD x y xx yy f g gg α) as lift.
  unfold cartesian_lift in lift.
  unfold cartesian_lift_2cell.
  cbn.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply cartesian_to_cartesian_2cell.
  exact (pr22 lift).
Defined.

Definition local_fib_weq_local_cleaving
           {B : bicat}
           (D : disp_bicat B)
  : local_cleaving D ≃ local_fib D.
Proof.
  use make_weq.
  - exact local_cleaving_to_local_fib.
  - use gradth.
    + exact local_fib_to_local_cleaving.
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_cartesian_2cell).
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_cartesian).
Defined.

(** Properties of cartesian 2-cells *)
Definition identity_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f : x --> y}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : is_cartesian_2cell D (disp_id2 ff).
Proof.
  apply cartesian_to_cartesian_2cell.
  exact (@is_cartesian_id_disp _ (disp_hom xx yy) f ff).
Defined.

Definition vcomp_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g h : x --> y}
           {α : f ==> g} {β : g ==> h}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           {hh : xx -->[ h ] yy}
           {αα : ff ==>[ α ] gg}
           {ββ : gg ==>[ β ] hh}
           (Hαα : is_cartesian_2cell D αα)
           (Hββ : is_cartesian_2cell D ββ)
  : is_cartesian_2cell D (αα •• ββ).
Proof.
  apply cartesian_to_cartesian_2cell.
  exact (@is_cartesian_comp_disp
           _ (disp_hom xx yy)
           f ff
           g gg
           h hh
           α β
           αα ββ
           (cartesian_2cell_to_cartesian _ Hαα)
           (cartesian_2cell_to_cartesian _ Hββ)).
Defined.

Definition invertible_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {Hα : is_invertible_2cell α}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           {αα : ff ==>[ α ] gg}
           (Hαα : is_disp_invertible_2cell Hα αα)
  : is_cartesian_2cell D αα.
Proof.
  apply cartesian_to_cartesian_2cell.
  apply (is_cartesian_disp_iso (disp_hom_disp_invertible_2cell_to_iso _ Hαα)).
Defined.

Definition disp_hcomp_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           (CD : cleaving_of_bicats D)
           {b₁ b₂ b₃ : B}
           {f₁ f₂ : b₁ --> b₂}
           {g₁ g₂ : b₂ --> b₃}
           {α : f₁ ==> f₂}
           {β : g₁ ==> g₂}
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           {bb₃ : D b₃}
           {ff₁ : bb₁ -->[ f₁ ] bb₂}
           {ff₂ : bb₁ -->[ f₂ ] bb₂}
           {gg₁ : bb₂ -->[ g₁ ] bb₃}
           {gg₂ : bb₂ -->[ g₂ ] bb₃}
           {αα : ff₁ ==>[ α ] ff₂}
           {ββ : gg₁ ==>[ β ] gg₂}
           (Hαα : is_cartesian_2cell D αα)
           (Hββ : is_cartesian_2cell D ββ)
  : is_cartesian_2cell D (disp_hcomp αα ββ).
Proof.
  use vcomp_is_cartesian_2cell.
  - apply CD.
    exact Hαα.
  - apply CD.
    exact Hββ.
Defined.

(** Cartesian pseudofunctor *)
Definition cartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := (∏ (b₁ b₂ : B₁)
        (f : b₁ --> b₂)
        (bb₁ : D₁ b₁)
        (bb₂ : D₁ b₂)
        (ff : bb₁ -->[ f ] bb₂)
        (Hff : cartesian_1cell D₁ ff),
      cartesian_1cell D₂ (disp_psfunctor_mor _ _ _ FF ff))
     ×
     (∏ (b₁ b₂ : B₁)
        (f g : b₁ --> b₂)
        (α : f ==> g)
        (bb₁ : D₁ b₁)
        (bb₂ : D₁ b₂)
        (ff : bb₁ -->[ f ] bb₂)
        (gg : bb₁ -->[ g ] bb₂)
        (αα : ff ==>[ α ] gg)
        (Hαα : is_cartesian_2cell D₁ αα),
      is_cartesian_2cell D₂ (disp_psfunctor_cell _ _ _ FF αα)).

Definition cartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : cartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  split.
  - intros ? ? ? ? ? ? H.
    exact H.
  - intros ? ? ? ? ? ? ? ? ? ? H.
    exact H.
Defined.

Definition cartesian_comp_psfunctor
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           {D₃ : disp_bicat B₃}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₂ D₃ G}
           (HFF : cartesian_disp_psfunctor FF)
           (HGG : cartesian_disp_psfunctor GG)
  : cartesian_disp_psfunctor (disp_pseudo_comp _ _ _ _ _ FF GG).
Proof.
  split.
  - intros ? ? ? ? ? ? H.
    apply HGG.
    apply HFF.
    exact H.
  - intros ? ? ? ? ? ? ? ? ? ? H.
    apply HGG.
    apply HFF.
    exact H.
Defined.
