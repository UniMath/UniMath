(*********************************************************************

 Cleavings of bicategories

 In this file, we define cleaving of bicategories

 Content:
 1. Definition of cleaving
 2. Properties of cartesian 1-cells
 3. Properties of cartesian 2-cells
 4. Local opcleavings
 5. Properties of opcartesian 2-cells
 6. Cartesian pseudofunctors
 7. Cartesian pseudofunctors from global cleavings

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

Local Open Scope cat.
Local Open Scope mor_disp.

(** MOVE *)

(** END MOVE *)

Definition transport_1cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           (p : f = g)
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : xx -->[ g ] yy
  := transportf (λ z, _ -->[ z ] _) p ff.

Definition transport_1cell_disp_invertible_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           (p : f = g)
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : disp_invertible_2cell
      (inv_of_invertible_2cell (idtoiso_2_1 _ _ p))
      (transport_1cell p ff)
      ff.
Proof.
  induction p.
  exact (disp_id2_invertible_2cell ff).
Defined.

Definition transport_along_inv_2cell
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           (α : invertible_2cell f g)
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : xx -->[ g ] yy
  := transport_1cell (isotoid_2_1 HB α) ff.

Definition transport_along_inv_2cell_disp_invertible_2cell
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           (α : invertible_2cell f g)
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : disp_invertible_2cell
      (inv_of_invertible_2cell α)
      (transport_along_inv_2cell HB α ff)
      ff.
Proof.
  refine (transportf
            (λ z, disp_invertible_2cell z _ _)
            _
            (transport_1cell_disp_invertible_2cell
               (isotoid_2_1 HB α)
               ff)).
  abstract
    (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
     cbn ;
     rewrite idtoiso_2_1_isotoid_2_1 ;
     apply idpath).
Defined.

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

  Section Cartesian2Cell.
    Context {x y : B}
            {xx : D x} {yy : D y}
            {f g : x --> y}
            {ff : xx -->[ f ] yy}
            {gg : xx -->[ g ] yy}
            {α : f ==> g}
            {αα : ff ==>[ α ] gg}
            (Hαα : is_cartesian_2cell αα).

    Definition is_cartesian_2cell_factor
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : h ==> f)
               (ββ : hh ==>[ γ • α ] gg)
      : hh ==>[ γ ] ff
      := pr11 (Hαα h hh γ ββ).

    Definition is_cartesian_2cell_comm
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : h ==> f)
               (ββ : hh ==>[ γ • α ] gg)
      : (is_cartesian_2cell_factor hh γ ββ •• αα) = ββ
      := pr21 (Hαα h hh γ ββ).

    Definition is_cartesian_2cell_unique
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : h ==> f)
               (ββ : hh ==>[ γ • α ] gg)
               {γγ₁ γγ₂ : hh ==>[ γ ] ff}
               (pγγ₁ : (γγ₁ •• αα) = ββ)
               (pγγ₂ : (γγ₂ •• αα) = ββ)
      : γγ₁ = γγ₂.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (Hαα h hh γ ββ))
                  (γγ₁ ,, pγγ₁) (γγ₂ ,, pγγ₂))).
    Qed.
  End Cartesian2Cell.

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

(** Constructing cartesian 1-cells with lifts up to iso *)
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

(** Weak cartesian 1-cells and cartesian 1-cells *)
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
           {h : B ⟦ c, a ⟧}
           {gg : cc -->[ h · f] bb}
           (ℓ : lift_1cell_factor D ff gg)
  : wk_lift_1cell_factor D ff gg.
Proof.
  refine (h ,, id2_invertible_2cell _ ,, disp_mor_lift_1cell_factor D _ ℓ ,, _).
  refine (transportf
            (λ z, disp_invertible_2cell z _ _)
            _
            (disp_cell_lift_1cell_factor D _ ℓ)).
  abstract
    (use subtypePath ; [ intro ; apply isaprop_is_invertible_2cell | ] ;
     exact (!(id2_rwhisker _ _))).
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

Section CartesianToWkCartesianTwoLift.
  Context {B : bicat}
          {D : disp_bicat B}
          (HB : is_univalent_2_1 B)
          {a b : B}
          {f : a --> b}
          {aa : D a}
          {bb : D b}
          {ff : aa -->[ f ] bb}
          (Hff : cartesian_1cell D ff)
          {c : B}
          {cc : D c}
          {h h' : c --> a}
          {gg : cc -->[ h · f ] bb}
          {gg' : cc -->[ h' · f ] bb}
          {δ : h ==> h'}
          (σσ : gg ==>[ δ ▹ f ] gg')
          (Lh : wk_lift_1cell_factor D ff gg)
          (Lh' : wk_lift_1cell_factor D ff gg').

  Let ℓ : lift_1cell_factor D ff gg
    := wk_lift_1cell_factor_to_lift_1cell_factor HB Lh.
  Let ℓ' : lift_1cell_factor D ff gg'
    := wk_lift_1cell_factor_to_lift_1cell_factor HB Lh'.

  Definition cartesian_1cell_to_wk_cartesian_1cell_unique
    : isaprop (wk_lift_2cell_factor_type D ff σσ Lh Lh').
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply disp_cellset_property.
    }
  Admitted.

  Definition cartesian_1cell_to_wk_cartesian_1cell_lift_2cell
    : Lh ==>[ (pr12 Lh • δ) • (pr12 Lh')^-1 ] Lh'.
  Proof.
    pose (cartesian_1cell_lift_2cell _ _ Hff σσ ℓ ℓ').
    refine (transportf
              (λ z, _ ==>[ z ] _)
              _
              _).
  Admitted.
End CartesianToWkCartesianTwoLift.

Definition cartesian_1cell_to_wk_cartesian_1cell
           {B : bicat}
           {D : disp_bicat B}
           (HB : is_univalent_2_1 B)
           {a b : B}
           {f : a --> b}
           {aa : D a}
           {bb : D b}
           {ff : aa -->[ f ] bb}
           (Hff : cartesian_1cell D ff)
  : wk_cartesian_1cell D ff.
Proof.
  split.
  - intros c cc h gg.
    exact (lift_1cell_factor_to_wk_lift_1cell_factor
             (cartesian_1cell_lift_1cell D _ Hff gg)).
  - intros c cc h h' gg gg' δ σσ Lh Lh'.
    pose (ℓ := wk_lift_1cell_factor_to_lift_1cell_factor HB Lh).
    pose (ℓ' := wk_lift_1cell_factor_to_lift_1cell_factor HB Lh').
    pose (pr2 Hff c cc h h' gg gg' δ σσ ℓ ℓ').
    use iscontraprop1.
    + admit.
    + simple refine (_ ,, _).
      ** exact (cartesian_1cell_to_wk_cartesian_1cell_lift_2cell HB Hff σσ Lh Lh').
      ** cbn.
         admit.
Admitted.

Definition wk_cartesian_1cell_to_cartesian_1cell
           {B : bicat}
           {D : disp_bicat B}
           (HB : is_univalent_2_1 B)
           {a b : B}
           {f : a --> b}
           {aa : D a}
           {bb : D b}
           {ff : aa -->[ f ] bb}
           (Hff : wk_cartesian_1cell D ff)
  : cartesian_1cell D ff.
Proof.
  split.
  - intros c cc h gg.
    exact (wk_lift_1cell_factor_to_lift_1cell_factor HB (pr1 Hff _ _ _ gg)).
  - intros c cc h h' gg gg' δ σσ Lh Lh'.
    pose (ℓ := lift_1cell_factor_to_wk_lift_1cell_factor Lh).
    pose (ℓ' := lift_1cell_factor_to_wk_lift_1cell_factor Lh').
    pose (pr2 Hff c cc h h' gg gg' δ σσ ℓ ℓ') as w.
    use iscontraprop1.
    + admit.
    + simple refine (_ ,, _).
      ** refine (transportf
                   (λ z, _ ==>[ z ] _)
                   _
                   (pr11 w)).
         abstract
           (cbn ;
            rewrite id2_left, id2_right ;
            apply idpath).
      ** cbn.
         rewrite disp_rwhisker_transport_left_new.
         rewrite disp_mor_transportf_postwhisker.
         rewrite transport_f_f.
         pose (pr21 w) as p.
         cbn in p.
         unfold invertible_2cell in p.
         admit.
Admitted.

(** Examples of cartesian 1-cells *)
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
        assert (∑ p,
                disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh
                •• σσ
                =
                transportf
                  (λ z, _ ==>[ z ] _)
                  p
                  (disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh
                   •• σσ
                   •• disp_inv_cell (disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh')
                   •• disp_cell_wk_lift_1cell_factor D (id_disp xx) Lh')).
        {
          eexists.
          rewrite !disp_vassocl.
          rewrite disp_vcomp_linv.
          unfold transportb.
          rewrite !disp_mor_transportf_prewhisker.
          rewrite !transport_f_f.
          rewrite disp_id2_right.
          unfold transportb.
          rewrite disp_mor_transportf_prewhisker.
          rewrite transport_f_f.
          refine (!_).
          cbn.
          admit.
        }
        refine (_ @ !(pr2 X)).
      Admitted.

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

  Definition comp_cartesian_1cell
             {x y z : B}
             {f : x --> y} {g : y --> z}
             {xx : D x}
             {yy : D y}
             {zz : D z}
             {ff : xx -->[ f ] yy}
             {gg : yy -->[ g ] zz}
             (Hff : cartesian_1cell D ff)
             (Hgg : cartesian_1cell D gg)
    : cartesian_1cell D (ff ;; gg).
  Proof.
  Admitted.

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

Section AdjEquivBetweenCartesian.
  Context {B : bicat}
          {D : disp_bicat B}
          (HB_2_1 : is_univalent_2_1 B).

  Definition map_between_cartesian_1cell
             {x y : B}
             {f : x --> y}
             {xx₁ xx₂ : D x}
             {yy : D y}
             {ff₁ : xx₁ -->[ f ] yy}
             (Hff₁ : cartesian_1cell D ff₁)
             {ff₂ : xx₂ -->[ f ] yy}
             (Hff₂ : cartesian_1cell D ff₂)
    : xx₁ -->[ id₁ _ ] xx₂.
  Proof.
    Check pr1 Hff₂ x xx₁ (id₁ _) (transport_along_inv_2cell
                                    HB_2_1
                                    _
                                    ff₁).
  Admitted.

  Definition map_between_cartesian_1cell_commute
             {x y : B}
             {f : x --> y}
             {xx₁ xx₂ : D x}
             {yy : D y}
             {ff₁ : xx₁ -->[ f ] yy}
             (Hff₁ : cartesian_1cell D ff₁)
             {ff₂ : xx₂ -->[ f ] yy}
             (Hff₂ : cartesian_1cell D ff₂)
    : disp_invertible_2cell
        (lunitor_invertible_2cell _)
        (map_between_cartesian_1cell Hff₁ Hff₂ ;; ff₂)
        ff₁.
  Proof.
  Admitted.

  Definition disp_adj_equiv_between_cartesian_1cell
             {x y : B}
             {f : x --> y}
             {xx₁ xx₂ : D x}
             {yy : D y}
             {ff₁ : xx₁ -->[ f ] yy}
             (Hff₁ : cartesian_1cell D ff₁)
             {ff₂ : xx₂ -->[ f ] yy}
             (Hff₂ : cartesian_1cell D ff₂)
    : disp_left_adjoint_equivalence
        (internal_adjoint_equivalence_identity _)
        (map_between_cartesian_1cell Hff₁ Hff₂).
  Proof.
  Admitted.
End AdjEquivBetweenCartesian.

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
  apply (is_cartesian_iso_disp (disp_hom_disp_invertible_2cell_to_iso _ Hαα)).
Defined.

Section Cartesian2CellUnique.
  Context {B : bicat}
          {D : disp_bicat B}
          {x y : B}
          {f g : x --> y}
          {α : f ==> g}
          {xx : D x}
          {yy : D y}
          {ff₁ ff₂ : xx -->[ f ] yy}
          {gg : xx -->[ g ] yy}
          {αα : ff₁ ==>[ α ] gg}
          {ββ : ff₂ ==>[ α ] gg}
          (Hαα : is_cartesian_2cell D αα)
          (Hββ : is_cartesian_2cell D ββ).

  Let m : ff₁ ==>[ id₂ f] ff₂.
  Proof.
    use (is_cartesian_2cell_factor _ Hββ).
    exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_left _)
             αα).
  Defined.

  Let i : ff₂ ==>[ id₂ f] ff₁.
  Proof.
    use (is_cartesian_2cell_factor _ Hαα).
    exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_left _)
             ββ).
  Defined.

  Local Lemma is_cartesian_2cell_unique_iso_inv₁
    : m •• i
      =
      transportb
        (λ z, ff₁ ==>[ z ] ff₁)
        (id2_left (id₂ f))
        (disp_id2 ff₁).
  Proof.
    use (is_cartesian_2cell_unique _ Hαα).
    - refine (transportb
                (λ z, _ ==>[ z ] _)
                _
                αα).
      abstract
        (rewrite !vassocl ;
         rewrite !id2_left ;
         apply idpath).
    - rewrite disp_vassocl.
      unfold i.
      rewrite is_cartesian_2cell_comm.
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      unfold m.
      rewrite is_cartesian_2cell_comm.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_id2_left.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Local Lemma is_cartesian_2cell_unique_iso_inv₂
    : i •• m
      =
      transportb
        (λ z, ff₂ ==>[ z ] ff₂)
        (id2_left (id₂ f))
        (disp_id2 ff₂).
  Proof.
    use (is_cartesian_2cell_unique _ Hββ).
    - refine (transportb
                (λ z, _ ==>[ z ] _)
                _
                ββ).
      abstract
        (rewrite !vassocl ;
         rewrite !id2_left ;
         apply idpath).
    - rewrite disp_vassocl.
      unfold m.
      rewrite is_cartesian_2cell_comm.
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      unfold i.
      rewrite is_cartesian_2cell_comm.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_id2_left.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Definition is_cartesian_2cell_unique_iso
    : disp_invertible_2cell (id2_invertible_2cell _) ff₁ ff₂
    := (m
        ,, i
        ,, is_cartesian_2cell_unique_iso_inv₁
        ,, is_cartesian_2cell_unique_iso_inv₂).

  Definition is_cartesian_2cell_unique_iso_com
    : αα
      =
      transportf
        (λ z, _ ==>[ z ] _)
        (id2_left _)
        (is_cartesian_2cell_unique_iso •• ββ).
  Proof.
    cbn ; unfold m.
    rewrite is_cartesian_2cell_comm.
    unfold transportb.
    rewrite transport_f_f.
    rewrite pathsinv0l.
    apply idpath.
  Qed.
End Cartesian2CellUnique.

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

(** 4. Local Opcleavings *)
Section LocalOpcleaving.
  Context {B : bicat}
          (D : disp_bicat B).

  Definition is_opcartesian_2cell
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
         (γ : g ==> h)
         (ββ : ff ==>[ α • γ ] hh),
       ∃! (γγ : gg ==>[ γ ] hh), (αα •• γγ) = ββ.

  Section OpCartesian2Cell.
    Context {x y : B}
            {xx : D x} {yy : D y}
            {f g : x --> y}
            {ff : xx -->[ f ] yy}
            {gg : xx -->[ g ] yy}
            {α : f ==> g}
            {αα : ff ==>[ α ] gg}
            (Hαα : is_opcartesian_2cell αα).

    Definition is_opcartesian_2cell_factor
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : g ==> h)
               (ββ : ff ==>[ α • γ ] hh)
      : gg ==>[ γ ] hh
      := pr11 (Hαα h hh γ ββ).

    Definition is_opcartesian_2cell_comm
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : g ==> h)
               (ββ : ff ==>[ α • γ ] hh)
      : (αα •• is_opcartesian_2cell_factor hh γ ββ) = ββ
      := pr21 (Hαα h hh γ ββ).

    Definition is_opcartesian_2cell_unique
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : g ==> h)
               (ββ : ff ==>[ α • γ ] hh)
               {γγ₁ γγ₂ : gg ==>[ γ ] hh}
               (pγγ₁ : (αα •• γγ₁) = ββ)
               (pγγ₂ : (αα •• γγ₂) = ββ)
      : γγ₁ = γγ₂.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (Hαα h hh γ ββ))
                  (γγ₁ ,, pγγ₁) (γγ₂ ,, pγγ₂))).
    Qed.
  End OpCartesian2Cell.

  Definition opcartesian_lift_2cell
             {x y : B}
             {xx : D x}
             {yy : D y}
             {f g : x --> y}
             (ff : xx -->[ f ] yy)
             (α : f ==> g)
    : UU
    := ∑ (gg : xx -->[ g ] yy) (αα : ff ==>[ α ] gg), is_opcartesian_2cell αα.

  Definition local_opcleaving
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (ff : xx -->[ f ] yy)
         (α : f ==> g),
       opcartesian_lift_2cell ff α.
End LocalOpcleaving.

(** 5. Properties of opcartesian 2-cells *)
Definition local_opfib
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∏ (x y : B)
       (xx : D x)
       (yy : D y),
     opcleaving (disp_hom xx yy).

(** Being a cartesian 2-cell is a proposition *)
Definition isaprop_is_opcartesian_2cell
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
  : isaprop (is_opcartesian_2cell D αα).
Proof.
  repeat (use impred ; intro).
  apply isapropiscontr.
Qed.

(** The two definitions of local cleavings coincide *)
Definition opcartesian_2cell_to_opcartesian
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
           (Hαα : is_opcartesian_2cell D αα)
  : @is_opcartesian _ (disp_hom xx yy) _ _ _ _ _ αα.
Proof.
  intros h γ hh γα.
  apply Hαα.
Qed.

Definition opcartesian_to_opcartesian_2cell
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
           (Hαα : @is_opcartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
  : is_opcartesian_2cell D αα.
Proof.
  intros h hh γ γα.
  apply Hαα.
Qed.

Definition opcartesian_2cell_weq_opcartesian
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
  : (@is_opcartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
    ≃
    is_opcartesian_2cell D αα.
Proof.
  use weqimplimpl.
  - apply opcartesian_to_opcartesian_2cell.
  - apply opcartesian_2cell_to_opcartesian.
  - apply isaprop_is_opcartesian.
  - apply isaprop_is_opcartesian_2cell.
Qed.

Definition local_opcleaving_to_local_opfib
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_opcleaving D)
  : local_opfib D.
Proof.
  intros x y xx yy f g ff α ; cbn in *.
  pose (HD x y xx yy f g ff α) as lift.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply opcartesian_2cell_to_opcartesian.
  exact (pr22 lift).
Defined.

Definition local_opfib_to_local_opcleaving
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_opfib D)
  : local_opcleaving D.
Proof.
  intros x y xx yy f g ff α ; cbn in *.
  pose (HD x y xx yy f g ff α) as lift.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply opcartesian_to_opcartesian_2cell.
  exact (pr22 lift).
Defined.

Definition local_opfib_weq_local_opcleaving
           {B : bicat}
           (D : disp_bicat B)
  : local_opcleaving D ≃ local_opfib D.
Proof.
  use make_weq.
  - exact local_opcleaving_to_local_opfib.
  - use gradth.
    + exact local_opfib_to_local_opcleaving.
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_opcartesian_2cell).
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_opcartesian).
Defined.

Definition identity_is_opcartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f : x --> y}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : is_opcartesian_2cell D (disp_id2 ff).
Proof.
  apply opcartesian_to_opcartesian_2cell.
  exact (@is_opcartesian_id_disp _ (disp_hom xx yy) f ff).
Defined.

Definition vcomp_is_opcartesian_2cell
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
           (Hαα : is_opcartesian_2cell D αα)
           (Hββ : is_opcartesian_2cell D ββ)
  : is_opcartesian_2cell D (αα •• ββ).
Proof.
  apply opcartesian_to_opcartesian_2cell.
  exact (@is_opcartesian_comp_disp
           _ (disp_hom xx yy)
           f ff
           g gg
           h hh
           α β
           αα ββ
           (opcartesian_2cell_to_opcartesian _ Hαα)
           (opcartesian_2cell_to_opcartesian _ Hββ)).
Defined.

Definition invertible_is_opcartesian_2cell
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
  : is_opcartesian_2cell D αα.
Proof.
  apply opcartesian_to_opcartesian_2cell.
  apply (is_opcartesian_iso_disp (disp_hom_disp_invertible_2cell_to_iso _ Hαα)).
Defined.

Definition lwhisker_opcartesian
           {B : bicat}
           (D : disp_bicat B)
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
     is_opcartesian_2cell _ αα → is_opcartesian_2cell _ (hh ◃◃ αα).

Definition rwhisker_opcartesian
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∏ (x y z : B)
       (xx : D x) (yy : D y) (zz : D z)
       (f g : x --> y) (h : y --> z)
       (ff : xx -->[ f ] yy)
       (gg : xx -->[ g ] yy)
       (hh : yy -->[ h ] zz)
       (α : f ==> g)
       (αα : ff ==>[ α ] gg),
     is_opcartesian_2cell _ αα → is_opcartesian_2cell _ (αα ▹▹ hh).

Section OpCartesian2CellUnique.
  Context {B : bicat}
          {D : disp_bicat B}
          {x y : B}
          {f g : x --> y}
          {α : f ==> g}
          {xx : D x}
          {yy : D y}
          {ff : xx -->[ f ] yy}
          {gg₁ gg₂ : xx -->[ g ] yy}
          {αα : ff ==>[ α ] gg₁}
          {ββ : ff ==>[ α ] gg₂}
          (Hαα : is_opcartesian_2cell D αα)
          (Hββ : is_opcartesian_2cell D ββ).

  Let m : gg₁ ==>[ id₂ g ] gg₂.
  Proof.
    use (is_opcartesian_2cell_factor _ Hαα).
    exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_right _)
             ββ).
  Defined.

  Let i : gg₂ ==>[ id₂ g ] gg₁.
  Proof.
    use (is_opcartesian_2cell_factor _ Hββ).
    exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_right _)
             αα).
  Defined.

  Local Lemma is_opcartesian_2cell_unique_iso_inv₁
    : i •• m
      =
      transportb
        (λ z, _ ==>[ z ] _)
        (id2_left _)
        (disp_id2 _).
  Proof.
    use (is_opcartesian_2cell_unique _ Hββ).
    - refine (transportb
                (λ z, _ ==>[ z ] _)
                _
                ββ).
      abstract
        (rewrite !id2_right ;
         apply idpath).
    - unfold i, m.
      rewrite disp_vassocr.
      rewrite is_opcartesian_2cell_comm.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite is_opcartesian_2cell_comm.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_id2_right.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Local Lemma is_opcartesian_2cell_unique_iso_inv₂
    : m •• i
      =
      transportb
        (λ z, _ ==>[ z ] _)
        (id2_left _)
        (disp_id2 gg₁).
  Proof.
    use (is_opcartesian_2cell_unique _ Hαα).
    - refine (transportb
                (λ z, _ ==>[ z ] _)
                _
                αα).
      abstract
        (rewrite !id2_right ;
         apply idpath).
    - unfold i, m.
      rewrite disp_vassocr.
      rewrite is_opcartesian_2cell_comm.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite is_opcartesian_2cell_comm.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_id2_right.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.


  Definition is_opcartesian_2cell_unique_iso
    : disp_invertible_2cell (id2_invertible_2cell _) gg₂ gg₁
    := (i
          ,, m
        ,, is_opcartesian_2cell_unique_iso_inv₁
        ,, is_opcartesian_2cell_unique_iso_inv₂).

  Definition is_opcartesian_2cell_unique_iso_com
    : αα
      =
      transportf
        (λ z, _ ==>[ z ] _)
        (id2_right _)
        (ββ •• is_opcartesian_2cell_unique_iso).
  Proof.
    cbn ; unfold i.
    rewrite is_opcartesian_2cell_comm.
    unfold transportb.
    rewrite transport_f_f.
    rewrite pathsinv0l.
    apply idpath.
  Qed.
End OpCartesian2CellUnique.

Definition disp_hcomp_is_opcartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           (HD_l : lwhisker_opcartesian D)
           (HD_r : rwhisker_opcartesian D)
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
           (Hαα : is_opcartesian_2cell D αα)
           (Hββ : is_opcartesian_2cell D ββ)
  : is_opcartesian_2cell D (disp_hcomp αα ββ).
Proof.
  use vcomp_is_opcartesian_2cell.
  - apply HD_r.
    exact Hαα.
  - apply HD_l.
    exact Hββ.
Defined.

(** 6. Cartesian pseudofunctors *)
Definition global_cartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := ∏ (b₁ b₂ : B₁)
       (f : b₁ --> b₂)
       (bb₁ : D₁ b₁)
       (bb₂ : D₁ b₂)
       (ff : bb₁ -->[ f ] bb₂)
       (Hff : cartesian_1cell D₁ ff),
     cartesian_1cell D₂ (disp_psfunctor_mor _ _ _ FF ff).

Definition local_cartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := ∏ (b₁ b₂ : B₁)
       (f g : b₁ --> b₂)
       (α : f ==> g)
       (bb₁ : D₁ b₁)
       (bb₂ : D₁ b₂)
       (ff : bb₁ -->[ f ] bb₂)
       (gg : bb₁ -->[ g ] bb₂)
       (αα : ff ==>[ α ] gg)
       (Hαα : is_cartesian_2cell D₁ αα),
     is_cartesian_2cell D₂ (disp_psfunctor_cell _ _ _ FF αα).

Definition local_opcartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := ∏ (b₁ b₂ : B₁)
       (f g : b₁ --> b₂)
       (α : f ==> g)
       (bb₁ : D₁ b₁)
       (bb₂ : D₁ b₂)
       (ff : bb₁ -->[ f ] bb₂)
       (gg : bb₁ -->[ g ] bb₂)
       (αα : ff ==>[ α ] gg)
       (Hαα : is_opcartesian_2cell D₁ αα),
     is_opcartesian_2cell D₂ (disp_psfunctor_cell _ _ _ FF αα).

Definition cartesian_disp_psfunctor
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := global_cartesian_disp_psfunctor FF × local_cartesian_disp_psfunctor FF.

(** Lmmas on cartesian pseudofunctors *)
Definition global_cartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : global_cartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  intros ? ? ? ? ? ? H.
  exact H.
Defined.

Definition global_cartesian_comp_psfunctor
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           {D₃ : disp_bicat B₃}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₂ D₃ G}
           (HFF : global_cartesian_disp_psfunctor FF)
           (HGG : global_cartesian_disp_psfunctor GG)
  : global_cartesian_disp_psfunctor (disp_pseudo_comp _ _ _ _ _ FF GG).
Proof.
  intros ? ? ? ? ? ? H.
  apply HGG.
  apply HFF.
  exact H.
Defined.

Definition local_cartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : local_cartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  exact H.
Defined.

Definition local_cartesian_comp_psfunctor
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           {D₃ : disp_bicat B₃}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₂ D₃ G}
           (HFF : local_cartesian_disp_psfunctor FF)
           (HGG : local_cartesian_disp_psfunctor GG)
  : local_cartesian_disp_psfunctor (disp_pseudo_comp _ _ _ _ _ FF GG).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  apply HGG.
  apply HFF.
  exact H.
Defined.

Definition local_opcartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : local_opcartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  exact H.
Defined.

Definition local_opcartesian_comp_psfunctor
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           {D₃ : disp_bicat B₃}
           {FF : disp_psfunctor D₁ D₂ F}
           {GG : disp_psfunctor D₂ D₃ G}
           (HFF : local_opcartesian_disp_psfunctor FF)
           (HGG : local_opcartesian_disp_psfunctor GG)
  : local_opcartesian_disp_psfunctor (disp_pseudo_comp _ _ _ _ _ FF GG).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? H.
  apply HGG.
  apply HFF.
  exact H.
Defined.

Definition cartesian_id_psfunctor
           {B : bicat}
           (D : disp_bicat B)
  : cartesian_disp_psfunctor (disp_pseudo_id D).
Proof.
  split.
  - apply global_cartesian_id_psfunctor.
  - apply local_cartesian_id_psfunctor.
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
  - apply global_cartesian_comp_psfunctor.
    + exact (pr1 HFF).
    + exact (pr1 HGG).
  - apply local_cartesian_comp_psfunctor.
    + exact (pr2 HFF).
    + exact (pr2 HGG).
Defined.

(**
 7. Cartesian pseudofunctors from global cleavings
 *)
Definition preserves_global_lifts
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (HD₁ : global_cleaving D₁)
           (FF : disp_psfunctor D₁ D₂ F)
  : UU
  := ∏ (b₁ b₂ : B₁)
       (f : b₁ --> b₂)
       (bb₂ : D₁ b₂),
     cartesian_1cell
       D₂
       (disp_psfunctor_mor _ _ _ FF (pr12 (HD₁ b₁ b₂ bb₂ f))).

Definition preserves_global_lifts_to_cartesian
           {B : bicat}
           {D₁ : disp_bicat B}
           {D₂ : disp_bicat B}
           (HB : is_univalent_2 B)
           (HD₂ : disp_univalent_2 D₂)
           (HD₁ : global_cleaving D₁)
           {FF : disp_psfunctor D₁ D₂ (id_psfunctor _)}
           (HFF : preserves_global_lifts HD₁ FF)
  : global_cartesian_disp_psfunctor FF.
Proof.
  intros b₁ b₂ f bb₁ bb₂ ff Hff.
  refine (invertible_2cell_from_cartesian
            HB (pr2 HD₂)
            _
            (pr2 (disp_psfunctor_invertible_2cell
                    FF
                    (map_between_cartesian_1cell_commute
                       (pr2 HB)
                       Hff
                       (pr22 (HD₁ b₁ b₂ bb₂ f)))))).
  use (invertible_2cell_from_cartesian
         HB (pr2 HD₂)
         _
         (pr2 (disp_psfunctor_comp _ _ _ _ _ _))).
  use (comp_cartesian_1cell HB).
  - exact (cartesian_1cell_disp_adj_equiv
             HB
             (pr1 HD₂)
             (disp_psfunctor_id_on_disp_adjequiv
                FF
                (disp_adj_equiv_between_cartesian_1cell
                   (pr2 HB)
                   Hff
                   (pr22 (HD₁ b₁ b₂ bb₂ f))))).
  - apply HFF.
Defined.
