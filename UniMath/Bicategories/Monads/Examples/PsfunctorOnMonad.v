(*******************************************************************

 Lifting pseudofunctors to monads

 If we have a pseudofunctor from `B₁` to `B₂`, then we can lift it
 to a pseudofunctor from `mnd B₁` to `mnd B₂`.

 Contents
 1. Action on monads
 2. Action on monad morphisms
 3. Action on monad cells
 4. The identitor
 5. The compositor
 6. The pseudofunctor

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EndoMap.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

(**
 1. Action on monads
 *)
Section PsfunctorOnMonad.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          (m : mnd B₁).

  Let Fm : B₂ := F (ob_of_mnd m).
  Let Fe : Fm --> Fm := #F (endo_of_mnd m).
  Let Fη : id₁ Fm ==> Fe := psfunctor_id F _ • ##F (unit_of_mnd m).
  Let Fμ : Fe · Fe ==> Fe := psfunctor_comp F _ _ • ##F (mult_of_mnd m).

  Definition psfunctor_on_mnd_left_unit
    : (linvunitor Fe • (Fη ▹ Fe)) • Fμ = id₂ Fe.
  Proof.
    unfold Fη, Fμ, Fe.
    refine (_ @ psfunctor_id2 F _).
    rewrite <- (mnd_unit_left m).
    rewrite !psfunctor_vcomp.
    rewrite psfunctor_linvunitor.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite psfunctor_rwhisker.
    apply idpath.
  Qed.

  Definition psfunctor_on_mnd_right_unit
    : (rinvunitor Fe • (Fe ◃ Fη)) • Fμ = id₂ Fe.
  Proof.
    unfold Fη, Fμ, Fe.
    refine (_ @ psfunctor_id2 F _).
    rewrite <- (mnd_unit_right m).
    rewrite !psfunctor_vcomp.
    rewrite psfunctor_rinvunitor.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite psfunctor_lwhisker.
    apply idpath.
  Qed.

  Definition psfunctor_on_mnd_mult_assoc
    : (rassociator Fe Fe Fe • (Fe ◃ Fμ)) • Fμ = (Fμ ▹ Fe) • Fμ.
  Proof.
    unfold Fμ, Fe.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    pose (maponpaths (λ z, ##F z) (mnd_mult_assoc m)) as p.
    cbn in p.
    rewrite !psfunctor_vcomp in p.
    etrans.
    {
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply psfunctor_lwhisker.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      refine (!_).
      apply psfunctor_rassociator.
    }
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      apply p.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    apply psfunctor_rwhisker.
  Qed.

  Definition psfunctor_on_mnd
    : mnd B₂.
  Proof.
    use make_mnd.
    - use make_mnd_data.
      + exact Fm.
      + exact Fe.
      + exact Fη.
      + exact Fμ.
    - repeat split.
      + exact psfunctor_on_mnd_left_unit.
      + exact psfunctor_on_mnd_right_unit.
      + exact psfunctor_on_mnd_mult_assoc.
  Defined.
End PsfunctorOnMonad.

(**
 2. Action on monad morphisms
 *)
Section PsfunctorOnMonadMor.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          {m₁ m₂ : mnd B₁}
          (f : m₁ --> m₂).

  Let Ff : F (ob_of_mnd m₁) --> F (ob_of_mnd m₂)
    := #F (mor_of_mnd_mor f).
  Let Fe : Ff · # F (endo_of_mnd m₂) ==> # F (endo_of_mnd m₁) · Ff
      := psfunctor_comp F _ _
         • ##F (mnd_mor_endo f)
         • (psfunctor_comp F _ _)^-1.

  Definition psfunctor_on_mnd_mor_unit
    : linvunitor Ff • (unit_of_mnd (psfunctor_on_mnd F m₁) ▹ Ff)
      =
      (rinvunitor Ff • (Ff ◃ unit_of_mnd (psfunctor_on_mnd F m₂))) • Fe.
  Proof.
    unfold Ff, Fe.
    pose (maponpaths (λ z, ##F z) (mnd_mor_unit f)) as p.
    cbn in p.
    rewrite !psfunctor_vcomp in p.
    rewrite psfunctor_linvunitor in p.
    rewrite psfunctor_rinvunitor in p.
    rewrite !vassocl in p.
    rewrite psfunctor_rwhisker in p.
    rewrite !vassocr.
    use vcomp_move_L_Mp ; [ is_iso | ].
    cbn -[psfunctor_comp psfunctor_id].
    rewrite !vassocl.
    refine (_ @ p @ _).
    - apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_vcomp.
      apply idpath.
    - apply maponpaths.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite psfunctor_lwhisker.
      apply idpath.
  Qed.

  Definition psfunctor_on_mnd_mor_mu
    : lassociator _ _ _
      • (Fe ▹ _)
      • rassociator _ _ _
      • (_ ◃ Fe)
      • lassociator _ _ _
      • (mult_of_mnd (psfunctor_on_mnd F m₁) ▹ Ff)
      =
      (Ff ◃ mult_of_mnd (psfunctor_on_mnd F m₂)) • Fe.
  Proof.
    unfold Fe, Ff.
    cbn -[psfunctor_id psfunctor_comp].
    pose (maponpaths (λ z, ##F z) (mnd_mor_mu f)).
    cbn in p.
    rewrite !psfunctor_vcomp in p.
    rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
    rewrite !vassocr.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- psfunctor_lwhisker.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite <- p.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite psfunctor_lassociator.
      apply idpath.
    }
    rewrite !vassocl.
    do 2 apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite psfunctor_rwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    use vcomp_move_L_pM ; [ is_iso | ].
    cbn -[psfunctor_id psfunctor_comp].
    etrans.
    {
      rewrite !vassocr.
      rewrite psfunctor_rassociator.
      rewrite !vassocl.
      apply idpath.
    }
    do 2 apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite psfunctor_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    use vcomp_move_L_pM ; [ is_iso | ].
    cbn -[psfunctor_id psfunctor_comp].
    etrans.
    {
      rewrite !vassocr.
      rewrite psfunctor_lassociator.
      rewrite !vassocl.
      apply idpath.
    }
    do 2 apply maponpaths.
    rewrite !vassocr.
    rewrite psfunctor_rwhisker.
    rewrite !vassocl.
    rewrite vcomp_rinv.
    apply id2_right.
  Qed.

  Definition psfunctor_on_mnd_mor
    : psfunctor_on_mnd F m₁ --> psfunctor_on_mnd F m₂.
  Proof.
    use make_mnd_mor.
    - use make_mnd_mor_data.
      + exact Ff.
      + exact Fe.
    - split.
      + exact psfunctor_on_mnd_mor_unit.
      + exact psfunctor_on_mnd_mor_mu.
  Defined.
End PsfunctorOnMonadMor.

(**
 3. Action on monad cells
 *)
Definition psfunctor_on_mnd_cell
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
           {m₁ m₂ : mnd B₁}
           {f g : m₁ --> m₂}
           (τ : f ==> g)
  : psfunctor_on_mnd_mor F f ==> psfunctor_on_mnd_mor F g.
Proof.
  use make_mnd_cell.
  - exact (##F (cell_of_mnd_cell τ)).
  - abstract
      (unfold is_mnd_cell ;
       cbn -[psfunctor_comp psfunctor_id] ;
       rewrite !vassocr ;
       rewrite <- psfunctor_rwhisker ;
       rewrite !vassocl ;
       apply maponpaths ;
       rewrite !vassocr ;
       rewrite <- psfunctor_vcomp ;
       rewrite <- (mnd_cell_endo τ) ;
       rewrite !psfunctor_vcomp ;
       rewrite !vassocl ;
       apply maponpaths ;
       use vcomp_move_R_pM ; [ is_iso | ] ;
       rewrite !vassocr ;
       use vcomp_move_L_Mp ; [ is_iso | ] ;
       cbn -[psfunctor_comp psfunctor_id] ;
       rewrite psfunctor_lwhisker ;
       apply idpath).
Defined.

(**
 4. The identitor
 *)
Definition psfunctor_on_mnd_id_mor
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
           (m : mnd B₁)
  : id₁ _ ==> psfunctor_on_mnd_mor F (id₁ m).
Proof.
  use make_mnd_cell.
  - unfold mnd_cell_data.
    exact (psfunctor_id F _).
  - abstract
      (unfold is_mnd_cell ;
       cbn -[psfunctor_id psfunctor_comp] ;
       rewrite !vassocl ;
       rewrite !psfunctor_vcomp ;
       rewrite psfunctor_lunitor ;
       rewrite !vassocl ;
       do 3 apply maponpaths ;
       rewrite psfunctor_rinvunitor ;
       rewrite !vassocl ;
       rewrite vcomp_rinv ;
       rewrite id2_right ;
       apply idpath).
Defined.

(**
 5. The compositor
 *)
Section PsfunctorOnMonadComposition.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          {m₁ m₂ m₃ : mnd B₁}
          (f : m₁ --> m₂)
          (g : m₂ --> m₃).

  Definition psfunctor_on_mnd_comp_mor_endo
    : mnd_mor_endo (psfunctor_on_mnd_mor F f · psfunctor_on_mnd_mor F g)
      • (_ ◃ psfunctor_comp F _ _)
      =
      (psfunctor_comp F _ _ ▹ _)
      • mnd_mor_endo (psfunctor_on_mnd_mor F (f · g)).
  Proof.
    cbn -[psfunctor_id psfunctor_comp].
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite !psfunctor_vcomp.
    rewrite !vassocr.
    rewrite psfunctor_rassociator.
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite !vassocr.
    use vcomp_move_L_Mp ; [ is_iso | ].
    cbn -[psfunctor_id psfunctor_comp].
    rewrite !vassocl.
    etrans.
    {
      do 6 apply maponpaths.
      rewrite !vassocr.
      refine (!_).
      apply psfunctor_rassociator.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      do 5 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      apply id2_left.
    }
    rewrite <- psfunctor_rwhisker.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      refine (!_).
      apply psfunctor_lassociator.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !lwhisker_vcomp.
    rewrite !vassocl.
    rewrite vcomp_linv.
    rewrite id2_right.
    rewrite psfunctor_lwhisker.
    apply idpath.
  Qed.

  Definition psfunctor_on_mnd_comp_mor
    : psfunctor_on_mnd_mor F f · psfunctor_on_mnd_mor F g
      ==>
      psfunctor_on_mnd_mor F (f · g).
  Proof.
    use make_mnd_cell.
    - unfold mnd_cell_data.
      exact (psfunctor_comp F _ _).
    - unfold is_mnd_cell.
      exact psfunctor_on_mnd_comp_mor_endo.
  Defined.
End PsfunctorOnMonadComposition.

(*
 6. The pseudofunctor
 *)
Section LiftPsfunctorToMonad.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂).

  Definition lift_mnd_psfunctor_data
    : psfunctor_data (mnd B₁) (mnd B₂).
  Proof.
    use make_psfunctor_data.
    - exact (psfunctor_on_mnd F).
    - exact (λ _ _ f, psfunctor_on_mnd_mor F f).
    - exact (λ _ _ _ _ τ, psfunctor_on_mnd_cell F τ).
    - exact (psfunctor_on_mnd_id_mor F).
    - exact (λ _ _ _ f g, psfunctor_on_mnd_comp_mor F f g).
  Defined.

  Definition lift_mnd_psfunctor_laws
    : psfunctor_laws lift_mnd_psfunctor_data.
  Proof.
    repeat split ; intro ; intros ; use eq_mnd_cell ; cbn.
    - apply psfunctor_id2.
    - apply psfunctor_vcomp.
    - apply psfunctor_lunitor.
    - apply psfunctor_runitor.
    - apply psfunctor_lassociator.
    - apply psfunctor_lwhisker.
    - apply psfunctor_rwhisker.
  Qed.

  Definition lift_mnd_psfunctor_invertible_cells
    : invertible_cells lift_mnd_psfunctor_data.
  Proof.
    split ; intros ; use is_invertible_mnd_2cell ; cbn -[psfunctor_id psfunctor_comp].
    - apply property_from_invertible_2cell.
    - apply property_from_invertible_2cell.
  Defined.

  Definition lift_mnd_psfunctor
    : psfunctor (mnd B₁) (mnd B₂).
  Proof.
    use make_psfunctor.
    - exact lift_mnd_psfunctor_data.
    - exact lift_mnd_psfunctor_laws.
    - exact lift_mnd_psfunctor_invertible_cells.
  Defined.
End LiftPsfunctorToMonad.
