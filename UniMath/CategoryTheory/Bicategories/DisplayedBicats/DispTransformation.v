(* ------------------------------------------------------------------------- *)
(** Displayed transformation.
    Contents:
      - Definition of displayed transformation.
      - Identity and composition of displayed transformations.                *)
(* ------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Initial.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Final.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.

Import PseudoFunctor.Notations.

Local Open Scope cat.

(** ** Definition of displayed transformation. *)

Section DispTransformation.

Context {B₁ : bicat} {D₁ : disp_bicat B₁}
        {B₂ : bicat} {D₂ : disp_bicat B₂}
        {F₁ F₂ : psfunctor B₁ B₂}
        (FF₁ : disp_psfunctor D₁ D₂ F₁)
        (FF₂ : disp_psfunctor D₁ D₂ F₂)
        (α : pstrans F₁ F₂).

(** *** Data *)

Definition disp_pstrans_data : UU
  := ∑ αα₁ : ∏ (x : B₁) (xx : D₁ x), FF₁ x xx -->[ α x] FF₂ x xx,
             ∏ (x y : B₁) (f : B₁ ⟦ x, y ⟧) (xx : D₁ x) (yy : D₁ y) (ff : xx -->[ f] yy),
             disp_invertible_2cell (psnaturality_of α f)
                                   (αα₁ x xx;; disp_psfunctor_mor D₁ D₂ F₂ FF₂ ff)
                                   (disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff;; αα₁ y yy).

Definition make_disp_pstrans_data
           (αα₁ : ∏ (x : B₁) (xx : D₁ x), FF₁ x xx -->[ α x] FF₂ x xx)
           (αα₂ : ∏ (x y : B₁) (f : B₁ ⟦ x, y ⟧) (xx : D₁ x) (yy : D₁ y) (ff : xx -->[ f] yy),
                  disp_invertible_2cell (psnaturality_of α f)
                                        (αα₁ x xx;; disp_psfunctor_mor D₁ D₂ F₂ FF₂ ff)
                                        (disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff;; αα₁ y yy))
  : disp_pstrans_data
  := (αα₁,, αα₂).

Definition disp_pscomponent_of (αα : disp_pstrans_data)
  : ∏ (x : B₁) (xx : D₁ x), FF₁ x xx -->[ α x] FF₂ x xx
  := pr1 αα.

Coercion disp_pscomponent_of : disp_pstrans_data >-> Funclass.

Definition disp_psnaturality_of (αα : disp_pstrans_data)
           {x y : B₁}
           {f : B₁ ⟦ x, y ⟧}
           {xx : D₁ x} {yy : D₁ y}
           (ff : xx -->[ f] yy)
  : disp_invertible_2cell (psnaturality_of α f)
                          (αα x xx;; disp_psfunctor_mor D₁ D₂ F₂ FF₂ ff)
                          (disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff;; αα y yy)
  := pr2 αα x y f xx yy ff.

Definition total_pstrans_data (ααdata : disp_pstrans_data)
  : pstrans_data (total_psfunctor _ _ _ FF₁) (total_psfunctor _ _ _ FF₂).
Proof.
  use make_pstrans_data.
  - exact (λ x, (α (pr1 x),, ααdata _ (pr2 x))).
  - exact (λ x y f, iso_in_E_weq _ _ (psnaturality_of α (pr1 f),,
                    disp_psnaturality_of ααdata (pr2 f))).
Defined.

(** *** Properties *)

Section DispPstransLaws.

Variable ααdata : disp_pstrans_data.

Definition disp_psnaturality_natural_law : UU
  := ∏ (x y : B₁) (f g : B₁ ⟦ x, y ⟧)
       (η : f ==> g)
       (xx : D₁ x) (yy : D₁ y)
       (ff : xx -->[ f] yy)
       (gg : xx -->[ g] yy)
       (ηη : ff ==>[ η] gg),
     (ααdata x xx ◃◃ disp_psfunctor_cell D₁ D₂ F₂ FF₂ ηη) •• disp_psnaturality_of ααdata gg
     =
     transportb
       (λ p, _ ==>[p] _)
       (psnaturality_natural α x y f g η)
       (disp_psnaturality_of ααdata ff •• (disp_psfunctor_cell D₁ D₂ F₁ FF₁ ηη ▹▹ ααdata y yy)).

Definition disp_pstrans_id_law : UU
  := ∏ (x : B₁) (xx : D₁ x),
     (ααdata x xx ◃◃ disp_psfunctor_id D₁ D₂ F₂ FF₂ xx)
       •• disp_psnaturality_of ααdata (id_disp xx)
     =
     transportb
       (λ p, _ ==>[p] _)
       (pstrans_id α x)
       ((disp_runitor (ααdata x xx) •• disp_linvunitor (ααdata x xx))
          •• (disp_psfunctor_id D₁ D₂ F₁ FF₁ xx ▹▹ ααdata x xx)).

Definition disp_pstrans_comp_law : UU
  := ∏ (x y z : B₁)
       (f : B₁ ⟦ x, y ⟧) (g : B₁ ⟦ y, z ⟧)
       (xx : D₁ x) (yy : D₁ y) (zz : D₁ z)
       (ff : xx -->[ f] yy) (gg : yy -->[ g] zz),
     (ααdata x xx ◃◃ disp_psfunctor_comp D₁ D₂ F₂ FF₂ ff gg)
       •• disp_psnaturality_of ααdata (ff;; gg) =
     transportb
       (λ p, _ ==>[p] _)
       (pstrans_comp α f g)
       (((((disp_lassociator
              (ααdata x xx)
              (disp_psfunctor_mor D₁ D₂ F₂ FF₂ ff)
              (disp_psfunctor_mor D₁ D₂ F₂ FF₂ gg)
              •• (disp_psnaturality_of ααdata ff ▹▹ disp_psfunctor_mor D₁ D₂ F₂ FF₂ gg))
             •• disp_rassociator (disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff) (ααdata y yy)
             (disp_psfunctor_mor D₁ D₂ F₂ FF₂ gg))
            •• (disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff ◃◃ disp_psnaturality_of ααdata gg))
           •• disp_lassociator (disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff)
           (disp_psfunctor_mor D₁ D₂ F₁ FF₁ gg) (ααdata z zz))
          •• (disp_psfunctor_comp D₁ D₂ F₁ FF₁ ff gg ▹▹ ααdata z zz)).

Definition is_disp_pstrans
  : UU
  := disp_psnaturality_natural_law
       × disp_pstrans_id_law
       × disp_pstrans_comp_law.

End DispPstransLaws.

(** *** Displayed transformation *)

Definition disp_pstrans : UU
  := ∑ αα : disp_pstrans_data, is_disp_pstrans αα.

Coercion disp_pstrans_to_disp_pstrans_data (αα : disp_pstrans)
  : disp_pstrans_data
  := pr1 αα.

Lemma total_pstrans_laws (αα : disp_pstrans)
  : is_pstrans (total_pstrans_data αα).
Proof.
  repeat apply make_dirprod; intro; intros.
  - use total2_paths_b; [apply (psnaturality_natural α) | apply αα].
  - use total2_paths_b; [apply (pstrans_id α) | apply αα].
  - use total2_paths_b. 2: apply αα.
Qed.

Definition total_pstrans (αα : disp_pstrans)
  : pstrans (total_psfunctor _ _ _ FF₁) (total_psfunctor _ _ _ FF₂).
Proof.
  use make_pstrans.
  - exact (total_pstrans_data αα).
  - exact (total_pstrans_laws αα).
Defined.

Definition is_disp_pstrans_from_total (αα : disp_pstrans_data)
  : is_pstrans (total_pstrans_data αα) → is_disp_pstrans αα.
Proof.
  intros Hαα.
  pose (Eα := make_pstrans _ Hαα).
  repeat split.
  - intros x y f g η xx yy ff gg ηη.
    pose (P := !fiber_paths (@psnaturality_natural _ _ _ _ Eα (x,,xx) (y,,yy) (f,,ff)
         (g,,gg) (η,,ηη))).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
  - intros x xx.
    pose (P := !fiber_paths (@pstrans_id _ _ _ _ Eα (x,,xx))).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
  - intros x y z f g xx yy zz ff gg.
    pose (P := !fiber_paths
                (@pstrans_comp _ _ _ _ Eα
                               (x,,xx) (y,,yy) (z,,zz) (f,,ff) (g,,gg)
         )).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
Qed.

End DispTransformation.

(** ** Identity *)


Section DispTrans_identity.

Context {B₁ B₂ : bicat}
        {D₁ : disp_bicat B₁}
        {D₂ : disp_bicat B₂}
        {F : psfunctor B₁ B₂}
        (FF : disp_psfunctor D₁ D₂ F).

Definition disp_id_trans_data
  : disp_pstrans_data FF FF (id_trans F).
Proof.
  use make_disp_pstrans_data; cbn.
  - exact (λ x xx, id_disp (FF x xx)).
  - intros.
    apply (vcomp_disp_invertible (disp_invertible_2cell_lunitor _)
                                 (disp_invertible_2cell_rinvunitor _)).
Defined.

Lemma disp_id_trans_laws : is_disp_pstrans _ _ _ disp_id_trans_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := id_trans (total_psfunctor _ _ _ FF)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (pr11 PP = total_pstrans_data FF FF (id_trans F) disp_id_trans_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf _ X PP2).
Qed.

Definition disp_id_trans : disp_pstrans FF FF (id_trans F)
  := disp_id_trans_data,, disp_id_trans_laws.

End DispTrans_identity.

(** ** Composition *)

Section DispTrans_comp.

Context {B₁ B₂ : bicat}
        (F₁ : psfunctor B₁ B₂)
        (F₂ : psfunctor B₁ B₂)
        (F₃ : psfunctor B₁ B₂)
        (η₁ : pstrans F₁ F₂)
        (η₂ : pstrans F₂ F₃)
        (D₁ : disp_bicat B₁)
        (D₂ : disp_bicat B₂)
        (FF₁ : disp_psfunctor D₁ D₂ F₁)
        (FF₂ : disp_psfunctor D₁ D₂ F₂)
        (FF₃ : disp_psfunctor D₁ D₂ F₃)
        (ηη₁ : disp_pstrans FF₁ FF₂ η₁)
        (ηη₂ : disp_pstrans FF₂ FF₃ η₂).

Local Notation "αα '••' ββ" := (vcomp_disp_invertible αα ββ).
Local Notation "ff '◃◃' αα" := (disp_invertible_2cell_lwhisker ff αα).
Local Notation "αα '▹▹' ff" := (disp_invertible_2cell_rwhisker ff αα).

Definition disp_ps_comp_data : disp_pstrans_data FF₁ FF₃ (comp_trans η₁ η₂).
Proof.
  use make_disp_pstrans_data; cbn.
  - exact (λ x xx, comp_disp (ηη₁ x xx) (ηη₂ x xx)).
  - exact (λ x y f xx yy ff,
           (disp_invertible_2cell_rassociator _ _ _)
             •• (_ ◃◃ disp_psnaturality_of _ _ _ ηη₂ ff)
             •• disp_invertible_2cell_lassociator _ _ _
             •• (disp_psnaturality_of _ _ _ ηη₁ ff ▹▹ _)
             •• disp_invertible_2cell_rassociator _ _ _).
Defined.

Lemma disp_ps_comp_laws : is_disp_pstrans _ _ _ disp_ps_comp_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := comp_trans (total_pstrans _ _ _ ηη₁) (total_pstrans _ _ _ ηη₂)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (pr11 PP = total_pstrans_data _ _ _ disp_ps_comp_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf _ X PP2).
Qed.

Definition disp_ps_comp : disp_pstrans _ _ (comp_trans η₁ η₂)
  := disp_ps_comp_data,, disp_ps_comp_laws.

End DispTrans_comp.
