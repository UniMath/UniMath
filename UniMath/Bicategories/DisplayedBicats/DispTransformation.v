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
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.Initial.
Require Import UniMath.Bicategories.Core.Examples.Final.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

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

Definition disp_comp_psfunctor_data : disp_pstrans_data FF₁ FF₃ (comp_trans η₁ η₂).
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

Lemma disp_comp_psfunctor_laws : is_disp_pstrans _ _ _ disp_comp_psfunctor_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := comp_trans (total_pstrans _ _ _ ηη₁) (total_pstrans _ _ _ ηη₂)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (pr11 PP = total_pstrans_data _ _ _ disp_comp_psfunctor_data).
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

Definition disp_comp_psfunctor : disp_pstrans _ _ (comp_trans η₁ η₂)
  := disp_comp_psfunctor_data,, disp_comp_psfunctor_laws.

End DispTrans_comp.

Definition disp_inv_invertible
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : invertible_2cell f g}
           {xx : D x} {yy : D y}
           {ff : xx -->[ f ] yy} {gg : xx -->[ g ] yy}
           (αα : disp_invertible_2cell α ff gg)
  : disp_invertible_2cell (inv_of_invertible_2cell α) gg ff.
Proof.
  use tpair.
  - exact (disp_inv_cell αα).
  - use tpair.
    + apply αα.
    + split ; cbn.
      * apply disp_vcomp_linv.
      * apply disp_vcomp_rinv.
Defined.

Section DispTrans_lwhisker.

Context {B₁ B₂ B₃ : bicat}
        {F₁ F₂ : psfunctor B₁ B₂}
        {G : psfunctor B₂ B₃}
        {η : pstrans F₁ F₂}
        {D₁ : disp_bicat B₁}
        {D₂ : disp_bicat B₂}
        {D₃ : disp_bicat B₃}
        {FF₁ : disp_psfunctor D₁ D₂ F₁}
        {FF₂ : disp_psfunctor D₁ D₂ F₂}
        (GG : disp_psfunctor D₂ D₃ G)
        (ηη : disp_pstrans FF₁ FF₂ η).

Local Notation "αα '••' ββ" := (vcomp_disp_invertible αα ββ).

Definition disp_left_whisker_data
  : disp_pstrans_data
      (disp_pseudo_comp _ _ _ _ _ FF₁ GG)
      (disp_pseudo_comp _ _ _ _ _ FF₂ GG)
      (G ◅ η).
Proof.
  use make_disp_pstrans_data; cbn.
  - exact (λ x xx, pr121 GG _ _ _ _ _ (pr11 ηη x xx)).
  - exact (λ x y f xx yy ff,
           (disp_psfunctor_comp _ _ _ GG _ _)
             •• disp_psfunctor_invertible_2cell GG (disp_psnaturality_of _ _ _ ηη ff)
             •• (disp_inv_invertible (disp_psfunctor_comp _ _ _ GG _ _))).
Defined.

Lemma disp_left_whisker_laws : is_disp_pstrans _ _ _ disp_left_whisker_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := (total_psfunctor _ _ _ GG) ◅ total_pstrans _ _ _ ηη).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (pstrans_to_pstrans_data PP = total_pstrans_data _ _ _ disp_left_whisker_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf is_pstrans X PP2). (* Slow, dunno why *)
Qed.

Definition disp_left_whisker
  : disp_pstrans
      (disp_pseudo_comp _ _ _ _ _ FF₁ GG)
      (disp_pseudo_comp _ _ _ _ _ FF₂ GG)
      (G ◅ η)
  := disp_left_whisker_data,, disp_left_whisker_laws.

End DispTrans_lwhisker.

Section DispTrans_rwhisker.

Context {B₁ B₂ B₃ : bicat}
        {F : psfunctor B₁ B₂}
        {G₁ G₂ : psfunctor B₂ B₃}
        {η : pstrans G₁ G₂}
        {D₁ : disp_bicat B₁}
        {D₂ : disp_bicat B₂}
        {D₃ : disp_bicat B₃}
        (FF : disp_psfunctor D₁ D₂ F)
        {GG₁ : disp_psfunctor D₂ D₃ G₁}
        {GG₂ : disp_psfunctor D₂ D₃ G₂}
        (ηη : disp_pstrans GG₁ GG₂ η).

Definition disp_right_whisker_data
  : disp_pstrans_data
      (disp_pseudo_comp _ _ _ _ _ FF GG₁)
      (disp_pseudo_comp _ _ _ _ _ FF GG₂)
      (η ▻ F).
Proof.
  use make_disp_pstrans_data; cbn.
  - exact (λ x xx, (pr11 ηη _ (FF _ xx))).
  - exact (λ x y f xx yy ff, disp_psnaturality_of _ _ _ ηη (pr121 FF _ _ _ _ _ ff)).
Defined.

Lemma disp_right_whisker_laws : is_disp_pstrans _ _ _ disp_right_whisker_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := (total_pstrans _ _ _ ηη) ▻ (total_psfunctor _ _ _ FF)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (X : pstrans_to_pstrans_data PP
              =
              total_pstrans_data _ _ _ disp_right_whisker_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      lazy.
      apply idpath.
  - exact (transportf is_pstrans X PP2). (* Also slow, dunno why *)
Qed.

Definition disp_right_whisker
  : disp_pstrans
      (disp_pseudo_comp _ _ _ _ _ FF GG₁)
      (disp_pseudo_comp _ _ _ _ _ FF GG₂)
      (η ▻ F)
  := disp_right_whisker_data,, disp_right_whisker_laws.

End DispTrans_rwhisker.

Section DispTransUnitality.
Context {B₁ B₂ : bicat}
        {F : psfunctor B₁ B₂}
        {D₁ : disp_bicat B₁}
        {D₂ : disp_bicat B₂}
        (FF : disp_psfunctor D₁ D₂ F).

Definition disp_pstrans_lunitor_data
  : disp_pstrans_data
      (disp_pseudo_comp _ _ _ _ _ FF (disp_pseudo_id D₂))
      FF
      (pstrans_lunitor F).
Proof.
  use make_disp_pstrans_data.
  - exact (λ x xx, id_disp (FF x xx)).
  - cbn.
    refine (λ x y f xx yy ff, _).
    apply (vcomp_disp_invertible (disp_invertible_2cell_lunitor _)
                                 (disp_invertible_2cell_rinvunitor _)).
Defined.

Lemma disp_pstrans_lunitor_laws : is_disp_pstrans _ _ _ disp_pstrans_lunitor_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := pstrans_lunitor (total_psfunctor _ _ _ FF)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (X : pstrans_to_pstrans_data PP
              =
              total_pstrans_data _ _ _ disp_pstrans_lunitor_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf is_pstrans X PP2).
Qed.

Definition disp_pstrans_lunitor
  : disp_pstrans
      (disp_pseudo_comp _ _ _ _ _ FF (disp_pseudo_id D₂))
      FF
      (pstrans_lunitor F)
  := disp_pstrans_lunitor_data,, disp_pstrans_lunitor_laws.

Definition disp_pstrans_linvunitor_data
  : disp_pstrans_data
      FF
      (disp_pseudo_comp _ _ _ _ _ FF (disp_pseudo_id D₂))
      (pstrans_linvunitor F).
Proof.
  use make_disp_pstrans_data.
  - exact (λ x xx, id_disp (FF x xx)).
  - cbn.
    refine (λ x y f xx yy ff, _).
    apply (vcomp_disp_invertible (disp_invertible_2cell_lunitor _)
                                 (disp_invertible_2cell_rinvunitor _)).
Defined.

Lemma disp_pstrans_linvunitor_laws : is_disp_pstrans _ _ _ disp_pstrans_linvunitor_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := pstrans_linvunitor (total_psfunctor _ _ _ FF)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (X : pstrans_to_pstrans_data PP
              =
              total_pstrans_data _ _ _ disp_pstrans_linvunitor_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf is_pstrans X PP2).
Qed.

Definition disp_pstrans_linvunitor
  : disp_pstrans
      FF
      (disp_pseudo_comp _ _ _ _ _ FF (disp_pseudo_id D₂))
      (pstrans_linvunitor F)
  := disp_pstrans_linvunitor_data,, disp_pstrans_linvunitor_laws.

Definition disp_pstrans_runitor_data
  : disp_pstrans_data
      (disp_pseudo_comp _ _ _ _ _ (disp_pseudo_id D₁) FF)
      FF
      (pstrans_runitor F).
Proof.
  use make_disp_pstrans_data.
  - exact (λ x xx, id_disp (FF x xx)).
  - cbn.
    refine (λ x y f xx yy ff, _).
    apply (vcomp_disp_invertible (disp_invertible_2cell_lunitor _)
                                 (disp_invertible_2cell_rinvunitor _)).
Defined.

Lemma disp_pstrans_runitor_laws : is_disp_pstrans _ _ _ disp_pstrans_runitor_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := pstrans_runitor (total_psfunctor _ _ _ FF)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (X : pstrans_to_pstrans_data PP
              =
              total_pstrans_data _ _ _ disp_pstrans_runitor_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf is_pstrans X PP2).
Qed.

Definition disp_pstrans_runitor
  : disp_pstrans
      (disp_pseudo_comp _ _ _ _ _ (disp_pseudo_id D₁) FF)
      FF
      (pstrans_runitor F)
  := disp_pstrans_runitor_data,, disp_pstrans_runitor_laws.

Definition disp_pstrans_rinvunitor_data
  : disp_pstrans_data
      FF
      (disp_pseudo_comp _ _ _ _ _ (disp_pseudo_id D₁) FF)
      (pstrans_rinvunitor F).
Proof.
  use make_disp_pstrans_data.
  - exact (λ x xx, id_disp (FF x xx)).
  - cbn.
    refine (λ x y f xx yy ff, _).
    apply (vcomp_disp_invertible (disp_invertible_2cell_lunitor _)
                                 (disp_invertible_2cell_rinvunitor _)).
Defined.

Lemma disp_pstrans_rinvunitor_laws : is_disp_pstrans _ _ _ disp_pstrans_rinvunitor_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := pstrans_rinvunitor (total_psfunctor _ _ _ FF)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (X : pstrans_to_pstrans_data PP
              =
              total_pstrans_data _ _ _ disp_pstrans_rinvunitor_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf is_pstrans X PP2).
Qed.

Definition disp_pstrans_rinvunitor
  : disp_pstrans
      FF
      (disp_pseudo_comp _ _ _ _ _ (disp_pseudo_id D₁) FF)
      (pstrans_rinvunitor F)
  := disp_pstrans_rinvunitor_data,, disp_pstrans_rinvunitor_laws.
End DispTransUnitality.

Section DispTransAssociativiy.
Context {B₁ B₂ B₃ B₄ : bicat}
        {F₁ : psfunctor B₁ B₂}
        {F₂ : psfunctor B₂ B₃}
        {F₃ : psfunctor B₃ B₄}
        {D₁ : disp_bicat B₁} {D₂ : disp_bicat B₂}
        {D₃ : disp_bicat B₃} {D₄ : disp_bicat B₄}
        (FF₁ : disp_psfunctor D₁ D₂ F₁)
        (FF₂ : disp_psfunctor D₂ D₃ F₂)
        (FF₃ : disp_psfunctor D₃ D₄ F₃).

Definition disp_pstrans_lassociator_data
  : disp_pstrans_data
      (disp_pseudo_comp
         _ _ _ _ _
         (disp_pseudo_comp
            _ _ _ _ _
            FF₁
            FF₂)
         FF₃
      )
      (disp_pseudo_comp
         _ _ _ _ _
         FF₁
         (disp_pseudo_comp
            _ _ _ _ _
            FF₂
            FF₃)
      )
      (pstrans_lassociator F₁ F₂ F₃).
Proof.
  use make_disp_pstrans_data.
  - exact (λ x xx, id_disp (_ x xx)).
  - cbn.
    refine (λ x y f xx yy ff, _).
    apply (vcomp_disp_invertible (disp_invertible_2cell_lunitor _)
                                 (disp_invertible_2cell_rinvunitor _)).
Defined.

Lemma disp_pstrans_lassociator_laws : is_disp_pstrans _ _ _ disp_pstrans_lassociator_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := pstrans_lassociator
                (total_psfunctor _ _ _ FF₁)
                (total_psfunctor _ _ _ FF₂)
                (total_psfunctor _ _ _ FF₃)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (X : pstrans_to_pstrans_data PP
              =
              total_pstrans_data _ _ _ disp_pstrans_lassociator_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf is_pstrans X PP2).
Qed.

Definition disp_pstrans_lassociator
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         (disp_pseudo_comp
            _ _ _ _ _
            FF₁
            FF₂)
         FF₃
      )
      (disp_pseudo_comp
         _ _ _ _ _
         FF₁
         (disp_pseudo_comp
            _ _ _ _ _
            FF₂
            FF₃)
      )
      (pstrans_lassociator F₁ F₂ F₃)
  := disp_pstrans_lassociator_data,, disp_pstrans_lassociator_laws.

Definition disp_pstrans_rassociator_data
  : disp_pstrans_data
      (disp_pseudo_comp
         _ _ _ _ _
         FF₁
         (disp_pseudo_comp
            _ _ _ _ _
            FF₂
            FF₃)
      )
      (disp_pseudo_comp
         _ _ _ _ _
         (disp_pseudo_comp
            _ _ _ _ _
            FF₁
            FF₂)
         FF₃
      )
      (pstrans_rassociator F₁ F₂ F₃).
Proof.
  use make_disp_pstrans_data.
  - exact (λ x xx, id_disp (_ x xx)).
  - cbn.
    refine (λ x y f xx yy ff, _).
    apply (vcomp_disp_invertible (disp_invertible_2cell_lunitor _)
                                 (disp_invertible_2cell_rinvunitor _)).
Defined.

Lemma disp_pstrans_rassociator_laws : is_disp_pstrans _ _ _ disp_pstrans_rassociator_data.
Proof.
  apply is_disp_pstrans_from_total.
  pose (PP := pstrans_rassociator
                (total_psfunctor _ _ _ FF₁)
                (total_psfunctor _ _ _ FF₂)
                (total_psfunctor _ _ _ FF₃)).
  pose (PP2 := pstrans_to_is_pstrans PP).
  assert (X : pstrans_to_pstrans_data PP
              =
              total_pstrans_data _ _ _ disp_pstrans_lassociator_data).
  - use total2_paths_f.
    + apply idpath.
    + apply funextsec. intro x.
      apply funextsec. intro y.
      apply funextsec. intro f.
      use subtypePath.
      { intro. apply isaprop_is_invertible_2cell. }
      apply idpath.
  - exact (transportf is_pstrans X PP2).
Qed.

Definition disp_pstrans_rassociator
  : disp_pstrans
      (disp_pseudo_comp
         _ _ _ _ _
         FF₁
         (disp_pseudo_comp
            _ _ _ _ _
            FF₂
            FF₃)
      )
      (disp_pseudo_comp
         _ _ _ _ _
         (disp_pseudo_comp
            _ _ _ _ _
            FF₁
            FF₂)
         FF₃
      )
      (pstrans_rassociator F₁ F₂ F₃)
  := disp_pstrans_rassociator_data,, disp_pstrans_rassociator_laws.
End DispTransAssociativiy.
