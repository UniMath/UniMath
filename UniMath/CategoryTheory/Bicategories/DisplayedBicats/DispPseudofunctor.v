(* ------------------------------------------------------------------------- *)
(** Displayed pseudofunctors.
    Marco Maggesi, Niccolò Veltri, Niels van der Weide
    July 2019

    Contents:
      - Definition of displayed pseudofunctors.
      - Identity and composition of displayed pseudofunctors.                *)
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
Import PseudoFunctor.Notations.

Local Open Scope cat.

(** ** Definition of displayed pseudofunctor *)

Section DispPseudofunctor.

Context {B₁ : bicat} (D₁ : disp_bicat B₁)
        {B₂ : bicat} (D₂ : disp_bicat B₂)
        (F : psfunctor B₁ B₂).

(** *** Data *)

Definition disp_psfunctor_data : UU
  :=
    ∑ (obFF : ∏ x:B₁, D₁ x → D₂ (F x))
      (morFF : ∏ (x y : B₁) (f : B₁⟦x,y⟧) (xx : D₁ x) (yy : D₁ y),
               (xx -->[f] yy) →
               (obFF x xx -->[#F f] obFF y yy))
      (cellFF : ∏ (x y : B₁) (f g : B₁⟦x,y⟧) (α : f ==> g) (xx : D₁ x) (yy : D₁ y)
                  (ff : xx -->[f] yy) (gg : xx -->[g] yy),
                (ff ==>[α] gg) → (morFF x y f xx yy ff ==>[##F α] morFF x y g xx yy gg))
      (disp_psfunctor_id : ∏ (x : B₁) (xx : D₁ x),
                           disp_invertible_2cell
                             (psfunctor_id F x)
                             (id_disp (obFF x xx))
                             (morFF x x (id₁ x) xx xx (id_disp xx))),
    (∏ (x y z : B₁) (f : x --> y) (g : y --> z)
       (xx : D₁ x) (yy : D₁ y) (zz : D₁ z)
       (ff : xx -->[f] yy) (gg : yy -->[g] zz),
     disp_invertible_2cell
       (psfunctor_comp F f g)
       (comp_disp (morFF x y f xx yy ff) (morFF y z g yy zz gg))
       (morFF x z (f · g) xx zz (comp_disp ff gg))).

Definition make_disp_psfunctor_data
           (obFF : ∏ x:B₁, D₁ x → D₂ (F x))
           (morFF : ∏ (x y : B₁) (f : B₁⟦x,y⟧) (xx : D₁ x) (yy : D₁ y),
                    (xx -->[f] yy) →
                    (obFF x xx -->[#F f] obFF y yy))
           (cellFF : ∏ (x y : B₁) (f g : B₁⟦x,y⟧) (α : f ==> g) (xx : D₁ x) (yy : D₁ y)
                       (ff : xx -->[f] yy) (gg : xx -->[g] yy),
                     (ff ==>[α] gg) → (morFF x y f xx yy ff ==>[##F α] morFF x y g xx yy gg))
           (disp_psfunctor_id : ∏ (x : B₁) (xx : D₁ x),
                                disp_invertible_2cell
                                  (psfunctor_id F x)
                                  (id_disp (obFF x xx))
                                  (morFF x x (id₁ x) xx xx (id_disp xx)))
           (disp_psfunctor_comp : ∏ (x y z : B₁) (f : x --> y) (g : y --> z)
                                    (xx : D₁ x) (yy : D₁ y) (zz : D₁ z)
                                    (ff : xx -->[f] yy) (gg : yy -->[g] zz),
                                  disp_invertible_2cell
                                    (psfunctor_comp F f g)
                                    (comp_disp (morFF x y f xx yy ff) (morFF y z g yy zz gg))
                                    (morFF x z (f · g) xx zz (comp_disp ff gg)))
  : disp_psfunctor_data
  := (obFF,, morFF,, cellFF,, disp_psfunctor_id,, disp_psfunctor_comp).

Definition disp_psfunctor_ob (FFdata : disp_psfunctor_data)
           {x : B₁}
           (xx : D₁ x)
  : D₂ (F x)
  := pr1 FFdata x xx.

Coercion disp_psfunctor_ob : disp_psfunctor_data >-> Funclass.

Section Projections.

Variable (FFdata : disp_psfunctor_data).

Definition disp_psfunctor_mor
           {x y : B₁} {f : B₁⟦x,y⟧} {xx : D₁ x} {yy : D₁ y}
           (ff : xx -->[f] yy)
  : FFdata x xx -->[#F f] FFdata y yy
  := pr12 FFdata x y f xx yy ff.

Definition disp_psfunctor_cell {x y : B₁} {f g : B₁⟦x,y⟧} {α : f ==> g}
           {xx : D₁ x} {yy : D₁ y}
           {ff : xx -->[f] yy} {gg : xx -->[g] yy}
           (αα : ff ==>[α] gg)
  : disp_psfunctor_mor ff ==>[##F α] disp_psfunctor_mor gg
  := pr122 FFdata x y f g α xx yy ff gg αα.

Definition disp_psfunctor_id {x : B₁} (xx : D₁ x)
  : disp_invertible_2cell (psfunctor_id F x)
                          (id_disp (FFdata x xx))
                          (disp_psfunctor_mor (id_disp xx))
  := pr122 (pr2 FFdata) x xx.

Definition disp_psfunctor_comp
           {x y z : B₁} {f : x --> y} {g : y --> z}
           {xx : D₁ x} {yy : D₁ y} {zz : D₁ z}
           (ff : xx -->[f] yy) (gg : yy -->[g] zz)
  : disp_invertible_2cell (psfunctor_comp F f g)
                          (comp_disp (disp_psfunctor_mor ff) (disp_psfunctor_mor gg))
                          (disp_psfunctor_mor (comp_disp ff gg))
  := pr222 (pr2 FFdata) x y z f g xx yy zz ff gg.

End Projections.

Definition total_psfunctor_data (FFdata : disp_psfunctor_data)
  : psfunctor_data (total_bicat D₁) (total_bicat D₂).
Proof.
  use make_psfunctor_data.
  - exact (λ x, (F (pr1 x),, FFdata _ (pr2 x))).
  - exact (λ x y f, (#F (pr1 f) ,, disp_psfunctor_mor FFdata (pr2 f))).
  - exact (λ x y f g α, (##F (pr1 α),, disp_psfunctor_cell FFdata (pr2 α))).
  - exact (λ x, iso_in_E_weq _ _ (psfunctor_id F (pr1 x),, disp_psfunctor_id FFdata (pr2 x))).
  - refine (λ x y z f g, iso_in_E_weq _ _ _).
    exact (psfunctor_comp F (pr1 f) (pr1 g),, disp_psfunctor_comp FFdata (pr2 f) (pr2 g)).
Defined.

(** *** Properties *)

Section DispPseudofunctorLaws.

Variable FFdata : disp_psfunctor_data.

Definition disp_psfunctor_id2_law
  : UU
  := ∏ (a b : B₁) (f : a --> b)
       (aa : D₁ a)
       (bb : D₁ b)
       (ff : aa -->[f] bb),
     disp_psfunctor_cell FFdata (disp_id2 ff) =
     transportb
       (λ p : # F f ==> # F f, disp_psfunctor_mor FFdata ff ==>[p] disp_psfunctor_mor FFdata ff)
       (psfunctor_id2 F f) (disp_id2 (disp_psfunctor_mor FFdata ff)).

Definition disp_psfunctor_vcomp2_law : UU
  := ∏ (a b : B₁) (f g h : B₁ ⟦a, b⟧) (η : f ==> g) (φ : g ==> h) (aa : D₁ a)
       (bb : D₁ b) (ff : aa -->[f] bb) (gg : aa -->[g] bb) (hh : aa -->[h] bb)
       (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh),
     disp_psfunctor_cell FFdata (ηη •• φφ) =
     transportb
       (λ p : # F f ==> # F h, disp_psfunctor_mor FFdata ff ==>[ p] disp_psfunctor_mor FFdata hh)
       (psfunctor_vcomp F η φ) (disp_psfunctor_cell FFdata ηη •• disp_psfunctor_cell FFdata φφ).

Definition disp_psfunctor_lunitor_law : UU
  := ∏ (a b : B₁) (f : B₁ ⟦ a, b ⟧) (aa : D₁ a) (bb : D₁ b) (ff : aa -->[ f] bb),
     disp_lunitor (disp_psfunctor_mor FFdata ff) =
     transportb
       (λ p, _ ==>[p] _)
       (psfunctor_lunitor F f)
       (((disp_psfunctor_id FFdata aa ▹▹ disp_psfunctor_mor FFdata ff)
           •• disp_psfunctor_comp FFdata (id_disp aa) ff)
          •• disp_psfunctor_cell FFdata (disp_lunitor ff)).

Definition disp_psfunctor_runitor_law : UU
  := ∏ (a b : B₁) (f : B₁ ⟦ a, b ⟧) (aa : D₁ a) (bb : D₁ b) (ff : aa -->[ f] bb),
     disp_runitor (disp_psfunctor_mor FFdata ff) =
     transportb
       (λ p, _ ==>[p] _)
       (psfunctor_runitor F f)
       (((disp_psfunctor_mor FFdata ff ◃◃ disp_psfunctor_id FFdata _)
           •• disp_psfunctor_comp FFdata _ _)
          •• disp_psfunctor_cell FFdata (disp_runitor ff)).

Definition disp_psfunctor_lassociator_law : UU
  :=
    ∏ (a b c d : B₁) (f : B₁ ⟦ a, b ⟧) (g : B₁ ⟦ b, c ⟧) (h : B₁ ⟦ c, d ⟧)
      (aa : D₁ a) (bb : D₁ b) (cc : D₁ c) (dd : D₁ d) (ff : aa -->[ f] bb) (gg : bb -->[ g] cc)
      (hh : cc -->[ h] dd),
    ((disp_psfunctor_mor FFdata ff ◃◃ disp_psfunctor_comp FFdata gg hh)
       •• disp_psfunctor_comp FFdata ff (gg;; hh))
      •• disp_psfunctor_cell FFdata (disp_lassociator ff gg hh) =
    transportb
      (λ p, _ ==>[p] _)
      (psfunctor_lassociator F f g h)
      ((disp_lassociator (disp_psfunctor_mor FFdata ff) (disp_psfunctor_mor FFdata gg)
                         (disp_psfunctor_mor FFdata hh)
         •• (disp_psfunctor_comp FFdata ff gg ▹▹ disp_psfunctor_mor FFdata hh))
        •• disp_psfunctor_comp FFdata (ff;; gg) hh).

Definition disp_psfunctor_lwhisker_law : UU
  := ∏ (a b c : B₁) (f : B₁ ⟦ a, b ⟧) (g₁ g₂ : B₁ ⟦ b, c ⟧) (η : g₁ ==> g₂)
       (aa : D₁ a) (bb : D₁ b) (cc : D₁ c) (ff : aa -->[ f] bb) (gg₁ : bb -->[ g₁] cc)
       (gg₂ : bb -->[ g₂] cc) (ηη : gg₁ ==>[ η] gg₂),
     disp_psfunctor_comp FFdata ff gg₁ •• disp_psfunctor_cell FFdata (ff ◃◃ ηη) =
     transportb
       (λ p, _ ==>[p] _)
       (psfunctor_lwhisker F f η)
       ((disp_psfunctor_mor FFdata ff ◃◃ disp_psfunctor_cell FFdata ηη)
          •• disp_psfunctor_comp FFdata ff gg₂).

Definition disp_psfunctor_rwhisker_law : UU
  := ∏ (a b c : B₁) (f₁ f₂ : B₁ ⟦ a, b ⟧) (g : B₁ ⟦ b, c ⟧) (η : f₁ ==> f₂)
       (aa : D₁ a) (bb : D₁ b) (cc : D₁ c)
       (ff₁ : aa -->[f₁] bb)
       (ff₂ : aa -->[f₂] bb)
       (gg : bb -->[g] cc)
       (ηη : ff₁ ==>[ η] ff₂),
     disp_psfunctor_comp FFdata _ _ •• disp_psfunctor_cell FFdata (ηη ▹▹ gg) =
     transportb
       (λ p, _ ==>[p] _)
       (psfunctor_rwhisker F g η)
       ((disp_psfunctor_cell FFdata ηη ▹▹ _)
          •• disp_psfunctor_comp FFdata _ _).

Definition is_disp_psfunctor : UU
    := disp_psfunctor_id2_law
         × disp_psfunctor_vcomp2_law
         × disp_psfunctor_lunitor_law
         × disp_psfunctor_runitor_law
         × disp_psfunctor_lassociator_law
         × disp_psfunctor_lwhisker_law
         × disp_psfunctor_rwhisker_law.

Definition disp_psfunctor_id2 (H : is_disp_psfunctor) := pr1 H.

Definition disp_psfunctor_vcomp2 (H : is_disp_psfunctor) := pr12 H.

Definition disp_psfunctor_vcomp2_alt (H : is_disp_psfunctor)
           (a b : B₁) (f g h : B₁ ⟦a, b⟧) (η : f ==> g) (φ : g ==> h) (aa : D₁ a)
           (bb : D₁ b) (ff : aa -->[f] bb) (gg : aa -->[g] bb) (hh : aa -->[h] bb)
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh)
  : transportf
      (λ p : # F f ==> # F h, disp_psfunctor_mor FFdata ff ==>[ p] disp_psfunctor_mor FFdata hh)
      (psfunctor_vcomp F η φ)
      (disp_psfunctor_cell FFdata (ηη •• φφ)) =
    disp_psfunctor_cell FFdata ηη •• disp_psfunctor_cell FFdata φφ.
Proof.
  refine (transportf_transpose_alt (P := λ p, _ ==>[p] _)).
  apply (disp_psfunctor_vcomp2 H).
Qed.

End DispPseudofunctorLaws.

(** *** Disp pseudofunct *)

Definition disp_psfunctor : UU
  := ∑ FF : disp_psfunctor_data, is_disp_psfunctor FF.

Coercion disp_psfunctor_to_disp_psfunctor_data (FF : disp_psfunctor)
  : disp_psfunctor_data
  := pr1 FF.

Lemma total_psfunctor_laws (FF : disp_psfunctor)
  : psfunctor_laws (total_psfunctor_data FF).
Proof.
  repeat apply make_dirprod; intro; intros; (use total2_paths_b; [ apply F | apply FF ]).
Qed.

Definition total_psfunctor (FF : disp_psfunctor)
  : psfunctor (total_bicat D₁) (total_bicat D₂).
Proof.
  use make_psfunctor.
  - exact (total_psfunctor_data FF).
  - exact (total_psfunctor_laws FF).
  - split; intros; use iso_in_E_weq.
Defined.

Definition is_disp_psfunctor_from_total (FF : disp_psfunctor_data)
  : is_psfunctor (total_psfunctor_data FF) → is_disp_psfunctor FF.
Proof.
  intros HFF.
  pose (EF := make_psfunctor _ (pr1 HFF) (pr2 HFF)).
  repeat split.
  - intros a b f aa bb ff.
    pose (P := !fiber_paths (@psfunctor_id2 _ _ EF (a,,aa) (b,,bb) (f,,ff))).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
  - intros a b f g h η φ aa bb ff gg hh ηη φφ.
    pose (P := !fiber_paths (@psfunctor_vcomp _ _ EF
                                              (a,,aa) (b,,bb) (f,,ff) (g,,gg) (h,,hh)
                                              (η,,ηη) (φ,,φφ))).
    cbn in P; rewrite P.
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
  - intros a b f aa bb ff.
    pose (P := !fiber_paths (@psfunctor_lunitor _ _
                                                EF (a,,aa) (b,,bb) (f,,ff))).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
  - intros a b f aa bb ff.
    pose (P := !fiber_paths (@psfunctor_runitor _ _
                                                EF (a,,aa) (b,,bb) (f,,ff))).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
  - intros a b c d f g h aa bb cc dd ff gg hh.
    pose (P := !fiber_paths (@psfunctor_lassociator _ _
                                                    EF (a,,aa) (b,,bb) (c,,cc) (d,,dd)
                                                    (f,,ff) (g,,gg)  (h,,hh))).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
  - intros a b c f g1 g2 η aa bb cc ff gg1 gg2 ηη.
    pose (P := !fiber_paths (@psfunctor_lwhisker _ _
                                                 EF (a,,aa) (b,,bb) (c,,cc)
                                                 (f,,ff) (g1,,gg1) (g2,,gg2) (η,,ηη))).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
  - intros a b c f1 f2 g η aa bb cc ff1 ff2 gg ηη.
    pose (P := !fiber_paths (@psfunctor_rwhisker _ _ EF (a,,aa) (b,,bb) (c,,cc)
                                                 (f1,,ff1) (f2,,ff2) (g,,gg) (η,,ηη))).
    symmetry.
    etrans. { apply maponpaths. exact P. }
    unfold transportb.
    rewrite transport_f_f.
    rewrite transportf_set.
    * apply idpath.
    * apply B₂.
Qed.

End DispPseudofunctor.

(** ** Identity *)

Section DispPseudofunctor_identity.

Context {B : bicat} (D : disp_bicat B).

Definition disp_pseudo_id_data : disp_psfunctor_data D D (ps_id_functor B).
Proof.
  use make_disp_psfunctor_data; cbn.
  - exact (λ _ y, y).
  - exact (λ _ _ _ _ _ ff, ff).
  - exact (λ _ _ _ _ _ _ _ _ _ αα, αα).
  - intros. apply disp_id2_invertible_2cell.
  - intros. apply disp_id2_invertible_2cell.
Defined.

Lemma disp_pseudo_id_laws : is_disp_psfunctor D D _ disp_pseudo_id_data.
Proof.
  apply is_disp_psfunctor_from_total.
  apply ps_id_functor.
Qed.

Definition disp_pseudo_id : disp_psfunctor D D (ps_id_functor B)
  := disp_pseudo_id_data,, disp_pseudo_id_laws.

End DispPseudofunctor_identity.

Definition disp_psfunctor_cell_transportb
           {B₁ B₂ : bicat}
           {F : psfunctor B₁ B₂}
           {D₁ : disp_bicat B₁}
           {D₂ : disp_bicat B₂}
           (FF : disp_psfunctor D₁ D₂ F)
           {x y : B₁}
           {f : x --> y}
           {φ ψ : f ==> f}
           {xx : D₁ x}
           {yy : D₁ y}
           {ff : xx -->[f] yy}
           (p : φ = ψ)
           (ψψ : ff ==>[ ψ ] ff)
  : disp_psfunctor_cell
      _ _ _ (pr1 FF)
      (transportb (λ z, ff ==>[ z ] ff) p ψψ)
    =
    transportb
      (λ z, _ ==>[ z ] _)
      (maponpaths (λ z, ##F z) p)
      (disp_psfunctor_cell
         _ _ _ (pr1 FF)
         ψψ).
Proof.
  induction p.
  cbn.
  apply idpath.
Defined.

Section DispPseudofunctorInvertible_2cell.

Context {B₁ B₂ : bicat}
        {F : psfunctor B₁ B₂}
        {D₁ : disp_bicat B₁}
        {D₂ : disp_bicat B₂}
        (FF : disp_psfunctor D₁ D₂ F)
        {x y : B₁}
        {f g : x --> y}
        {α : invertible_2cell f g}
        {xx : D₁ x}
        {yy : D₁ y}
        {ff : xx -->[f] yy}
        {gg : xx -->[g] yy}
        (αα : disp_invertible_2cell α ff gg).

Definition disp_psfunctor_invertible_2cell
  : disp_invertible_2cell
      (_,, psfunctor_is_iso F α)
      (disp_psfunctor_mor _ _ _ FF ff)
      (disp_psfunctor_mor _ _ _ FF gg).
Proof.
  repeat use tpair; cbn.
  - exact (disp_psfunctor_cell _ _ _ FF αα).
  - exact (disp_psfunctor_cell _ _ _ FF (disp_inv_cell αα)).
  - abstract
      (rewrite <- (disp_psfunctor_vcomp2_alt _ _ _ _ (pr2 FF));
       rewrite disp_vcomp_rinv;
       rewrite disp_psfunctor_cell_transportb;
       unfold transportb;
       rewrite transport_f_f;
       rewrite (disp_psfunctor_id2 _ _ _ _ (pr2 FF));
       unfold transportb;
       rewrite transport_f_f;
       apply (@transportf_paths _ (λ p, _ ==>[ p ] _));
       apply B₂).
  - abstract
      (rewrite <- (disp_psfunctor_vcomp2_alt _ _ _ _ (pr2 FF));
       rewrite disp_vcomp_linv;
       rewrite disp_psfunctor_cell_transportb;
       unfold transportb;
       rewrite transport_f_f;
       rewrite (disp_psfunctor_id2 _ _ _ _ (pr2 FF));
       unfold transportb;
       rewrite transport_f_f;
       apply (@transportf_paths _ (λ p, _ ==>[ p ] _));
       apply B₂).
Defined.

End DispPseudofunctorInvertible_2cell.

(** ** Composition *)

Section DispPseudofunctor_comp.

Context {B₁ B₂ B₃ : bicat}
        (F₁ : psfunctor B₁ B₂)
        (F₂ : psfunctor B₂ B₃)
        (D₁ : disp_bicat B₁)
        (D₂ : disp_bicat B₂)
        (D₃ : disp_bicat B₃)
        (FF₁ : disp_psfunctor D₁ D₂ F₁)
        (FF₂ : disp_psfunctor D₂ D₃ F₂).

Definition disp_pseudo_comp_data : disp_psfunctor_data D₁ D₃ (ps_comp F₂ F₁).
Proof.
  use make_disp_psfunctor_data; cbn.
  - exact (λ x xx, FF₂ _ (FF₁ _ xx)).
  - exact (λ x y f xx yy ff, disp_psfunctor_mor _ _ _ FF₂ (disp_psfunctor_mor _ _ _ FF₁ ff)).
  - exact (λ x y f g α xx yy ff gg αα, disp_psfunctor_cell _ _ _ FF₂ (disp_psfunctor_cell _ _ _ FF₁ αα)).
  - intros x xx.
    exact (vcomp_disp_invertible
             (disp_psfunctor_id _ _ _ FF₂ (FF₁ _ xx))
             (disp_psfunctor_invertible_2cell FF₂ (disp_psfunctor_id _ _ _ FF₁ xx))).
  - intros x y z f g xx yy zz ff gg.
    exact (vcomp_disp_invertible
             (disp_psfunctor_comp _ _ _ FF₂
                                  (disp_psfunctor_mor _ _ _ FF₁ ff)
                                  (disp_psfunctor_mor _ _ _ FF₁ gg))
             (disp_psfunctor_invertible_2cell FF₂ (disp_psfunctor_comp _ _ _ FF₁ ff gg))).
Defined.

Lemma disp_pseudo_comp_laws : is_disp_psfunctor _ _ _ disp_pseudo_comp_data.
Proof.
  apply is_disp_psfunctor_from_total.
  apply (ps_comp (total_psfunctor _ _ _ FF₂) (total_psfunctor _ _ _ FF₁)).
Qed.

Definition disp_pseudo_comp : disp_psfunctor _ _ (ps_comp F₂ F₁)
  := disp_pseudo_comp_data,, disp_pseudo_comp_laws.

End DispPseudofunctor_comp.
