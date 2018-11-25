(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat. Import DispBicat.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition mk_total_ob {C : bicat} {D : disp_bicat C} {a : C} (aa : D a)
  : total_bicat D
  := (a,, aa).

Definition mk_total_mor {C : bicat} {D : disp_bicat C}
           {a b : C} {f : C⟦a, b⟧}
           {aa : D a} {bb : D b} (ff : aa -->[f] bb)
  : mk_total_ob aa --> mk_total_ob bb
  := (f,, ff).

Definition mk_total_cell {C : bicat} {D : disp_bicat C}
           {a b : C} {f g : C⟦a, b⟧} {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : aa -->[g] bb}
           (η : f ==> g)
           (ηη : ff ==>[η] gg)
  : prebicat_cells _ (mk_total_mor ff) (mk_total_mor gg)
  := (η,, ηη).

(* Useful? *)
Lemma total_cell_eq {C : bicat} {D : disp_bicat C}
      {a b : C} {f g : C⟦a, b⟧} {aa : D a} {bb : D b}
      {ff : aa -->[f] bb} {gg : aa -->[g] bb}
      (x y : mk_total_mor ff ==> mk_total_mor gg)
      (e : pr1 x = pr1 y)
      (ee : pr2 x = transportb (λ η : f ==> g, ff ==>[ η] gg) e (pr2 y))
  : x = y.
Proof.
  exact (total2_paths2_b e ee).
Defined.

Section Sigma.

Variable C : bicat.
Variable D : disp_bicat C.
Variable E : disp_bicat (total_bicat D).

Definition sigma_disp_cat_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ c, ∑ (d : D c), (E (c,,d))).
  intros x y xx yy f.
  exact (∑ (fD : pr1 xx -->[f] pr1 yy), pr2 xx -->[f,,fD] pr2 yy).
Defined.

Definition sigma_disp_cat_id_comp
  : disp_cat_id_comp _ sigma_disp_cat_ob_mor.
Proof.
  apply tpair.
  - intros x xx.
    exists (id_disp _). exact (id_disp (pr2 xx)).
  - intros x y z f g xx yy zz ff gg.
    exists (pr1 ff ;; pr1 gg). exact (pr2 ff ;; pr2 gg).
Defined.

Definition sigma_disp_cat_data : disp_cat_data C
  := (_ ,, sigma_disp_cat_id_comp).

Definition sigma_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
Proof.
  exists sigma_disp_cat_data.
  red.
  intros c c' f g x d d' ff gg.
  cbn in *.
  use (∑ xx : pr1 ff ==>[x] pr1 gg , _).
  set (PPP := @prebicat_cells (total_bicat D) (c,, pr1 d) (c',, pr1 d')
                              (f,, pr1 ff) (g,, pr1 gg)).
  exact (pr2 ff ==>[(x,, xx) : PPP] pr2 gg).
Defined.

Definition sigma_bicat_data : disp_prebicat_data C.
Proof.
  exists sigma_prebicat_1_id_comp_cells.
  repeat split; cbn; first [intros until 0 | intros].
  - exists (disp_id2 _). exact (disp_id2 _).
  - exists (disp_lunitor (pr1 f')). exact (disp_lunitor (pr2 f')).
  - exists (disp_runitor (pr1 f')). exact (disp_runitor (pr2 f')).
  - exists (disp_linvunitor (pr1 f')). exact (disp_linvunitor (pr2 f')).
  - exists (disp_rinvunitor (pr1 f')). exact (disp_rinvunitor (pr2 f')).
  - exists (disp_rassociator (pr1 ff) (pr1 gg) (pr1 hh)).
    exact (disp_rassociator (pr2 ff) (pr2 gg) (pr2 hh)).
  - exists (disp_lassociator (pr1 ff) (pr1 gg) (pr1 hh)).
    exact (disp_lassociator (pr2 ff) (pr2 gg) (pr2 hh)).
  - intros xx yy.
    exists (disp_vcomp2 (pr1 xx) (pr1 yy)).
    exact (disp_vcomp2 (pr2 xx) (pr2 yy)).
  - intros xx.
    exists (disp_lwhisker (pr1 ff) (pr1 xx)).
    exact (disp_lwhisker (pr2 ff) (pr2 xx)).
  - intros xx.
    exists (disp_rwhisker (pr1 gg) (pr1 xx)).
    exact (disp_rwhisker (pr2 gg) (pr2 xx)).
Defined.

(* Needed? *)
Lemma total_sigma_cell_eq
      {a b : total_bicat E}
      {f g : total_bicat E ⟦a,b⟧}
      (x y : f ==> g)
      (eq1 : pr1 x = pr1 y)
      (eq2 : pr2 x = transportb (λ z, pr2 f ==>[z] pr2 g) eq1 (pr2 y))
  : x = y.
Proof.
  induction x as (x, xx).
  induction y as (y, yy).
  cbn in *.
  induction eq1.
  cbn in *.
  apply pair_path_in2.
  exact eq2.
Defined.

Lemma sigma_prebicat_laws : disp_prebicat_laws sigma_bicat_data.
Proof.
    repeat split; red; cbn; intros until 0;
  use (@total2_reassoc_paths'
           (_ ==> _) (fun x' => _ ==>[ x'] _)
           (fun x'xx => _ ==>[ mk_total_cell (pr1 x'xx) (pr2 x'xx)] _));
  cbn.
  - apply disp_id2_left.
  - apply (disp_id2_left (pr2 ηη)).
  - apply disp_id2_right.
  - apply (disp_id2_right (pr2 ηη)).
  - apply disp_vassocr.
  - apply (disp_vassocr (pr2 ηη) (pr2 φφ) (pr2 ψψ)).
  - apply disp_lwhisker_id2.
  - apply (disp_lwhisker_id2 (pr2 ff) (pr2 gg)).
  - apply disp_id2_rwhisker.
  - apply (disp_id2_rwhisker (pr2 ff) (pr2 gg)).
  - apply disp_lwhisker_vcomp.
  - apply (disp_lwhisker_vcomp (ff := (pr2 ff)) (pr2 ηη) (pr2 φφ)).
  - apply disp_rwhisker_vcomp.
  - apply (disp_rwhisker_vcomp (ii := pr2 ii) (pr2 ηη) (pr2 φφ)).
  - apply disp_vcomp_lunitor.
  - apply (disp_vcomp_lunitor (pr2 ηη)).
  - apply disp_vcomp_runitor.
  - apply (disp_vcomp_runitor (pr2 ηη)).
  - apply disp_lwhisker_lwhisker.
  - apply (disp_lwhisker_lwhisker (pr2 ff) (pr2 gg) (pr2 ηη)).
  - apply disp_rwhisker_lwhisker.
  - apply (disp_rwhisker_lwhisker (pr2 ff) (pr2 ii) (pr2 ηη)).
  - apply disp_rwhisker_rwhisker.
  - apply (disp_rwhisker_rwhisker _ _ (pr2 hh) (pr2 ii) (pr2 ηη)).
  - apply disp_vcomp_whisker.
  - apply (disp_vcomp_whisker _ _ _ _ _ (pr2 ff) (pr2 gg) (pr2 hh) (pr2 ii) (pr2 ηη) (pr2 φφ)).
  - apply disp_lunitor_linvunitor.
  - apply (disp_lunitor_linvunitor (pr2 ff)).
  - apply disp_linvunitor_lunitor.
  - apply (disp_linvunitor_lunitor (pr2 ff)).
  - apply disp_runitor_rinvunitor.
  - apply (disp_runitor_rinvunitor (pr2 ff)).
  - apply disp_rinvunitor_runitor.
  - apply (disp_rinvunitor_runitor (pr2 ff)).
  - apply disp_lassociator_rassociator.
  - apply (disp_lassociator_rassociator (pr2 ff) (pr2 gg) (pr2 hh)).
  - apply disp_rassociator_lassociator.
  - apply (disp_rassociator_lassociator _ (pr2 ff) (pr2 gg) (pr2 hh)).
  - apply disp_runitor_rwhisker.
  - apply (disp_runitor_rwhisker (pr2 ff) (pr2 gg)).
  - apply disp_lassociator_lassociator.
  - apply (disp_lassociator_lassociator (pr2 ff) (pr2 gg) (pr2 hh) (pr2 ii)).
Qed.

Definition sigma_prebicat : disp_prebicat C
  := sigma_bicat_data,, sigma_prebicat_laws.

Lemma has_disp_cellset_sigma_prebicat
  : has_disp_cellset sigma_prebicat.
Proof.
  red; cbn; intros.
  apply isaset_total2.
  - apply disp_cellset_property.
  - intros. apply disp_cellset_property.
Qed.

Definition sigma_bicat
  : disp_bicat C
  := sigma_prebicat,, has_disp_cellset_sigma_prebicat.

End Sigma.
