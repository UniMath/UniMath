Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.bicat.bicat.
Require Import UniMath.CategoryTheory.bicat.disp_bicat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Open Scope cat.
Open Scope mor_disp_scope.

Notation "f' ==>[ x ] g'" := (disp_cells _ x f' g') (at level 60).
Notation "f' <==[ x ] g'" := (disp_cells _ x g' f') (at level 60, only parsing).

Section Sigma.

Variable C : bicat.
Variable D : disp_bicat C.
Variable E : disp_bicat (total_bicat C D).

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
  set (PPP := @prebicat_cells (total_bicat C D) (c,, pr1 d) (c',, pr1 d')
                              (f,, pr1 ff) (g,, pr1 gg)).
  exact (pr2 ff ==>[(x,, xx) : PPP] pr2 gg).
Defined.

Definition sigma_bicat_data : disp_prebicat_data C.
Proof.
  exists sigma_prebicat_1_id_comp_cells.
  repeat split; cbn; first [intros until 0 | intros].
  - exists (id2_disp _ _). exact (id2_disp _ _).
  - exists (lunitor_disp _ (pr1 f')). exact (lunitor_disp _ (pr2 f')).
  - exists (runitor_disp _ (pr1 f')). exact (runitor_disp _ (pr2 f')).
  - exists (linvunitor_disp _ (pr1 f')). exact (linvunitor_disp _ (pr2 f')).
  - exists (rinvunitor_disp _ (pr1 f')). exact (rinvunitor_disp _ (pr2 f')).
  - exists (rassociator_disp _ (pr1 ff) (pr1 gg) (pr1 hh)).
    exact (rassociator_disp _ (pr2 ff) (pr2 gg) (pr2 hh)).
  - exists (lassociator_disp _ (pr1 ff) (pr1 gg) (pr1 hh)).
    exact (lassociator_disp _ (pr2 ff) (pr2 gg) (pr2 hh)).
  - intros xx yy.
    exists (vcomp2_disp _ (pr1 xx) (pr1 yy)).
    exact (vcomp2_disp _ (pr2 xx) (pr2 yy)).
  - intros xx.
    exists (lwhisker_disp _ (pr1 ff) (pr1 xx)).
    exact (lwhisker_disp _ (pr2 ff) (pr2 xx)).
  - intros xx.
    exists (rwhisker_disp _ (pr1 gg) (pr1 xx)).
    exact (rwhisker_disp _ (pr2 gg) (pr2 xx)).
Defined.

Definition sigma_bicat : disp_bicat C.
Proof.
  exists sigma_bicat_data.
  repeat split; red; cbn; intros until 0.
Admitted.
