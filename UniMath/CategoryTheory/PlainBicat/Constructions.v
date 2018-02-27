(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.PlainBicat.Bicat.
Require Import UniMath.CategoryTheory.PlainBicat.DispBicat.

Open Scope cat.
Open Scope mor_disp_scope.

Notation "f' ==>[ x ] g'" := (disp_cells x f' g') (at level 60).

Section dirprod.

Context {C : prebicat} (D1 D2 : disp_prebicat C).

(** TODO: the next three defs are the same as for 1-cats, but there
    they are not well-written

    For the time being, I am making the same mistake here...

*)
Definition dirprod_disp_cat_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ c, D1 c × D2 c).
  intros x y xx yy f.
  exact (pr1 xx -->[f] pr1 yy × pr2 xx -->[f] pr2 yy).
Defined.

Definition dirprod_disp_cat_id_comp
  : disp_cat_id_comp _ dirprod_disp_cat_ob_mor.
Proof.
  apply tpair.
  - intros x xx. exact (id_disp _,, id_disp _).
  - intros x y z f g xx yy zz ff gg.
    exact ((pr1 ff ;; pr1 gg),, (pr2 ff ;; pr2 gg)).
Defined.

Definition dirprod_disp_cat_data : disp_cat_data C
  := (_ ,, dirprod_disp_cat_id_comp).

Definition dirprod_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
Proof.
  exists dirprod_disp_cat_data.
  intros c c' f g x d d' f' g'.
  cbn in *.
  exact ( (pr1 f' ==>[ x ] pr1 g') × (pr2 f' ==>[ x ] pr2 g')).
Defined.

Definition dirprod_disp_prebicat_ops : disp_prebicat_ops dirprod_disp_prebicat_1_id_comp_cells.
Proof.
  repeat (use tpair).
  - cbn. intros.
    apply (dirprodpair (id2_disp _ ) (id2_disp  _)).
  - cbn. intros.
    apply (dirprodpair (lunitor_disp _ ) (lunitor_disp  _)).
  - cbn. intros.
    apply (dirprodpair (runitor_disp _ ) (runitor_disp  _)).
  - cbn. intros.
    apply (dirprodpair (linvunitor_disp _ ) (linvunitor_disp  _)).
  - cbn. intros.
    apply (dirprodpair (rinvunitor_disp _ ) (rinvunitor_disp  _)).
  - cbn. intros.
    apply (dirprodpair (rassociator_disp _ _ _ ) (rassociator_disp _ _ _)).
  - cbn. intros.
    apply (dirprodpair (lassociator_disp _ _ _ ) (lassociator_disp _ _ _)).
  - cbn. intros.
    apply (dirprodpair (vcomp2_disp (pr1 X) (pr1 X0)) (vcomp2_disp (pr2 X) (pr2 X0))).
  - cbn. intros.
    apply (dirprodpair (lwhisker_disp (pr1 ff) (pr1 X)) (lwhisker_disp (pr2 ff) (pr2 X))).
  - cbn. intros.
    apply (dirprodpair (rwhisker_disp (pr1 gg) (pr1 X)) (rwhisker_disp (pr2 gg) (pr2 X))).
Defined.

Definition dirprod_disp_prebicat_data : disp_prebicat_data C := _ ,, dirprod_disp_prebicat_ops.

Definition dirprod_disp_brebicat_laws : disp_prebicat_laws dirprod_disp_prebicat_data.
Proof.
  repeat split; intro.
  - cbn. intros.
    apply dirprod_paths; cbn; use (id2_disp_left _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (id2_disp_right _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (vassocr_disp _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (lwhisker_id2_disp _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (id2_rwhisker_disp _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (lwhisker_vcomp_disp _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (rwhisker_vcomp_disp _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (vcomp_lunitor_disp _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (vcomp_runitor_disp _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (lwhisker_lwhisker_disp _ _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (rwhisker_lwhisker_disp _ _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (rwhisker_rwhisker_disp _ _ _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (vcomp_whisker_disp _ _  _ _ _ _ _ _ _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (lunitor_linvunitor_disp _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (linvunitor_lunitor_disp _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (runitor_rinvunitor_disp _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (rinvunitor_runitor_disp _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (lassociator_rassociator_disp _ _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (rassociator_lassociator_disp _ _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (runitor_rwhisker_disp _ _  @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  - cbn. intros.
    apply dirprod_paths; cbn; use (lassociator_lassociator_disp _ _ _ _ @ _ ); apply pathsinv0.
    + exact (pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
    + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
Qed.

Definition dirprod_disp_prebicat : disp_prebicat C := _ ,, dirprod_disp_brebicat_laws.

End dirprod.