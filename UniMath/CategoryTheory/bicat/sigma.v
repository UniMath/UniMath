Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.bicat.bicat.
Require Import UniMath.CategoryTheory.bicat.disp_bicat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Open Scope cat.
Open Scope mor_disp_scope.

Notation "f' ==>[ x ] g'" := (disp_cells x f' g') (at level 60).
Notation "f' <==[ x ] g'" := (disp_cells x g' f') (at level 60, only parsing).

(* --------------------------------------------------------------------------------------------- *)
(* Miscellanea.                                                                                  *)
(* --------------------------------------------------------------------------------------------- *)

(* Nice, but not used here. *)
Definition transportf_strong (A : UU) (a b : A) (P : ∏ (x : A), a = x -> UU)
           (e : a = b) (p : P a (idpath a))
  : P b e.
Proof.
  set (T:= @transportf (∑ a' : A, a = a') (λ a'e, P (pr1 a'e) (pr2 a'e)) ).
  specialize (T (a,, idpath _ )).
  specialize (T (b,, e)).
  apply T.
  - use total2_paths_f.
    + exact e.
    + cbn. apply transportf_id1.
  - cbn. apply p.
Defined.

Lemma pr2_transportf_map (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
      (a a' : A) (e : a = a') (xs : ∑ b : B a, P a b) :
  P a (pr1 xs) -> P a' (transportf (λ x : A, B x) e (pr1 xs)).
Proof.
  intro p. induction e. apply p.
Defined.

Lemma pr2_transportf_map' (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
      (a a' : A) (e : a = a') (xs : ∑ b : B a, P a b) :
  P a (pr1 xs) -> P a' (pr1 (transportf (λ x : A, ∑ b : B x, P x b) e xs)).
Proof.
  intro p.
  set (T:= transportf_strong A a a'
                             (λ (x : A) (e' : a = x),
                              P x (pr1 (transportf (λ y : A, ∑ b : B y, P y b)
                                                   e' xs)))).
  cbn in T. apply T. apply p.
Defined.

Lemma pr2_transportf (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
   (a a' : A) (e : a = a') (xs : ∑ b : B a, P a b):
  pr2 (transportf (λ x, ∑ b : B x, P _ b) e xs) =
  pr2_transportf_map' A B P a a' e xs (pr2 xs).
Proof.
  destruct e; apply idpath.
Defined.

Definition mk_total_ob {C : prebicat} {D : disp_prebicat C} {a : C} (aa : D a)
  : total_bicat D
  := (a,, aa).

Definition mk_total_mor {C : prebicat} {D : disp_prebicat C}
           {a b : C} {f : C⟦a, b⟧}
           {aa : D a} {bb : D b} (ff : aa -->[f] bb)
  : mk_total_ob aa --> mk_total_ob bb
  := (f,, ff).

Definition mk_total_cell  {C : prebicat} {D : disp_prebicat C}
           {a b : C} {f g : C⟦a, b⟧}
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : aa -->[g] bb}
           (η : f ==> g)
           (ηη : ff ==>[η] gg)
  : prebicat_cells _ (mk_total_mor ff) (mk_total_mor gg)
  := (η,, ηη).

(* Useful? *)
Lemma total_cell_eq
      {C : prebicat}
      {D : disp_prebicat C}
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

Variable C : prebicat.
Variable D : disp_prebicat C.
Variable E : disp_prebicat (total_bicat D).

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
  - exists (id2_disp _). exact (id2_disp _).
  - exists (lunitor_disp (pr1 f')). exact (lunitor_disp (pr2 f')).
  - exists (runitor_disp (pr1 f')). exact (runitor_disp (pr2 f')).
  - exists (linvunitor_disp (pr1 f')). exact (linvunitor_disp (pr2 f')).
  - exists (rinvunitor_disp (pr1 f')). exact (rinvunitor_disp (pr2 f')).
  - exists (rassociator_disp (pr1 ff) (pr1 gg) (pr1 hh)).
    exact (rassociator_disp (pr2 ff) (pr2 gg) (pr2 hh)).
  - exists (lassociator_disp (pr1 ff) (pr1 gg) (pr1 hh)).
    exact (lassociator_disp (pr2 ff) (pr2 gg) (pr2 hh)).
  - intros xx yy.
    exists (vcomp2_disp (pr1 xx) (pr1 yy)).
    exact (vcomp2_disp (pr2 xx) (pr2 yy)).
  - intros xx.
    exists (lwhisker_disp (pr1 ff) (pr1 xx)).
    exact (lwhisker_disp (pr2 ff) (pr2 xx)).
  - intros xx.
    exists (rwhisker_disp (pr1 gg) (pr1 xx)).
    exact (rwhisker_disp (pr2 gg) (pr2 xx)).
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
  destruct x as (x, xx).
  destruct y as (y, yy).
  cbn in *.
  destruct eq1.
  cbn in *.
  apply pair_path_in2.
  exact eq2.
Defined.

Definition sigma_prebicat : disp_prebicat C.
Proof.
  exists sigma_bicat_data.
  repeat split; red; cbn; intros until 0;
  use (@total2_reassoc_paths'
           (_ ==> _) (fun x' => _ ==>[ x'] _)
           (fun x'xx => _ ==>[ mk_total_cell (pr1 x'xx) (pr2 x'xx)] _));
  cbn.
  - apply id2_disp_left.
  - apply (id2_disp_left (pr2 ηη)).
  - apply id2_disp_right.
  - apply (id2_disp_right (pr2 ηη)).
  - apply vassocr_disp.
  - apply (vassocr_disp (pr2 ηη) (pr2 φφ) (pr2 ψψ)).
  - apply lwhisker_id2_disp.
  - apply (lwhisker_id2_disp (pr2 ff) (pr2 gg)).
  - apply id2_rwhisker_disp.
  - apply (id2_rwhisker_disp (pr2 ff) (pr2 gg)).
  - apply lwhisker_vcomp_disp.
  - apply (lwhisker_vcomp_disp (ff := (pr2 ff)) (pr2 ηη) (pr2 φφ)).
  - apply rwhisker_vcomp_disp.
  - apply (rwhisker_vcomp_disp (ii := pr2 ii) (pr2 ηη) (pr2 φφ)).
  - apply vcomp_lunitor_disp.
  - apply (vcomp_lunitor_disp (pr2 ηη)).
  - apply vcomp_runitor_disp.
  - apply (vcomp_runitor_disp (pr2 ηη)).
  - apply lwhisker_lwhisker_disp.
  - apply (lwhisker_lwhisker_disp (pr2 ff) (pr2 gg) (pr2 ηη)).
  - apply rwhisker_lwhisker_disp.
  - apply (rwhisker_lwhisker_disp (pr2 ff) (pr2 ii) (pr2 ηη)).
  - apply rwhisker_rwhisker_disp.
  - apply (rwhisker_rwhisker_disp _ _ (pr2 hh) (pr2 ii) (pr2 ηη)).
  - apply vcomp_whisker_disp.
  - apply (vcomp_whisker_disp _ _ _ _ _ (pr2 ff) (pr2 gg) (pr2 hh) (pr2 ii) (pr2 ηη) (pr2 φφ)).
  - apply lunitor_linvunitor_disp.
  - apply (lunitor_linvunitor_disp (pr2 ff)).
  - apply linvunitor_lunitor_disp.
  - apply (linvunitor_lunitor_disp (pr2 ff)).
  - apply runitor_rinvunitor_disp.
  - apply (runitor_rinvunitor_disp (pr2 ff)).
  - apply rinvunitor_runitor_disp.
  - apply (rinvunitor_runitor_disp (pr2 ff)).
  - apply lassociator_rassociator_disp.
  - apply (lassociator_rassociator_disp (pr2 ff) (pr2 gg) (pr2 hh)).
  - apply rassociator_lassociator_disp.
  - apply (rassociator_lassociator_disp _ (pr2 ff) (pr2 gg) (pr2 hh)).
  - apply runitor_rwhisker_disp.
  - apply (runitor_rwhisker_disp (pr2 ff) (pr2 gg)).
  - apply lassociator_lassociator_disp.
  - apply (lassociator_lassociator_disp (pr2 ff) (pr2 gg) (pr2 hh) (pr2 ii)).
Qed.

End Sigma.
