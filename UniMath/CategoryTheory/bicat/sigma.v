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

Definition mk_total_ob
           {a : C} (aa : D a)
  : total_bicat C D
  := (a,,aa).

Definition mk_total_mor
           {a b : C}{f : C⟦a, b⟧}
           {aa : D a} {bb : D b}
           (ff : aa -->[f] bb)
  : mk_total_ob aa --> mk_total_ob bb
  := (_ ,, ff).

Definition mk_total_cell
           {a b : C}{f g : C⟦a, b⟧}
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : aa -->[g] bb}
           (η : f ==> g)
           (ηη : ff ==>[η] gg)
  : prebicat_cells _ (mk_total_mor ff) (mk_total_mor gg)
  := ( η ,, ηη).

Lemma pr2_transportf_map (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
      (a a' : A) (e : a = a') (xs : ∑ b : B a, P a b) :
  P a (pr1 xs) -> P a' (transportf (λ x : A, B x) e (pr1 xs)).
Proof.
  intro p.
  induction e.
  apply p.
Defined.


Definition transportf_strong (A : UU) (a b : A) (P : ∏ (x : A), a = x -> UU)
           (e : a = b) (p : P a (idpath a))
  : P b e.
Proof.
  set (T:= @transportf (∑ a' : A, a = a') (λ a'e, P (pr1 a'e) (pr2 a'e)) ).
  specialize (T (a,, idpath _ )).
  specialize (T (b,, e)).
  apply T.
  -
    use total2_paths_f.
    + exact e.
    + cbn.
      apply transportf_id1.
  - cbn.
    apply p.
Defined.

Lemma pr2_transportf_map' (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
      (a a' : A) (e : a = a') (xs : ∑ b : B a, P a b) :
  P a (pr1 xs) -> P a' (pr1 (transportf (λ x : A, ∑ b : B x, P x b) e xs)).
Proof.
  intro p.

  set (T:= transportf_strong A a a' (λ (x : A) (e' : a = x),
                                     P x (pr1 (transportf (λ y : A, ∑ b : B y, P y b)
                                                 (e') xs)))).
  cbn in T.
  apply T.
  (*
  exact (
      @transportf _ (λ (a'0 : A) (e0 : a = a'0), P a'0 (pr1 (transportf (λ x : A, ∑ b : B x, P x b) e0 xs))) e p).
*)


  apply p.
Defined.


Lemma pr2_transportf (A : UU) (B : A -> UU) (P : ∏ a, B a -> UU)
   (a a' : A) (e : a = a') (xs : ∑ b : B a, P a b):
  pr2 (transportf (λ x, ∑ b : B x, P _ b) e xs) =
  pr2_transportf_map' A B P a a' e xs (pr2 xs).
Proof.
  destruct e; apply idpath.
Defined.

Definition sigma_bicat : disp_bicat C.
Proof.
  exists sigma_bicat_data.
  repeat split; red; cbn; intros until 0.
  - set (T:= @total2_reassoc_paths').
    cbn in T.
    specialize (T (f ==> g)  (fun x' => pr1 ff ==>[ x'] pr1 gg)).
    cbn in T.
    specialize (T (fun x'xx => pr2 ff ==>[ mk_total_cell (pr1 x'xx) (pr2 x'xx)] pr2 gg)).
    cbn in T.
    use T.
    + cbn.
      apply id2_disp_left.
    + cbn.
      etrans.
      apply (id2_disp_left _ (pr2 ηη)).
      apply maponpaths_2.  (* apply homset_property. *)
      admit.
Abort.

End Sigma.