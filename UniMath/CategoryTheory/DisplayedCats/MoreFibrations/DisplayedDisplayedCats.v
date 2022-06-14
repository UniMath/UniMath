Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence. (* only coercions *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Foundations.All.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.


Section DisplayedDisplayedCategories.

Definition disp_disp_cat (C : category) : UU
  := ∑ (D : disp_cat C), disp_cat (total_category D).

Definition base_disp_cat {C : category} (E : disp_disp_cat C) : disp_cat C
  := pr1 E.

Definition top_disp_cat {C : category} (E : disp_disp_cat C)
  : disp_cat (total_category (base_disp_cat E))
  := pr2 E.

End DisplayedDisplayedCategories.


Section CompositeDisplayedCategories.

Definition composite_disp_cat_ob_mor {C : category} (DD : disp_disp_cat C)
  : disp_cat_ob_mor C.
Proof.
  destruct DD as [D E].
  use tpair.
  - intro x.
    exact (∑ xx : D x, E (x ,, xx)).
  - simpl.
    intros x y [xx xxx] [yy yyy] f.
    exact (∑ ff : xx -->[f] yy, xxx -->[(f ,, ff)] yyy).
Defined.

Definition composite_disp_cat_id_comp {C : category} (DD : disp_disp_cat C)
  : disp_cat_id_comp C (composite_disp_cat_ob_mor DD).
Proof.
  destruct DD as [D E].
  use tpair.
  - intros x [xx xxx].
    use tpair.
    + simpl.
      exact (id_disp xx).
    + simpl.
      exact (id_disp xxx).
  - simpl.
    intros x y z f g [xx xxx] [yy yyy] [zz zzz] [ff fff] [gg ggg].
    use tpair.
    + exact (ff ;; gg).
    + simpl.
      exact (fff ;; ggg).
Defined.

Definition composite_disp_cat_data {C : category} (DD : disp_disp_cat C)
  := (composite_disp_cat_ob_mor DD ,, composite_disp_cat_id_comp DD) : disp_cat_data C.

Definition composite_disp_cat_axioms {C : category} (DD : disp_disp_cat C)
  : disp_cat_axioms C (composite_disp_cat_data DD).
Proof.
  destruct DD as [D E].
  repeat split.
  - intros x y f [xx xxx] [yy yyy] [ff fff].
    use total2_reassoc_paths'.
    + simpl.
      apply id_left_disp.
    + simpl.
      apply (pathscomp0 (id_left_disp fff)).
      apply maponpaths_2.
      apply homset_property.
  - intros x y f [xx xxx] [yy yyy] [ff fff].
    use total2_reassoc_paths'.
    + simpl.
      apply id_right_disp.
    + simpl.
      eapply pathscomp0.
      * apply (id_right_disp fff).
      * apply maponpaths_2.
        apply homset_property.
  - intros x y z w f g h [xx xxx] [yy yyy] [zz zzz] [ww www] [ff fff] [gg ggg] [hh hhh].
    use total2_reassoc_paths'.
    + simpl.
      apply assoc_disp.
    + simpl.
      eapply pathscomp0.
      * apply (assoc_disp fff ggg hhh).
      * apply maponpaths_2.
        apply homset_property.
  - intros x y f [xx xxx] [yy yyy].
    apply isaset_total2.
    + apply homsets_disp.
    + intros ff.
      apply homsets_disp.
Qed.

Definition composite_disp_cat {C : category} (DD : disp_disp_cat C)
  : disp_cat C
  := (_,, composite_disp_cat_axioms DD).

End CompositeDisplayedCategories.


Section Auxiliary. (* Auxiliary lemmas for the axioms of fiber displayed categories. *)

(* analogous to UniMath.MoreFoundations.PartA.total2_reassoc_paths' for fiber instead of composite: *)
Definition total2_fiber_path {A : UU} {B : A -> UU} {C : (∑ a, B a) -> UU} (a : A)
    (Ca : B a -> UU := λ b, C (a ,, b))
    {b1 b2 : B a} (c1 : Ca b1) (c2 : Ca b2)
    (eb : b1 = b2)
    (ec : c1 = transportb C (two_arg_paths_b (idpath a) eb) c2)
  : c1 = transportb Ca eb c2.
Proof.
  destruct eb; cbn.
  destruct (! ec); cbn.
  apply idpath.
Defined.

(* the following lemma roughly means that a morphism of dependent types commutes with transport: *)
Definition mor_disp_types_comm_transp {A B : UU} (P: A → UU) (Q : B → UU)
    (f0: A → B) (f1: ∏ a : A, P a → Q(f0 a))
    {x x' : A} (h: x = x')
  : ∏ (p : P x), transportf Q (maponpaths f0 h) (f1 x p) = f1 x' (transportf P h p).
Proof.
  intro p.
  induction h.
  apply idpath.
Defined.

End Auxiliary.


Section FiberDisplayedCategories.

Definition fiber_disp_cat_ob_mor {C : category} (DD : disp_disp_cat C) (c : C)
  : disp_cat_ob_mor (base_disp_cat DD)[{c}].
Proof.
  destruct DD as [D E].
  use tpair.
  - simpl. intro x.
    exact (E (c ,, x)).
  - simpl.
    intros x y xx yy f.
    exact (xx -->[(identity c ,, f)] yy).
Defined.

Definition fiber_disp_cat_id_comp {C : category} (DD : disp_disp_cat C) (c : C)
  : disp_cat_id_comp (base_disp_cat DD)[{c}] (fiber_disp_cat_ob_mor DD c).
Proof.
  destruct DD as [D E].
  split.
  - simpl.
    intros x xx.
    apply (@id_disp _ E _ xx).
  - simpl.
    intros x y z f g xx yy zz ff gg.
    use (transportf _ _ (ff ;; gg)).
    use total2_paths_f; simpl.
    + apply id_right.
    + apply idpath.
Defined.

Definition fiber_disp_cat_data {C : category} (DD : disp_disp_cat C) (c : C)
  := (fiber_disp_cat_ob_mor DD c,, fiber_disp_cat_id_comp DD c)
  : disp_cat_data (base_disp_cat DD)[{c}].

Definition fiber_disp_cat_axioms {C : category} (DD : disp_disp_cat C) (c : C)
  : disp_cat_axioms (base_disp_cat DD)[{c}] (fiber_disp_cat_data DD c).
Proof.
  destruct DD as [D E].
  repeat split; intros; simpl.
  - simpl in *.
    use total2_fiber_path.
    unfold ";;".
    apply transportf_transpose_left.
    apply (pathscomp0 (id_left_disp ff)).
    eapply pathscomp0.
    2: { apply pathsinv0. apply transport_b_b. }
    + unfold transportb.
      apply maponpaths_2.
      apply homset_property.
  - simpl in *.
    use total2_fiber_path.
    unfold ";;".
    apply transportf_transpose_left.
    apply (pathscomp0 (id_right_disp ff)).
    eapply pathscomp0.
    2: { apply pathsinv0. apply transport_b_b. }
    unfold transportb.
    apply maponpaths_2.
    apply homset_property.
  - simpl in *.
    use total2_fiber_path.
    unfold ";;"; simpl.
    apply transportf_transpose_left.
    eapply pathscomp0.
    2: { apply pathsinv0. apply transport_b_b. }
    use pathscomp0.
    + eapply transportf.
      2: { exact (ff ;; (gg ;; hh)). }
      unfold "·"; simpl.
      use total2_paths_f; simpl.
      * apply maponpaths.
        apply id_right.
      * apply (mor_disp_types_comm_transp _ _ (λ e, identity c · e) (λ e ee, f ;; ee)).
    + eapply pathscomp0.
      * apply pathsinv0.
        unfold "·"; simpl.
        apply (mor_disp_types_comm_transp (mor_disp yy ww) (mor_disp xx ww) _ (λ e ee, ff ;; ee) (@total2_paths_f _ _ (identity c · identity c,, _) (identity c,, _) (id_right (identity c)) (idpath (transportf (mor_disp y w) (id_right (identity c)) (g ;; h)))) (gg ;; hh)).
      * apply maponpaths_2.
        apply (homset_property (total_category D) (c,, x) (c,, w)).
    + eapply pathscomp0.
      2: { apply pathsinv0. apply transport_b_f. }
      apply transportf_transpose_right.
      use pathscomp0.
      * use transportf.
        -- exact ((identity c,, f : total_category D ⟦(c,, x), (c,, y)⟧) · (identity c,, g : total_category D ⟦(c,, y), (c,, z)⟧) · (identity c,, h : total_category D ⟦(c,, z), (c,, w)⟧)).
        -- simpl.
           apply (maponpaths (λ e, pr2 (pr2 (total_category_data D)) (c,, x) (c,, z) (c,, w) e (identity c,, h))).
           use total2_paths_f; simpl.
           ++ apply id_right.
           ++ apply idpath.
        -- exact (ff ;; gg ;; hh).
      * eapply pathscomp0.
        -- apply transport_b_f.
        -- apply transportf_transpose_left.
           apply (pathscomp0 (assoc_disp ff gg hh)).
           eapply pathscomp0.
           2: { apply pathsinv0. apply transport_b_f. }
           unfold transportb.
           unfold ";;" at 1 2 9 10.
           apply maponpaths_2.
           apply (homset_property (total_category D) (c,, x) (c,, w)).
      * apply (mor_disp_types_comm_transp _ _ (λ e : total_category_data D ⟦ c,, x, c,, z ⟧, e · (identity c,, h : total_category D ⟦(c,, z), (c,, w)⟧)) (λ e ee, ee ;; hh)).
  - apply homsets_disp.
Qed.

Definition fiber_disp_cat {C : category} (DD : disp_disp_cat C) (c : C)
  : disp_cat (base_disp_cat DD)[{c}]
  := (_,, fiber_disp_cat_axioms DD c).

End FiberDisplayedCategories.
