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

About transportD.

Section Auxiliary.

Definition transportD' {A : UU} (B : A -> UU) (C : (∑ a : A, B a) -> UU)
           {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C (x1 ,, y)) :
  C (x2 ,, (transportf _ p y)).
Proof.
  use (transportf _ _ z).
  use (@total2_paths_f _ _ (x1 ,, y)).
  - simpl.
    exact p.
  - simpl.
    apply idpath.
Defined.

Definition transportD'' {A : UU} (B : A -> UU) (C : (∑ a : A, B a) -> UU)
           {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C (x1 ,, y)) :
  C (x2 ,, (transportf _ p y)).
Proof.
  induction p.
  exact z.
Defined.

Definition transportf_total2' {A : UU} {B : A -> UU} {C : (∑ a:A, B a) -> UU}
           {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C (x1 ,, y)) :
  transportf (λ x, ∑ y : B x, C (x ,, y)) p (y ,, z) =
  tpair (λ y, C (x2 ,, y)) (transportf _ p y)
        (transportD' _ _ p y z).
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Definition transportf_total2'_pr1 {A : UU} {B : A -> UU} {C : (∑ a:A, B a) -> UU}
           {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C (x1 ,, y)) :
  pr1 (transportf (λ x, ∑ y : B x, C (x ,, y)) p (y ,, z)) = transportf _ p y.
Proof.
  exact (maponpaths pr1 (transportf_total2' p y z)).
Defined.

End Auxiliary.


Section DisplayedDisplayedCategories.

Definition disp_disp_cat (C : category) : UU
  := ∑ (D : disp_cat C), disp_cat (total_category D).

Definition base_disp_cat {C : category} (E : disp_disp_cat C) : disp_cat C
  := pr1 E.

Definition top_disp_cat {C : category} (E : disp_disp_cat C)
  : disp_cat (total_category (base_disp_cat E))
  := pr2 E.


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

Definition composite_disp_cat_axioms0 {C : category} (DD : disp_disp_cat C)
  : disp_cat_axioms C (composite_disp_cat_data DD).
Proof.
  destruct DD as [D E].
  repeat split.
  - intros x y f [xx xxx] [yy yyy] [ff fff].
    use total2_reassoc_paths'.
    + simpl.
      apply id_left_disp.
    + simpl.
      set (temp := (id_left_disp fff)).
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
Defined.

End CompositeDisplayedCategories.


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
    (* eapply (transportf _ _ (ff ;; gg)). *) (* Why does this get stuck with an unfocused subgoal? *)
    use (transportf _ _ (ff ;; gg)).
    use total2_paths_f.
    + simpl.
      (* apply id_left. In the definition of fiber categories, id_right is used! *)
      apply id_right.
    + simpl.
      apply idpath.
Defined.

Definition fiber_disp_cat_data {C : category} (DD : disp_disp_cat C) (c : C)
  := (fiber_disp_cat_ob_mor DD c,, fiber_disp_cat_id_comp DD c)
  : disp_cat_data (base_disp_cat DD)[{c}].

Definition my_lemma {A : UU} {B : A -> UU} {C : (∑ a, B a) -> UU} (a : A)
    (Ca : B a -> UU := λ b, C (a ,, b))
    {b1 b2 : B a} (c1 : Ca b1) (c2 : Ca b2)
    (eb : b1 = b2)
    (ec : c1 = transportb C (two_arg_paths_b (idpath a) eb) c2)
  : c1 = transportb Ca eb c2.
Proof.
  destruct eb; cbn.
  destruct (! ec); cbn.
  apply idpath.
Qed.

Definition my_lemma' {A : UU} {B : A -> UU} {C : (∑ a, B a) -> UU} (a : A)
    (Ca : B a -> UU := λ b, C (a ,, b))
    {b1 b2 : B a} (c1 : Ca b1) (c2 : Ca b2)
    (eb : b1 = b2)
    (ec : transportb C (two_arg_paths_b (idpath a) eb) c2 = c1)
  : c1 = transportb Ca eb c2.
Proof.
  destruct eb; cbn.
  destruct ec; cbn.
  apply idpath.
Qed.

Definition my_lemma'' {A : UU} {B : A -> UU} {C : (∑ a, B a) -> UU} (a : A)
    (Ca : B a -> UU := λ b, C (a ,, b))
    {b1 b2 : B a} (c1 : Ca b1) (c2 : Ca b2)
    (eb : b1 = b2)
    (ec : transportf C (two_arg_paths_b (idpath a) eb) c1 = c2)
  : c1 = transportb Ca eb c2.
Proof.
  destruct eb; cbn.
  destruct ec; cbn.
  apply idpath.
Qed.

Definition another_lemma {A B : UU} (P: A → UU) (Q : B → UU)
    (f0: A → B) (f1: ∏ a : A, P a → Q(f0 a))
    {x x' : A} (h: x = x')
  : ∏ (p : P x), transportf Q (maponpaths f0 h) (f1 x p) = f1 x' (transportf P h p).
Proof.
  intro p.
  induction h.
  apply idpath.
Defined.

Definition fiber_disp_cat_axioms {C : category} (DD : disp_disp_cat C) (c : C)
  : disp_cat_axioms (base_disp_cat DD)[{c}] (fiber_disp_cat_data DD c).
Proof.
  destruct DD as [D E].
  repeat split; intros; simpl.
  - simpl in x, y, f, xx, yy, ff.
    use my_lemma.
    (* apply (pathscomp0 (id_left_disp ff)). *)
    unfold ";;"; simpl.
    apply transportf_transpose_left.
    apply (pathscomp0 (id_left_disp ff)).
    eapply pathscomp0.
    2: {
      apply pathsinv0.
      apply transport_f_f.
    }
    unfold transportb.
    apply maponpaths_2.
    apply homset_property.
  - simpl in x, y, f, xx, yy, ff.
    use my_lemma.
    unfold ";;"; simpl.
    apply transportf_transpose_left.
    apply (pathscomp0 (id_right_disp ff)).
    eapply pathscomp0.
    2: {
      apply pathsinv0.
      apply transport_f_f.
    }
    unfold transportb.
    apply maponpaths_2.
    apply homset_property.
  - simpl in x, y, z, w, f, g, h, xx, yy, zz, ww, ff, gg, hh.
    set (assocffgghh := assoc_disp ff gg hh).
    use my_lemma.
    (* apply (pathscomp0 (assoc_disp ff gg hh)). *)
    unfold ";;"; simpl.
    apply transportf_transpose_left.
    eapply pathscomp0.
    + Unshelve.
      2: {
        eapply (transportf).
        2: { exact (ff ;; (gg ;; hh)). }
        unfold "·"; simpl.
        eapply total2_paths_f. Unshelve.
        2: {
          simpl.
          apply maponpaths.
          apply id_right.
        }
        simpl.
        set (temp := another_lemma (mor_disp y w) (mor_disp x w) (compose (identity c)) (λ (e : C ⟦ c, c ⟧) (ee : y -->[ e] w), f ;; ee) (id_right (identity c))).
        apply (another_lemma _ _ (compose (identity c)) (λ e ee, f ;; ee) _).
      }
      simpl.

      admit.
    +
      admit.
  - apply homsets_disp.
Admitted.

End FiberDisplayedCategories.
