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

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Foundations.All.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.


Definition transportD' {A : UU} (B : A -> UU) (C : (∑ a : A, B a) -> UU)
           {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C (x1 ,, y)) :
  C (x2 ,, (transportf _ p y)).
Proof.
  intros.
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



Definition disp_disp_cat (C : category) : UU
  := ∑ (D : disp_cat C), disp_cat (total_category D).

Definition base_disp_cat {C : category} (E : disp_disp_cat C) : disp_cat C
  := pr1 E.

Definition top_disp_cat {C : category} (E : disp_disp_cat C)
  : disp_cat (total_category (base_disp_cat E))
  := pr2 E.

Definition composite_disp_cat {C : category} (DD : disp_disp_cat C) : disp_cat C.
Proof.
  destruct DD as [D E].
  use tpair.
  - unfold disp_cat_data.
    use tpair.
    + unfold disp_cat_ob_mor.
      use tpair.
      * intro x.
        exact (∑ (xx : D x), E (x ,, xx)).
      * simpl.
        intros x y [xx xxx] [yy yyy] f.
        exact (∑ (ff : xx -->[f] yy), xxx -->[(f ,, ff)] yyy).
    + simpl.
      split.
      * simpl.
        intros x [xx xxx].
        exists (id_disp xx).
        exact (id_disp xxx).
      * simpl.
        intros x y z f g [xx xxx] [yy yyy] [zz zzz] [ff fff] [gg ggg].
        exists (comp_disp ff gg).
        exact (comp_disp fff ggg).
  - simpl.
    split.
    + simpl.
      intros x y f [xx xxx] [yy yyy] [ff fff].
      (* eapply transportf_total2'. *)
      use total2_paths_b.
      * simpl.
        eapply pathscomp0.
        -- apply id_left_disp.
        -- apply pathsinv0.
           apply transportf_total2'_pr1.
      * simpl.
        eapply pathscomp0.
        -- exact (id_left_disp fff).
        --
           admit.
    + simpl.
      split.
      * intros x y f [xx xxx] [yy yyy] [ff fff].
        set (temp := @id_right_disp _ E _ _ _ _ _ fff).
        admit.
      * split.
        -- intros x y z w f g h [xx xxx] [yy yyy] [zz zzz] [ww www] [ff fff] [gg ggg] [hh hhh].
           set (temp := @assoc_disp _ E _ _ _ _ _ _ _ _ _ _ _ fff ggg hhh).
           admit.
        --
           admit.
Admitted.

Definition fiber_disp_cat {C : category} (DD: disp_disp_cat C) (c : C)
  : disp_cat (fiber_category (base_disp_cat DD) c).
Proof.
  destruct DD as [D E]. simpl.

Admitted.
