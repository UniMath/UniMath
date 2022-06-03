
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Local Open Scope cat.
Local Open Scope mor_disp.

(** ** Saturation: displayed univalent categories *)
Section Univalent_Categories.

  Definition is_univalent_disp {C} (D : disp_cat C)
    := ∏ x x' (e : x = x') (xx : D x) (xx' : D x'),
      isweq (λ ee, @idtoiso_disp _ _ _ _ e xx xx' ee).

  Definition isaprop_is_univalent_disp
             {C : category}
             (D : disp_cat C)
    : isaprop (is_univalent_disp D).
  Proof.
    unfold is_univalent_disp.
    do 5 (use impred ; intro).
    apply isapropisweq.
  Defined.

  Definition is_univalent_in_fibers {C} (D : disp_cat C) : UU
    := ∏ x (xx xx' : D x), isweq (fun e : xx = xx' => idtoiso_fiber_disp e).

  (* TODO: maybe rename further.  *)
  Lemma is_univalent_disp_from_fibers {C} {D : disp_cat C}
    : is_univalent_in_fibers D
      -> is_univalent_disp D.
  Proof.
    intros H x x' e. destruct e. apply H.
  Qed.

  Definition is_univalent_in_fibers_from_univalent_disp {C} (D : disp_cat C)
    : is_univalent_disp D -> is_univalent_in_fibers D.
  Proof.
    unfold is_univalent_disp , is_univalent_in_fibers.
    intros H x xx xx'.
    specialize (H x x (idpath _ ) xx xx').
    apply H.
  Defined.

  Lemma univalent_disp_cat_has_groupoid_obs {C} (D : disp_cat C)
        (is_u : is_univalent_disp D) : ∏ c, isofhlevel 3 (D c).
  Proof.
    intro c.
    change (isofhlevel 3 (D c)) with
      (∏ a b : D c, isofhlevel 2 (a = b)).
    intros xx xx'.
    set (XR := is_univalent_in_fibers_from_univalent_disp _ is_u).
    apply (isofhlevelweqb _ (make_weq _ (XR _ xx xx'))).
    apply isaset_z_iso_disp.
  Defined.

  Definition disp_univalent_category C
    := ∑ D : disp_cat C, is_univalent_disp D.

  Definition make_disp_univalent_category
             {C} {D : disp_cat C} (H : is_univalent_disp D)
    : disp_univalent_category C
    := (D,,H).

  Definition disp_cat_of_disp_univalent_cat {C} (D : disp_univalent_category C)
    : disp_cat C
    := pr1 D.
  Coercion disp_cat_of_disp_univalent_cat : disp_univalent_category >-> disp_cat.

  Definition disp_univalent_category_is_univalent_disp {C} (D : disp_univalent_category C)
    : is_univalent_disp D
    := pr2 D.
  Coercion disp_univalent_category_is_univalent_disp : disp_univalent_category >-> is_univalent_disp.

  Definition isotoid_disp
             {C} {D : disp_cat C} (D_cat : is_univalent_disp D)
             {c c' : C} (e : c = c') {d : D c} {d'} (i : z_iso_disp (idtoiso e) d d')
    : transportf _ e d = d'.
  Proof.
    exact (invmap (make_weq (idtoiso_disp e) (D_cat _ _ _ _ _)) i).
  Defined.

  Definition idtoiso_isotoid_disp
             {C} {D : disp_cat C} (D_cat : is_univalent_disp D)
             {c c' : C} (e : c = c') {d : D c} {d'} (i : z_iso_disp (idtoiso e) d d')
    : idtoiso_disp e (isotoid_disp D_cat e i) = i.
  Proof.
    use homotweqinvweq.
  Qed.

  Definition isotoid_idtoiso_disp
             {C} {D : disp_cat C} (D_cat : is_univalent_disp D)
             {c c' : C} (e : c = c') {d : D c} {d'} (ee : transportf _ e d = d')
    : isotoid_disp D_cat e (idtoiso_disp e ee) = ee.
  Proof.
    use homotinvweqweq.
  Qed.

End Univalent_Categories.
