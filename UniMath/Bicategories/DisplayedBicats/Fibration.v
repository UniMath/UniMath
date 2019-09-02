(* ******************************************************************************* *)
(** * Fiber category of a displayed bicategory whose displayed 2-cells form a
      proposition. In addition, we ask the displayed bicategory to be locally
      univalent and to be equipped with a local iso-cleaving.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section LocalIsoFibration.
  Context {C : bicat}.

  Definition local_iso_cleaving (D : disp_prebicat C)
    : UU
    := ∏ (c c' : C) (f f' : C⟦c,c'⟧)
         (d : D c) (d' : D c')
         (ff' : d -->[f'] d')
         (α : invertible_2cell f f'),
       ∑ ff : d -->[f] d', disp_invertible_2cell α ff ff'.

  Section Projections.
    Context {D : disp_prebicat C} (lic : local_iso_cleaving D)
            {c c' : C} {f f' : C⟦c,c'⟧}
            {d : D c} {d' : D c'}
            (ff' : d -->[f'] d')
            (α : invertible_2cell f f').

    Definition local_iso_cleaving_1cell
      : d -->[f] d'
      := pr1 (lic c c' f f' d d' ff' α).

    Definition disp_local_iso_cleaving_invertible_2cell
      : disp_invertible_2cell α local_iso_cleaving_1cell ff'
      := pr2 (lic c c' f f' d d' ff' α).
  End Projections.

  Section Discrete_Fiber.
    Variable (D : disp_prebicat C)
             (h : local_iso_cleaving D)
             (c : C).

    Definition discrete_fiber_ob_mor : precategory_ob_mor.
    Proof.
      use tpair.
      - exact (D c).
      - cbn. exact (λ (d : D c) (d' : D c), d -->[identity c] d').
    Defined.

    Definition idempunitor : invertible_2cell (identity c) (identity c · identity c).
    Proof.
      exists (linvunitor (identity c)).
      apply is_invertible_2cell_linvunitor.
    Defined.

    Definition discrete_fiber_precategory_data : precategory_data.
    Proof.
      exists discrete_fiber_ob_mor.
      split; cbn.
      - intro d. exact (id_disp d).
      - intros x y z ff gg.
        use (local_iso_cleaving_1cell h).
        + exact (identity c · identity c).
        + exact (ff ;; gg).
        + exact idempunitor.
    Defined.
  End Discrete_Fiber.
End LocalIsoFibration.

Definition univalent_2_1_to_local_iso_cleaving_help
           {C : bicat}
           {D : disp_prebicat C}
           {c c' : C}
           {f f' : C⟦c,c'⟧}
           {d : D c} {d' : D c'}
           (ff' : d -->[f'] d')
           (α : f  = f')
  : ∑ ff : d -->[f] d', disp_invertible_2cell (idtoiso_2_1 _ _ α) ff ff'.
Proof.
  induction α.
  refine (ff' ,, _).
  apply disp_id2_invertible_2cell.
Defined.

Definition univalent_2_1_to_local_iso_cleaving
           {C : bicat}
           (HC : is_univalent_2_1 C)
           (D : disp_prebicat C)
  : local_iso_cleaving D.
Proof.
  intros x y f g xx yy ff gg.
  pose (univalent_2_1_to_local_iso_cleaving_help ff (isotoid_2_1 HC gg)) as t.
  rewrite idtoiso_2_1_isotoid_2_1 in t.
  exact t.
Defined.
