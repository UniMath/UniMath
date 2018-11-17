(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat. Import DispBicat.Notations.

Open Scope cat.
Open Scope mor_disp_scope.

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

    Variable (D : disp_prebicat C) (h : local_iso_cleaving D) (c : C).

    Definition discrete_fiber_ob_mor : precategory_ob_mor.
    Proof.
      use tpair.
      - exact (D c).
      - cbn. exact (λ (d : D c) (d' : D c), d -->[identity _] d').
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

    Definition discrete_fiber_1_id_comp_cells : prebicat_1_id_comp_cells.
    Proof.
      exists discrete_fiber_precategory_data.
      red. cbn. intros d d' f f'.
      exact (f ==>[id2 (identity c)] f').
    Defined.

    Definition discrete_fiber_data : prebicat_data.
    Proof.
      exists discrete_fiber_1_id_comp_cells.
      repeat split; cbn.
      - intros. exact (disp_id2 _).
      - intros d d' ff.
        set (PP := disp_local_iso_cleaving_invertible_2cell h (id_disp d;; ff) idempunitor).
        set (RR := PP •• disp_lunitor ff).
        assert (Heq : idempunitor • lunitor (identity c) = id2 (identity c)).
        { unfold idempunitor. simpl. apply linvunitor_lunitor. }
        exact (transportf (λ x, _ ==>[x] _) Heq RR).
      - intros d d' ff.
        assert (Heq : idempunitor • runitor (identity c) = id2 (identity c)).
        { unfold idempunitor. cbn.
          etrans. apply maponpaths. apply pathsinv0.
          apply lunitor_runitor_identity. apply linvunitor_lunitor. }
        set (PP := disp_local_iso_cleaving_invertible_2cell h (ff;; id_disp d') idempunitor).
        exact (transportf (λ x, _ ==>[x] _) Heq (PP •• disp_runitor ff)).
      - intros d d' ff.
        set (PP := disp_inv_cell
                     (disp_local_iso_cleaving_invertible_2cell h (id_disp d;; ff) idempunitor)).
        assert (Heq : linvunitor (identity c) • inv_cell idempunitor = id2 (identity c)).
        { unfold idempunitor. cbn. apply linvunitor_lunitor. }
        exact (transportf (λ x, _ ==>[x] _) Heq (disp_linvunitor ff •• PP)).
      - cbn. intros d d' ff.
        set (PP := disp_inv_cell
                     (disp_local_iso_cleaving_invertible_2cell h (ff;; id_disp d') idempunitor)).
        assert (Heq : rinvunitor (identity c) • inv_cell idempunitor = id2 (identity c)).
        { unfold idempunitor. cbn.
          etrans; [ apply maponpaths, lunitor_runitor_identity | ].
          apply rinvunitor_runitor.
        }
        exact (transportf (λ x, _ ==>[x] _) Heq (disp_rinvunitor ff •• PP)).
      - intros d0 d1 d2 d3 ff gg hh.
        set (Hfg := disp_local_iso_cleaving_invertible_2cell h (ff;; gg) idempunitor).
        set (Hgh := disp_local_iso_cleaving_invertible_2cell h (gg;; hh) idempunitor).
        set (Hfg_h := disp_local_iso_cleaving_invertible_2cell
                        h (local_iso_cleaving_1cell h (ff;; gg) idempunitor;; hh) idempunitor).
        set (Hf_gh := disp_local_iso_cleaving_invertible_2cell
                        h (ff;; local_iso_cleaving_1cell h (gg;; hh) idempunitor) idempunitor).
        set (h1 := Hfg_h •• (Hfg ▹▹ hh)).
        set (h2 := Hf_gh •• (ff ◃◃ Hgh)).
        admit.
    Abort.

    Definition discrete_fiber : prebicat.
    Proof.
      use tpair.
    Abort.

  End Discrete_Fiber.

End LocalIsoFibration.
