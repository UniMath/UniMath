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
Require Import UniMath.CategoryTheory.Bicategories.Bicat.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.

Open Scope cat.
Open Scope mor_disp_scope.

Section LocalIsoFibration.

  Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
  Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).
  Notation "rr •• ss" := (vcomp2_disp rr ss) (at level 60).

  Context {C : prebicat}.

  Definition local_iso_cleaving (D : disp_prebicat C)
    : UU
    := ∏ (c c' : C) (f f' : C⟦c,c'⟧)
         (d : D c) (d' : D c')
         (ff' : d -->[f'] d')
         (α : equivalence f f'),
       ∑ ff : d -->[f] d', disp_equivalence ff ff' α.

  Section Projections.

    Context {D : disp_prebicat C} (lic : local_iso_cleaving D)
            {c c' : C} {f f' : C⟦c,c'⟧}
            {d : D c} {d' : D c'}
            (ff' : d -->[f'] d')
            (α : equivalence f f').

    Definition local_iso_cleaving_1cell
      : d -->[f] d'
      := pr1 (lic c c' f f' d d' ff' α).

    Definition local_iso_cleaving_disp_equivalence
      : disp_equivalence local_iso_cleaving_1cell ff' α
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

    Definition idempunitor : equivalence (identity c) (identity c · identity c).
    Proof.
      exists (linvunitor (identity c)).
      apply is_equivalence_linvunitor.
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

    (*
    Definition discrete_fiber_data : prebicat_data.
    Proof.
      exists discrete_fiber_1_id_comp_cells.
      repeat split; cbn.
      - intros. exact (id2_disp _).
      - intros d d' ff.
        set (PP := local_iso_cleaving_disp_equivalence h (id_disp d;; ff) idempunitor).
        set (RR := PP •• lunitor_disp ff).
        assert (Heq : idempunitor • lunitor (identity c) = id2 (identity c)).
        { unfold idempunitor. simpl. apply linvunitor_lunitor. }
        exact (transportf (λ x, _ ==>[x] _) Heq RR).
      - intros d d' ff.
        set (PP := local_iso_cleaving_disp_equivalence h (ff;; id_disp d') idempunitor).
        set (RR := PP •• runitor_disp ff).
        assert (Heq : idempunitor • runitor (identity c) = id2 (identity c)).
        { admit. }
        exact (transportf (λ x, _ ==>[x] _) Heq RR).
      - intros d d' ff.
        set (PP := local_iso_cleaving_disp_equivalence h (id_disp d;; ff) idempunitor).
        set (RR := lunitor_disp ff •• PP).


    Definition discrete_fiber : prebicat.
    Proof.
      use tpair.
     *)

    End Discrete_Fiber.

End LocalIsoFibration.
