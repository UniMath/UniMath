(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    April 2018

 Displayed version of the proof that,
 left and right unitor coincide on the identity.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.OpMorBicat.
Require Import UniMath.CategoryTheory.Bicategories.OpCellBicat.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Import UniMath.CategoryTheory.Bicategories.DispBicat.Notations.

Open Scope cat.
Open Scope mor_disp_scope.

Section Handy.

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* TODO: move where more appropriate.                                        *)
(* ------------------------------------------------------------------------- *)

Context {C : bicat} {D : disp_prebicat C}.

Definition disp_cell_f
           {a b : C} {f g : C⟦a,b⟧}
           {α β : f ==> g}
           (e : α = β)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : aa -->[g] bb}
           (αα : ff ==>[α] gg)
  : ff ==>[β] gg
  := transportf (λ x : f ==> g, ff ==>[x] gg) e αα.

Definition disp_cell_b
           {a b : C} {f g : C⟦a,b⟧}
           {α β : f ==> g}
           (e : α = β)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : aa -->[g] bb}
           (ββ : ff ==>[β] gg)
  : ff ==>[α] gg
  := transportb (λ x : f ==> g, ff ==>[x] gg) e ββ.

Lemma disp_cell_f_pathsinv0
      {a b : C} {f g : C⟦a,b⟧}
      {α β : f ==> g}
      (e : α = β)
      {aa : D a} {bb : D b}
      {ff : aa -->[f] bb}
      {gg : aa -->[g] bb}
      {αα : ff ==>[α] gg}
      {ββ : ff ==>[β] gg}
      (ee : disp_cell_f (!e) ββ = αα)
  : disp_cell_f e αα = ββ.
Proof.
  unfold disp_cell_f.
  apply (transportf_pathsinv0 (λ x : f ==> g, ff ==>[x] gg)).
  exact ee.
Defined.

Lemma disp_cell_b_to_f
      {a b : C} {f g : C⟦a,b⟧}
      {α β : f ==> g}
      {e : α = β}
      {aa : D a} {bb : D b}
      {ff : aa -->[f] bb}
      {gg : aa -->[g] bb}
      {αα : ff ==>[α] gg}
      {ββ : ff ==>[β] gg}
      (ee : αα = disp_cell_b e ββ)
  : disp_cell_f e αα = ββ.
Proof.
  apply disp_cell_f_pathsinv0.
  apply pathsinv0.
  exact ee.
Defined.

Lemma disp_cell_f_to_b
      {a b : C} {f g : C⟦a,b⟧}
      {α β : f ==> g}
      {e : α = β}
      {aa : D a} {bb : D b}
      {ff : aa -->[f] bb}
      {gg : aa -->[g] bb}
      {αα : ff ==>[α] gg}
      {ββ : ff ==>[β] gg}
      (ee : disp_cell_f e αα = ββ)
  :  αα = disp_cell_b e ββ.
Proof.
  apply pathsinv0.
  apply (transportf_pathsinv0 (λ x : f ==> g, ff ==>[ x] gg)).
  etrans.
  { apply maponpaths_2.
    apply pathsinv0inv0. }
  exact ee.
Defined.

End Handy.

Theorem disp_lunitor_runitor_identity {C : bicat} {D : disp_bicat C} (a : C) (aa : D a)
  : disp_lunitor (id_disp aa) =
    transportb (λ x, _ ==>[x] _) (lunitor_runitor_identity a) (disp_runitor (id_disp aa)).
Proof.
  set (TT := fiber_paths (lunitor_runitor_identity (C := total_bicat D) (a ,, aa))).
  cbn in TT.
  apply disp_cell_f_to_b.
  etrans.
  2: apply TT.
  unfold disp_cell_f.
  apply maponpaths_2.
  apply cellset_property.
Qed.
