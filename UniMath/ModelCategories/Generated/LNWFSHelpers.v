
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pushouts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.EqDiag.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monads.ComonadCoalgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.

Require Import UniMath.ModelCategories.NWFS.
Require Import UniMath.ModelCategories.Generated.MonoidalHelpers.
Require Import UniMath.ModelCategories.Helpers.
Require Import UniMath.ModelCategories.Generated.MonoidalHelpers.
Require Import UniMath.ModelCategories.Generated.FFMonoidalStructure.


Local Open Scope cat.

Section Helpers.

Context {C : category}.

Lemma lnwfs_Σ_top_map_id {F : Ff C} (L : lnwfs_over F) (f : arrow C) :
    arrow_mor00 (pr1 L f) = identity _.
Proof.
  set (law1 := Comonad_law1 (T:=lnwfs_L_monad L) f).
  set (top := arrow_mor00_eq law1).
  apply pathsinv0.
  etrans.
  exact (pathsinv0 top).
  apply id_right.
Qed.

Lemma lnwfs_Σ_bottom_map_inv {F : Ff C} (L : lnwfs_over F) (f : arrow C) :
    arrow_mor11 (pr1 L f) · arrow_mor (fact_R F (fact_L F f)) = identity _.
Proof.
  set (law1 := Comonad_law1 (T:=lnwfs_L_monad L) f).
  set (bottom := arrow_mor11_eq law1).
  exact bottom.
Qed.

(* some useful proofs on the comonoidal structure that corresponds
   with LNWFS on Ff C *)
   Lemma LNWFS_comon_structure_whiskerequals
   (L L' L'' : total_category (LNWFS C))
   (α : fact_mor (pr1 L) (pr1 L'))
   (α' : fact_mor (pr1 L') (pr1 L''))
   (f : arrow C) :
 arrow_mor11 (#(lnwfs_L_monad (pr2 L')) (lnwfs_mor (pr2 L) (pr2 L') α f)) · arrow_mor11 (lnwfs_mor (pr2 L') (pr2 L'') α' ((lnwfs_L_monad (pr2 L')) f))
 = arrow_mor11 (lnwfs_mor (pr2 L') (pr2 L'') α' (lnwfs_L_monad (pr2 L) f)) · arrow_mor11 (#(lnwfs_L_monad (pr2 L'')) (lnwfs_mor (pr2 L) (pr2 L') α f)).
Proof.
 set (α'nat := nat_trans_ax α' _ _ (lnwfs_mor (pr2 L) (pr2 L') α f)).
 set (α'nat11 := base_paths _ _ (fiber_paths α'nat)).

 apply pathsinv0.
 etrans. exact (pathsinv0 α'nat11).
 etrans. apply pr1_transportf_const.
 reflexivity.
Qed.

(* A more general lemma of the above is
  (above is just below with Λ = L' and Λ' = L'' ) *)
Lemma LNWFS_comon_structure_whiskercommutes
   (L L' Λ Λ' : total_category (LNWFS C))
   (α : fact_mor (pr1 L) (pr1 L'))
   (β : fact_mor (pr1 Λ) (pr1 Λ'))
   (f : arrow C) :
  arrow_mor11 (lnwfs_mor (pr2 Λ) (pr2 Λ') β (lnwfs_L_monad (pr2 L) f)) · arrow_mor11 (#(lnwfs_L_monad (pr2 Λ')) (lnwfs_mor (pr2 L) (pr2 L') α f))
  = arrow_mor11 (#(lnwfs_L_monad (pr2 Λ)) (lnwfs_mor (pr2 L) (pr2 L') α f)) · arrow_mor11 (lnwfs_mor (pr2 Λ) (pr2 Λ') β ((lnwfs_L_monad (pr2 L')) f)).
Proof.
 set (βnat := nat_trans_ax β _ _ (lnwfs_mor (pr2 L) (pr2 L') α f)).
 set (βnat11 := base_paths _ _ (fiber_paths βnat)).

 etrans. exact (pathsinv0 βnat11).
 etrans. apply pr1_transportf_const.
 reflexivity.
Qed.

Lemma Ff_mor_eq_LNWFS_mor
    {L L' : total_category (LNWFS C)}
    (τ : pr1 L --> pr1 L')
    (τL : L --> L') :
  pr1 τL = τ -> pr2 L -->[τ] pr2 L'.
Proof.
  intro H.
  rewrite <- H.
  exact (pr2 τL).
Qed.

Lemma LNWFS_inv_in_precat_if_Ff_inv_in_precat
    {L L' : total_category (LNWFS C)}
    (τ : L --> L')
    (τ' : L' --> L)
    (HFf : is_inverse_in_precat (pr1 τ) (pr1 τ')) :
  is_inverse_in_precat τ τ'.
Proof.
  split; (apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|]).
  - exact (pr1 HFf).
  - exact (pr2 HFf).
Qed.

Lemma Ff_iso_inv_LNWFS_mor
    (L L' : total_category (LNWFS C))
    (iso : z_iso (pr1 L) (pr1 L'))
    (Hiso : (pr2 L) -->[iso] (pr2 L')) :
  pr2 L' -->[z_iso_inv iso] pr2 L.
Proof.
  (* base mor component at f is z_iso (obvious since base_mor is an iso) *)
  transparent assert (Hiso11 : (∏ f, is_z_isomorphism (three_mor11 (section_nat_trans (z_iso_mor iso) f)))).
  {
    intro f.
    exists (three_mor11 (section_nat_trans (z_iso_mor (z_iso_inv iso)) f)).
    split.
    - exact (eq_section_nat_trans_comp_component11 (pr122 iso) f).
    - exact (eq_section_nat_trans_comp_component11 (pr222 iso) f).
  }

  split; intro f.
  - use arrow_mor_eq.
    * etrans. apply id_left.
      etrans. exact (lnwfs_Σ_top_map_id (pr2 L) f).
      apply pathsinv0.
      etrans. apply cancel_postcomposition.
              apply cancel_postcomposition.
              exact (lnwfs_Σ_top_map_id (pr2 L') f).
      etrans. apply cancel_postcomposition.
              apply id_left.
      apply id_left.
    * set (inv := Hiso11 f).
      apply (pre_comp_with_z_iso_is_inj inv).
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (pr12 inv).
      etrans. apply id_left.
      etrans. exact (pathsinv0 (id_right _)).
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              etrans. apply assoc.
              apply cancel_postcomposition.
              exact (arrow_mor11_eq (pr1 Hiso f)).
      etrans. apply assoc'.
      etrans. apply assoc'.
      etrans. apply assoc'.
      apply cancel_precomposition.

      etrans. apply assoc.
      etrans. apply assoc.
      etrans. apply assoc4.
      etrans. apply cancel_postcomposition, cancel_precomposition.
              apply (LNWFS_comon_structure_whiskercommutes).
      etrans. apply cancel_postcomposition, assoc.
      etrans. apply assoc'.
      etrans. apply cancel_postcomposition.
      {
        etrans. apply (pr1_section_disp_on_morphisms_comp (pr1 L)).
        etrans. use (section_disp_on_eq_morphisms (pr1 L) (γ' := identity _)).
        - apply id_left.
        - exact (pr12 inv).
        - apply maponpaths.
          apply (section_disp_id (pr1 L)).
      }
      etrans. apply id_left.
      exact (eq_section_nat_trans_comp_component11 (pr122 iso) (fact_L (pr1 L) f)).
  - use arrow_mor_eq; [apply id_left|].
    set (inv := Hiso11 f).
    apply (pre_comp_with_z_iso_is_inj inv).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            exact (pr12 inv).
    etrans. apply id_left.
    apply pathsinv0.
    exact (arrow_mor11_eq (pr2 Hiso f)).
Qed.

End Helpers.
