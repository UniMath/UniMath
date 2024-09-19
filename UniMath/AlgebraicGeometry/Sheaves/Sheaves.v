Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.CategoryTheory.Categories.Commring.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Algebra.Groups.

Require Import UniMath.AlgebraicGeometry.CategoryOfOpens.
Require Import UniMath.AlgebraicGeometry.Sheaves.Presheaves.

Local Open Scope cat.
Local Open Scope subtype.
Local Open Scope open_scope.

Section SheafProperty.

  Context {C : category}.
  Context {X : TopologicalSpace}.
  Context (F : presheaf C X).
  Context (HC : ∏ I, Products I C).

  Definition is_sheaf
    : UU.
  Proof.
    refine (∏ (A : hsubtype (Open (T := X))), _).
    use (isEqualizer _ _ _ _).
    - exact C.
    - exact (F (⋃ A)).
    - exact (ProductObject _ _ (HC A (λ U, F (pr1carrier _ U)))).
    - exact (ProductObject _ _ (HC (A × A) (λ UV, F (pr11 UV ∩ pr12 UV)))).
    - apply ProductArrow.
      intro UV.
      refine (ProductPr _ _ _ (pr1 UV) · _).
      exact (#F (intersection_contained1 _ _)).
    - apply ProductArrow.
      intro UV.
      refine (ProductPr _ _ _ (pr2 UV) · _).
      exact (#F (intersection_contained2 _ _)).
    - apply ProductArrow.
      intro U.
      exact (#F (contained_in_union_open _)).
    - abstract (
        apply ProductArrow_eq;
        intro UV;
        do 2 refine (assoc' _ _ _ @ !_);
        do 2 refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ !_);
        do 2 refine (assoc _ _ _ @ !_);
        refine (maponpaths (λ x, x · _) (ProductPrCommutes _ _ _ _ _ _ (pr1 UV)) @ !_);
        refine (maponpaths (λ x, x · _) (ProductPrCommutes _ _ _ _ _ _ (pr2 UV)) @ !_);
        do 2 refine (!_ @ functor_comp _ _ _);
        apply maponpaths;
        apply propproperty
      ).
  Defined.

  Lemma isaprop_is_sheaf
    : isaprop is_sheaf.
  Proof.
    apply impred_isaprop.
    intro.
    apply isaprop_isEqualizer.
  Qed.

End SheafProperty.

Section SheafOfRings.

  Context {X : TopologicalSpace}.
  Context (F : presheaf commring_category X).

  Let F0 : Open → commring := F.

  Definition restriction {U V : Open} (H : U ⊆ V) : ringfun (F0 V) (F0 U) := # F H.

  Definition restrict (A : hsubtype Open) (f : F0 (⋃ A)) (U : A) : F0 (pr1 U) :=
    restriction (contained_in_union_open U) f.

  Definition has_locality
    : UU
    := ∏ (A : hsubtype Open) (f g : F0 (⋃ A)),
      (∏ (U : A), restrict A f U = restrict A g U) → f = g.

  Definition has_locality_0
    : UU
    := ∏ (A : hsubtype Open) (f : F0 (⋃ A)),
      (∏ (U : A), restrict A f U = 0%ring) → f = 0%ring.

  Lemma has_locality_0_to_has_locality
    (H : has_locality_0)
    : has_locality.
  Proof.
    intros A f g Hg.
    apply (grtopathsxy (ringaddabgr (F0 (⋃ A)))).
    apply H.
    intro U.
    refine (monoidfunmul (rigaddfun (restriction _)) _ _ @ _).
    refine (maponpaths _ (grinvandmonoidfun (ringaddabgr _) (ringaddabgr _) (pr2 (rigaddfun (restriction _))) g) @ _).
    apply (grfrompathsxy (ringaddabgr (F0 _))).
    exact (Hg U).
  Qed.

  Definition agree_on_intersections {A : hsubtype Open}
                                    (g : ∏ U : A, F0 (pr1 U)) : UU :=
    ∏ U V : A, restriction (intersection_contained1 _ _) (g U) =
               restriction (intersection_contained2 _ _) (g V).

  Definition has_gluing : UU
    := ∏ (A : hsubtype Open)
      (g : ∏ U : A, F0 (pr1 U)),
      agree_on_intersections g → ∑ f, ∏ (U : A), restrict A f U = g U.

  Lemma isaprop_gluing
    (H : has_locality)
    (A : hsubtype Open)
    (g : ∏ U : A, F0 (pr1 U))
    (Hg : agree_on_intersections g)
    : isaprop (∑ f, ∏ (U : A), restrict A f U = g U).
  Proof.
      intros f f'.
      use make_iscontr.
      + use subtypePath.
        * intro h.
          apply impred_isaprop.
          intro x.
          apply setproperty.
        * apply (H A (pr1 f) (pr1 f')).
          intro U.
          exact (pr2 f U @ !pr2 f' U).
      + intro t.
        refine (pr1 (isaset_carrier_subset _ (λ _, make_hProp _ _) f f' t _)).
        apply impred_isaprop.
        intro.
        apply setproperty.
  Qed.

  Definition is_sheaf' : UU
    := has_locality
      × has_gluing.

  Lemma isaprop_is_sheaf'
    : isaprop is_sheaf'.
  Proof.
    use (isaprop_total2 (make_hProp _ _) (λ H, make_hProp _ _)).
    - do 4 (apply impred_isaprop; intro).
      apply setproperty.
    - apply impred_isaprop.
      intro A.
      apply impred_isaprop.
      intro g.
      apply impred_isaprop.
      apply isaprop_gluing.
      exact H.
  Qed.

  Lemma is_sheaf_weq_is_sheaf'
    : is_sheaf F Products_commring_category ≃ is_sheaf'.
  Proof.
    refine (weqiff _ (isaprop_is_sheaf _ _) isaprop_is_sheaf').
    split.
  Abort.
    (* - intro H.
      split.
      + intros A f g Hfg.
        pose (equalizer_iso := z_iso_from_Equalizer_to_Equalizer (make_Equalizer _ _ _ _ (H A)) (Equalizers_commring_category _ _ _ _)).
        pose (equalizer_to := z_iso_mor equalizer_iso : ringfun _ _).
        pose (equalizer_from := inv_from_z_iso equalizer_iso : ringfun _ _).
        pose (equalizer_to f).
        pose (equalizer_to g).
        epose (isEqualizer'_weq_isEqualizer _ _ _ _ _ (H A)).
        unfold isEqualizer' in i.
        cbn in i.
        unfold postcomp_with_equalizer_mor in i.
  Qed. *)

End SheafProperty.
