Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.CategoryTop.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.Test.Opens.

Local Open Scope subtype.
Local Open Scope cat.

Definition presheafed_space
  (D : category)
  : UU
  := ∑ (X : TopologicalSpace), topological_space_category X ⟶ D.

Coercion presheafed_space_to_space
  {D : category}
  (X : presheafed_space D)
  : TopologicalSpace
  := pr1 X.

Definition presheafed_space_presheaf
  {D : category}
  (X : presheafed_space D)
  : topological_space_category X ⟶ D
  := pr2 X.


Definition presheafed_space_morphism
  {D : category}
  (X Y : presheafed_space D)
  : UU
  := ∑ (f : continuous_function X Y),
    continuous_to_functor f ∙ presheafed_space_presheaf X ⟹ presheafed_space_presheaf Y.

Coercion presheafed_space_morphism_to_continuous
  {D : category}
  {X Y : presheafed_space D}
  (f : presheafed_space_morphism X Y)
  : continuous_function X Y
  := pr1 f.

Definition presheafed_space_morphism_to_nat_trans
  {D : category}
  {X Y : presheafed_space D}
  (f : presheafed_space_morphism X Y)
  : continuous_to_functor f ∙ presheafed_space_presheaf X ⟹ presheafed_space_presheaf Y
  := pr2 f.


Definition presheafed_identity
  {D : category}
  (X : presheafed_space D)
  : presheafed_space_morphism X X.
Proof.
  exists (continuous_identity X).
  refine (nat_trans_comp _ _ _ _ (lunitor (C := bicat_of_cats) _)).
  refine (post_whisker _ _).
  exact (z_iso_mor (continuous_to_functor_identity _)).
Defined.

Definition presheafed_comp
  {D : category}
  {X Y Z : presheafed_space D}
  (f : presheafed_space_morphism X Y)
  (g : presheafed_space_morphism Y Z)
  : presheafed_space_morphism X Z.
Proof.
  exists (((f : continuous_function _ _) : top_cat⟦_, _⟧) · (g : continuous_function _ _)).
  refine (nat_trans_comp _ _ _ _ (presheafed_space_morphism_to_nat_trans g)).
  refine (nat_trans_comp _ _ _ _ (pre_whisker _ (presheafed_space_morphism_to_nat_trans f))).
  refine (nat_trans_comp _ _ _ _ (rassociator (C := bicat_of_cats) _ _ _)).
  refine (post_whisker _ (presheafed_space_presheaf X)).
  exact (z_iso_mor (continuous_to_functor_comp _ _)).
Defined.

Opaque continuous_to_functor_identity.
Opaque continuous_to_functor_comp.

Definition presheafed_space_cat_data
  (D : category)
  : precategory_data
  := make_precategory_data
    (make_precategory_ob_mor
      (presheafed_space D)
      presheafed_space_morphism)
    presheafed_identity
    (λ _ _ _, presheafed_comp).


Lemma presheafed_space_morphism_eq
  {D : category}
  {X Y : presheafed_space D}
  (f f' : presheafed_space_morphism X Y)
  (H1 : (f : continuous_function _ _) = f')
  (H2 : ∏ x, presheafed_space_morphism_to_nat_trans f x = # (presheafed_space_presheaf X) (idtoiso (maponpaths (λ f, continuous_to_functor f x) H1)) · presheafed_space_morphism_to_nat_trans f' x)
  : f = f'.
Proof.
  induction f as [f1 f2], f' as [f1' f2'].
  simpl in H1.
  induction H1.
  apply maponpaths.
  apply nat_trans_eq_alt.
  intro x.
  refine (H2 x @ _).
  refine (_ @ id_left _).
  apply (maponpaths (λ x, x · _) (functor_id (presheafed_space_presheaf X) _)).
Qed.

Lemma presheafed_space_is_cat
  (D : category)
  : is_precategory (presheafed_space_cat_data D).
Proof.
  use make_is_precategory_one_assoc.
  - intros X Y f.
    use presheafed_space_morphism_eq.
    + apply (id_left (C := top_cat)).
    + intro x.
      apply (maponpaths (λ x, x · _)).
      refine (maponpaths (λ x, x · _) (id_right _) @ _).
      refine (maponpaths (λ x, _ · x) (id_right _) @ _).
      refine (!functor_comp (presheafed_space_presheaf X) _ _ @ _).
      apply maponpaths.
      apply isaprop_subtype_containedIn.
  - intros X Y f.
    use presheafed_space_morphism_eq.
    + apply (id_right (C := top_cat)).
    + intro x.
      refine (maponpaths (λ x, x · _ · _) (id_right _) @ _).
      refine (maponpaths (λ x, _ · x) (id_right _) @ _).
      refine (assoc' _ _ _ @ _).
      refine (!maponpaths _ (nat_trans_ax (presheafed_space_morphism_to_nat_trans f) _ _ _) @ _).
      refine (assoc _ _ _ @ _).
      apply (maponpaths (λ x, x · _)).
      refine (!functor_comp (presheafed_space_presheaf X) _ _ @ _).
      apply maponpaths.
      apply isaprop_subtype_containedIn.
  - intros W X Y Z f g h.
    use presheafed_space_morphism_eq.
    + apply (assoc (C := top_cat)).
    + intro x.
      refine (maponpaths (λ x, x · _ · _) (id_right _) @ _).
      refine (maponpaths (λ x, _ · (x · _ · _)) (id_right _) @ _).
      refine (_ @ !maponpaths (λ x, _ · (x · _ · _)) (id_right _)).
      refine (_ @ !maponpaths (λ x, _ · (_ · (x · _ · _) · _)) (id_right _)).
      do 2 refine (assoc _ _ _ @ !_).
      apply (maponpaths (λ x, x · _)).
      refine (assoc _ _ _ @ _).
      do 2 refine (_ @ assoc' _ _ _).
      apply (maponpaths (λ x, x · _)).
      refine (assoc' _ _ _ @ _).
      refine (!maponpaths _ (nat_trans_ax (presheafed_space_morphism_to_nat_trans f) _ _ _) @ _).
      refine (assoc _ _ _ @ _).
      refine (_ @ assoc' _ _ _).
      apply (maponpaths (λ x, x · _)).
      refine (!functor_comp (presheafed_space_presheaf W) _ _ @ _).
      refine (_ @ maponpaths (λ x, x · _) (functor_comp (presheafed_space_presheaf W) _ _)).
      refine (_ @ functor_comp (presheafed_space_presheaf W) _ _).
      apply maponpaths.
      apply isaprop_subtype_containedIn.
Qed.

Lemma presheafed_space_cat_homsets
  (D : category)
  : has_homsets (presheafed_space_cat_data D).
Proof.
  intros a b.
  apply isaset_total2.
  - apply (homset_property top_cat).
  - intro f.
    apply isaset_nat_trans.
    apply homset_property.
Qed.

Definition presheafed_space_cat
  (D : category)
  : category
  := make_category
    (make_precategory
      (presheafed_space_cat_data D)
      (presheafed_space_is_cat D))
    (presheafed_space_cat_homsets D).
