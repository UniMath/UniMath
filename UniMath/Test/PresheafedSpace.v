Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.Topology.Topology.

Require Import UniMath.Test.Opens.

Local Open Scope subtype.
Local Open Scope cat.

(** Category *)

Definition presheafed_space_disp_cat_data
  (D : category)
  : disp_cat_data top_cat.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + intro X.
      exact ((topological_space_category X)^op ⟶ D).
    + intros X Y Xdata Ydata f.
      exact (functor_opp (continuous_to_functor f) ∙ Xdata ⟹ Ydata).
  - use tpair.
    + intros X Xdata.
      refine (nat_trans_comp _ _ _ _ (lunitor (C := bicat_of_cats) Xdata)).
      refine (post_whisker _ _).
      refine (nat_trans_comp _ _ _ (op_nt (inv_from_z_iso (continuous_to_functor_identity _))) _).
      apply (inv_from_z_iso (C := [_^op, _^op])).
      apply (z_iso_from_nat_z_iso (homset_property _)).
      exact (op_triangle_nat_z_iso _).
    + intros X Y Z f g Xdata Ydata Zdata fdata gdata.
      refine (nat_trans_comp _ _ _ _ gdata).
      refine (nat_trans_comp _ _ _ _ (pre_whisker _ fdata)).
      refine (nat_trans_comp _ _ _ _ (rassociator (C := bicat_of_cats) (a := (topological_space_category Z)^op) (b := (topological_space_category Y)^op) _ _ _)
      ).
      refine (post_whisker _ Xdata).
      refine (nat_trans_comp _ _ _ (op_nt (inv_from_z_iso (continuous_to_functor_comp _ _))) _).
      apply (inv_from_z_iso (C := [_^op, _^op])).
      apply (z_iso_from_nat_z_iso (homset_property _)).
      exact (functor_comp_op_nat_z_iso _ _).
Defined.

Local Lemma aux1
  {D : category}
  {X Y : TopologicalSpace}
  (f g : continuous_function X Y)
  (H : f = g)
  {Xdata : (topological_space_category X)^op ⟶ D}
  {Ydata : (topological_space_category Y)^op ⟶ D}
  (fdata : functor_opp (continuous_to_functor f) ∙ Xdata ⟹ Ydata)
  : transportf (λ x, functor_opp (continuous_to_functor x) ∙ Xdata ⟹ Ydata) H fdata
    = nat_trans_comp _ _ _ (post_whisker (op_nt (z_iso_mor (idtoiso (C := [_, _]) (maponpaths continuous_to_functor H)))) Xdata) fdata.
Proof.
  induction H.
  apply (nat_trans_eq_alt _ Ydata).
  intro x.
  refine (!id_left _ @ _).
  apply (maponpaths (λ x, x · _)).
  now refine (!functor_id Xdata _ @ _).
Qed.

Lemma presheafed_space_disp_cat_axioms
  (D : category)
  : disp_cat_axioms _ (presheafed_space_disp_cat_data D).
Proof.
  repeat split.
  - intros X Y f Xdata Ydata fdata.
    refine (_ @ !aux1 _ _ _ _).
    apply (nat_trans_eq_alt _ Ydata).
    intro x.
    apply (maponpaths (λ x, x · _)).
    refine (maponpaths (λ x, x · _) (id_right (# (Xdata : _ ⟶ _) _)) @ _).
    refine (maponpaths (λ x, _ · x) (id_right (# (Xdata : _ ⟶ _) _)) @ _).
    refine (!functor_comp _ _ _ @ _).
    apply (maponpaths (# (Xdata : _ ⟶ _))).
    apply isaprop_subtype_containedIn.
  - intros X Y f Xdata Ydata fdata.
    refine (_ @ !aux1 _ _ _ _).
    apply (nat_trans_eq_alt _ Ydata).
    intro x.
    refine (maponpaths (λ x, x · _ · _) (id_right (# (Xdata : _ ⟶ _) _)) @ _).
    refine (maponpaths (λ x, _ · x) (id_right (# (Ydata : _ ⟶ _) _)) @ _).
    refine (assoc' _ _ _ @ _).
    refine (!maponpaths _ (nat_trans_ax fdata _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    apply (maponpaths (λ x, x · _)).
    refine (!functor_comp _ _ _ @ _).
    apply (maponpaths (# (Xdata : _ ⟶ _))).
    apply isaprop_subtype_containedIn.
  - intros W X Y Z f g h Wdata Xdata Ydata Zdata fdata gdata hdata.
    refine (_ @ !aux1 _ _ _ _).
    apply (nat_trans_eq_alt _ Zdata).
    intro x.
    refine (maponpaths (λ x, x · _ · _) (id_right (# (Wdata : _ ⟶ _) _)) @ _).
    refine (maponpaths (λ x, _ · (x · _ · _)) (id_right (# (Xdata : _ ⟶ _) _)) @ _).
    refine (_ @ !maponpaths (λ x, _ · (x · _ · _)) (id_right (# (Wdata : _ ⟶ _) _))).
    refine (_ @ !maponpaths (λ x, _ · (_ · (x · _ · _) · _)) (id_right (# (Wdata : _ ⟶ _) _))).
    do 2 refine (assoc _ _ _ @ !_).
    apply (maponpaths (λ x, x · _)).
    refine (assoc _ _ _ @ _).
    do 2 refine (_ @ assoc' _ _ _).
    apply (maponpaths (λ x, x · _)).
    refine (assoc' _ _ _ @ _).
    refine (!maponpaths _ (nat_trans_ax fdata _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (_ @ assoc' _ _ _).
    apply (maponpaths (λ x, x · _)).
    refine (!functor_comp _ _ _ @ _).
    refine (_ @ maponpaths (λ x, x · _) (functor_comp _ _ _)).
    refine (_ @ functor_comp _ _ _).
    apply maponpaths.
    apply isaprop_subtype_containedIn.
  - intros.
    apply isaset_nat_trans.
    apply homset_property.
Qed.

Definition presheafed_space_disp_cat
  (D : category)
  : disp_cat top_cat
  := _ ,, presheafed_space_disp_cat_axioms D.

Definition presheafed_space_cat
  (D : category)
  : category
  := total_category (presheafed_space_disp_cat D).


(** Accessors *)

Definition presheafed_space
  (D : category)
  : UU
  := presheafed_space_cat D.

Coercion presheafed_space_to_space
  {D : category}
  (X : presheafed_space D)
  : TopologicalSpace
  := pr1 X.

Definition presheafed_space_presheaf
  {D : category}
  (X : presheafed_space D)
  : (topological_space_category X)^op ⟶ D
  := pr2 X.

Definition presheafed_space_morphism
  {D : category}
  (X Y : presheafed_space D)
  : UU
  := (presheafed_space_cat D)⟦X, Y⟧.

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
  : functor_opp (continuous_to_functor f) ∙ presheafed_space_presheaf X ⟹ presheafed_space_presheaf Y
  := pr2 f.
