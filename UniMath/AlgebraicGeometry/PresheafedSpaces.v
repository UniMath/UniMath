(**************************************************************************************************

  Presheafed Spaces

  This file defines, for a category D, the category of D-presheafed spaces as a displayed category
  over `top_cat`.
  The fiber over a topological space T is equivalent to `[(open_category T)^op, D].
  For (T, P) and (T', P') pairs of spaces and presheaves, a displayed morphism over a continuous
  function `f: T → T'` is a natural transformation `α : F* T ⟹ T'`, with F* denoting pullback
  along the functor on the categories of opens, induced by f.
  Next, the explicit fully faithful embedding of `[(open_category T)^op, D]` into the fiber over T
  is used to show univalence.
  Lastly, this file defines types and accessors for the objects and morphisms in the category.

  Contents
  1. The category [presheafed_space_cat]
  2. The embedding of the functor category into a fiber
    [functor_to_fiber_presheaf_functor] [functor_to_fiber_presheaf_functor_fully_faithful]
  3. Univalence [is_univalent_presheafed_space_cat]
  4. Types and accessors [presheafed_space] [presheafed_space_morphism]

 **************************************************************************************************)
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

Require Import UniMath.AlgebraicGeometry.CategoryOfOpens.

Local Open Scope subtype.
Local Open Scope cat.

(** * 1. The category *)

Definition presheafed_space_disp_cat_data
  (D : category)
  : disp_cat_data top_cat.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + intro X.
      exact ((open_category X)^op ⟶ D).
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
      refine (nat_trans_comp _ _ _ _ (rassociator (C := bicat_of_cats) (a := (open_category Z)^op) (b := (open_category Y)^op) _ _ _)
      ).
      refine (post_whisker _ Xdata).
      refine (nat_trans_comp _ _ _ (op_nt (inv_from_z_iso (continuous_to_functor_compose _ _))) _).
      apply (inv_from_z_iso (C := [_^op, _^op])).
      apply (z_iso_from_nat_z_iso (homset_property _)).
      exact (functor_comp_op_nat_z_iso _ _).
Defined.

Local Lemma aux1
  {D : category}
  {X Y : top_cat}
  (f g : top_cat⟦X, Y⟧)
  (H : f = g)
  {Xdata : presheafed_space_disp_cat_data D X}
  {Ydata : presheafed_space_disp_cat_data D Y}
  (fdata : Xdata -->[f] Ydata)
  : transportf (mor_disp Xdata Ydata) H fdata
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

(** * 2. The embedding of the functor category into a fiber *)

Lemma id_disp_inv
  {D : category}
  {X : top_cat}
  (P : (presheafed_space_disp_cat D)[{X}])
  : (P : _ ⟶ _) ⟹ functor_opp (continuous_to_functor (identity X)) ∙ P.
Proof.
  refine (nat_trans_comp _ _ _ (linvunitor (C := bicat_of_cats) P) _).
  apply post_whisker.
  refine (nat_trans_comp _ _ _ _ (op_nt (z_iso_mor (continuous_to_functor_identity _)))).
  apply (z_iso_mor (C := [_^op, _^op])).
  apply (z_iso_from_nat_z_iso (homset_property _)).
  exact (op_triangle_nat_z_iso _).
Defined.

Lemma id_disp_inv_after_id_disp
  {D : category}
  {X : top_cat}
  (P : (presheafed_space_disp_cat D)[{X}])
  : nat_trans_comp _ _ _ (id_disp (D := presheafed_space_disp_cat D) P) (id_disp_inv P) = nat_trans_id _.
Proof.
  apply (nat_trans_eq (homset_property D)).
  intro x.
  refine (maponpaths (λ x, x · _) (id_right _) @ _).
  refine (maponpaths (λ x, _ · x) (id_left _) @ _).
  refine (!functor_comp P _ _ @ _).
  refine (_ @ functor_id P _).
  apply maponpaths.
  apply isaprop_subtype_containedIn.
Qed.

Lemma id_disp_after_id_disp_inv
  {D : category}
  {X : top_cat}
  (P : (presheafed_space_disp_cat D)[{X}])
  : nat_trans_comp _ _ _ (id_disp_inv P) (id_disp (D := presheafed_space_disp_cat D) P) = nat_trans_id _.
Proof.
  apply (nat_trans_eq (homset_property D)).
  intro x.
  refine (maponpaths (λ x, x · _) (id_left _) @ _).
  refine (maponpaths (λ x, _ · x) (id_right _) @ _).
  refine (!functor_comp P _ _ @ _).
  refine (_ @ functor_id P _).
  apply maponpaths.
  apply isaprop_subtype_containedIn.
Qed.

Lemma functor_to_fiber_presheaf_is_functor
  {D : category}
  (X : top_cat)
  : is_functor
    (make_functor_data
      (C := [(open_category X)^op, D])
      (C' := (presheafed_space_disp_cat D)[{X}])
      (idfun _)
      (λ P Q, nat_trans_comp _ _ _ (id_disp (D := presheafed_space_disp_cat D) P))).
Proof.
  split.
  - intro P.
    apply (nat_trans_eq (homset_property _)).
    intro x.
    apply id_right.
  - intros P Q R f g.
    refine (_ @ !aux1 _ _ _ _).
    apply (nat_trans_eq (homset_property _)).
    intro x.
    cbn.
    refine (maponpaths (λ x, x · _) (id_right _) @ _).
    refine (_ @ !maponpaths (λ x, _ · (x · _ · _)) (id_right _)).
    refine (_ @ !maponpaths (λ x, _ · (_ · (x · _) · _)) (id_right _)).
    refine (_ @ !maponpaths (λ x, _ · (_ · (x · _))) (id_right _)).
    refine (_ @ assoc' _ _ _).
    refine (_ @ assoc' _ _ _).
    refine (_ @ maponpaths (λ x, x · _ · _) (assoc' _ _ _)).
    refine (_ @ maponpaths (λ x, x · _ · _) (assoc' _ _ _)).
    refine (_ @ maponpaths (λ x, x · _) (assoc _ _ _)).
    refine (_ @ maponpaths (λ x, _ · x · _) (nat_trans_ax f _ _ _)).
    refine (_ @ maponpaths (λ x, x · _) (assoc' _ _ _)).
    refine (_ @ assoc _ _ _).
    apply (maponpaths (λ x, x · _)).
    refine (_ @ maponpaths (λ x, x · _ · _) (functor_comp P _ _)).
    refine (_ @ maponpaths (λ x, x · _) (functor_comp P _ _)).
    refine (_ @ functor_comp P _ _).
    apply (maponpaths (# (P : _ ⟶ _))).
    apply isaprop_subtype_containedIn.
Qed.

Definition functor_to_fiber_presheaf_functor
  (D : category)
  (X : top_cat)
  : [(open_category X)^op, D] ⟶ (presheafed_space_disp_cat D)[{X}]
  := make_functor _ (functor_to_fiber_presheaf_is_functor X).

Definition functor_to_fiber_presheaf_functor_fully_faithful
  {D : category}
  (X : top_cat)
  : fully_faithful (functor_to_fiber_presheaf_functor D X).
Proof.
  intros P Q.
  use isweq_iso.
  - exact (nat_trans_comp _ _ _ (id_disp_inv P)).
  - abstract (
      intro f;
      refine (nat_trans_comp_assoc (homset_property _) _ _ _ _ _ _ _ @ _);
      refine (maponpaths (λ x, nat_trans_comp _ _ _ x _) (id_disp_after_id_disp_inv P) @ _);
      apply (nat_trans_comp_id_left (homset_property _))
    ).
  - abstract (
      intro f;
      refine (nat_trans_comp_assoc (homset_property _) _ _ _ _ _ _ _ @ _);
      refine (maponpaths (λ x, nat_trans_comp _ _ _ x _) (id_disp_inv_after_id_disp P) @ _);
      apply (nat_trans_comp_id_left (homset_property _))
    ).
Defined.

(** * 3. Univalence *)

Lemma is_univalent_disp_presheafed_space_disp_cat
  (D : category)
  (H : is_univalent D)
  : is_univalent_disp (presheafed_space_disp_cat D).
Proof.
  apply is_univalent_disp_from_is_univalent_fiber.
  intros X P Q.
  use isweqhomot.
  - exact (weqcomp
      (make_weq _ (is_univalent_functor_category (_^op) D H _ _))
      (weq_ff_functor_on_z_iso (functor_to_fiber_presheaf_functor_fully_faithful _) P Q)).
  - abstract (
      intro H';
      induction H';
      apply z_iso_eq;
      apply (nat_trans_eq (homset_property _));
      intro x;
      apply id_right
    ).
  - apply weqproperty.
Defined.

Lemma is_univalent_presheafed_space_cat
  {D : category}
  (H : is_univalent D)
  : is_univalent (presheafed_space_cat D).
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_top_cat.
  - apply is_univalent_disp_presheafed_space_disp_cat.
    exact H.
Defined.

(** * 4. Types and accessors *)

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
  : (open_category X)^op ⟶ D
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
