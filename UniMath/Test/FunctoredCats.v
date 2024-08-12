Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Invertible_2cells.

Local Open Scope cat.

Definition univalent_setcategory
  : UU
  := ∑ (C : category), isaset C × is_univalent C.

Coercion univalent_setcategory_to_category
  (C : univalent_setcategory)
  : category
  := pr1 C.

Definition univalent_setcategory_isaset
  (C : univalent_setcategory)
  : isaset C
  := pr12 C.

Definition univalent_setcategory_is_univalent
  (C : univalent_setcategory)
  : is_univalent C
  := pr22 C.


Definition presheafed_category (D : category)
  : UU
  := ∑ (C : univalent_setcategory), C ⟶ D.

Coercion presheafed_category_to_univalent_setcategory
  {D : category}
  (C : presheafed_category D)
  : univalent_setcategory
  := pr1 C.

Definition presheafed_category_presheaf
  {D : category}
  (C : presheafed_category D)
  : C ⟶ D
  := pr2 C.


Definition presheafed_category_morphism
  {D : category}
  (X Y : presheafed_category D)
  : UU
  := ∑ (F : Y ⟶ X), F ∙ presheafed_category_presheaf X ⟹ presheafed_category_presheaf Y.

Coercion presheafed_category_morphism_to_functor
  {D : category}
  {X Y : presheafed_category D}
  (F : presheafed_category_morphism X Y)
  : Y ⟶ X
  := pr1 F.

Definition presheafed_category_morphism_nat_trans
  {D : category}
  {X Y : presheafed_category D}
  (F : presheafed_category_morphism X Y)
  : F ∙ presheafed_category_presheaf X ⟹ presheafed_category_presheaf Y
  := pr2 F.


(* Lemma aux1
  {A B C : category}
  {F F' : A ⟶ B}
  {G : A ⟶ C}
  {H : B ⟶ C}
  (f : G ⟹ F ∙ H)
  (p : F = F')
  : transportf (λ x, G ⟹ x ∙ H) p f = nat_trans_comp _ _ _ f (post_whisker (z_iso_mor (idtoiso (C := [A, B]) p)) H).
Proof.
  induction p.
  refine (_ @ !maponpaths _ (post_whisker_identity _ _ _ _ _)).
  exact (!nat_trans_comp_id_right (homset_property _) _ _ f).
Qed. *)

Lemma aux1
  {A B C : category}
  {F F' : A ⟶ B}
  {G : A ⟶ C}
  {H : B ⟶ C}
  (f : F ∙ H ⟹ G)
  (p : F = F')
  : transportf (λ x, x ∙ H ⟹ G) p f = nat_trans_comp _ _ _ (post_whisker (inv_from_z_iso (idtoiso (C := [A, B]) p)) H) f.
Proof.
  induction p.
  refine (_ @ !maponpaths (λ x, nat_trans_comp _ _ _ x _) (post_whisker_identity _ _ _ _ _)).
  exact (!nat_trans_comp_id_left (homset_property _) _ _ f).
Qed.

Lemma presheafed_category_morphism_eq
  {D : category}
  {X Y : presheafed_category D}
  (F F' : presheafed_category_morphism X Y)
  (f : z_iso (C := [Y, X]) (F : Y ⟶ X) (F' : Y ⟶ X))
  (H : nat_trans_comp _ _ _ (post_whisker (inv_from_z_iso f) _)(presheafed_category_morphism_nat_trans F) = presheafed_category_morphism_nat_trans F')
  : F = F'.
Proof.
  use total2_paths_f.
  - refine (isotoid _ _ f).
    apply is_univalent_functor_category.
    apply univalent_setcategory_is_univalent.
  - refine (aux1 _ _ @ _).
    refine (maponpaths (λ x, nat_trans_comp _ _ _ (post_whisker (inv_from_z_iso (C := [_, _]) x) _) _) (idtoiso_isotoid _ _ _ _ _) @ _).
    exact H.
Qed.

Definition presheafed_category_identity
  {D : category}
  (X : presheafed_category D)
  : presheafed_category_morphism X X.
Proof.
  exists (functor_identity _).
  apply nat_trans_functor_id_right.
Defined.

Definition presheafed_category_comp
  {D : category}
  {X Y Z : presheafed_category D}
  (f : presheafed_category_morphism X Y)
  (g : presheafed_category_morphism Y Z)
  : presheafed_category_morphism X Z.
Proof.
  exists (g ∙ f).
  refine (nat_trans_comp _ _ _ (nat_trans_functor_assoc _ _ _) _).
  refine (nat_trans_comp _ _ _ (pre_whisker g (presheafed_category_morphism_nat_trans f)) _).
  exact (presheafed_category_morphism_nat_trans g).
Defined.

Definition presheafed_category_category_data
  (D : category)
  : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact (presheafed_category D).
    + exact presheafed_category_morphism.
  - exact presheafed_category_identity.
  - intros X Y Z.
    exact presheafed_category_comp.
Defined.

Lemma presheafed_category_is_category
  (D : category)
  : is_precategory (presheafed_category_category_data D).
Proof.
  use make_is_precategory_one_assoc.
  - intros X Y F.
    use presheafed_category_morphism_eq.
    + exact (lunitor_invertible_2cell (B := bicat_of_cats) _).
    + apply (nat_trans_eq_alt _ _ _ (presheafed_category_morphism_nat_trans F)).
      intro.
      refine (maponpaths (λ x, x · _) (functor_id (presheafed_category_presheaf X) _) @ _).
      now do 3 refine (id_left _ @ _).
  - intros X Y F.
    use presheafed_category_morphism_eq.
    + exact (runitor_invertible_2cell (B := bicat_of_cats) _).
    + apply (nat_trans_eq_alt _ _ _ (presheafed_category_morphism_nat_trans F)).
      intro.
      refine (maponpaths (λ x, x · _) (functor_id (presheafed_category_presheaf X) _) @ _).
      do 2 refine (id_left _ @ _).
      apply id_right.
  - intros W X Y Z F G H.
    use presheafed_category_morphism_eq.
    + exact (rassociator_invertible_2cell (B := bicat_of_cats) _ _ _).
    + apply (nat_trans_eq_alt _ _ _ (presheafed_category_morphism_nat_trans (F · G · H))).
      intro.
      refine (maponpaths (λ x, x · _) (functor_id (presheafed_category_presheaf W) _) @ _).
      do 2 refine (maponpaths (λ x, _ · x) (_ @ assoc _ _ _)).
      apply (maponpaths (λ x, _ · x)).
      apply id_left.
Qed.

Lemma presheafed_category_has_homsets
  (D : category)
  : has_homsets (presheafed_category_category_data D).
Proof.
  intros X Y.
  apply isaset_total2.
  - apply functor_isaset.
    + apply homset_property.
    + apply univalent_setcategory_isaset.
  - intro F.
    apply isaset_nat_trans.
    apply homset_property.
Qed.

Definition presheafed_category_category
  (D : category)
  : category
  := make_category
    (make_precategory
      (presheafed_category_category_data D)
      (presheafed_category_is_category D))
    (presheafed_category_has_homsets D).
