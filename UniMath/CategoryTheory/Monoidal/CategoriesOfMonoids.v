(** Categories of monoids for monoidal categories **)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Local Open Scope cat.

Section Precategory_of_Monoids.

Context (Mon : monoidal_precat).

Local Definition C := monoidal_precat_precat Mon.
Local Definition tensor := monoidal_precat_tensor Mon.
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "f #⊗ g" := (# tensor (f #, g)) (at level 31).
Local Definition I := monoidal_precat_unit Mon.
Local Definition α' := monoidal_precat_associator Mon.
Local Definition λ' := monoidal_precat_left_unitor Mon.
Local Definition ρ' := monoidal_precat_right_unitor Mon.

Definition monoid_ob_data : UU :=
  ∑ X : C, (X ⊗ X --> X) × (I --> X).

Definition is_monoid_ob (X : C) (μ : X ⊗ X --> X) (η : I --> X) : UU :=
	(μ #⊗ id X · μ = pr1 α' ((X, X), X) · id X #⊗ μ · μ) × (* Pentagon diagram *)
	(pr1 λ' X = η #⊗ id X · μ) × (pr1 ρ' X = id X #⊗ η · μ). (* Unitor diagrams *)
(* This definition deviates from that by Mac Lane (CWM 2nd ed., p.170) since the associator goes in the opposite direction. However, it conforms to the def. on Wikipedia for monoid objects. *)


Definition monoid_ob : UU :=
	∑ X : monoid_ob_data, is_monoid_ob (pr1 X) (pr1 (pr2 X)) (pr2 (pr2 X)).

Definition monoid_carrier (X : monoid_ob) : C := pr1 (pr1 X).
Local Coercion monoid_carrier : monoid_ob >-> ob.

Definition monoid_mult (X : monoid_ob) := pr1 (pr2 (pr1 X)).

Definition monoid_unit (X : monoid_ob) := pr2 (pr2 (pr1 X)).

Definition is_monoid_mor (X Y : monoid_ob) (f : monoid_carrier X --> monoid_carrier Y) : UU :=
  ((@monoid_mult X) · f = f #⊗ f · (@monoid_mult Y)) ×
   (@monoid_unit X) · f = (@monoid_unit Y).

Definition monoid_mor (X Y : monoid_ob) : UU :=
  ∑ f : X --> Y, is_monoid_mor X Y f.
Coercion mor_from_monoid_mor (X Y : monoid_ob) (f : monoid_mor X Y) : X --> Y := pr1 f.

Definition isaprop_is_monoid_mor (hs : has_homsets C) (X Y : monoid_ob) (f : monoid_carrier X --> monoid_carrier Y):
  isaprop (is_monoid_mor X Y f).
Proof.
  use isapropdirprod; apply hs.
Qed.

Definition isaset_monoid_mor (hs : has_homsets C) (X Y : monoid_ob) : isaset (monoid_mor X Y).
Proof.
  apply (isofhleveltotal2 2).
  - apply hs.
  - intro.
    apply isasetaprop.
    apply isaprop_is_monoid_mor; assumption.
Qed.

Definition monoid_mor_eq (hs : has_homsets C) {X Y : monoid_ob} {f g : monoid_mor X Y} :
  (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro.
  apply isaprop_is_monoid_mor; assumption.
Defined.

Definition monoid_mor_id (X : monoid_ob) : monoid_mor X X.
Proof.
  exists (id _).
  red.
  rewrite id_right.
  rewrite tensor_id.
  rewrite id_left.
  rewrite id_right.
  split; apply idpath.
Defined.

Definition monoid_mor_comp (X Y Z : monoid_ob) (f : monoid_mor X Y) (g : monoid_mor Y Z) : monoid_mor X Z.
Proof.
  use tpair; [| split].
  - exact (f · g).
  - rewrite assoc.
    change (monoid_mult X · pr1 f · g = # tensor (f · g #, f · g) · monoid_mult Z).
    rewrite (pr1 (pr2 f)).
    rewrite <- assoc.
    change ((# tensor (f #, f) · (monoid_mult Y · g) =
             # tensor (precatbinprodmor (f · g) (f · g)) · monoid_mult Z)).
    rewrite binprod_comp.
    change ((# tensor (pr1 f #, pr1 f) · (monoid_mult Y · pr1 g) =
             # tensor ((f #, f) · (g #, g)) · monoid_mult Z)).
    rewrite functor_comp.
    rewrite (pr1 (pr2 g)).
    rewrite assoc.
    apply idpath.
  - rewrite assoc.
    rewrite <- (pr2 (pr2 g)).
    rewrite <- (pr2 (pr2 f)).
    apply idpath.
Defined.

Definition precategory_monoid_ob_mor : precategory_ob_mor.
Proof.
  exists monoid_ob.
  exact monoid_mor.
Defined.

Definition precategory_monoid_data : precategory_data.
Proof.
  exists precategory_monoid_ob_mor.
  exists monoid_mor_id.
  exact monoid_mor_comp.
Defined.

Lemma is_precategory_precategory_monoid_data (hs : has_homsets C)
  : is_precategory precategory_monoid_data.
Proof.
  repeat split; intros; simpl; apply monoid_mor_eq; try apply hs.
  - apply id_left.
  - apply id_right.
  - apply assoc.
  - apply assoc'.
Defined.

Definition precategory_monoid (hs : has_homsets C)
  : precategory := tpair _ _ (is_precategory_precategory_monoid_data hs).

Local Notation monoid := precategory_monoid.

Lemma precategory_monoid_has_homsets (hs: has_homsets C):
  has_homsets (precategory_monoid hs).
Proof.
  red.
  intros X Y.
  red.
  intros f g.
  apply (isofhlevelweqf 1 (monoid_mor_eq hs (f := f) (g := g))).
  apply hs.
Qed.

Definition category_monoid (hs: has_homsets C): category.
Proof.
  exists (precategory_monoid hs).
  apply precategory_monoid_has_homsets.
Defined.

End Precategory_of_Monoids.
