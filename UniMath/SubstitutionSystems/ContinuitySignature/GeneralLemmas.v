Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.limits.coproducts.

Local Open Scope cat.

Definition CoproductOfArrowsIsos
           (I : UU) (C : category) (a : I -> C) (CC : Coproduct I C a)
           (c : I -> C) (CC' : Coproduct I C c) (f : ∏ i : I, C⟦a i, c i⟧)
  : (∏ i : I, is_z_isomorphism (f i)) -> is_z_isomorphism (CoproductOfArrows I C CC CC' f).
Proof.
  intro fi_iso.
  use make_is_z_isomorphism.
  - use CoproductOfArrows.
    exact (λ i, pr1 (fi_iso i)).
  - split.
    + etrans. { apply precompWithCoproductArrow. }
      apply pathsinv0, CoproductArrowUnique.
      intro i.
      refine (id_right _ @ ! id_left _ @ _).
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      apply pathsinv0, (pr2 (fi_iso i)).
    + etrans. { apply precompWithCoproductArrow. }
      apply pathsinv0, CoproductArrowUnique.
      intro i.
      refine (id_right _ @ ! id_left _ @ _).
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      apply pathsinv0, (pr2 (fi_iso i)).
Defined.

Lemma constant_functor_composition_nat_trans
      (A B C : category) (b : B) (F : functor B C)
  : nat_trans (functor_composite (constant_functor A B b) F)
              (constant_functor A C (F b)).
Proof.
  use make_nat_trans.
  + intro ; apply identity.
  + intro ; intros.
    apply maponpaths_2.
    exact (functor_id F b).
Defined.

Lemma constant_functor_composition_nat_z_iso (A B C : category) (b : B) (F : functor B C)
  : nat_z_iso (functor_composite (constant_functor A B b) F)
              (constant_functor A C (F b)).
Proof.
  exists (constant_functor_composition_nat_trans A B C b F).
  intro ; apply identity_is_z_iso.
Defined.

Lemma coproduct_of_functors_nat_trans
      {I : UU} {C D : category} (CP : Coproducts I D) {F G : I → C ⟶ D}
      (α : ∏ i : I, nat_trans (F i) (G i))
  : nat_trans (coproduct_of_functors I C D CP F) (coproduct_of_functors I C D CP G).
Proof.
  use make_nat_trans.
  - intro c.
    use CoproductOfArrows.
    exact (λ i, α i c).
  - intros c1 c2 f.
    etrans.
    1: apply precompWithCoproductArrow.
    etrans.
    2: apply pathsinv0, precompWithCoproductArrow.
    apply maponpaths.
    apply funextsec ; intro i.
    etrans.
    1: apply assoc.
    etrans.
    2: apply assoc'.
    apply maponpaths_2.
    exact (pr2 (α i) _ _ f).
Defined.

Lemma coproduct_of_functors_nat_z_iso
      {I : UU} {C D : category} (CP : Coproducts I D) {F G : I → C ⟶ D}
      (α : ∏ i : I, nat_z_iso (F i) (G i))
  : nat_z_iso (coproduct_of_functors I C D CP F) (coproduct_of_functors I C D CP G).
Proof.
  exists (coproduct_of_functors_nat_trans CP α).
  intro c.
  use tpair.
  - use CoproductOfArrows.
    exact (λ i, pr1 (pr2 (α i) c)).
  - split.
    + etrans.
      1: apply precompWithCoproductArrow.
      apply pathsinv0, CoproductArrowUnique.
      intro i.
      etrans.
      2: apply assoc'.
      etrans.
      2: apply maponpaths_2, pathsinv0, (pr2 (pr2 (α i) c)).
      exact (id_right _ @ ! id_left _).
    + etrans.
      1: apply precompWithCoproductArrow.
      apply pathsinv0, CoproductArrowUnique.
      intro i.
      etrans.
      2: apply assoc'.
      etrans.
      2: apply maponpaths_2, pathsinv0, (pr2 (pr2 (α i) c)).
      exact (id_right _ @ ! id_left _).
Defined.
