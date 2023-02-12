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


(*
The following lemmas has to be moved accordingly,
e.g. in the file CategoryTheory.Chains.Omegacontfunctors
 *)

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Chains.All.
Lemma nat_trans_preserve_cone
      {A B : category}
      {F G : functor A B}
      (α : nat_trans F G)
      {coch : cochain A}
      {b : B} (b_con : cone (mapdiagram F coch) b)
  : cone (mapdiagram G coch) b.
Proof.
  exists (λ v, pr1 b_con v · α (dob coch v)).
  intros u v p.
  etrans.
  1: apply assoc'.
  cbn.
  etrans.
  1: apply maponpaths, pathsinv0, (pr2 α).
  etrans.
  1: apply assoc.
  apply maponpaths_2.
  exact (pr2 b_con u v p).
Defined.

Lemma nat_z_iso_preserve_ωlimits {A B : category}
      (F G : functor A B)
  : is_omega_cont F -> nat_z_iso F G -> is_omega_cont G.
Proof.
  (* This lemma should be split up in data and property and there is also a repeat of proof, need a more "general, but easy" lemma.
 *)
  intros Fc i.
  intros coch a a_con a_lim.
  intros b b_con.
  set (b'_con := nat_trans_preserve_cone (nat_z_iso_inv i) b_con).
  set (t := Fc coch a a_con a_lim b b'_con).
  use tpair.
  - exists (pr11 t · pr1 i a).
    intro v.
    etrans.
    1: apply assoc'.
    etrans.
    1: apply maponpaths, pathsinv0, (pr21 i).
    etrans.
    1: apply assoc.
    etrans.
    1: apply maponpaths_2, (pr21 t v).
    etrans.
    1: apply assoc'.
    etrans.
    1: apply maponpaths, (pr2 i (dob coch v)).
    apply id_right.
  - intro f.
    use total2_paths_f.
    + use (cancel_z_iso _ _ (_ ,, pr2 (nat_z_iso_inv i) a)).
      etrans.
      2: apply assoc.
      etrans.
      2: apply maponpaths, pathsinv0, (pr2 (pr2 i a)).
      etrans.
      2: apply pathsinv0, id_right.

      transparent assert (c' : (∑ x : B ⟦ b, F a ⟧, limits.is_cone_mor b'_con (limits.mapcone F coch a_con) x)).
      {
        exists (pr1 f · pr1 (pr2 i a)).
        intro v.
        cbn.
        etrans.
        1: apply assoc'.
        etrans.
        1: apply maponpaths, pathsinv0, (pr21 (nat_z_iso_inv i)).
        etrans.
        1: apply assoc.
        apply maponpaths_2, (pr2 f v).
      }

      exact (base_paths _ _ (pr2 t c')).
    + apply (impred_isaprop) ; intro ; apply homset_property.
Defined.
