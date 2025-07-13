(*
  Interaction Weak Equivalences And Extensivity

  Given a weak equivalence into a univalent category (i.e., the Rezk completion),
  then extensivity transfers from the domain into the codomain.

  Contents.
  1. If F : C → D is a weak equivalence, then so is C/(a+b) → D/(Fa + Fb) [functor_to_functor_on_slices_between_coprod_is_weak_equiv]
  2. The extensivity functor commutes with isomorphisms [extensivity_functor_commutes_with_isos]
  3. Rezk completion of an extensive category is extensive [weak_equiv_preserves_extensivity]

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.TwoOutOfThree.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Bincoproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Slice.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodExtensivity.

Local Open Scope cat.

(** * 1. C/(a+b) → D/(Fa + Fb) is a weak equivalence *)
Section WeakEquivalenceSliceOverCoprod.

  Context {C D : category} (cC : BinCoproducts C) (cD : BinCoproducts D)
    {F : functor C D} (F_pc : preserves_bincoproduct F).

  Lemma functor_to_functor_on_slices_between_coprod_is_ff (a b : C)
    (ff : fully_faithful F)
    : fully_faithful (comp_functor_on_coprod cC cD F_pc a b).
  Proof.
    use comp_ff_is_ff.
    - apply functor_to_functor_on_slice_is_ff, ff.
    - apply fully_faithful_from_equivalence.
      apply functor_on_slices_iso_is_adj_equiv.
  Qed.

  Lemma functor_to_functor_on_slices_between_coprod_is_eso (a b : C)
    (w : is_weak_equiv F)
    : essentially_surjective (comp_functor_on_coprod cC cD F_pc a b).
  Proof.
    use comp_essentially_surjective.
    - apply functor_to_functor_on_slice_is_eso, w.
    - apply functor_from_equivalence_is_essentially_surjective.
      apply functor_on_slices_iso_is_adj_equiv.
  Qed.

  Lemma functor_to_functor_on_slices_between_coprod_is_weak_equiv
    (a b : C) (w : is_weak_equiv F)
    : is_weak_equiv (comp_functor_on_coprod cC cD F_pc a b).
  Proof.
    split.
    - apply functor_to_functor_on_slices_between_coprod_is_eso, w.
    - apply functor_to_functor_on_slices_between_coprod_is_ff, w.
  Qed.

End WeakEquivalenceSliceOverCoprod.

(** * 2. Extensivity functor up to iso *)
Section ExtensivityFunctorUpToIso.

  Context {C : category} (cC : BinCoproducts C) {a a' b b' : C}
    (i : z_iso a a') (j : z_iso b b').

  Definition functor_on_slices_iso_bincoprod
    : (C / cC a' b') ⟶ (C / cC a b).
  Proof.
    use comp_functor.
    apply bincoproduct_of_z_iso.
    - exact (z_iso_inv i).
    - exact (z_iso_inv j).
  Defined.

  Definition extensivity_functor_composed_with_isos
    : category_binproduct (C / a) (C / b) ⟶ (C / cC a b).
  Proof.
    use (functor_composite _ (functor_composite (extensivity_functor cC a' b') _)).
    - use pair_functor ; apply comp_functor.
      + exact i.
      + exact j.
    - apply functor_on_slices_iso_bincoprod.
  Defined.

  Lemma extensivity_functor_commutes_with_isos
    : nat_z_iso
        (extensivity_functor cC a b)
        (extensivity_functor_composed_with_isos).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intros [p q].
        exists (identity _).
        abstract (
            simpl ; rewrite id_left, id_right;
            etrans; [ apply precompWithBinCoproductArrow
                    | use maponpaths_12 ;
                      rewrite ! assoc;
                      apply maponpaths_2;
                      rewrite assoc';
                      rewrite z_iso_inv_after_z_iso;
                      apply id_right ]).
      + abstract
          (intro ; intros;
           use subtypePath;
           [ intro ; apply homset_property
           | cbn;
             etrans;
             [ apply (@pr1_transportf (C⟦_,_⟧) (λ _, C⟦_,_⟧))
             | rewrite transportf_const;
               apply pathsinv0;
               etrans; [ apply (@pr1_transportf (C⟦_,_⟧) (λ _, C⟦_,_⟧))
                       | rewrite transportf_const
                         ; cbn
                         ; now rewrite id_left, id_right ]]]).
    - intro.
      use make_is_z_iso_in_slice.
      apply identity_is_z_iso.
  Defined.

End ExtensivityFunctorUpToIso.

(** * 3.  Rezk completion of an extensive category is extensive *)
Section ExtensivityAlongRC.

  Local Lemma pair_functor_is_weak_equiv
    {A₀ A₁ B₀ B₁ : category}
    {F : functor A₀ B₀} {G : functor A₁ B₁}
    (F_weq : is_weak_equiv F) (G_weq : is_weak_equiv G)
    : is_weak_equiv (pair_functor F G).
  Proof.
    split.
    - apply pair_functor_eso ; apply eso_from_weak_equiv.
      + exact F_weq.
      + exact G_weq.
    - apply pair_functor_ff ; apply ff_from_weak_equiv.
      + exact F_weq.
      + exact G_weq.
  Qed.

  Context {C D : category} (D_univ : is_univalent D)
    {F : functor C D}
    (F_weq : is_weak_equiv F)
    {cC : BinCoproducts C} (E : is_extensive cC).

  Context (cD : BinCoproducts D).

  Let F_cc := weak_equiv_preserves_bincoproducts F_weq.

  Lemma weak_equiv_preserves_extensitivity_in_image (c c' : C)
    : adj_equivalence_of_cats (extensivity_functor cD (F c) (F c')).
  Proof.
    set (α' := make_nat_z_iso _ _ _
                 (bincoproduct_preserving_functor_commutes_with_extensivity cC cD F_cc c c')).
    use rad_equivalence_of_cats''.
    {
      apply is_univalent_category_binproduct
      ; apply (is_univalent_cod_slice (C := D ,, D_univ)).
    }

    apply (two_out_of_three_weak_equiv _ _ _ α').
    - apply comp_is_weak_equiv.
      + apply weak_equiv_from_equiv.
        exact (E c c').
      + apply functor_to_functor_on_slices_between_coprod_is_weak_equiv, F_weq.
    - apply pair_functor_is_weak_equiv
      ; apply functor_to_functor_on_slice_is_weq, F_weq.
  Qed.

  Lemma weak_equiv_preserves_extensitivity'
    {d d' : D} {c c' : C}
    (i : z_iso (F c) d)
    (i' : z_iso (F c') d')
    : adj_equivalence_of_cats (extensivity_functor cD d d').
  Proof.
    use (adj_equivalence_of_cats_closed_under_iso
           (F := extensivity_functor_composed_with_isos
                   cD
                   (z_iso_inv i)
                   (z_iso_inv i'))
        ).

    - use FunctorCategory.z_iso_from_nat_z_iso.
      apply nat_z_iso_inv.
      apply extensivity_functor_commutes_with_isos.
    - use comp_adj_equivalence_of_cats.
      + use pair_adj_equivalence_of_cats
        ; apply functor_on_slices_iso_is_adj_equiv.
      + use comp_adj_equivalence_of_cats.
        * apply weak_equiv_preserves_extensitivity_in_image.
        * apply functor_on_slices_iso_is_adj_equiv.
  Defined.

  Proposition weak_equiv_preserves_extensivity
    : is_extensive cD.
  Proof.
    intros d d'.
    apply rad_equivalence_of_cats''.
    {
      apply is_univalent_category_binproduct
      ; apply (is_univalent_cod_slice (C := D ,, D_univ)).
    }

    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq d)).
    { apply isaprop_is_weak_equiv. }
    intros [c i].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq d')).
    { apply isaprop_is_weak_equiv. }
    intros [c' i'].

    set (α := weak_equiv_preserves_extensitivity' i i').
    split.
    - apply functor_from_equivalence_is_essentially_surjective, α.
    - apply fully_faithful_from_equivalence, α.
  Qed.

End ExtensivityAlongRC.
