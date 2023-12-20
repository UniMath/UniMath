(*
In this file, it is shown how any bicategory is weakly biequivalent to a locally univalent bicategory.
From any bicategory B, we construct a locally univalent bicategory LRB "local Rezk completion of B", which is defined by the following data:
ob LRB := ob B.
hom x y := RC(hom x y),
where RC is the Rezk completion for categories.
Since each hom-category of LRB is univalent, it is indeed locally univalent .
There is a pseudofunctor from B to LRB which is the identity on objects and
its action on morphisms is induced by the unit of the rezk completion of RC(hom _ _).

Most work lies in showing how LRB is indeed a bicategory.
In essence, this follows since all pieces of data (at level 1 and 2) of a bicategory correspond with a functor between some hom-categories. Those pieces of data can then be constructed using the universal property of the Rezk completion.

As a consequence, we can conclude that any bicategory admits a Rezk completion (this is formulated in Bicategories/RezkCompletions/RezkCompletion.v
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.PrecompEquivalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.RezkCompletion.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.YonedaLemma.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Properties.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.

Local Open Scope cat.

Section FunctorCompositionWeakBiequivalences.

  Lemma comp_local_weak_equivalence
        {B1 B2 B3 : bicat}
        {F : psfunctor B1 B2}
        {G : psfunctor B2 B3}
        (Feso : local_weak_equivalence F)
        (Geso : local_weak_equivalence G)
    : local_weak_equivalence (comp_psfunctor G F).
  Proof.
    intros x y.
    split.
    - use (comp_essentially_surjective (Fmor F x y) _ (Fmor G _ _)).
      + exact (pr1 (Feso x y)).
      + apply (pr1 (Geso _ _)).
    - use (comp_ff_is_ff _ _ _ (Fmor F x y) _ (Fmor G _ _)).
      + exact (pr2 (Feso x y)).
      + apply (pr2 (Geso _ _)).
  Defined.

  Lemma comp_essentially_surjective
        {B1 B2 B3 : bicat}
        {F : psfunctor B1 B2}
        {G : psfunctor B2 B3}
        (Feso : essentially_surjective_psfunctor F)
        (Geso : essentially_surjective_psfunctor G)
    : essentially_surjective_psfunctor (comp_psfunctor G F).
  Proof.
    intro z.
    use (factor_through_squash_hProp _ _ (Geso z)).
    intros [y yp].
    use (factor_through_squash_hProp _ _ (Feso y)).
    intros [x xp].
    apply hinhpr.
    exists x.
    use (Composition.comp_adjequiv _ yp).
    use (psfunctor_preserve_adj_equiv G).
    exact xp.
  Qed.

  Lemma comp_weak_biequivalence
        {B1 B2 B3 : bicat}
        {F : psfunctor B1 B2}
        {G : psfunctor B2 B3}
        (Fw : weak_biequivalence F)
        (Gw : weak_biequivalence G)
    : weak_biequivalence (comp_psfunctor G F).
  Proof.
    split.
    - apply (comp_essentially_surjective (pr1 Fw) (pr1 Gw)).
    - apply (comp_local_weak_equivalence (pr2 Fw) (pr2 Gw)).
  Defined.

End FunctorCompositionWeakBiequivalences.

Section LocalUnivalenceRezk.

  Context (RC : RezkCat).
  Let R : category -> univalent_category := λ C, pr1 (RC C).
  Let η : ∏ C : category, functor C (R C) := λ C, pr12 (RC C).
  Let eso : ∏ C : category, Functors.essentially_surjective (η C) := λ C, pr122 (RC C).
  Let ff : ∏ C : category, Functors.fully_faithful (η C) := λ C, pr222 (RC C).

  Notation "η_{ x , y }" := (η (hom x y)).
  Notation "eso_{ x , y }" := (eso (hom x y)).
  Notation "ff_{ x , y }" := (ff (hom x y)).

  Notation "C ⊠ D" := (category_binproduct C D) (at level 38).
  Notation "( c , d )" := (make_catbinprod c d).
  Notation "( f #, g )" := (catbinprodmor f g).

  Context (B : bicat).

  Definition LRB_precat_ob_mor
    : precategory_ob_mor.
  Proof.
    exists (ob B).
    exact (λ x y, ob (R (hom x y))).
  Defined.

  Definition LRB_composition (x y z : B)
    : functor (R (hom x y) ⊠ R (hom y z)) (R (hom x z)).
  Proof.
    use lift_functor_along.
    - exact (hom x y ⊠ hom y z).
    - exact (pair_functor (η_{x,y}) (η_{y,z})).
    - apply pair_functor_eso ; apply eso.
    - apply pair_functor_ff ; apply ff.
    - exact (functor_composite hcomp_functor (η (hom x z))).
  Defined.

  Definition LRB_composition_comm (x y z : B)
    : nat_z_iso
        (functor_composite (pair_functor (η (hom _ _)) (η (hom _ _))) (LRB_composition x y z))
        (functor_composite hcomp_functor (η (hom x z)))
    := lift_functor_along_comm _ _ _ _ _.

  Definition LRB_composition_curry1 (x y z : B)
    : functor (R (hom x y))
              (FunctorCategory.functor_category (R (hom y z)) (R (hom x z)))
    := curry_functor' (LRB_composition x y z).

  Definition LRB_composition_curry2 (x y z : B)
    : functor (R (hom y z))
              (FunctorCategory.functor_category (R (hom x y)) (R (hom x z)))
    := curry_functor _ _ _ (LRB_composition x y z).

  Definition LRB_precat_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact LRB_precat_ob_mor.
    - exact (λ x, η (hom x x) (identity x)).
    - exact (λ x y z f g, LRB_composition x y z (f , g)).
  Defined.

  Definition LRB_prebicat_2cell_struct
    : prebicat_2cell_struct LRB_precat_data
    := λ x y f g, (R (hom x y))⟦f,g⟧.

  Definition LRB_prebicat_1_id_comp_cells
    : prebicat_1_id_comp_cells.
  Proof.
    exists LRB_precat_data.
    exact LRB_prebicat_2cell_struct.
  Defined.

  Local Definition LRB_functor_lcomp_id (x y : B)
    : functor (R (hom x y)) (R (hom x y)).
  Proof.
    use (lift_functor_along (R (hom x y)) _ (eso (hom x y)) (ff_{x,y})).
    use (functor_composite _ (η_{x,y})).
    use functor_composite.
    - exact (hom x x ⊠ hom x y).
    - use bindelta_pair_functor.
      + apply constant_functor.
        exact (identity x).
      + apply functor_identity.
    - apply hcomp_functor.
  Defined.

  Definition LRB_lunitor_nat_z_iso_pre (x y : B)
    : nat_z_iso
    (η_{x,y}
     ∙ (bindelta_pair_functor (constant_functor (R (hom x y)) (R (hom x x)) (η (hom x x) (id₁ x)))
          (functor_identity (R (hom x y))) ∙ LRB_composition x x y))
    (η_{x,y} ∙ functor_identity (R (hom x y))).
  Proof.
    transparent assert (p :
                         (nat_z_iso (η_{x,y}
              ∙ (bindelta_pair_functor
                   (constant_functor (R (hom x y)) (R (hom x x)) (η (hom x x) (id₁ x)))
                   (functor_identity (R (hom x y)))
                ))
                (bindelta_pair_functor
                (constant_functor (hom x y) (hom x x) (id₁ x))
                (functor_identity (hom x y))
                ∙ (pair_functor (η (hom x x)) (η_{x,y}))))
           ).
    {
      use make_nat_z_iso.
      - use make_nat_trans.
        + intro ; apply identity.
        + intro ; intros.
          cbn.
          do 3 rewrite id_left.
          rewrite id_right.
          apply maponpaths_2.
          apply (! functor_id (η (hom x x)) _).
      - intro ; apply (identity_is_z_iso (C := _ ⊠ _)).
    }
    use (nat_z_iso_comp (nat_z_iso_functor_comp_assoc _ _ _)).
    use (nat_z_iso_comp (post_whisker_nat_z_iso p _) _).
    use (nat_z_iso_comp (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _))).
    use (nat_z_iso_comp (pre_whisker_nat_z_iso _ _) _).
    2: apply lift_functor_along_comm.
    use (nat_z_iso_comp _ (nat_z_iso_inv (functor_commutes_with_id _))).
    use (nat_z_iso_comp (nat_z_iso_functor_comp_assoc _ _ _)).
    use post_whisker_nat_z_iso.
    use make_nat_z_iso.
    - apply lunitor_transf.
    - intro ; apply is_z_iso_lunitor.
  Defined.
  Definition LRB_runitor_nat_z_iso_pre (x y : B)
    :  nat_z_iso
    (η_{x,y}
     ∙ (bindelta_pair_functor (functor_identity (R (hom x y)))
          (constant_functor (R (hom x y)) (R (hom y y)) (η (hom y y) (id₁ y)))
          ∙ LRB_composition x y y)) (η_{x,y} ∙ functor_identity (R (hom x y))).
  Proof.
    transparent assert (p :
                         (nat_z_iso
                            (η_{x,y}
              ∙ (bindelta_pair_functor
                   (functor_identity (R (hom x y)))
                   (constant_functor (R (hom x y)) (R (hom y y)) (η (hom y y) (id₁ y)))
                ))
                            (bindelta_pair_functor
                               (functor_identity (hom x y))
                               (constant_functor (hom x y) (hom y y) (id₁ y))
                               ∙ (pair_functor (η_{x,y}) (η (hom y y)))))
           ).
    {
      use make_nat_z_iso.
      - use make_nat_trans.
        + intro ; apply identity.
        + intro ; intros.
          cbn.
          do 3 rewrite id_left.
          rewrite id_right.
          apply maponpaths.
          apply (! functor_id (η (hom y y)) _).
      - intro ; apply (identity_is_z_iso (C := _ ⊠ _)).
    }
    use (nat_z_iso_comp (nat_z_iso_functor_comp_assoc _ _ _)).
    use (nat_z_iso_comp (post_whisker_nat_z_iso p _) _).
    use (nat_z_iso_comp (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _))).
    use (nat_z_iso_comp (pre_whisker_nat_z_iso _ _) _).
    2: apply lift_functor_along_comm.
    use (nat_z_iso_comp _ (nat_z_iso_inv (functor_commutes_with_id _))).
    use (nat_z_iso_comp (nat_z_iso_functor_comp_assoc _ _ _)).
    use post_whisker_nat_z_iso.
    use make_nat_z_iso.
    - apply runitor_transf.
    - intro ; apply is_z_iso_runitor.
  Defined.

  Definition LRB_lunitor_nat_z_iso (x y : B)
    : nat_z_iso (functor_composite
                   (bindelta_pair_functor (constant_functor _ _ (η (hom x x) (identity x))) (functor_identity _))
                   (LRB_composition x x y)
                )
                (functor_identity (R (hom x y))).
  Proof.
    apply (lift_nat_z_iso_along  (R (hom x y)) _ (eso (hom x y)) (ff_{x,y})).
    apply LRB_lunitor_nat_z_iso_pre.
  Defined.

  Definition LRB_lunitor {x y : B} (f : R (hom x y))
    : z_iso (LRB_composition x x y (η (hom x x) (identity x) , f)) f.
  Proof.
    use make_z_iso ; try (apply (LRB_lunitor_nat_z_iso x y)).
    split ; apply (pr2 (LRB_lunitor_nat_z_iso x y)).
  Defined.

  Definition LRB_runitor_nat_z_iso (x y : B)
    : nat_z_iso (functor_composite
                   (bindelta_pair_functor
                      (functor_identity _)
                      (constant_functor _ _ (η (hom y y) (identity y)))
                   )
                   (LRB_composition x y y)
                )
                (functor_identity (R (hom x y))).
  Proof.
    apply (lift_nat_z_iso_along  (R (hom x y)) _ (eso (hom x y)) (ff_{x,y})).
    apply LRB_runitor_nat_z_iso_pre.
  Defined.

  Definition LRB_runitor {x y : B} (f : R (hom x y))
    : z_iso (LRB_composition x y y (f, η (hom y y) (identity y))) f.
  Proof.
    use make_z_iso ; try (apply (LRB_runitor_nat_z_iso x y)).
    split ; apply (pr2 (LRB_runitor_nat_z_iso x y)).
  Defined.

  Let LRB_lunitor_comm := λ x y : B, lift_nat_trans_along_comm (R (hom x y)) _ (eso (hom x y)) (ff_{x,y}) (LRB_lunitor_nat_z_iso_pre x y).
  Let LRB_runitor_comm := λ x y : B, lift_nat_trans_along_comm (R (hom x y)) _ (eso (hom x y)) (ff_{x,y}) (LRB_runitor_nat_z_iso_pre x y).

  Definition LRB_lwhisker {x y z : B}
             (f : R (hom x y))
             {g1 g2 : R (hom y z)}
             (α : R (hom y z) ⟦ g1, g2 ⟧)
    : R (hom x z) ⟦LRB_composition _ _ _ (f, g1), LRB_composition _ _ _ (f, g2)⟧
    := #(LRB_composition_curry1 x y z f : functor _ _) α.

  Definition LRB_rwhisker {x y z : B}
             {f1 f2 : R (hom x y)}
             (α : R (hom x y) ⟦ f1, f2 ⟧)
             (g: R (hom y z))
    : R (hom x z) ⟦LRB_composition _ _ _ (f1, g), LRB_composition _ _ _ (f2, g)⟧
    := #(LRB_composition_curry2 x y z g : functor _ _) α.

  Definition LRB_associator_nat_z_iso_pre
             (x y z w : B)
    : nat_z_iso
        (pair_functor
           (η_{x,y})
           (pair_functor (η_{y,z}) (η (hom z w)))
           ∙ (((precategory_binproduct_assoc (R (hom x y)) (R (hom y z)) (R (hom z w)))
                 ∙ pair_functor (LRB_composition x y z) (functor_identity (R (hom z w))))
                ∙ LRB_composition x z w)
        )
        (pair_functor
           (η_{x,y})
           (pair_functor (η_{y,z}) (η (hom z w)))
           ∙ (pair_functor (functor_identity (R (hom x y))) (LRB_composition y z w)
                           ∙ LRB_composition x y w)).
  Proof.
    use (nat_z_iso_comp (nat_z_iso_functor_comp_assoc _ _ _)).
    transparent assert (p : (nat_z_iso
                   (pair_functor (η_{x,y}) (pair_functor (η_{y,z}) (η (hom z w)))
                                 ∙ precategory_binproduct_assoc (R (hom x y)) (R (hom y z)) (R (hom z w)))
                   (precategory_binproduct_assoc
                      (hom x y) (hom y z) (hom z w)
                      ∙ (pair_functor (pair_functor (η_{x,y}) (η_{y,z})) (η (hom z w)))))).
    {
      use make_nat_z_iso.
      - use make_nat_trans.
        + intro ; apply identity.
        + intro ; intros.
          cbn.
          do 3 rewrite id_left.
          now do 3 rewrite id_right.
      - intro ; apply (identity_is_z_iso (C := _ ⊠ _)).
    }
    transparent assert (q :
                         (nat_z_iso
                            (pair_functor (pair_functor (η_{x,y}) (η_{y,z})) (η (hom z w))
                                          ∙ pair_functor (LRB_composition x y z) (functor_identity (R (hom z w))))
                            (pair_functor hcomp_functor (functor_identity (hom z w)) ∙ (pair_functor (η _) (η _)))
                         )
                       ).
    {
      use (nat_z_iso_comp (nat_z_iso_inv (nat_z_iso_pair _ _ _ _))).
      use (nat_z_iso_comp _ (nat_z_iso_pair _ _ _ _)).
      use nat_z_iso_between_pair.
      - apply LRB_composition_comm.
      - apply functor_commutes_with_id.
    }
    transparent assert ( q' :
                         (nat_z_iso
                            ((pair_functor (functor_identity (hom x y)) hcomp_functor)
                            ∙ pair_functor (η (hom _ _)) (η (hom _ _)))
                                          (pair_functor (η_{x,y}) (pair_functor (η_{y,z}) (η (hom z w))) ∙ pair_functor (functor_identity (R (hom x y))) (LRB_composition y z w)))).
    {
      use (nat_z_iso_comp (nat_z_iso_inv (nat_z_iso_pair _ _ _ _))).
      use (nat_z_iso_comp _ (nat_z_iso_pair _ _ _ _)).
      use nat_z_iso_between_pair.
      - apply functor_commutes_with_id.
      - apply nat_z_iso_inv, LRB_composition_comm.
    }
    use (nat_z_iso_comp (post_whisker_nat_z_iso _ _) _).
    2: {
      use (nat_z_iso_comp (nat_z_iso_functor_comp_assoc _ _ _)).
      use (nat_z_iso_comp (post_whisker_nat_z_iso p _) _).
      use (nat_z_iso_comp (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _))).
      apply (pre_whisker_nat_z_iso _ q).
    }
    use (nat_z_iso_comp (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _))).
    use (nat_z_iso_comp (pre_whisker_nat_z_iso _ _) _).
    2: {
      use (nat_z_iso_comp (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _))).
      use (pre_whisker_nat_z_iso _ _).
      2: apply LRB_composition_comm.
    }
    use (nat_z_iso_comp (pre_whisker_nat_z_iso _ _) _).
    2: apply (nat_z_iso_functor_comp_assoc _ _ _).
    use (nat_z_iso_comp (nat_z_iso_functor_comp_assoc _ _ _)).
    use (nat_z_iso_comp (post_whisker_nat_z_iso _ _) _).
    2: {
      use (nat_z_iso_comp (nat_z_iso_functor_comp_assoc _ _ _)).
      use tpair.
      - exact (rassociator_transf x y z w).
      - intro ; apply is_z_iso_rassociator.
    }
    use (nat_z_iso_comp _ (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _))).
    use (nat_z_iso_comp _ (post_whisker_nat_z_iso q' _)).
    use (nat_z_iso_comp _ (nat_z_iso_functor_comp_assoc _ _ _)).
    use (nat_z_iso_comp _ (pre_whisker_nat_z_iso _ _)).
    3: apply nat_z_iso_inv, LRB_composition_comm.
    apply nat_z_iso_inv, nat_z_iso_functor_comp_assoc.
  Defined.

  Lemma LRB_lunitor_pre_simpl {x y : B} (f : B⟦x,y⟧)
    :  pr1 (LRB_lunitor_nat_z_iso_pre x y) f = (pr1 (LRB_composition_comm x x y) (id₁ x : hom _ _, f : hom _ _) · #(η_{x,y}) (lunitor f)).
  Proof.
    cbn.
    rewrite ! id_left.
    etrans. { apply maponpaths_2, maponpaths, binprod_id. }
    etrans. { apply maponpaths_2, functor_id. }
    refine (id_left _ @ _).
    now rewrite id_right.
  Qed.

  Lemma LRB_runitor_pre_simpl {x y : B} (f : B⟦x,y⟧)
    :  pr1 (LRB_runitor_nat_z_iso_pre x y) f
       = (pr1 (LRB_composition_comm x y y) (_,_)) · #(η_{x,y}) (runitor f).
  Proof.
    cbn.
    rewrite ! id_left.
    etrans. { apply maponpaths_2, maponpaths, binprod_id. }
    etrans. { apply maponpaths_2, functor_id. }
    refine (id_left _ @ _).
    now rewrite id_right.
  Qed.

  Definition LRB_associator_nat_z_iso
             (x y z w : B)
    : nat_z_iso
        (functor_composite
         (functor_composite
            (precategory_binproduct_assoc
               (R (hom (C := B) x y))
               (R (hom (C := B) y z))
               (R (hom (C := B) z w))
            )
            (pair_functor (LRB_composition x y z)
                          (functor_identity (R (hom z w)))
            )
         )
         (LRB_composition x z w)
        )
        (functor_composite
           (pair_functor
              (functor_identity (R (hom (C := B) x y)))
              (LRB_composition y z w))
           (LRB_composition x y w)).
  Proof.
    use lift_nat_z_iso_along.
    - exact ((hom x y) ⊠ ((hom y z) ⊠ (hom z w))).
    - repeat (apply pair_functor) ; apply (η (hom _ _)).
    - repeat (apply pair_functor_eso) ; apply eso.
    - repeat (apply pair_functor_ff) ; apply ff.
    - exact (LRB_associator_nat_z_iso_pre x y z w).
  Defined.

  Let eso3 := λ C1 C2 C3 : category, pair_functor_eso _ _ (eso C1) (pair_functor_eso _ _ (eso C2) (eso C3)).
  Let ff3 := λ C1 C2 C3 : category, pair_functor_ff _ _ (ff C1) (pair_functor_ff _ _ (ff C2) (ff C3)).

  Lemma LRB_associator_comm (x y z w : B)
    : pre_whisker (pair_functor (η_{x,y}) (pair_functor (η_{y,z}) (η (hom z w))))
         (lift_nat_trans_along (R (hom x w))
            (pair_functor (η_{x,y}) (pair_functor (η_{y,z}) (η (hom z w))))
            (eso3 _ _ _)
            (ff3 _ _ _)
            (LRB_associator_nat_z_iso_pre x y z w)
         )
       = LRB_associator_nat_z_iso_pre x y z w.
  Proof.
    apply (lift_nat_trans_along_comm _ _ _ _ (LRB_associator_nat_z_iso_pre x y z w)).
  Defined.

  Definition LRB_associator_pre_simpl_mor {x y z w : B} (f : B⟦x,y⟧) (g : B⟦y,z⟧) (h : B⟦z,w⟧)
    : R (hom x w)
 ⟦ (pair_functor (η_{x,y}) (pair_functor (η_{y,z}) (η (hom z w)))
    ∙ ((precategory_binproduct_assoc (R (hom x y)) (R (hom y z)) (R (hom z w))
        ∙ pair_functor (LRB_composition x y z) (functor_identity (R (hom z w))))
       ∙ LRB_composition x z w)) (f : hom x y, (g : hom y z, h : hom z w)),
 (pair_functor (η_{x,y}) (pair_functor (η_{y,z}) (η (hom z w)))
  ∙ (pair_functor (functor_identity (R (hom x y))) (LRB_composition y z w) ∙ LRB_composition x y w))
   (f : hom x y, (g : hom y z, h : hom z w)) ⟧.
  Proof.
    refine (#(LRB_composition x z w) (pr1 (LRB_composition_comm x y z) (f : hom _ _ , g : hom _ _) #, identity _) · _).
    refine (_ · #( LRB_composition x y w) (identity _ #, pr1 (nat_z_iso_inv (LRB_composition_comm y z w)) (g : hom _ _ , h : hom _ _))).
    cbn.
    refine (pr1 (LRB_composition_comm x z w) (f · g : hom _ _ , h : hom _ _) · _).
    refine (_ · pr1 (nat_z_iso_inv (LRB_composition_comm x y w)) (f : hom _ _ , g · h : hom _ _)).
    apply (#(η (hom x w))).
    exact (rassociator f g h).
  Defined.

  Lemma LRB_associator_pre_simpl
        {x y z w : B} (f : B⟦x,y⟧) (g : B⟦y,z⟧) (h : B⟦z,w⟧)
    : pr1 (LRB_associator_nat_z_iso_pre x y z w) (f : hom _ _, (g : hom _ _, h : hom _ _))
      = LRB_associator_pre_simpl_mor f g h.
  Proof.
    cbn.
    unfold LRB_associator_pre_simpl_mor.
    rewrite ! id_left.
    rewrite ! id_right.
    rewrite ! assoc.
    rewrite id2_left.
    do 4 (apply maponpaths_2).
    apply maponpaths.
    cbn.
    use total2_paths_f.
    - cbn ; refine (_ @ id_left _).
      apply maponpaths_2.
      etrans. { apply maponpaths, binprod_id. }
      apply functor_id.
    - now rewrite transportf_const.
  Qed.

  Definition LRB_associator
             {x y z w : B}
             (f : R (hom x y))
             (g : R (hom y z))
             (h : R (hom z w))
    : z_iso (C := R (hom x w))
            (LRB_composition _ _ _ (LRB_composition _ _ _ (f,g), h))
            (LRB_composition _ _ _ (f, LRB_composition _ _ _ (g,h))).
  Proof.
    exists (pr1 (LRB_associator_nat_z_iso x y z w) (f,(g,h))).
    exists (pr1 (pr2 (LRB_associator_nat_z_iso x y z w) (f,(g,h)))).
    split ; apply (pr2 (LRB_associator_nat_z_iso x y z w) (f,(g,h))).
  Defined.

  Definition LRB_prebicat_2_id_comp_struct
    : prebicat_2_id_comp_struct LRB_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - exact (λ x y f, identity f).
    - exact (λ x y f, pr1 (LRB_lunitor f)).
    - exact (λ x y f, pr1 (LRB_runitor f)).
    - intro ; intros ; apply LRB_lunitor.
    - intro ; intros ; apply LRB_runitor.
    - intro ; intros ; apply LRB_associator.
    - intro ; intros ; apply LRB_associator.
    - exact (λ x y f g h α β, α · β).
    - exact (λ x y z f g1 g2 α, LRB_lwhisker f α).
    - exact (λ x y z f1 f2 g α, LRB_rwhisker α g).
  Defined.

  Definition LRB_data : prebicat_data.
  Proof.
    use make_prebicat_data.
    - exact LRB_prebicat_1_id_comp_cells.
    - exact LRB_prebicat_2_id_comp_struct.
  Defined.

  Lemma prewhisker_LRB_lunitor {x y : B} (f : B⟦x,y⟧)
    : pr1 (LRB_lunitor (η_{x,y} f))
      = LRB_rwhisker (id₁ (η (hom x x) (id₁ x))) (η_{x,y} f)
                     · pr1 (LRB_composition_comm x x y)
                     (make_catbinprod (C := hom x x) (D := hom x y) (id₁ x) f)
                     · # (η_{x,y}) (lunitor f).
  Proof.
    refine (toforallpaths _ _ _ (base_paths _ _ (LRB_lunitor_comm x y)) f @ _).
    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply (! functor_id (LRB_composition_curry2 x x y (η_{x,y} f)) _).
    }
    rewrite id_left.
    unfold LRB_lunitor_nat_z_iso_pre.
    cbn.
    rewrite ! id_left.
    etrans. {
      apply maponpaths_2.
      etrans. { apply maponpaths, binprod_id. }
      apply functor_id.
    }
    now rewrite id_left, id_right.
  Qed.

  Lemma prewhisker_LRB_runitor {x y : B} (f : B⟦x,y⟧)
    :  pr1 (LRB_runitor (η_{x,y} f))
       = LRB_lwhisker (η_{x,y} f) (id₁ (η (hom y y) (id₁ y)))
                      · pr1 (LRB_composition_comm x y y)
                      (make_catbinprod (C := hom x y) (D := hom y y) f (id₁ y))
                      · # (η_{x,y}) (runitor f).
  Proof.
    refine (toforallpaths _ _ _ (base_paths _ _ (LRB_runitor_comm x y)) f @ _).
    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply (! functor_id (LRB_composition_curry1 x y y (η_{x,y} f)) _).
    }
    rewrite id_left.
    unfold LRB_runitor_nat_z_iso_pre.
    cbn.
    rewrite ! id_left.
    etrans. {
      apply maponpaths_2.
      etrans. { apply maponpaths, binprod_id. }
      apply functor_id.
    }
    now rewrite id_left, id_right.
  Qed.

  Lemma prewhisker_LRB_associator'
        {x y z w : B}
        (f : B ⟦ x, y ⟧)
        (g : B ⟦ y, z ⟧)
        (h : B ⟦ z, w ⟧)
    : pr1 (LRB_associator (η_{x,y} f) (η_{y,z} g) (η (hom z w) h)) = LRB_associator_pre_simpl_mor f g h.
  Proof.
    refine ((toforallpaths _ _ _ (base_paths _ _ (LRB_associator_comm x y z w)) (f : hom _ _, (g : hom _ _, h : hom _ _))) @ _).
    apply (LRB_associator_pre_simpl f g h).
  Qed.

  Lemma prewhisker_LRB_associator
        {x y z w : B}
        (f : B ⟦ x, y ⟧)
        (g : B ⟦ y, z ⟧)
        (h : B ⟦ z, w ⟧)
    : # (LRB_composition x y w) (id₁ (η_{x,y} f) #, pr1 (LRB_composition_comm y z w) (g : hom _ _, h : hom _ _))
        · pr1 (LRB_composition_comm x y w) (f : hom _ _, g · h : hom _ _) · # (η (hom x w)) (lassociator f g h) =
        pr1 (pr2 (LRB_associator_nat_z_iso x y z w) (η_{x,y} f, (η_{y,z} g, η (hom z w) h)))
            · # (LRB_composition x z w)
            (make_dirprod
               (pr1 (LRB_composition_comm x y z) (f : hom _ _, g : hom _ _))
               (id₁ (η (hom z w) h))
              : R (hom x z) ⊠ R (hom z w) ⟦((pair_functor (η_{x,y}) (η_{y,z}) ∙ LRB_composition x y z) (f : hom _ _, g : hom _ _) ,  η (hom z w) h), ((hcomp_functor ∙ η (hom x z)) (f : hom _ _, g : hom _ _), η (hom z w) h) ⟧
            )
            · pr1 (LRB_composition_comm x z w) (f · g : hom _ _, h : hom _ _).
  Proof.
    etrans.
    2: apply assoc.

    use (z_iso_inv_to_left _ _ _ (z_iso_inv (_ ,, pr2 (LRB_associator_nat_z_iso x y z w) (η_{x,y} f, (η_{y,z} g, η (hom z w) h)) : z_iso _ _))).
    etrans. {
      apply maponpaths_2.
      apply (toforallpaths _ _ _ (base_paths _ _ (LRB_associator_comm x y z w)) (f : hom _ _, (g : hom _ _ , h : hom _ _))).
    }

    cbn.
    rewrite ! id_left, ! id_right.
    etrans. {
      do 2 apply maponpaths_2.
      apply maponpaths.
      do 2 apply maponpaths_2.
      etrans. { apply maponpaths, binprod_id. }
      apply functor_id.
    }
    rewrite id_left, id2_left, ! assoc'.
    apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    etrans. {
      do 2 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply pathsinv0, (functor_comp (LRB_composition x y w)).
    }
    etrans. {
      do 2 apply maponpaths.
      apply maponpaths_2.
      cbn.
      etrans. {
        do 2 apply maponpaths.
        apply (pr2 (pr2 (LRB_composition_comm y z w) (g : hom _ _, h : hom _ _))).
      }
      rewrite id_left.
      apply (functor_id (LRB_composition x y w)).
    }
    rewrite id_left.
    etrans. {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply  (pr2 (LRB_composition_comm x y w) (f : hom _ _, g · h : hom _ _)).
    }
    rewrite id_left.
    etrans. { apply pathsinv0, (functor_comp (η (hom x w))). }
    etrans. { apply maponpaths, rassociator_lassociator. }
    apply (functor_id (η (hom x w))).
  Qed.

  Lemma prewhisker_LRB_associator_co
        {x y z w : B}
        (f : B ⟦ x, y ⟧)
        (g : B ⟦ y, z ⟧)
        (h : B ⟦ z, w ⟧)
    : # (LRB_composition x z w) (pr1 (LRB_composition_comm x y z) (f : hom _ _, g : hom _ _) #, id₁ (η (hom z w) h) )
        · pr1 (LRB_composition_comm x z w) (f  · g : hom _ _, h : hom _ _) · # (η (hom x w)) (rassociator f g h) =
        ((LRB_associator_nat_z_iso x y z w) (η_{x,y} f, (η_{y,z} g, η (hom z w) h)))
            · # (LRB_composition x y w)
            (make_dirprod
               (id₁ (η_{x,y} f))
               (pr1 (LRB_composition_comm y z w) (g : hom _ _, h : hom _ _))
              : R (hom x y) ⊠ R (hom y w)⟦(_,_),(_,_)⟧
            )
            · pr1 (LRB_composition_comm x y w) (f : hom _ _, g · h: hom _ _).
  Proof.
    set (l := prewhisker_LRB_associator f g h).

    transparent assert (l1 : (is_z_isomorphism (#η_{ x, w} (rassociator f g h)))).
    {
      use functor_on_is_z_isomorphism.
      apply is_z_iso_rassociator.
    }

    apply pathsinv0.
    use (z_iso_inv_on_left _ _ _ _ (z_iso_inv (_,,l1))).

    transparent assert (l2 : (is_z_isomorphism (LRB_associator_nat_z_iso x y z w (η_{ x, y} f, (η_{ y, z} g, η_{ z, w} h))))).
    {
      apply LRB_associator_nat_z_iso.
    }

    rewrite ! assoc'.
    apply pathsinv0, (z_iso_inv_on_right _ _ _ (z_iso_inv (_,,l2))).

    rewrite ! assoc' in l.
    exact l.
  Qed.

  Lemma LRB_vcomp_lunitor
        {x y : B}
        {f g : R (hom x y)}
        (α : R(hom x y)⟦f,g⟧)
    : LRB_lwhisker (η (hom x x) (identity x)) α · LRB_lunitor g
       = pr1 (LRB_lunitor f) · α.
  Proof.
    use (factor_through_squash _ _ (eso (hom x y) f)).
    { apply homset_property. }
    intros [f0 pf].
    induction (isotoid _ (pr2 (R (hom x y))) pf).
    use (factor_through_squash _ _ (eso (hom x y) g)).
    { apply homset_property. }
    intros [g0 pg].
    induction (isotoid _ (pr2 (R (hom x y))) pg).
    clear pf pg.

    etrans. {
      apply maponpaths.
      exact (toforallpaths _ _ _ (base_paths _ _ (LRB_lunitor_comm _ _)) g0).
    }

    assert (α' : ∑ α0 : (hom x y)⟦f0,g0⟧, #(η_{x,y}) α0 = α).
    { apply (ff_{x,y} f0 g0). }
    induction α' as [α0 αp].
    induction αp.

    etrans.
    2: apply maponpaths_2, (! prewhisker_LRB_lunitor f0).
    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      apply (functor_comp (η_{x,y})).
    }
    etrans.
    2: {
      do 2 apply maponpaths.
      apply (vcomp_lunitor f0 g0 α0).
    }

    etrans. { apply maponpaths, (LRB_lunitor_pre_simpl g0). }

    etrans.
    2: apply maponpaths, pathsinv0, (functor_comp (η_{x,y})).
    rewrite ! assoc.
    apply maponpaths_2.

    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply pathsinv0, (functor_id (LRB_composition_curry2 x x y (η_{x,y} f0))).
    }
    rewrite id_left.
    refine (_ @ pr21 (LRB_composition_comm x x y) _ _ (id2 (id₁ x) : (hom _ _)⟦_,_⟧ #, α0) @ _) ; cbn.
    - apply maponpaths_2, maponpaths, maponpaths_2, pathsinv0, (functor_id (η (hom x x))).
    - do 2 apply maponpaths.
      apply pathsinv0, lwhisker_hcomp.
  Qed.

  Lemma LRB_vcomp_runitor
        {x y : B}
        {f g : R (hom x y)}
        (α : R(hom x y)⟦f,g⟧)
    : LRB_rwhisker α (η (hom y y) (identity y)) · LRB_runitor g
      = pr1 (LRB_runitor f) · α.
  Proof.
    use (factor_through_squash _ _ (eso (hom x y) f)).
    { apply homset_property. }
    intros [f0 pf].
    induction (isotoid _ (pr2 (R (hom x y))) pf).
    use (factor_through_squash _ _ (eso (hom x y) g)).
    { apply homset_property. }
    intros [g0 pg].
    induction (isotoid _ (pr2 (R (hom x y))) pg).
    clear pf pg.

    etrans. {
      apply maponpaths.
      exact (toforallpaths _ _ _ (base_paths _ _ (LRB_runitor_comm _ _)) g0).
    }

    assert (α' : ∑ α0 : (hom x y)⟦f0,g0⟧, #(η_{x,y}) α0 = α).
    { apply (ff_{x,y} f0 g0). }
    induction α' as [α0 αp].
    induction αp.

    etrans.
    2: apply maponpaths_2, (! prewhisker_LRB_runitor f0).
    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      apply (functor_comp (η_{x,y})).
    }
    etrans.
    2: {
      do 2 apply maponpaths.
      apply (vcomp_runitor f0 g0 α0).
    }

    etrans. { apply maponpaths, (LRB_runitor_pre_simpl g0). }

    etrans.
    2: apply maponpaths, pathsinv0, (functor_comp (η_{x,y})).
    rewrite ! assoc.
    apply maponpaths_2.

    etrans.
    2: {
      do 2 apply maponpaths_2.
      apply pathsinv0, (functor_id (LRB_composition_curry1 x y y (η_{x,y} f0))).
    }
    rewrite id_left.
    refine (_ @ pr21 (LRB_composition_comm x y y) _ _ (α0 #, id2 (id₁ y) : (hom _ _)⟦_,_⟧ ) @ _) ; cbn.
    - unfold functor_fix_snd_arg_mor.
      apply maponpaths_2, maponpaths, maponpaths, pathsinv0, (functor_id (η (hom y y))).
    - do 2 apply maponpaths.
      apply pathsinv0, rwhisker_hcomp.
  Qed.

  Lemma LRB_lwhisker_lwhisker
        {x y z w : B}
        (f : R (hom x y)) (g : R (hom y z))
        {h i : R (hom z w)}
        (α : R (hom z w)⟦h,i⟧)
    : LRB_lwhisker f (LRB_lwhisker g α) · inv_from_z_iso (LRB_associator f g i)
      = inv_from_z_iso (LRB_associator f g h) · LRB_lwhisker (LRB_composition _ _ _ (f,g)) α.
  Proof.
    apply pathsinv0, z_iso_inv_on_right.
    rewrite assoc.
    apply z_iso_inv_on_left.

    use (factor_through_squash _ _ (eso (hom x y) f)).
    { apply homset_property. }
    intros [f0 pf].
    induction (isotoid _ (pr2 (R (hom x y))) pf).
    use (factor_through_squash _ _ (eso (hom _ _) g)).
    { apply homset_property. }
    intros [g0 pg].
    induction (isotoid _ (pr2 (R (hom _ _))) pg).
    use (factor_through_squash _ _ (eso (hom _ _) h)).
    { apply homset_property. }
    intros [h0 ph].
    induction (isotoid _ (pr2 (R (hom _ _))) ph).
    use (factor_through_squash _ _ (eso (hom _ _) i)).
    { apply homset_property. }
    intros [i0 pi].
    induction (isotoid _ (pr2 (R (hom _ _))) pi).
    clear pf pg ph pi.

    assert (α' : ∑ α0 : (hom _ _)⟦h0,i0⟧, #(η (hom _ _)) α0 = α).
    { apply (ff (hom _ _) h0 i0). }
    induction α' as [α0 αp].
    induction αp.

    set (t := λ x y z w f g h, toforallpaths _ _ _ (base_paths _ _ (LRB_associator_comm x y z w)) (f , (g, h))).

    etrans. { apply maponpaths_2, t. }
    etrans.
    2: { apply maponpaths, pathsinv0, t. }

    etrans.
    { apply maponpaths_2, (LRB_associator_pre_simpl f0 g0 h0). }
    etrans.
    2: { apply maponpaths, (! LRB_associator_pre_simpl f0 g0 i0). }

    assert (p : (LRB_lwhisker (η_{y,z} g0) (# (η (hom z w)) α0))
                = (LRB_composition_comm y z w (g0 , h0))
                    · #(η (hom _ _)) (lwhisker g0 α0)
                    · (nat_z_iso_inv (LRB_composition_comm y z w)) (g0 , i0)).
    {
      cbn.
      etrans.
      2: {
        apply maponpaths_2.
        refine (pr21 (LRB_composition_comm y z w) _ _ (id2 g0 : (hom _ _)⟦_,_⟧ #, α0) @ _) ; cbn.
        do 2 apply maponpaths.
        apply hcomp_identity_left.
      }

      cbn.
      rewrite assoc'.
      etrans.
      2: {
        apply maponpaths.
        apply pathsinv0, (pr2 (LRB_composition_comm y z w) (g0, i0)).
      }
      rewrite (functor_id (η_{y,z})).
      apply (! id_right _).
    }

    etrans. {
      apply maponpaths.
      unfold LRB_lwhisker.
      apply maponpaths.
      apply p.
    }

    unfold LRB_associator_pre_simpl_mor.
    cbn.

    etrans. {
      do 3 apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      refine (_ @ pr21 (nat_z_iso_inv (LRB_composition_comm y z w)) _ _  (identity g0 #, α0)).
      cbn.
      apply maponpaths_2, maponpaths, lwhisker_hcomp.
    }
    do 2 rewrite assoc.
    etrans. {
      do 3 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply (pr2 ((pr2 (LRB_composition_comm y z w)) (g0, h0))).
    }
    rewrite id_left.
    cbn.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      2: { apply functor_comp. }
      cbn.
      now rewrite id_left, id_right.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      etrans. { apply pathsinv0, functor_comp. }
      cbn.
      rewrite id_right.
      do 2 apply maponpaths.
      exact (! pr21 (nat_z_iso_inv (LRB_composition_comm y z w)) _ _ ( (id₂ g0) #, α0)).
    }
    simpl.

    etrans. {
      apply maponpaths.
      etrans. { apply maponpaths, maponpaths_2, (! id_left _). }
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition x y w)).
    }
    rewrite ! assoc.
    apply maponpaths_2.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      refine (_ @ ! pr21 (nat_z_iso_inv (LRB_composition_comm x y w)) _ _ (id₁ f0 #, (α0 ⋆⋆ id₂ g0) : (hom _ _)⟦_,_⟧)).
      cbn.
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply pathsinv0, (functor_id (η_{x,y})).
    }
    rewrite ! assoc.
    apply maponpaths_2.

    cbn.
    do 2 rewrite hcomp_identity_left.
    etrans. {
      rewrite assoc'.
      apply maponpaths.
      etrans. { apply pathsinv0, functor_comp. }
      apply maponpaths.
      apply lwhisker_lwhisker_rassociator.
    }
    etrans. { apply maponpaths, (functor_comp (η (hom _ _))). }
    rewrite ! assoc.
    apply maponpaths_2.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      refine (_ @ ! pr21 (LRB_composition_comm x z w) _ _ (id2 (f0 · g0) : (hom _ _)⟦_,_⟧ #, α0)).
      cbn.
      do 2 apply maponpaths.
      apply pathsinv0, hcomp_identity_left.
    }
    cbn.
    rewrite assoc.
    apply maponpaths_2.
    etrans. { apply pathsinv0, functor_comp. }
    cbn.
    apply maponpaths.
    use total2_paths_f.
    - cbn.
      rewrite (functor_id (η (hom x z))).
      apply id_right.
    - rewrite transportf_const.
      cbn.
      apply id_left.
  Qed.

  Lemma LRB_rwhisker_lwhisker
        {x y z w : B}
        (f : R (hom x y))
        {g h : R (hom y z)}
        (α : R (hom y z)⟦g,h⟧)
        (i : R (hom z w))
    : LRB_lwhisker f (LRB_rwhisker α i) · inv_from_z_iso (LRB_associator f h i)
      = inv_from_z_iso (LRB_associator f g i) · (LRB_rwhisker (LRB_lwhisker f α) i).
  Proof.
    apply pathsinv0, z_iso_inv_on_right.
    rewrite assoc.
    apply z_iso_inv_on_left.

    use (factor_through_squash _ _ (eso (hom x y) f)).
    { apply homset_property. }
    intros [f0 pf].
    induction (isotoid _ (pr2 (R (hom x y))) pf).
    use (factor_through_squash _ _ (eso (hom _ _) g)).
    { apply homset_property. }
    intros [g0 pg].
    induction (isotoid _ (pr2 (R (hom _ _))) pg).
    use (factor_through_squash _ _ (eso (hom _ _) h)).
    { apply homset_property. }
    intros [h0 ph].
    induction (isotoid _ (pr2 (R (hom _ _))) ph).
    use (factor_through_squash _ _ (eso (hom _ _) i)).
    { apply homset_property. }
    intros [i0 pi].
    induction (isotoid _ (pr2 (R (hom _ _))) pi).
    clear pf pg ph pi.

    assert (α' : ∑ α0 : (hom _ _)⟦g0,h0⟧, #(η (hom _ _)) α0 = α).
    { apply (ff (hom _ _) g0 h0). }
    induction α' as [α0 αp].
    induction αp.

    set (t := λ x y z w f g h, toforallpaths _ _ _ (base_paths _ _ (LRB_associator_comm x y z w)) (f , (g, h))).

    etrans. { apply maponpaths_2, t. }
    etrans.
    2: { apply maponpaths, pathsinv0, t. }

    etrans.
    { apply maponpaths_2, (LRB_associator_pre_simpl f0 g0 i0). }
    etrans.
    2: { apply maponpaths, (! LRB_associator_pre_simpl f0 h0 i0). }

    unfold LRB_associator_pre_simpl_mor ; cbn.
    unfold functor_fix_snd_arg_mor.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      2: { apply functor_comp. }
      cbn.
      apply maponpaths.
      rewrite id_right.

      etrans.
      2: {
        do 2 apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        apply (functor_id (η_{x,y})).
      }

      etrans.
      2: {
        apply maponpaths.
        apply (functor_id (η (hom z w))).
      }
      apply maponpaths_2.
      exact (! pr21 (LRB_composition_comm x y z) _ _ ((id₁ f0) #, α0)).
    }

    etrans.
    2: {
      apply maponpaths_2.
      etrans.
      2: { do 2 apply maponpaths. apply id_left. }
      etrans.
      2: { apply maponpaths, pathsinv0, binprod_comp. }
      cbn.
      apply pathsinv0.

      set (t1 := pr11 (LRB_composition_comm x y z) (f0, g0)).
      set (t2 := # (η (hom z w)) (id₂ i0)).

      set (s1 :=  # (η (hom x z)) (α0 ⋆⋆ id₂ f0)).
      set (s2 :=  id₁ (η (hom z w) i0)).
      set (t3 := (t1 #, s2)).
      set (s3 := (s1 #, t2)).
      exact (functor_comp (LRB_composition x z w) t3 s3).
    }

    rewrite ! assoc'.
    apply maponpaths.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      exact (! pr21 (LRB_composition_comm x z w) _ _ ( (α0 ⋆⋆ id₂ f0) : (hom _ _)⟦_,_⟧ #, id2 i0)).
    }

    rewrite assoc'.
    apply maponpaths.
    cbn.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      2: { apply functor_comp. }
      apply maponpaths.
      refine (rwhisker_lwhisker_rassociator _ _ _ _ _ _ _ _ _ @ _).
      apply maponpaths_2.
      rewrite hcomp_identity_right.
      now rewrite hcomp_identity_left.
    }

    etrans.
    2: {
      apply maponpaths_2.
      apply pathsinv0, (functor_comp (η (hom x w))).
    }

    rewrite ! assoc'.
    apply maponpaths.
    etrans. {
      apply maponpaths.
      etrans. { apply pathsinv0, functor_comp. }
      cbn.
      rewrite id_right.
      do 2 apply maponpaths.
      refine (_ @ ! pr21 (nat_z_iso_inv (LRB_composition_comm y z w)) _ _ (α0 #, id2 i0)).
      cbn.
      do 3 apply maponpaths.
      apply pathsinv0, (functor_id (η (hom z w))).
    }
    cbn.
    etrans. {
      do 2 apply maponpaths.
      apply maponpaths_2, pathsinv0, id_right.
    }

    etrans. {
      apply maponpaths.
      refine (_ @ functor_comp (LRB_composition x y w) (id₁ (η_{x,y} f0) #, # (η (hom y w)) (id₂ i0 ⋆⋆ α0)) (_ #,  is_z_isomorphism_mor (pr2 (LRB_composition_comm y z w) (h0, i0)))).
      apply maponpaths.
      rewrite id_right.
      cbn.
      apply maponpaths_2.
      apply pathsinv0, id_right.
    }

    rewrite ! assoc.
    apply maponpaths_2.

    etrans. {
      refine (_ @ ! pr21 (nat_z_iso_inv (LRB_composition_comm x y w)) _ _ (id2 f0 #, (id₂ i0 ⋆⋆ α0) : (hom _ _)⟦_,_⟧)).
      cbn.
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply pathsinv0, (functor_id (η_{x,y})).
    }

    apply maponpaths_2.
    cbn.
    apply maponpaths.
    rewrite hcomp_identity_right.
    now rewrite hcomp_identity_left.
  Qed.

  Lemma LRB_rwhisker_rwhisker
        {x y z w : B}
        {f g : R (hom x y)}
        (α : R (hom x y)⟦f,g⟧)
        (h : R (hom y z))
        (i : R (hom z w))
    : inv_from_z_iso (LRB_associator f h i) · LRB_rwhisker (LRB_rwhisker α h) i
      = LRB_rwhisker α (LRB_composition _ _ _ (h, i)) · inv_from_z_iso (LRB_associator g h i).
  Proof.
    apply z_iso_inv_on_right.
    rewrite assoc.
    apply z_iso_inv_on_left.

    use (factor_through_squash _ _ (eso (hom _ _) f)).
    { apply homset_property. }
    intros [f0 pf].
    induction (isotoid _ (pr2 (R (hom x y))) pf).
    use (factor_through_squash _ _ (eso (hom _ _) g)).
    { apply homset_property. }
    intros [g0 pg].
    induction (isotoid _ (pr2 (R (hom _ _))) pg).
    use (factor_through_squash _ _ (eso (hom _ _) h)).
    { apply homset_property. }
    intros [h0 ph].
    induction (isotoid _ (pr2 (R (hom _ _))) ph).
    use (factor_through_squash _ _ (eso (hom _ _) i)).
    { apply homset_property. }
    intros [i0 pi].
    induction (isotoid _ (pr2 (R (hom _ _))) pi).
    clear pf pg ph pi.

    assert (α' : ∑ α0 : (hom _ _)⟦f0,g0⟧, #(η (hom _ _)) α0 = α).
    { apply (ff (hom _ _) f0 g0). }
    induction α' as [α0 αp].
    induction αp.

    set (t := λ x y z w f g h, toforallpaths _ _ _ (base_paths _ _ (LRB_associator_comm x y z w)) (f , (g, h))).

    etrans. { apply maponpaths_2, t. }
    etrans.
    2: { apply maponpaths, pathsinv0, t. }

    etrans.
    { apply maponpaths_2, (LRB_associator_pre_simpl f0 h0 i0). }
    etrans.
    2: { apply maponpaths, (! LRB_associator_pre_simpl g0 h0 i0). }
    unfold LRB_associator_pre_simpl_mor ; cbn.
    unfold functor_fix_snd_arg_mor.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      2: { apply functor_comp. }
      cbn.
      apply maponpaths.
      rewrite id_right.

      etrans.
      2: {
        do 2 apply maponpaths_2.
        do 2 apply maponpaths.
        apply (functor_id (η_{y,z})).
      }

      etrans.
      2: {
        apply maponpaths.
        apply (functor_id (η (hom z w))).
      }
      apply maponpaths_2.
      exact (! pr21 (LRB_composition_comm x y z) _ _ (α0 #, (id₁ h0))).
    }

    etrans.
    2: {
      apply maponpaths_2.
      etrans.
      2: { do 2 apply maponpaths. apply id_left. }
      etrans.
      2: { apply maponpaths, pathsinv0, binprod_comp. }
      cbn.
      apply pathsinv0.

      set (t1 := pr11 (LRB_composition_comm x y z) (f0, h0)).
      set (t2 := # (η (hom z w)) (id₂ i0)).

      set (s1 :=  # (η (hom x z)) (id₂ h0 ⋆⋆ α0)).
      set (s2 :=  id₁ (η (hom z w) i0)).
      set (t3 := (t1 #, s2)).
      set (s3 := (s1 #, t2)).
      exact (functor_comp (LRB_composition x z w) t3 s3).
    }

    rewrite ! assoc'.
    apply maponpaths.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      exact (! pr21 (LRB_composition_comm x z w) _ _ ( (id₂ h0 ⋆⋆ α0) : (hom _ _)⟦_,_⟧ #, id2 i0)).
    }

    rewrite assoc'.
    apply maponpaths.
    cbn.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      2: { apply functor_comp. }
      apply maponpaths.
      refine (! rwhisker_rwhisker_alt _ _ _  @ _).
      apply maponpaths_2.
      now do 2 rewrite hcomp_identity_right.
    }

    etrans.
    2: {
      apply maponpaths_2.
      apply pathsinv0, (functor_comp (η (hom x w))).
    }

    rewrite ! assoc'.
    apply maponpaths.

    etrans. {
      apply maponpaths.
      etrans. { apply pathsinv0, functor_comp. }
      cbn.
      now rewrite id_right.
    }

    rewrite id_left.
    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.



      refine (! pr21 (nat_z_iso_inv (LRB_composition_comm x y w)) _ _ (α0 #, id2 (h0 · i0) : (hom _ _)⟦_,_⟧) @ _).
      cbn.
      apply maponpaths_2, maponpaths.
      now rewrite hcomp_identity_right.
    }
    cbn.

    rewrite ! assoc'.
    apply maponpaths.
    etrans.
    2: { apply functor_comp. }
    apply maponpaths.
    cbn.
    rewrite id_right.
    rewrite (functor_id (η (hom y w))).
    now rewrite id_left.
  Qed.

  Lemma LRB_runitor_rwhisker
        {x y z : B}
        (f : R (hom x y))
        (g : R (hom y z))
    : inv_from_z_iso (LRB_associator f (η (hom y y) (identity y)) g) · (LRB_rwhisker (LRB_runitor f) g)
      = LRB_lwhisker f (LRB_lunitor g).
  Proof.
    use z_iso_inv_on_right.
    use (factor_through_squash _ _ (eso (hom _ _) f)).
    { apply homset_property. }
    intros [f0 pf].
    induction (isotoid _ (pr2 (R (hom x y))) pf).
    use (factor_through_squash _ _ (eso (hom _ _) g)).
    { apply homset_property. }
    intros [g0 pg].
    induction (isotoid _ (pr2 (R (hom _ _))) pg).
    clear pf pg.

    etrans. {
      unfold LRB_rwhisker.
      apply maponpaths.
      apply prewhisker_LRB_runitor.
    }

    etrans.
    2: {
      unfold LRB_lwhisker.
      do 2 apply maponpaths.
      apply pathsinv0, prewhisker_LRB_lunitor.
    }

    etrans.
    2: apply maponpaths_2, pathsinv0, prewhisker_LRB_associator'.

    cbn.
    unfold functor_fix_snd_arg_mor.
    unfold LRB_associator_pre_simpl_mor.
    cbn.

    etrans.
    2: {
      do 3 apply maponpaths.
      do 2 apply maponpaths_2.
      etrans.
      2: { apply maponpaths, binprod_id. }
      apply pathsinv0, (functor_id (LRB_composition y y z)).
    }
    rewrite id_left.

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: apply (functor_comp (LRB_composition x y z)).
      apply maponpaths.
      cbn.
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply pathsinv0, (pr2 (pr2 (LRB_composition_comm y y z) (id₁ y : hom _ _, g0))).
    }
    do 2 rewrite id_left.
    etrans.
    2: {
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite (! functor_id  (η_{x,y}) _).
      apply (pr21 (nat_z_iso_inv (LRB_composition_comm x y z)) _ _ (_ #, lunitor g0 : (hom _ _)⟦_,_⟧)).
    }
    simpl.
    etrans.
    2: {
      do 2 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      2: apply functor_comp.
      apply maponpaths.
      refine (! lunitor_lwhisker _ _ @ _).
      apply maponpaths.
      apply pathsinv0, hcomp_identity_left.
    }

    etrans. {
      apply maponpaths.
      do 3 apply maponpaths_2.
      apply (functor_id (LRB_composition x y y)).
    }
    rewrite id_left.

    etrans. {
      do 2 apply maponpaths.
      apply (! id_right _).
    }

    etrans. {
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition x y z)).
    }

    apply maponpaths.

    etrans.
    2: {
      apply maponpaths.
      rewrite <- hcomp_identity_right.
      exact (! pr21 (nat_z_iso_inv (LRB_composition_comm x y z)) _ _ (runitor f0 : (hom _ _)⟦_,_⟧ #, id2 g0)).
    }

    cbn.
    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      apply pathsinv0, (pr2 (pr2 (LRB_composition_comm x y z) (f0 · id₁ y : hom _ _, g0))).
    }
    rewrite id_left.
    do 2 apply maponpaths.
    apply pathsinv0, (functor_id (η_{y,z})).
  Qed.

  Definition LRB_associator_comp_l
             {a b c d e : B}
        (f : hom a b)
        (g : hom b c)
        (h : hom c d)
        (i : hom d e)
    :  R (hom a e) ⟦ LRB_composition a d e (LRB_composition a c d (LRB_composition a b c (η (hom a b) f, η (hom b c) g), η (hom c d) h), η (hom d e) i), η (hom a e) ((f · g) · h · i) ⟧.
  Proof.
    use (_ · _).
    2: {
      use (#(LRB_composition a d e)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: {
          use (#(LRB_composition a c d)).
          2: {
            use catbinprodmor.
            4: apply identity.
            2: exact (pr1 (LRB_composition_comm a b c) (f,g)).
          }
        }
      }
    }
    use (_ · _).
    2: {
      use (#(LRB_composition a d e)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: exact (pr1 (LRB_composition_comm a c d) (f·g : hom _ _,h)).
      }
    }
    exact (pr1 (LRB_composition_comm a d e) (f·g·h : hom _ _,i)).
  Defined.

  Definition LRB_associator_comp_l'
             {a b c d e : B}
             (f0 : hom a b)
             (g0 : hom b c)
             (h0 : hom c d)
             (i0 : hom d e)
    : R (hom a e) ⟦ η (hom a e) (f0 · g0 · (h0 · i0)), LRB_composition a c e (LRB_composition a b c (η (hom a b) f0, η (hom b c) g0), LRB_composition c d e (η (hom c d) h0, η (hom d e) i0)) ⟧.
  Proof.
    use (_ · _).
    3: {
      use (#(LRB_composition a c e)).
      2: {
        use catbinprodmor.
        3: exact (pr1 (nat_z_iso_inv (LRB_composition_comm a b c)) (f0,g0)).
        2: exact (pr1 (nat_z_iso_inv (LRB_composition_comm c d e)) (h0,i0)).
      }
    }
    exact (pr1 (nat_z_iso_inv (LRB_composition_comm a c e)) (f0·g0 : hom _ _, h0·i0 : hom _ _)).
  Defined.

  Definition LRB_associator_comp_l_on
             {a b c d e : B}
             (f0 : hom a b)
             (g0 : hom b c)
             (h0 : hom c d)
             (i0 : hom d e)
    :  pr1 (LRB_associator (LRB_composition a b c (η (hom a b) f0, η (hom b c) g0))
                           (η (hom c d) h0) (η (hom d e) i0))
       = LRB_associator_comp_l f0 g0 h0 i0 · #(η (hom a e)) (pr1 (rassociator_transf _ _ _ _) ((f0 · g0 : hom _ _),(h0,i0))) · LRB_associator_comp_l' f0 g0 h0 i0.
  Proof.
    unfold LRB_associator_comp_l, LRB_associator_comp_l'.

    set (n2 := LRB_composition_comm a b c).
    set (n1 := LRB_associator_comm a c d e).

    set (q := toforallpaths _ _ _ (base_paths _ _ n1) (f0 · g0 : hom _ _, (h0, i0))).

    etrans.
    2: {
      apply maponpaths_2.
      unfold n2.
      rewrite assoc'.
      apply maponpaths.
      exact (! prewhisker_LRB_associator_co (f0 · g0) h0 i0).
    }

    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, (pr2 (pr2 (LRB_composition_comm a c e) (f0 · g0 : hom _ _, h0 · i0 : hom _ _))).
    }
    rewrite id_right.
    unfold n2.

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: apply (functor_comp (LRB_composition a c e)).
      apply maponpaths.
      cbn.
      rewrite id_left.
      apply maponpaths, pathsinv0,  (pr2 (LRB_composition_comm c d e) (h0, i0)).
    }

    etrans.
    2: {
      apply maponpaths, maponpaths_2.
      exact (! prewhisker_LRB_associator' (f0 · g0) h0 i0).
    }
    unfold LRB_associator_pre_simpl_mor.

    etrans.
    2: {
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: apply functor_comp.
      cbn.
      rewrite id_left.
      now rewrite id_right.
    }

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      2: apply functor_comp.
      apply maponpaths.
      cbn.
      now rewrite id_right.
    }

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths_2.
      do 2 apply maponpaths.
      exact (id_left (id₁ (η (hom d e) i0))).
    }
    etrans.
    2: {
      apply maponpaths_2.
      etrans.
      2: {
        apply maponpaths.
        apply pathsinv0, binprod_comp.
      }

      apply pathsinv0, (functor_comp (LRB_composition a d e)).
    }

    etrans.
    2: {
      rewrite ! assoc'.
      apply maponpaths.
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      exact (! prewhisker_LRB_associator_co (f0 · g0) h0 i0).
    }

    etrans.
    2: {
      apply maponpaths.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, (pr2 (pr2 (LRB_composition_comm a c e) (f0 · g0 : hom _ _, h0 · i0 : hom _ _))).
    }
    rewrite id_right.

    etrans.
    2: {
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: apply (functor_comp (LRB_composition a c e)).
      apply maponpaths.
      etrans.
      2: apply binprod_comp.
      rewrite id_left.
      apply maponpaths.
      apply pathsinv0, (pr2 (pr2 (LRB_composition_comm c d e) (h0, i0))).
    }

    transparent assert (i1 : (is_z_isomorphism (# (LRB_composition a c e)
         (is_z_isomorphism_mor (pr2 (LRB_composition_comm a b c) (f0, g0))
                               #, id₁ ((pair_functor (η (hom c d)) (η (hom d e)) ∙ LRB_composition c d e) (h0, i0)))))).
    {
      apply functor_on_is_z_isomorphism.
      apply is_z_iso_binprod_z_iso.
      - apply (pr2 (z_iso_inv (_ ,, pr2 (LRB_composition_comm a b c) (f0, g0)))).
      - apply identity_is_z_iso.
    }


    rewrite assoc.
    use (z_iso_inv_on_left _ _ _ _ (z_iso_inv (_ ,, i1))).
    etrans.
    2: {
      apply maponpaths.
      simpl.
      cbn.
      apply idpath.
    }

    set (t := pr21 (LRB_associator_nat_z_iso a c d e)).
    unfold is_nat_trans in t.

    set (tt := t _ _ (pr1 (LRB_composition_comm a b c) (f0, g0) #, (id₁ (η_{ c, d} h0) #, id₁ (η_{ d, e} i0)))).

    refine (tt @ _).
    apply maponpaths.
    (* Opaque LRB_composition. *)
    cbn.
    do 2 apply maponpaths.
    apply (functor_id (LRB_composition c d e)).
  Qed.

  Definition LRB_associator_comp_m
             {a b c d e : B}
        (f : hom a b)
        (g : hom b c)
        (h : hom c d)
        (i : hom d e)
    : R (hom a e) ⟦LRB_composition a d e (LRB_composition a b d (η (hom a b) f, LRB_composition b c d (η (hom b c) g, η (hom c d) h)), η (hom d e) i), η (hom a e) (f · (g · h) · i) ⟧.
  Proof.
    use (_ · _).
    2: {
      use (#(LRB_composition a d e)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: {
          use (#(LRB_composition a b d)).
          2: {
            use catbinprodmor.
            3: apply identity.
            2: exact (pr1 (LRB_composition_comm b c d) (g,h)).
          }
        }
      }
    }
    use (_ · _).
    2: {
      use (#(LRB_composition a d e)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: exact (pr1 (LRB_composition_comm a b d) (f,g·h : hom _ _)).
      }
    }

    exact (pr1 (LRB_composition_comm a d e) ( (f · (g · h)) : hom _ _ , i)).
  Defined.

  Definition LRB_associator_comp_m'
             {a b c d e : B}
             (f : hom a b)
             (g : hom b c)
             (h : hom c d)
             (i : hom d e)
    :  R (hom a e) ⟦ η (hom a e) (f · (g · h · i)),
  LRB_composition a b e
    (η (hom a b) f,
      LRB_composition b d e (LRB_composition b c d (η (hom b c) g, η (hom c d) h), η (hom d e) i)) ⟧.
  Proof.
    use (_ · _).
    3: {
      use (#(LRB_composition a b e)).
      2: {
        use catbinprodmor.
        3: apply identity.
        2: {
          use (#(LRB_composition b d e)).
          2: {
            use catbinprodmor.
            4: apply identity.
            2: exact (pr1 (nat_z_iso_inv (LRB_composition_comm b c d)) (g,h)).
          }
        }
      }
    }
    use (_ · _).
    3: {
      use (#(LRB_composition a b e)).
      2: {
        use catbinprodmor.
        3: apply identity.
        2: exact (pr1 (nat_z_iso_inv (LRB_composition_comm b d e)) (g · h : hom _ _ , i)).
      }
    }

    exact (pr1 (nat_z_iso_inv (LRB_composition_comm a b e)) (f , (g · h · i) : hom _ _)).
  Defined.

  Lemma LRB_associator_comp_m_on
        {a b c d e : B}
        (f : hom a b)
        (g : hom b c)
        (h : hom c d)
        (i : hom d e)
    : pr1 (LRB_associator (η (hom a b) f) (LRB_composition b c d (η (hom b c) g, η (hom c d) h))
                          (η (hom d e) i))
      = LRB_associator_comp_m f g h i · #(η (hom a e)) (pr1 (rassociator_transf _ _ _ _) (f , ((g · h : hom _ _),i))) · LRB_associator_comp_m' f g h i.
  Proof.
    unfold LRB_associator_comp_m, LRB_associator_comp_m'.

    set (n2 := LRB_composition_comm a d e ).
    set (n1 := LRB_associator_comm a b d e).

    set (q := toforallpaths _ _ _ (base_paths _ _ n1) (f, (g·h : hom _ _, i))).

    etrans.
    2: {
      apply maponpaths_2.
      unfold n2.
      rewrite assoc'.
      apply maponpaths.
      exact (! prewhisker_LRB_associator_co _ _ _).
    }

    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      simpl.
      rewrite assoc.
      apply maponpaths_2.
      apply pathsinv0, (pr2 (pr2 (LRB_composition_comm a b e) (f, g · h · i : hom _ _))).
    }
    rewrite id_left.
    etrans.
    2: {
      apply maponpaths_2.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: apply (functor_comp (LRB_composition a b e)).
      apply maponpaths.
      etrans.
      2: apply binprod_comp.
      rewrite id_left.
      apply maponpaths.
      apply pathsinv0,  (pr2 (pr2 (LRB_composition_comm b d e) (g · h : hom _ _, i))).
    }
    etrans.
    2: {
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply pathsinv0, (functor_id (LRB_composition a b e)).
    }
    rewrite id_right.

    set (t := pr21 (LRB_associator_nat_z_iso a b d e)).
    unfold is_nat_trans in t.

    etrans.
    2: {
      apply maponpaths_2.
      exact (! (t _ _ (id₁ (η_{ a, b} f) #, (pr1 (LRB_composition_comm b c d) (g, h) #, id₁ (η_{ d, e} i))))).
    }

    Opaque LRB_composition.
    Opaque LRB_composition_comm.
    Opaque LRB_associator_nat_z_iso.
    cbn.

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: apply (functor_comp (LRB_composition a b e)).
      etrans.
      2: apply maponpaths, binprod_comp.
      rewrite id_left.
      etrans.
      2: {
        do 2 apply maponpaths.
        etrans.
        2: apply (functor_comp (LRB_composition b d e)).
        apply maponpaths.
        etrans.
        2: apply binprod_comp.
        rewrite id_left.
        apply maponpaths_2.
        apply pathsinv0, (pr2 (pr2 (LRB_composition_comm b c d) (g, h))).
      }
      rewrite binprod_id.
      rewrite (functor_id (LRB_composition b d e)).
      now rewrite (functor_id (LRB_composition a b e)).
    }
    apply pathsinv0, id_right.
  Qed.

  Definition LRB_associator_comp_r
             {a b c d e : B}
             (f0 : hom a b)
             (g0 : hom b c)
             (h0 : hom c d)
             (i0 : hom d e)
    : R (hom a e)⟦ LRB_composition a c e (LRB_composition a b c (η (hom a b) f0, η (hom b c) g0), LRB_composition c d e (η (hom c d) h0, η (hom d e) i0)), η (hom a e) (f0 · g0 · (h0 · i0)) ⟧.
  Proof.
    use (_ · _).
    2: {
      use (#(LRB_composition a c e)).
      2: {
        use catbinprodmor.
        4: exact (pr1 (LRB_composition_comm c d e) (h0,i0)).
        2: exact (pr1 (LRB_composition_comm a b c) (f0,g0)).
      }
    }
    exact (pr1 (LRB_composition_comm a c e) (f0 · g0 : hom _ _ ,h0 · i0 : hom _ _)).
  Defined.

  Definition LRB_associator_comp_r'
             {a b c d e : B}
             (f0 : hom a b)
             (g0 : hom b c)
             (h0 : hom c d)
             (i0 : hom d e)
    : R (hom a e) ⟦ η (hom a e) (f0 · (g0 · (h0 · i0))), LRB_composition a b e (η (hom a b) f0, LRB_composition b c e (η (hom b c) g0, LRB_composition c d e (η (hom c d) h0, η (hom d e) i0)))⟧.
  Proof.
    use (_ · _).
    3: {
      use (#(LRB_composition a b e)).
      2: {
        use catbinprodmor.
        3: apply identity.
        2: {
          use (#(LRB_composition b c e)).
          2: {
            use catbinprodmor.
            3: apply identity.
            2: exact (pr1 (nat_z_iso_inv (LRB_composition_comm c d e)) (h0,i0)).
          }
        }
      }
    }
    use (_ · _).
    3: {
      use (#(LRB_composition a b e)).
      2: {
        use catbinprodmor.
        3: apply identity.
        2: exact (pr1 (nat_z_iso_inv (LRB_composition_comm b c e)) (g0,h0 · i0 : hom _ _)).
      }
    }
    exact (pr1 (nat_z_iso_inv (LRB_composition_comm a b e)) (f0, g0 · (h0 · i0) : hom _ _)).
  Defined.

  Definition LRB_associator_comp_r_on
             {a b c d e : B}
             (f0 : hom a b)
             (g0 : hom b c)
             (h0 : hom c d)
             (i0 : hom d e)
    : pr1 (LRB_associator (η (hom a b) f0) (η (hom b c) g0)
                          (LRB_composition c d e (η (hom c d) h0, η (hom d e) i0)))
      =  LRB_associator_comp_r f0 g0 h0 i0 · #(η (hom a e)) (pr1 (rassociator_transf _ _ _ _) (f0 , (g0, (h0 · i0 : hom _ _)))) · LRB_associator_comp_r' f0 g0 h0 i0.
  Proof.

    unfold LRB_associator_comp_r, LRB_associator_comp_r'.

    etrans.
    2: {
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: apply (functor_comp (LRB_composition a b e)).
      etrans.
      2: apply maponpaths, binprod_comp.
      now rewrite id_left.
    }

    etrans.
    2: {
      do 3 apply maponpaths_2.
      etrans.
      2: {
        do 2 apply maponpaths.
        apply id_right.
      }
      etrans.
      2: {
        apply maponpaths.
        apply maponpaths_2.
        apply id_left.
      }

      etrans.
      2: apply maponpaths, pathsinv0, binprod_comp.
      apply pathsinv0, (functor_comp (LRB_composition a c e)).
    }

    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (! prewhisker_LRB_associator_co f0 g0 (h0 · i0)).
    }

    etrans.
    2: {
      rewrite ! assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, (pr2 (pr2 (LRB_composition_comm a b e) (f0, g0 · (h0 · i0) : hom _ _))).
    }
    rewrite id_right.

    etrans.
    2: {
      rewrite ! assoc'.
      do 2 apply maponpaths.
      etrans.
      2: apply (functor_comp (LRB_composition a b e)).
      etrans.
      2: apply maponpaths, binprod_comp.
      simpl.
      rewrite id_left.
      etrans.
      2: {
        do 2 apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        apply pathsinv0, (pr2 (pr2 (LRB_composition_comm b c e) (g0, h0 · i0 : hom _ _))).
      }
      now rewrite id_left.
    }

    set (t := pr21 (LRB_associator_nat_z_iso a b c e)).
    set (tt := ((t _ _ (id₁ (η_{ a, b} f0) #, (id₁ (η_{ b, c} g0) #, (pr1 (LRB_composition_comm _ _ _) (h0, i0))))))).
    cbn in tt.


    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      refine (! tt @ _).
      apply maponpaths_2, maponpaths.
      apply maponpaths_2.
      apply (functor_id (LRB_composition a b c)).
    }

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: apply (functor_comp (LRB_composition a b e)).
      etrans.
      2: apply maponpaths, binprod_comp.
      rewrite id_left.
      etrans.
      2: {
        do 2 apply maponpaths.
        etrans.
        2: apply (functor_comp (LRB_composition b c e)).
        apply maponpaths.
        etrans.
        2: apply binprod_comp.
        rewrite id_left.
        apply maponpaths.
        apply pathsinv0, (pr2 (pr2 (LRB_composition_comm c d e) (h0, i0))).
      }
      rewrite binprod_id.
      rewrite (functor_id (LRB_composition b c e)).
      now rewrite (functor_id (LRB_composition a b e)).
    }
    apply pathsinv0, id_right.
  Qed.

  Definition LRB_lassociator_rwhisker
             {a b c d e : B}
        (f0 : hom a b)
        (g0 : hom b c)
        (h0 : hom c d)
        (i0 : hom d e)
    : R (hom a e)
 ⟦ LRB_composition a d e
     (LRB_composition a c d
        (LRB_composition a b c (η (hom a b) f0, η (hom b c) g0), η (hom c d) h0),
       η (hom d e) i0), η (hom a e) (f0 · g0 · h0 · i0) ⟧.
  Proof.
    use (_ · _).
    2: {
      use (#(LRB_composition a d e)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: {
          use (#(LRB_composition a c d)).
          2: {
            use catbinprodmor.
            4: apply identity.
            2: exact ((LRB_composition_comm a b c) (f0,g0)).
          }
        }
      }
    }

    simpl.
    use (_ · _).
    2: {
      use (#(LRB_composition a d e)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: exact ((LRB_composition_comm a c d) (f0 · g0 : hom _ _, h0)).
      }
    }
    exact ((LRB_composition_comm a d e) (f0 · g0 · h0 : hom _ _, i0)).
  Defined.

  Definition LRB_lassociator_rwhisker'
               {a b c d e : B}
        (f0 : hom a b)
        (g0 : hom b c)
        (h0 : hom c d)
        (i0 : hom d e)
    : R (hom a e) ⟦ η (hom a e) (f0 · (g0 · h0) · i0),
 LRB_composition a d e
   (LRB_composition a b d (η (hom a b) f0, LRB_composition b c d (η (hom b c) g0, η (hom c d) h0)),
     η (hom d e) i0) ⟧.
  Proof.
    use (_ · _).
    3: {
      use (#(LRB_composition a d e)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: {
          use (#(LRB_composition a b d)).
          2: {
            use catbinprodmor.
            3: apply identity.
            2: exact (nat_z_iso_inv (LRB_composition_comm b c d) (g0,h0)).
          }
        }
      }
    }

    simpl.
    use (_ · _).
    3: {
      use (#(LRB_composition a d e)).
      2: {
        use catbinprodmor.
        4: apply identity.
        2: exact (nat_z_iso_inv (LRB_composition_comm a b d) (f0,g0 · h0 : hom _ _)).
      }
    }
    exact (nat_z_iso_inv (LRB_composition_comm a d e) (f0 · (g0 · h0) : hom _ _, i0)).
  Defined.

  Lemma LRB_lassociator_rwhisker_on
  {a b c d e : B}
        (f0 : hom a b)
        (g0 : hom b c)
        (h0 : hom c d)
        (i0 : hom d e)
    : LRB_rwhisker (LRB_associator (η (hom a b) f0) (η (hom b c) g0) (η (hom c d) h0))
                   (η (hom d e) i0) = LRB_lassociator_rwhisker f0 g0 h0 i0 · #(η (hom a e)) (rassociator f0 g0 h0 ▹ i0) · LRB_lassociator_rwhisker' f0 g0 h0 i0.
  Proof.

    etrans. {
      unfold LRB_rwhisker.
      apply maponpaths.
      exact (prewhisker_LRB_associator' f0 g0 h0).
    }

    unfold LRB_associator_pre_simpl_mor.
    simpl.
    unfold functor_fix_snd_arg_mor.
    unfold LRB_lassociator_rwhisker, LRB_lassociator_rwhisker'.
    simpl.

    etrans. {
      do 2 apply maponpaths.
      exact (! id_left (id₁ (η (hom d e) i0))).
    }
    etrans. {
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition a d e)).
    }

    rewrite ! assoc'.
    apply maponpaths.

    etrans. {
      do 2 apply maponpaths.
      exact (! id_left (id₁ (η (hom d e) i0))).
    }
    etrans. {
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition a d e)).
    }

    apply maponpaths.

    etrans. {
      do 2 apply maponpaths.
      exact (! id_left (id₁ (η (hom d e) i0))).
    }
    etrans. {
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition a d e)).
    }

    rewrite ! assoc.

    etrans. {
      do 3 apply maponpaths.
      exact (! id_left (id₁ (η (hom d e) i0))).
    }
    etrans. {
      apply maponpaths.
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition a d e)).
    }

    rewrite ! assoc.
    apply maponpaths_2.

    etrans.
    2: {
      do 2 apply maponpaths_2.

      refine (pr21 (LRB_composition_comm a d e) _ _ ((rassociator f0 g0 h0 : (hom _ _)⟦_,_⟧) #,  id₁ i0) @ _).
      apply maponpaths.
      cbn.
      apply maponpaths.
      apply hcomp_identity_right.
    }
    apply maponpaths_2.

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0.
      apply (pr2 (pr2 (LRB_composition_comm a d e) (f0 · (g0 · h0) : hom _ _, i0))).
    }
    rewrite id_right.
    cbn.
    do 2 apply maponpaths.
    apply pathsinv0, (functor_id (η (hom d e))).
  Qed.


  Definition LRB_lassociator_lwhisker
             {a b c d e : B}
        (f0 : hom a b)
        (g0 : hom b c)
        (h0 : hom c d)
        (i0 : hom d e)
    : R (hom a e) ⟦ LRB_composition a b e (η (hom a b) f0, LRB_composition b d e (LRB_composition b c d (η (hom b c) g0, η (hom c d) h0), η (hom d e) i0)), η (hom a e) (f0 · (g0 · h0 · i0)) ⟧.
  Proof.
    use (_ · _).
    2: {
      use (#(LRB_composition a b e)).
      2: {
        use catbinprodmor.
        3: apply identity.
        2: {
          use (#(LRB_composition b d e)).
          2: {
            use catbinprodmor.
            4: apply identity.
            2: exact (pr1 (LRB_composition_comm b c d) (g0,h0)).
          }
        }
      }
    }
    use (_ · _).
    2: {
      use (#(LRB_composition a b e)).
      2: {
        use catbinprodmor.
        3: apply identity.
        2: exact (pr1 (LRB_composition_comm b d e) (g0·h0 : hom _ _ , i0)).
      }
    }
    exact (pr1 (LRB_composition_comm a b e) (f0, (g0 · h0 · i0) : hom _ _ )).
  Defined.

  Definition LRB_lassociator_lwhisker'
             {a b c d e : B}
             (f0 : hom a b)
             (g0 : hom b c)
             (h0 : hom c d)
             (i0 : hom d e)
    : R (hom a e) ⟦ η (hom a e) (f0 · (g0 · (h0 · i0))), LRB_composition a b e (η (hom a b) f0, LRB_composition b c e (η (hom b c) g0, LRB_composition c d e (η (hom c d) h0, η (hom d e) i0)))⟧.
  Proof.
    exact (LRB_associator_comp_r' f0 g0 h0 i0).
  Defined.

  Lemma LRB_lassociator_lwhisker_on
        {a b c d e : B}
        (f0 : hom a b)
        (g0 : hom b c)
        (h0 : hom c d)
        (i0 : hom d e)
    :  LRB_lwhisker (η (hom a b) f0)
                    (LRB_associator (η (hom b c) g0) (η (hom c d) h0) (η (hom d e) i0))
       = LRB_lassociator_lwhisker f0 g0 h0 i0 · #(η (hom _ _)) (f0 ◃ rassociator g0 h0 i0) · LRB_lassociator_lwhisker' f0 g0 h0 i0.
  Proof.
    etrans. {
      unfold LRB_lwhisker.
      apply maponpaths.
      exact (prewhisker_LRB_associator' g0 h0 i0).
    }

    unfold LRB_associator_pre_simpl_mor.
    simpl.
    unfold functor_fix_snd_arg_mor.
    unfold LRB_lassociator_lwhisker, LRB_lassociator_lwhisker'.
    simpl.

    etrans. {
      apply maponpaths, maponpaths_2.
      exact (! id_left (id₁ (η (hom a b) f0))).
    }
    etrans. {
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition a b e)).
    }

    rewrite ! assoc'.
    apply maponpaths.

    etrans. {
      apply maponpaths, maponpaths_2.
      exact (! id_left (id₁ (η (hom a b) f0))).
    }
    etrans. {
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition a b e)).
    }

    apply maponpaths.

    etrans. {
      apply maponpaths, maponpaths_2.
      exact (! id_left (id₁ (η (hom a b) f0))).
    }
    etrans. {
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition a b e)).
    }

    rewrite ! assoc.
    etrans. {
      do 2 apply maponpaths.
      apply maponpaths_2.
      exact (! id_left (id₁ (η (hom a b) f0))).
    }
    etrans. {
      apply maponpaths.
      etrans. { apply maponpaths, binprod_comp. }
      apply (functor_comp (LRB_composition a b e)).
    }

    rewrite ! assoc.
    etrans.
    2: {
      apply maponpaths_2.
      refine (pr21 (LRB_composition_comm a b e) _ _ (id₁ f0 #, (rassociator g0 h0 i0 : (hom _ _)⟦_,_⟧)) @ _).
      apply maponpaths.
      cbn.
      apply maponpaths.
      apply hcomp_identity_left.
    }
    cbn.
    etrans. {
      do 2 apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      apply pathsinv0, (functor_id (η (hom _ _))).
    }

    rewrite ! assoc'.
    apply maponpaths.
    unfold LRB_associator_comp_r'.
    cbn.

    rewrite ! assoc.
    apply maponpaths_2.

    etrans.
    2: {
      apply maponpaths_2.
      apply pathsinv0.
      apply (pr2 (pr2 (LRB_composition_comm a b e) (f0, g0 · (h0 · i0) : hom _ _))).
    }
    now rewrite id_left.
  Qed.

  Lemma LRB_lassociator_lassociator
        {a b c d e : B}
        (f : R (hom a b))
        (g : R (hom b c))
        (h : R (hom c d))
        (i : R (hom d e))
    : LRB_lwhisker f (inv_from_z_iso (LRB_associator g h i))
                   · (inv_from_z_iso (LRB_associator f (LRB_composition _ _ _ (g, h)) i))
                   · (LRB_rwhisker (inv_from_z_iso (LRB_associator f g h)) i)
      = inv_from_z_iso (LRB_associator f g (LRB_composition _ _ _ (h,i)))
                       · inv_from_z_iso (LRB_associator (LRB_composition _ _ _ (f,g)) h i).
  Proof.
    use z_iso_inv_on_left.

    transparent assert (f_lw_a : (is_z_isomorphism (LRB_lwhisker f (inv_from_z_iso (LRB_associator g h i))))).
    {
      use functor_on_is_z_isomorphism.
      use is_z_iso_binprod_z_iso.
      - apply identity_is_z_iso.
      - apply is_z_iso_inv_from_z_iso.
    }

    transparent assert (r_a_i : (is_z_isomorphism  (LRB_rwhisker (inv_from_z_iso (LRB_associator f g h)) i))).
    {
      use functor_on_is_z_isomorphism.
      use is_z_iso_binprod_z_iso.
      - apply is_z_iso_inv_from_z_iso.
      - apply identity_is_z_iso.
    }

    rewrite ! assoc'.
    use (z_iso_inv_to_left _ _ _ (_ ,, f_lw_a)).
    apply pathsinv0, z_iso_inv_on_left.
    rewrite ! assoc'.
    apply pathsinv0.
    use z_iso_inv_on_right.
    apply pathsinv0, (z_iso_inv_to_left _ _ _ (_ ,, r_a_i)).

    assert (p : inv_from_z_iso (LRB_rwhisker (inv_from_z_iso (LRB_associator f g h)) i,, r_a_i)
                = LRB_rwhisker (LRB_associator f g h) i).
    { apply idpath. }
    rewrite p.
    clear p.
    assert (p : inv_from_z_iso (LRB_lwhisker f (inv_from_z_iso (LRB_associator g h i)),, f_lw_a)
                = LRB_lwhisker f (LRB_associator g h i)).
    { apply idpath. }
    rewrite p.
    clear p.

    use (factor_through_squash _ _ (eso (hom _ _) f)).
    { apply homset_property. }
    intros [f0 pf].
    induction (isotoid _ (pr2 (R (hom _ _))) pf).
    use (factor_through_squash _ _ (eso (hom _ _) g)).
    { apply homset_property. }
    intros [g0 pg].
    induction (isotoid _ (pr2 (R (hom _ _))) pg).
    use (factor_through_squash _ _ (eso (hom _ _) h)).
    { apply homset_property. }
    intros [h0 ph].
    induction (isotoid _ (pr2 (R (hom _ _))) ph).
    use (factor_through_squash _ _ (eso (hom _ _) i)).
    { apply homset_property. }
    intros [i0 pi].
    induction (isotoid _ (pr2 (R (hom _ _))) pi).
    clear pf pg ph pi.

    clear f_lw_a r_a_i.

    etrans. {
      apply maponpaths, maponpaths_2.
      exact (LRB_associator_comp_m_on f0 g0 h0 i0).
    }

    etrans.
    2: {
      apply maponpaths.
      exact (! LRB_associator_comp_r_on f0 g0 h0 i0).
    }

    etrans.
    2: {
      apply maponpaths_2.
      exact (! LRB_associator_comp_l_on f0 g0 h0 i0).
    }

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths, pathsinv0.
      unfold LRB_associator_comp_l', LRB_associator_comp_r.
      simpl.
      rewrite assoc.
      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, (functor_comp (LRB_composition a c e)).
      }
      etrans. {
        apply maponpaths_2.
        do 2 apply maponpaths.
        simpl.
        cbn.
        etrans. {
          apply maponpaths.
          apply (pr2 (pr2 (LRB_composition_comm c d e) (h0, i0))).
        }
        apply maponpaths_2.
        apply (pr2 (pr2 (LRB_composition_comm a b c) (f0, g0))).
      }
      etrans. {
        apply maponpaths_2, maponpaths.
        apply (functor_id (LRB_composition a c e)).
      }
      rewrite id_right.
      apply (pr2 (LRB_composition_comm a c e) (f0 · g0 : hom _ _, h0 · i0 : hom _ _)).
    }
    rewrite id_right.
    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply (functor_comp (η (hom a e))).
    }
    unfold LRB_associator_comp_l.

    etrans. {
      apply maponpaths_2.
      exact (LRB_lassociator_rwhisker_on f0 g0 h0 i0).
    }

    etrans. {
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc.
      apply maponpaths_2.
      unfold LRB_lassociator_rwhisker', LRB_associator_comp_m.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      etrans. {
        apply pathsinv0, (functor_comp (LRB_composition a d e)).
      }
      cbn.
      rewrite id_right.
      apply maponpaths, maponpaths_2.
      etrans. {
        apply pathsinv0, (functor_comp (LRB_composition a b d)).
      }

      rewrite <- binprod_comp.
      rewrite id_right.
      etrans. {
        do 2 apply maponpaths.
        apply (pr2 (pr2 (LRB_composition_comm b c d) (g0, h0))).
      }
      apply (functor_id (LRB_composition a b d)).
    }


    etrans. {
      apply maponpaths.
      exact (LRB_lassociator_lwhisker_on f0 g0 h0 i0).
    }

    etrans.
    2: {
      apply maponpaths_2, maponpaths, maponpaths.
      exact (rassociator_rassociator f0 g0 h0 i0).
    }

    etrans.
    2: {
      apply maponpaths_2, maponpaths.
      etrans.
      2: apply pathsinv0, (functor_comp (η (hom _ _))).
      apply maponpaths_2.
      apply pathsinv0, (functor_comp (η (hom _ _))).
    }

    rewrite ! assoc.
    do 2 apply maponpaths_2.

    assert (q :  # (η (hom a e)) (pr1 (rassociator_transf a b d e) (f0, (g0 · h0 : hom _ _, i0)))
               · LRB_associator_comp_m' f0 g0 h0 i0 · LRB_lassociator_lwhisker f0 g0 h0 i0 =  # (η (hom a e)) (rassociator f0 (g0 · h0) i0)).
    {
      refine (_ @ id_right _).
      rewrite assoc'.
      apply maponpaths.
      unfold LRB_associator_comp_m'.
      unfold LRB_lassociator_lwhisker.

      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        etrans. { apply pathsinv0, functor_comp. }
        etrans. { apply maponpaths, pathsinv0, binprod_comp. }
        now rewrite id_right.
      }

      etrans. {
        rewrite assoc.
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        etrans. { apply pathsinv0, functor_comp. }
        etrans. { apply maponpaths, pathsinv0, binprod_comp. }
        rewrite id_right.
        do 2 apply maponpaths.
        rewrite assoc'.
        apply maponpaths.
        etrans. { apply pathsinv0, functor_comp. }
        etrans. { apply maponpaths, pathsinv0, binprod_comp. }
        rewrite id_right.
        etrans. {
          apply maponpaths, maponpaths_2.
          apply (pr2 (LRB_composition_comm b c d)).
        }
        apply (functor_id (LRB_composition b d e)).
      }
      rewrite id_right.

      etrans. {
        rewrite assoc.
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        etrans. { apply pathsinv0, functor_comp. }
        etrans. { apply maponpaths, pathsinv0, binprod_comp. }
        rewrite id_right.
        do 2 apply maponpaths.
        apply (pr2 (LRB_composition_comm b d e)).
      }

      rewrite (functor_id (LRB_composition a b e)).
      rewrite id_right.
      apply (pr2 (LRB_composition_comm a b e)).
    }

    rewrite <- q.
    rewrite ! assoc.
    do 3 apply maponpaths_2.
    unfold LRB_lassociator_rwhisker.
    rewrite ! assoc'.
    do 3 apply maponpaths.

    refine (_ @ id_right _).
    apply maponpaths.
    rewrite (functor_id (LRB_composition a d e)).
    rewrite id_left.
    etrans. {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- (functor_comp (LRB_composition a d e)).
      etrans. {
        apply maponpaths.
        rewrite <- binprod_comp.
        apply maponpaths_2.
        apply (pr2 (pr2 (LRB_composition_comm a b d) (f0 , g0 · h0 : hom _ _))).
      }
      rewrite id_right.
      apply (functor_id (LRB_composition a d e)).
    }

    rewrite id_left.
    apply (pr2 (pr2 (LRB_composition_comm a d e) (f0 · (g0 · h0) : hom _ _ , i0))).
  Qed.

  Lemma LRB_laws : prebicat_laws LRB_data.
  Proof.
    repeat split ; intro ; intros.
    - apply id_left.
    - apply id_right.
    - apply assoc.
    - exact (functor_id (LRB_composition_curry1 a b c f) g).
    - exact (functor_id (LRB_composition_curry2 a b c g) f).
    - exact (! functor_comp (LRB_composition_curry1 _ _ _ _) _ _).
    - exact (! functor_comp (LRB_composition_curry2 _ _ _ _) _ _).
    - apply LRB_vcomp_lunitor.
    - apply LRB_vcomp_runitor.
    - apply LRB_lwhisker_lwhisker.
    - apply LRB_rwhisker_lwhisker.
    - apply LRB_rwhisker_rwhisker.
    - refine (! functor_comp (LRB_composition a b c) (x #, id2 h) (id2 g #, y) @ _).
      refine (_ @ functor_comp (LRB_composition a b c) (id2 f #, y) (x #, id2 i)).
      do 2 rewrite <- binprod_comp.
      now rewrite ! id_left, ! id_right.
    - apply (pr22 (LRB_lunitor f)).
    - apply (pr22 (LRB_lunitor f)).
    - apply (pr22 (LRB_runitor f)).
    - apply (pr22 (LRB_runitor f)).
    - apply (pr22 (LRB_associator f g h)).
    - apply (pr22 (LRB_associator f g h)).
    - apply LRB_runitor_rwhisker.
    - apply LRB_lassociator_lassociator.
  Qed.

  Definition LRB_pre : prebicat
    := LRB_data ,, LRB_laws.

  Definition LRB : bicat.
  Proof.
    exists LRB_pre.
    abstract (intro ; intros ; apply homset_property).
  Defined.

  Lemma locally_univalent_lemma (x y : B)
    : is_univalent (R (hom (C := B) x y)) -> is_univalent (hom (C := LRB) x y).
  Proof.
    intro u.
    intros f g.

    assert (p : (λ p : f = g, @idtoiso (R (@hom B x y)) f g p)
            = (λ p : f = g, @idtoiso (@hom LRB x y) f g p)).
    {
      apply funextsec ; intro p.
      induction p.
      use total2_paths_f.
      2: apply isaprop_is_z_isomorphism.
      apply idpath.
    }

    induction p.
    apply u.
  Qed.

  Lemma LRB_is_locally_univalent
    : is_univalent_2_1 LRB.
  Proof.
    apply is_univalent_2_1_if_hom_is_univ.
    intros x y f g.
    assert (p : (λ p : f = g, @idtoiso (R (@hom B x y)) f g p)
            = (λ p : f = g, @idtoiso (@hom LRB x y) f g p)).
    {
      apply funextsec ; intro p.
      induction p.
      use total2_paths_f.
      2: apply isaprop_is_z_isomorphism.
      apply idpath.
    }

    induction p.
    apply R.
  Qed.

  Definition psfunctor_B_to_LRB_data
    : psfunctor_data B LRB.
  Proof.
    use make_psfunctor_data.
    - exact (idfun B).
    - exact (λ x y, η_{x,y}).
    - exact (λ x y f g α, #(η_{x,y}) α).
    - intro ; apply identity.
    - exact (λ x y z f g, pr1 (LRB_composition_comm x y z) (make_catbinprod (C := hom x y) (D := hom y z) f g)).
  Defined.

  Lemma psfunctor_B_to_LRB_laws
    : psfunctor_laws psfunctor_B_to_LRB_data.
  Proof.
    repeat split.
    - exact (λ x y f, functor_id (η_{x,y}) f).
    - intros x y f g h α β.
      apply (functor_comp (η_{x,y})).
    - exact (λ x y f, prewhisker_LRB_lunitor f).
    - exact (λ x y f, prewhisker_LRB_runitor f).
    - exact (λ x y z w f g h, prewhisker_LRB_associator f g h).
    - intro ; intros.
      set (t := λ fg, ! pr21 (LRB_composition_comm a b c)
            (make_catbinprod (C:=hom _ _) (D:=hom _ _) f g₁)
            (make_catbinprod (C:=hom _ _) (D:=hom _ _) f g₂) fg).
      cbn in t.

      refine (_ @ t (catbinprodmor (C:=hom _ _) (D:=hom _ _) (id2 f) η0) @ _).
      + do 2 apply maponpaths.
        apply lwhisker_hcomp.
      + now rewrite (functor_id (η (hom a b))).
    - intro ; intros.
      unfold psfunctor_B_to_LRB_data.
      set (t := λ fg, ! pr21 (LRB_composition_comm a b c)
            (make_catbinprod (C:=hom _ _) (D:=hom _ _) f₁ g)
            (make_catbinprod (C:=hom _ _) (D:=hom _ _) f₂ g) fg).
      cbn in t.

      refine (_ @ t (catbinprodmor (C:=hom _ _) (D:=hom _ _) η0 (id2 g)) @ _).
      + do 2 apply maponpaths.
        apply rwhisker_hcomp.
      + now rewrite (functor_id (η (hom b c))).
  Qed.

  Definition psfunctor_B_to_LRB_invertible_cells
    : invertible_cells psfunctor_B_to_LRB_data.
  Proof.
    split.
    - exact (λ x, is_invertible_2cell_id₂ (C := LRB)  (η (hom x x) (id₁ x))).
    - exact (λ x y z f g, pr2 (lift_functor_along_comm (R (hom x z)) (pair_functor (η_{x,y}) (η_{y,z})) (pair_functor_eso (η_{x,y}) (η_{y,z}) (eso (hom x y)) (eso_{y,z})) (pair_functor_ff (η_{x,y}) (η_{y,z}) (ff_{x,y}) (ff_{y,z})) (hcomp_functor ∙ η_{x,z})) (make_catbinprod (C := hom x y) (D := hom y z) f g)).
  Defined.

  Definition psfunctor_B_to_LRB
    : psfunctor B LRB.
  Proof.
    use make_psfunctor.
    - exact psfunctor_B_to_LRB_data.
    - exact psfunctor_B_to_LRB_laws.
    - exact psfunctor_B_to_LRB_invertible_cells.
  Defined.

  Definition psfunctor_B_to_LRB_is_weak_biequivalence
    : weak_biequivalence psfunctor_B_to_LRB.
  Proof.
    split.
    - intro x.
      apply hinhpr.
      exists x.
      apply internal_adjoint_equivalence_identity.
    - intros x y.
      exists eso_{x,y}.
      exact ff_{x,y}.
  Defined.

End LocalUnivalenceRezk.
