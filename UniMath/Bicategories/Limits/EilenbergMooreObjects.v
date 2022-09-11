(***********************************************************************************

 Eilenberg-Moore objects

 In this file, we study Eilenberg-Moore objects internal to arbitrary
 bicategories. This generalizes Eilenberg-Moore categories to arbitrary
 bicategories.

 We present three equivalent definitions. The first one expresses Eilenberg-Moore
 objects using universal properties. The second definition coincides with universal
 arrows, and it is remniscent of the work by Street (Formal Theory of Monads) where
 Eilenberg-Moore objects are defined as a right adjoint of the inclusion
 pseudofunctor of `B` into `mnd B`. The third definition is another reformulation
 where Eilenberg-Moore categories are used.

 Contents
 1. Definition via universal properties
 1.1 Cones and morphisms of cones
 1.2 The mapping properties
 1.3 It is a proposition
 2. Definition similar to universal arrows
 2.1 The functor
 2.2 The definition
 2.3 It is a proposition
 3. Equivalence of the first two definitions
 4. Definition via Eilenberg-Moore category
 4.1 The functor
 4.2 The definition
 4.3 It is a proposition
 5. Equivalence to the other two definitions
 6. Bicategories with Eilenberg-Moore objects

 ***********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.EilenbergMoore.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Monads.Examples.ToMonadInCat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.

Local Open Scope cat.

Definition idtoiso_mnd_incl
           {B : bicat}
           {a b : B}
           {f g : a --> b}
           (p : f = g)
           (m : mnd B)
           (h : mnd_incl B b --> m)
  : pr1 (idtoiso_2_1
           _
           _
           (maponpaths
              (λ z, # (mnd_incl B) z · h)
              p))
    =
    ## (mnd_incl B) (idtoiso_2_1 _ _ p) ▹ h.
Proof.
  induction p.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply psfunctor_id2.
  }
  apply id2_rwhisker.
Qed.

Section EMObject.
  Context {B : bicat}
          (m : mnd B).

  (**
   1. Definition via universal properties
   *)

  (**
    1.1 Cones and morphisms of cones
   *)
  Definition em_cone
    : UU
    := ∑ (x : B), mnd_incl B x --> m.

  Section MakeCone.
    Context (x : B)
            (f : x --> ob_of_mnd m)
            (fm : f · endo_of_mnd m ==> id₁ x · f)
            (fη : linvunitor f = rinvunitor f • (f ◃ unit_of_mnd m) • fm)
            (fμ : lassociator _ _ _
                  • (fm ▹ endo_of_mnd m)
                  • (lunitor f ▹ endo_of_mnd m)
                  • fm
                  =
                  (f ◃ mult_of_mnd m)
                  • fm).

    Definition make_em_cone_mnd_mor_data
      : mnd_mor_data (mnd_incl B x) m.
    Proof.
      use make_mnd_mor_data.
      - exact f.
      - exact fm.
    Defined.

    Definition make_em_cone_mnd_mor_laws
      : mnd_mor_laws make_em_cone_mnd_mor_data.
    Proof.
      split.
      - cbn.
        rewrite id2_rwhisker.
        rewrite id2_right.
        exact fη.
      - cbn.
        rewrite !vassocl.
        rewrite lunitor_triangle.
        rewrite vcomp_lunitor.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite <- lunitor_triangle.
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        exact fμ.
    Qed.

    Definition make_em_cone
      : em_cone.
    Proof.
      refine (x ,, _).
      use make_mnd_mor.
      - exact make_em_cone_mnd_mor_data.
      - exact make_em_cone_mnd_mor_laws.
    Defined.
  End MakeCone.

  Coercion em_cone_to_ob (e : em_cone) : B := pr1 e.

  Definition mor_of_em_cone (e : em_cone) : mnd_incl B e --> m := pr2 e.

  Definition em_cone_mor
             (e₁ e₂ : em_cone)
    : UU
    := ∑ (g : e₁ --> e₂),
       invertible_2cell
         (# (mnd_incl B) g · mor_of_em_cone e₂)
         (mor_of_em_cone e₁).

  Definition make_em_cone_mor
             {e₁ e₂ : em_cone}
             (g : e₁ --> e₂)
             (α : invertible_2cell
                    (# (mnd_incl B) g · mor_of_em_cone e₂)
                    (mor_of_em_cone e₁))
    : em_cone_mor e₁ e₂
    := g ,, α.

  Coercion mor_of_em_cone_mor
           {e₁ e₂ : em_cone}
           (f : em_cone_mor e₁ e₂)
    : e₁ --> e₂
    := pr1 f.

  Definition cell_of_em_cone_mor
             {e₁ e₂ : em_cone}
             (f : em_cone_mor e₁ e₂)
    : invertible_2cell
        (# (mnd_incl B) f · mor_of_em_cone e₂)
        (mor_of_em_cone e₁)
    := pr2 f.

  Definition path_em_cone_mor
             (HB : is_univalent_2_1 B)
             {e₁ e₂ : em_cone}
             {f₁ f₂ : em_cone_mor e₁ e₂}
             (α : invertible_2cell f₁ f₂)
             (p : (## (mnd_incl B) α ▹ mor_of_em_cone e₂) • pr12 f₂ = pr12 f₁)
    : f₁ = f₂.
  Proof.
    use total2_paths_f.
    - exact (isotoid_2_1 HB α).
    - use subtypePath.
      {
        intro ; apply isaprop_is_invertible_2cell.
      }
      etrans.
      {
        apply (@pr1_transportf
                 (e₁ --> e₂)
                 (λ x, # (mnd_incl B) x · mor_of_em_cone e₂ ==> mor_of_em_cone e₁)).
      }
      rewrite transport_two_cell_FlFr.
      rewrite maponpaths_for_constant_function.
      use vcomp_move_R_pM ; [ is_iso | ].
      refine (id2_right _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (idtoiso_mnd_incl (isotoid_2_1 HB α) m (mor_of_em_cone e₂)).
      }
      rewrite idtoiso_2_1_isotoid_2_1.
      exact p.
  Qed.

  (**
   1.2 The mapping properties
   *)
  Definition em_ump_1
             (e : em_cone)
    : UU
    := ∏ (q : em_cone), em_cone_mor q e.

  Definition em_ump_2
             (e : em_cone)
    : UU
    := ∏ (x : B)
         (g₁ g₂ : x --> e)
         (α : # (mnd_incl B) g₁ · mor_of_em_cone e
              ==>
              # (mnd_incl B) g₂ · mor_of_em_cone e),
      ∃! (β : g₁ ==> g₂), ## (mnd_incl B) β ▹ _ = α.

  Definition has_em_ump
             (e : em_cone)
    : UU
    := em_ump_1 e × em_ump_2 e.

  Section MappingProperties.
    Context {e : em_cone}
            (He : has_em_ump e).

    Definition em_ump_1_mor
               (q : em_cone)
      : q --> e
      := pr1 He q.

    Definition em_ump_1_inv2cell
               (q : em_cone)
      : invertible_2cell
          (# (mnd_incl B) (em_ump_1_mor q) · mor_of_em_cone e)
          (mor_of_em_cone q)
      := cell_of_em_cone_mor (pr1 He q).

    Definition em_ump_2_cell
               {x : B}
               {g₁ g₂ : x --> e}
               (α : # (mnd_incl B) g₁ · mor_of_em_cone e
                    ==>
                    # (mnd_incl B) g₂ · mor_of_em_cone e)
      : g₁ ==> g₂
      := pr11 (pr2 He x g₁ g₂ α).

    Definition em_ump_2_eq
               {x : B}
               {g₁ g₂ : x --> e}
               (α : # (mnd_incl B) g₁ · mor_of_em_cone e
                    ==>
                    # (mnd_incl B) g₂ · mor_of_em_cone e)
      : ## (mnd_incl B) (em_ump_2_cell α) ▹ _ = α
      := pr21 (pr2 He x g₁ g₂ α).

    Definition em_ump_eq
               {x : B}
               {g₁ g₂ : x --> e}
               (α : # (mnd_incl B) g₁ · mor_of_em_cone e
                    ==>
                    # (mnd_incl B) g₂ · mor_of_em_cone e)
               (β₁ β₂ : g₁ ==> g₂)
               (Hβ₁ : ## (mnd_incl B) β₁ ▹ _ = α)
               (Hβ₂ : ## (mnd_incl B) β₂ ▹ _ = α)
      : β₁ = β₂.
    Proof.
      exact (maponpaths
               pr1
               (pr1 (isapropifcontr (pr2 He x g₁ g₂ α) (β₁ ,, Hβ₁) (β₂ ,, Hβ₂)))).
    Qed.

    Definition em_ump_2_cell_is_invertible
               {x : B}
               {g₁ g₂ : x --> e}
               (α : # (mnd_incl B) g₁ · mor_of_em_cone e
                    ==>
                    # (mnd_incl B) g₂ · mor_of_em_cone e)
               (Hα : is_invertible_2cell α)
      : is_invertible_2cell (em_ump_2_cell α).
    Proof.
      use make_is_invertible_2cell.
      - exact (em_ump_2_cell (Hα^-1)).
      - use (em_ump_eq (id2 _)).
        + abstract
            (rewrite psfunctor_vcomp ;
             rewrite <- rwhisker_vcomp ;
             rewrite !em_ump_2_eq ;
             apply vcomp_rinv).
        + abstract
            (rewrite psfunctor_id2 ;
             apply id2_rwhisker).
      - use (em_ump_eq (id2 _)).
        + abstract
            (rewrite psfunctor_vcomp ;
             rewrite <- rwhisker_vcomp ;
             rewrite !em_ump_2_eq ;
             apply vcomp_linv).
        + abstract
            (rewrite psfunctor_id2 ;
             apply id2_rwhisker).
    Defined.

    Definition em_ump_2_inv2cell
               {x : B}
               {g₁ g₂ : x --> e}
               (α : invertible_2cell
                      (# (mnd_incl B) g₁ · mor_of_em_cone e)
                      (# (mnd_incl B) g₂ · mor_of_em_cone e))
      : invertible_2cell g₁ g₂.
    Proof.
      use make_invertible_2cell.
      - exact (em_ump_2_cell α).
      - exact (em_ump_2_cell_is_invertible _ (pr2 α)).
    Defined.
  End MappingProperties.

  (**
   1.3 It is a proposition
   *)
  Definition isaprop_has_em_ump
             (HB : is_univalent_2_1 B)
             (e : em_cone)
    : isaprop (has_em_ump e).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      do 4 (use impred ; intro).
      apply isapropiscontr.
    }
    use funextsec.
    intro q.
    use (path_em_cone_mor HB).
    - use (em_ump_2_inv2cell φ₁).
      exact (comp_of_invertible_2cell
               (cell_of_em_cone_mor (pr1 φ₁ q))
               (inv_of_invertible_2cell
                  (cell_of_em_cone_mor (pr1 φ₂ q)))).
    - etrans.
      {
        apply maponpaths_2.
        apply em_ump_2_eq.
      }
      refine (vassocl _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply (vcomp_linv (pr2 (pr1 φ₂ q))).
      }
      apply id2_right.
  Qed.

  (**
   2. Definition similar to universal arrows
   *)

  (**
   2.1 The functor
   *)
  Section EilenbergMooreFunctor.
    Context (e : em_cone)
            (x : B).

    Definition em_hom_functor_ob_data
               (f : x --> e)
      : mnd_mor_data (mnd_incl B x) m.
    Proof.
      use make_mnd_mor_data.
      - exact (f · mor_of_mnd_mor (mor_of_em_cone e)).
      - exact (rassociator _ _ _
               • (_ ◃ mnd_mor_endo (mor_of_em_cone e))
               • (_ ◃ lunitor _)
               • linvunitor _).
    Defined.

    Definition em_hom_functor_ob_laws
               (f : x --> e)
      : mnd_mor_laws (em_hom_functor_ob_data f).
    Proof.
      split.
      - cbn.
        rewrite id2_rwhisker, id2_right.
        rewrite !vassocl.
        pose (mnd_mor_unit (mor_of_em_cone e)) as p.
        cbn in p.
        rewrite id2_rwhisker, id2_right in p.
        rewrite <- rinvunitor_triangle.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- lwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite !lwhisker_vcomp.
        rewrite <- p.
        rewrite linvunitor_lunitor.
        rewrite lwhisker_id2.
        apply id2_left.
      - cbn.
        rewrite !vassocl.
        rewrite lunitor_triangle.
        rewrite vcomp_lunitor.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite <- lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        etrans.
        {
          rewrite <- lunitor_triangle.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite rassociator_lassociator.
            rewrite id2_left.
            rewrite !vassocl.
            apply idpath.
          }
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite !vassocl.
          rewrite linvunitor_lunitor.
          rewrite id2_right.
          apply idpath.
        }
        rewrite <- !rwhisker_vcomp.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocr.
        rewrite inverse_pentagon_7.
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          apply id2_left.
        }
        rewrite !lwhisker_vcomp.
        apply maponpaths.
        refine (_ @ mnd_mor_mu (mor_of_em_cone e)) ; cbn.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite lunitor_triangle.
        rewrite vcomp_lunitor.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite <- lunitor_triangle.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
    Qed.

    Definition em_hom_functor_ob
               (f : x --> e)
      : mnd_incl B x --> m.
    Proof.
      use make_mnd_mor.
      - exact (em_hom_functor_ob_data f).
      - exact (em_hom_functor_ob_laws f).
    Defined.

    Definition em_hom_functor_mor_data
               {f g : x --> e}
               (α : f ==> g)
      : mnd_cell_data (em_hom_functor_ob f) (em_hom_functor_ob g)
      := α ▹ _.

    Definition em_hom_functor_mor_is_mnd_cell
               {f g : x --> e}
               (α : f ==> g)
      : is_mnd_cell (em_hom_functor_mor_data α).
    Proof.
      unfold is_mnd_cell ; cbn.
      unfold em_hom_functor_mor_data.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite lwhisker_hcomp.
        rewrite <- linvunitor_natural.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_whisker.
      apply idpath.
    Qed.

    Definition em_hom_functor_mor
               {f g : x --> e}
               (α : f ==> g)
      : em_hom_functor_ob f ==> em_hom_functor_ob g.
    Proof.
      use make_mnd_cell.
      - exact (em_hom_functor_mor_data α).
      - exact (em_hom_functor_mor_is_mnd_cell α).
    Defined.

    Definition em_hom_functor_data
      : functor_data (hom x e) (hom (mnd_incl B x) m).
    Proof.
      use make_functor_data.
      - exact em_hom_functor_ob.
      - exact (λ _ _ α, em_hom_functor_mor α).
    Defined.

    Definition em_hom_functor_is_functor
      : is_functor em_hom_functor_data.
    Proof.
      split.
      - intros f.
        use eq_mnd_cell ; cbn.
        unfold em_hom_functor_mor_data.
        apply id2_rwhisker.
      - intros f g h α β.
        use eq_mnd_cell ; cbn.
        unfold em_hom_functor_mor_data ; cbn.
        rewrite rwhisker_vcomp.
        apply idpath.
    Qed.
  End EilenbergMooreFunctor.

  Definition em_hom_functor
             (e : em_cone)
             (x : B)
    : hom x e ⟶ hom (mnd_incl B x) m.
  Proof.
    use make_functor.
    - exact (em_hom_functor_data e x).
    - exact (em_hom_functor_is_functor e x).
  Defined.

  (**
   2.2 The definition
   *)
  Definition is_universal_em_cone
             (e : em_cone)
    : UU
    := ∏ (x : B), adj_equivalence_of_cats (em_hom_functor e x).

  (**
   2.3 It is a proposition
   *)
  Definition isaprop_is_universal_em_cone
             (HB_2_1 : is_univalent_2_1 B)
             (e : em_cone)
    : isaprop (is_universal_em_cone e).
  Proof.
    use impred ; intro x.
    use isofhlevelweqf.
    - exact (@left_adjoint_equivalence
               bicat_of_univ_cats
               (univ_hom HB_2_1 x e)
               (univ_hom (is_univalent_2_1_mnd _ HB_2_1) (mnd_incl B x) m)
               (em_hom_functor e x)).
    - exact (@adj_equiv_is_equiv_cat
               (univ_hom HB_2_1 x e)
               _
               _).
    - apply isaprop_left_adjoint_equivalence.
      exact univalent_cat_is_univalent_2_1.
  Qed.

  (**
   3. Equivalence of the two definitions
   *)
  Section UMPIsUniversal.
    Context {e : em_cone}
            (He : has_em_ump e)
            (x : B).

    Definition has_em_ump_right_adjoint_data
      : functor_data (hom (mnd_incl B x) m) (hom x e).
    Proof.
      use make_functor_data.
      - exact (λ f, em_ump_1_mor He (x ,, f)).
      - exact (λ f g α,
               em_ump_2_cell
                 He
                 (em_ump_1_inv2cell He (x ,, f)
                  • α
                  • (em_ump_1_inv2cell He (x ,, g))^-1)).
    Defined.

    Definition has_em_ump_right_adjoint_is_functor
      : is_functor has_em_ump_right_adjoint_data.
    Proof.
      split.
      - intros f.
        use (em_ump_eq He).
        + apply id2.
        + etrans.
          {
            apply em_ump_2_eq.
          }
          etrans.
          {
            apply maponpaths_2.
            apply id2_right.
          }
          apply vcomp_rinv.
        + refine (_ @ id2_rwhisker _ _).
          apply maponpaths.
          apply psfunctor_id2.
      - intros f g h α β.
        use (em_ump_eq He).
        + exact (em_ump_1_inv2cell He (x ,, f)
                 • α • β
                 • (em_ump_1_inv2cell He (x ,, h))^-1).
        + etrans.
          {
            apply em_ump_2_eq.
          }
          rewrite !vassocl.
          apply maponpaths.
          refine (vassocl _ _ _ @ _).
          apply idpath.
        + etrans.
          {
            apply maponpaths.
            apply psfunctor_vcomp.
          }
          rewrite <- rwhisker_vcomp.
          etrans.
          {
            apply maponpaths.
            apply em_ump_2_eq.
          }
          etrans.
          {
            apply maponpaths_2.
            apply em_ump_2_eq.
          }
          rewrite !vassocl.
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_linv.
          rewrite id2_left.
          apply idpath.
    Qed.

    Definition has_em_ump_right_adjoint
      : hom (mnd_incl B x) m ⟶ hom x e.
    Proof.
      use make_functor.
      - exact has_em_ump_right_adjoint_data.
      - exact has_em_ump_right_adjoint_is_functor.
    Defined.

    Definition unit_help_data
               (f : x --> e)
      : mnd_cell_data
          (# (mnd_incl B) (functor_identity (hom x e) f) · mor_of_em_cone e)
          (mor_of_em_cone (x,, em_hom_functor_ob e x f))
      := id2 _.

    Definition unit_help_is_mnd_cell
               (f : x --> e)
      : is_mnd_cell (unit_help_data f).
    Proof.
      red ; unfold unit_help_data.
      cbn.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite linvunitor_assoc.
      apply idpath.
    Qed.

    Definition unit_help
               (f : x --> e)
      : # (mnd_incl B) f · mor_of_em_cone e
        ==>
        mor_of_em_cone (x,, em_hom_functor_ob e x f).
    Proof.
      use make_mnd_cell.
      - exact (unit_help_data f).
      - exact (unit_help_is_mnd_cell f).
    Defined.

    Definition has_em_ump_unit_data
      : nat_trans_data
          (functor_identity (hom x e))
          (em_hom_functor e x ∙ has_em_ump_right_adjoint)
      := λ f, em_ump_2_cell
                He
                (unit_help f • (em_ump_1_inv2cell He (x,, em_hom_functor_ob e x f))^-1).

    Definition has_em_ump_unit_is_nat_trans
      : is_nat_trans _ _ has_em_ump_unit_data.
    Proof.
      intros f₁ f₂ α.
      use (em_ump_eq He).
      - refine (unit_help f₁
                • _
                • (em_ump_1_inv2cell He (x,, em_hom_functor_ob e x f₂))^-1).
        use make_mnd_cell.
        + exact (α ▹ _).
        + abstract
            (red ; cbn ;
             rewrite !vassocl ;
             etrans ;
               [ do 3 apply maponpaths ;
                 rewrite lwhisker_hcomp ;
                 rewrite <- linvunitor_natural ;
                 apply idpath
               | ] ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite !vassocl ;
             rewrite <- vcomp_whisker ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite rwhisker_rwhisker_alt ;
             rewrite !vassocl ;
             apply maponpaths ;
             rewrite vcomp_whisker ;
             apply idpath).
      - use eq_mnd_cell.
        refine (_ @ maponpaths (λ z, z • _) (!(id2_left _))).
        refine (!(rwhisker_vcomp _ _ _) @ _).
        apply maponpaths.
        etrans.
        {
          exact (maponpaths
                   pr1
                   (em_ump_2_eq
                      He
                      _)).
        }
        apply id2_left.
      - use eq_mnd_cell.
        refine (_ @ maponpaths (λ z, z • _) (!(id2_left _))).
        refine (!(rwhisker_vcomp _ _ _) @ _).
        etrans.
        {
          apply maponpaths_2.
          exact (maponpaths
                   pr1
                   (em_ump_2_eq
                      He
                      _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   pr1
                   (em_ump_2_eq
                      He
                      _)).
        }
        refine (vassocl _ _ _ @ _).
        refine (id2_left _ @ _).
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (vassocr _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            exact (maponpaths
                     pr1
                     (vcomp_linv
                        (em_ump_1_inv2cell He (x,, em_hom_functor e x f₁)))).
          }
          apply id2_left.
        }
        apply idpath.
    Qed.

    Definition has_em_ump_unit
      : functor_identity _
        ⟹
        em_hom_functor e x ∙ has_em_ump_right_adjoint.
    Proof.
      use make_nat_trans.
      - exact has_em_ump_unit_data.
      - exact has_em_ump_unit_is_nat_trans.
    Defined.

    Definition counit_help_data
               (f : hom (mnd_incl B x) m)
      : mnd_cell_data
          (em_hom_functor e x (em_ump_1_mor He (x,, f)))
          (# (mnd_incl B) (em_ump_1_mor He (x,, f)) · mor_of_em_cone e)
      := id2 _.

    Definition counit_help_is_mnd_cell
               (f : hom (mnd_incl B x) m)
      : is_mnd_cell (counit_help_data f).
    Proof.
      unfold is_mnd_cell.
      unfold counit_help_data.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      do 2 refine (vassocl _ _ _ @ _).
      do 3 refine (_ @ vassocr _ _ _).
      do 2 apply maponpaths.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (!(rwhisker_vcomp _ _ _)).
        }
        refine (vassocr _ _ _ @ _).
        apply maponpaths_2.
        refine (vassocr _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply runitor_rwhisker.
        }
        apply idpath.
      }
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      rewrite linvunitor_assoc.
      apply idpath.
    Qed.

    Definition counit_help
               (f : hom (mnd_incl B x) m)
      : em_hom_functor e x (em_ump_1_mor He (x ,, f))
        ==>
        # (mnd_incl B) (em_ump_1_mor He (x,, f)) · mor_of_em_cone e.
    Proof.
      use make_mnd_cell.
      - exact (counit_help_data f).
      - exact (counit_help_is_mnd_cell f).
    Defined.

    Definition has_em_ump_counit_data
      : nat_trans_data
          (has_em_ump_right_adjoint ∙ em_hom_functor e x)
          (functor_identity _)
      := λ f, counit_help f • em_ump_1_inv2cell He (x,, f).

    Definition has_em_ump_counit_is_nat_trans
      : is_nat_trans _ _ has_em_ump_counit_data.
    Proof.
      intros f₁ f₂ α.
      use eq_mnd_cell.
      etrans.
      {
        refine (maponpaths (λ z, _ • z) _).
        apply id2_left.
      }
      refine (_ @ maponpaths (λ z, z • _) (!(id2_left _))).
      etrans.
      {
        apply maponpaths_2.
        exact (maponpaths
                 pr1
                 (em_ump_2_eq
                    He
                    _)).
      }
      do 2 refine (vassocl _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   pr1
                   (vcomp_linv
                      (em_ump_1_inv2cell He (x ,, _)))).
        }
        apply id2_right.
      }
      apply idpath.
    Qed.

    Definition has_em_ump_counit
      : has_em_ump_right_adjoint ∙ em_hom_functor e x
        ⟹
        functor_identity _.
    Proof.
      use make_nat_trans.
      - exact has_em_ump_counit_data.
      - exact has_em_ump_counit_is_nat_trans.
    Defined.

    Definition has_em_ump_adjunction_data
      : adjunction_data (hom x e) (hom (mnd_incl B x) m).
    Proof.
      use make_adjunction_data.
      - exact (em_hom_functor e x).
      - exact has_em_ump_right_adjoint.
      - exact has_em_ump_unit.
      - exact has_em_ump_counit.
    Defined.

    Definition has_em_ump_forms_equivalence
      : forms_equivalence has_em_ump_adjunction_data.
    Proof.
      split.
      - intro f.
        use is_inv2cell_to_is_z_iso.
        apply em_ump_2_cell_is_invertible.
        apply is_invertible_mnd_2cell.
        simpl.
        unfold unit_help_data.
        is_iso.
        exact (from_invertible_mnd_2cell
                 (inv_of_invertible_2cell
                    (em_ump_1_inv2cell He (x,, em_hom_functor_ob e x f)))).
      - intro f.
        use is_inv2cell_to_is_z_iso.
        apply is_invertible_mnd_2cell.
        simpl.
        unfold counit_help_data.
        is_iso.
        exact (from_invertible_mnd_2cell
                 (em_ump_1_inv2cell He (x,, f))).
    Defined.

    Definition has_em_ump_equivalence_of_cats
      : equivalence_of_cats (hom x e) (hom (mnd_incl B x) m).
    Proof.
      use make_equivalence_of_cats.
      - exact has_em_ump_adjunction_data.
      - exact has_em_ump_forms_equivalence.
    Defined.

    Definition has_em_ump_adj_equivalence_of_cats
      : adj_equivalence_of_cats (em_hom_functor e x)
      := adjointificiation has_em_ump_equivalence_of_cats.
  End UMPIsUniversal.

  Definition has_em_ump_is_universal
             {e : em_cone}
             (He : has_em_ump e)
    : is_universal_em_cone e.
  Proof.
    intro x.
    exact (has_em_ump_adj_equivalence_of_cats He x).
  Defined.

  Section IsUniversalHasUMP.
    Context {e : em_cone}
            (He : is_universal_em_cone e).

    Definition is_universal_has_em_ump_1_help_cell_data
               (q : em_cone)
      : mnd_cell_data
          (# (mnd_incl B) (right_adjoint (He q) (mor_of_em_cone q)) · mor_of_em_cone e)
          (em_hom_functor_ob e q (right_adjoint (He q) (mor_of_em_cone q)))
      := id2 _.

    Definition is_universal_has_em_ump_1_help_cell_is_mnd_cell
               (q : em_cone)
      : is_mnd_cell (is_universal_has_em_ump_1_help_cell_data q).
    Proof.
      unfold is_mnd_cell, is_universal_has_em_ump_1_help_cell_data.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite id2_left, id2_right.
      cbn.
      do 3 refine (vassocl _ _ _ @ _).
      do 2 refine (_ @ vassocr _ _ _).
      do 2 apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      refine (!_).
      apply linvunitor_assoc.
    Qed.

    Definition is_universal_has_em_ump_1_help_cell
               (q : em_cone)
      : # (mnd_incl B) (right_adjoint (He q) (mor_of_em_cone q)) · mor_of_em_cone e
        ==>
        em_hom_functor_ob e q (right_adjoint (He q) (mor_of_em_cone q)).
    Proof.
      use make_mnd_cell.
      - exact (is_universal_has_em_ump_1_help_cell_data q).
      - exact (is_universal_has_em_ump_1_help_cell_is_mnd_cell q).
    Defined.

    Definition is_universal_has_em_ump_1
      : em_ump_1 e.
    Proof.
      intro q.
      use make_em_cone_mor.
      - exact (right_adjoint (He q) (mor_of_em_cone q)).
      - pose (z_iso_to_inv2cell
                (nat_z_iso_pointwise_z_iso
                   (counit_nat_z_iso_from_adj_equivalence_of_cats (He q))
                   (mor_of_em_cone q))).
        refine (comp_of_invertible_2cell _ i).
        use make_invertible_2cell.
        + exact (is_universal_has_em_ump_1_help_cell q).
        + apply is_invertible_mnd_2cell.
          cbn.
          unfold is_universal_has_em_ump_1_help_cell_data.
          is_iso.
    Defined.

    Section UMP2.
      Context {x : B}
              {g₁ g₂ : x --> e}
              (α : # (mnd_incl B) g₁ · mor_of_em_cone e
                   ==>
                   # (mnd_incl B) g₂ · mor_of_em_cone e).

      Let H : fully_faithful (em_hom_functor e x)
        := fully_faithful_from_equivalence _ _ _ (He x).

      Definition is_universal_has_em_ump_2_unique
        : isaprop
            (∑ (β : g₁ ==> g₂),
             ## (mnd_incl B) β ▹ mor_of_em_cone e = α).
      Proof.
        use invproofirrelevance.
        intros β₁ β₂.
        use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        use (invmaponpathsweq (make_weq _ (H g₁ g₂))).
        use eq_mnd_cell.
        exact (maponpaths pr1 (pr2 β₁ @ !(pr2 β₂))).
      Qed.

      Definition is_universal_has_em_ump_2_cell_mnd_cell_data
        : mnd_cell_data
            (em_hom_functor e x g₁)
            (em_hom_functor e x g₂)
        := pr1 α.

      Definition is_universal_has_em_ump_2_cell_mnd_cell_is_mnd_cell
        : is_mnd_cell is_universal_has_em_ump_2_cell_mnd_cell_data.
      Proof.
        unfold is_mnd_cell, is_universal_has_em_ump_2_cell_mnd_cell_data.
        cbn.
        pose (mnd_cell_endo α) as p.
        cbn in p.
        refine (_ @ p @ _).
        - apply maponpaths_2.
          do 2 refine (vassocl _ _ _ @ _).
          do 3 refine (_ @ vassocr _ _ _).
          do 2 apply maponpaths.
          rewrite <- !rwhisker_vcomp.
          rewrite !vassocr.
          rewrite runitor_rwhisker.
          rewrite !vassocl.
          rewrite linvunitor_assoc.
          apply idpath.
        - apply maponpaths.
          do 3 refine (vassocl _ _ _ @ _).
          do 2 refine (_ @ vassocr _ _ _).
          do 2 apply maponpaths.
          rewrite <- !rwhisker_vcomp.
          rewrite !vassocr.
          rewrite runitor_rwhisker.
          rewrite !vassocl.
          rewrite linvunitor_assoc.
          apply idpath.
      Qed.

      Definition is_universal_has_em_ump_2_cell_mnd_cell
        : em_hom_functor e x g₁ --> em_hom_functor e x g₂.
      Proof.
        use make_mnd_cell.
        - exact is_universal_has_em_ump_2_cell_mnd_cell_data.
        - exact is_universal_has_em_ump_2_cell_mnd_cell_is_mnd_cell.
      Defined.

      Definition is_universal_has_em_ump_2_cell
        : g₁ ==> g₂
        := invmap (make_weq _ (H g₁ g₂)) is_universal_has_em_ump_2_cell_mnd_cell.

      Definition is_universal_has_em_ump_2_eq
        : ## (mnd_incl B) is_universal_has_em_ump_2_cell ▹ mor_of_em_cone e = α.
      Proof.
        use eq_mnd_cell.
        exact (maponpaths
                 pr1
                 (homotweqinvweq
                    (make_weq _ (H g₁ g₂))
                    is_universal_has_em_ump_2_cell_mnd_cell)).
      Qed.
    End UMP2.

    Definition is_universal_has_em_ump_2
      : em_ump_2 e.
    Proof.
      intros x g₁ g₂ α.
      use iscontraprop1.
      - exact (is_universal_has_em_ump_2_unique α).
      - refine (is_universal_has_em_ump_2_cell α ,, _).
        exact (is_universal_has_em_ump_2_eq α).
    Defined.

    Definition is_universal_has_em_ump
      : has_em_ump e.
    Proof.
      split.
      - exact is_universal_has_em_ump_1.
      - exact is_universal_has_em_ump_2.
    Defined.
  End IsUniversalHasUMP.

  Definition has_em_ump_weq_is_universal_em_cone
             (HB_2_1 : is_univalent_2_1 B)
             (e : em_cone)
    : has_em_ump e ≃ is_universal_em_cone e.
  Proof.
    use weqimplimpl.
    - exact has_em_ump_is_universal.
    - exact is_universal_has_em_ump.
    - apply isaprop_has_em_ump.
      exact HB_2_1.
    - apply isaprop_is_universal_em_cone.
      exact HB_2_1.
  Defined.

  (*
   4. Definition via Eilenberg-Moore category
   *)

  (**
   4.1 The functor
   *)
  Definition is_em_universal_em_cone_functor_ob
             {e : em_cone}
             {x : B}
             (f : x --> e)
    : eilenberg_moore_cat (mnd_to_cat_Monad m x).
  Proof.
    use make_ob_eilenberg_moore.
    - exact (f · mor_of_mnd_mor (mor_of_em_cone e)).
    - exact (rassociator _ _ _ • (_ ◃ (mnd_mor_endo (mor_of_em_cone e) • lunitor _))).
    - abstract
        (cbn ;
         rewrite !vassocl ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite <- lwhisker_lwhisker_rassociator ;
         rewrite !vassocr ;
         rewrite <- rinvunitor_triangle ;
         rewrite !vassocl ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite lassociator_rassociator ;
         rewrite id2_left ;
         rewrite !lwhisker_vcomp ;
         rewrite !vassocr ;
         refine (_ @ lwhisker_id2 _ _) ;
         apply maponpaths ;
         use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
         rewrite id2_left ;
         pose (mnd_mor_unit (mor_of_em_cone e)) as p ;
         cbn in p ;
         rewrite id2_rwhisker, id2_right in p ;
         exact (!p)).
    - abstract
        (cbn ;
         rewrite !vassocl ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite <- lwhisker_lwhisker_rassociator ;
         rewrite !vassocl ;
         rewrite lwhisker_vcomp ;
         rewrite !vassocr ;
         etrans ;
           [ do 2 apply maponpaths ;
             apply maponpaths_2 ;
             exact (!(mnd_mor_mu (mor_of_em_cone e)))
           | ] ;
         cbn ;
         rewrite <- !lwhisker_vcomp ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         rewrite <- rassociator_rassociator ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
         rewrite lwhisker_vcomp ;
         rewrite rassociator_lassociator ;
         rewrite lwhisker_id2 ;
         rewrite id2_left ;
         rewrite !vassocr ;
         rewrite rwhisker_lwhisker_rassociator ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite !lwhisker_vcomp ;
         rewrite lunitor_triangle ;
         rewrite vcomp_lunitor ;
         rewrite !vassocr ;
         rewrite <- lunitor_triangle ;
         rewrite !vassocr ;
         rewrite rassociator_lassociator ;
         rewrite id2_left ;
         rewrite <- !lwhisker_vcomp ;
         rewrite !vassocr ;
         rewrite rwhisker_lwhisker_rassociator ;
         apply idpath).
  Defined.

  Definition is_em_universal_em_cone_functor_mor
             {e : em_cone}
             {x : B}
             {f g : x --> e}
             (α : f ==> g)
    : is_em_universal_em_cone_functor_ob f
      -->
      is_em_universal_em_cone_functor_ob g.
  Proof.
    use make_mor_eilenberg_moore.
    - exact (α ▹ _).
    - abstract
        (cbn ;
         rewrite !vassocr ;
         rewrite rwhisker_rwhisker_alt ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite vcomp_whisker ;
         apply idpath).
  Defined.

  Definition is_em_universal_em_cone_functor_data
             (e : em_cone)
             (x : B)
    : functor_data
        (hom x e)
        (eilenberg_moore_cat (mnd_to_cat_Monad m x)).
  Proof.
    use make_functor_data.
    - exact is_em_universal_em_cone_functor_ob.
    - exact (λ _ _ α, is_em_universal_em_cone_functor_mor α).
  Defined.

  Definition is_em_universal_em_cone_functor_is_functor
             (e : em_cone)
             (x : B)
    : is_functor (is_em_universal_em_cone_functor_data e x).
  Proof.
    split.
    - intros f.
      use eq_mor_eilenberg_moore ; cbn.
      rewrite id2_rwhisker.
      apply idpath.
    - intros f g h α β.
      use eq_mor_eilenberg_moore ; cbn.
      rewrite rwhisker_vcomp.
      apply idpath.
  Qed.

  Definition is_em_universal_em_cone_functor
             (e : em_cone)
             (x : B)
    : hom x e ⟶ eilenberg_moore_cat (mnd_to_cat_Monad m x).
  Proof.
    use make_functor.
    - exact (is_em_universal_em_cone_functor_data e x).
    - exact (is_em_universal_em_cone_functor_is_functor e x).
  Defined.

  (**
   4.2 The definition
   *)
  Definition is_em_universal_em_cone
             (e : em_cone)
    : UU
    := ∏ (x : B), adj_equivalence_of_cats (is_em_universal_em_cone_functor e x).

  (**
   4.3 It is a proposition
   *)
  Definition isaprop_is_em_universal_em_cone
             (HB_2_1 : is_univalent_2_1 B)
             (e : em_cone)
    : isaprop (is_em_universal_em_cone e).
  Proof.
    use impred ; intro x.
    use isofhlevelweqf.
    - exact (@left_adjoint_equivalence
               bicat_of_univ_cats
               (univ_hom HB_2_1 x e)
               (eilenberg_moore_univalent_cat
                  (univ_hom HB_2_1 _ _)
                  (mnd_to_cat_Monad m x))
               (is_em_universal_em_cone_functor e x)).
    - exact (@adj_equiv_is_equiv_cat
               (univ_hom HB_2_1 x e)
               _
               _).
    - apply isaprop_left_adjoint_equivalence.
      exact univalent_cat_is_univalent_2_1.
  Qed.

  (**
   5. Equivalence to the other two definitions
   *)
  Section EilenbergMooreEquivalence.
    Context (x : B).

    Definition eilenberg_moore_to_hom_ob_data
               (h : eilenberg_moore_cat (mnd_to_cat_Monad m x))
      : mnd_mor_data (mnd_incl B x) m.
    Proof.
      use make_mnd_mor_data.
      - exact (ob_of_eilenberg_moore_ob h).
      - exact (mor_of_eilenberg_moore_ob h • linvunitor _).
    Defined.

    Definition eilenberg_moore_to_hom_ob_laws
               (h : eilenberg_moore_cat (mnd_to_cat_Monad m x))
      : mnd_mor_laws (eilenberg_moore_to_hom_ob_data h).
    Proof.
      repeat split ; cbn.
      - rewrite id2_rwhisker, id2_right.
        rewrite !vassocr.
        refine (!(id2_left _) @ _).
        apply maponpaths_2.
        exact (!(eilenberg_moore_ob_unit h)).
      - rewrite !vassocl.
        rewrite lunitor_triangle.
        rewrite vcomp_lunitor.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite <- lunitor_triangle.
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          rewrite id2_left.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite !vassocl.
          rewrite linvunitor_lunitor.
          rewrite id2_right.
          apply idpath.
        }
        pose (eilenberg_moore_ob_mult h) as p.
        cbn in p.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocl in p.
        exact (!p).
    Qed.

    Definition eilenberg_moore_to_hom_ob
               (h : eilenberg_moore_cat (mnd_to_cat_Monad m x))
      : mnd_incl B x --> m.
    Proof.
      use make_mnd_mor.
      - exact (eilenberg_moore_to_hom_ob_data h).
      - exact (eilenberg_moore_to_hom_ob_laws h).
    Defined.

    Definition eilenberg_moore_to_hom_mor
               {h₁ h₂ : eilenberg_moore_cat (mnd_to_cat_Monad m x)}
               (α : h₁ --> h₂)
      : eilenberg_moore_to_hom_ob h₁ ==> eilenberg_moore_to_hom_ob h₂.
    Proof.
      use make_mnd_cell.
      - exact (mor_of_eilenberg_moore_mor α).
      - abstract
          (unfold is_mnd_cell ; cbn ;
           rewrite !vassocl ;
           rewrite lwhisker_hcomp ;
           rewrite <- linvunitor_natural ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           exact (eq_of_eilenberg_moore_mor α)).
    Defined.

    Definition eilenberg_moore_to_hom_data
      : functor_data
          (eilenberg_moore_cat (mnd_to_cat_Monad m x))
          (hom (mnd_incl B x) m).
    Proof.
      use make_functor_data.
      - exact eilenberg_moore_to_hom_ob.
      - exact (λ _ _ α, eilenberg_moore_to_hom_mor α).
    Defined.

    Definition eilenberg_moore_to_hom_is_functor
      : is_functor eilenberg_moore_to_hom_data.
    Proof.
      split.
      - intro h.
        use eq_mnd_cell ; cbn.
        apply idpath.
      - intros h₁ h₂ h₃ α β.
        use eq_mnd_cell ; cbn.
        apply idpath.
    Qed.

    Definition eilenberg_moore_to_hom
      : eilenberg_moore_cat (mnd_to_cat_Monad m x)
        ⟶
        hom (mnd_incl B x) m.
    Proof.
      use make_functor.
      - exact eilenberg_moore_to_hom_data.
      - exact eilenberg_moore_to_hom_is_functor.
    Defined.

    Definition hom_to_eilenberg_moore_ob
               (f : mnd_incl B x --> m)
      : eilenberg_moore_cat (mnd_to_cat_Monad m x).
    Proof.
      use make_ob_eilenberg_moore.
      - exact (mor_of_mnd_mor f).
      - exact (mnd_mor_endo f • lunitor _).
      - abstract
          (cbn ;
           rewrite !vassocr ;
           refine (maponpaths (λ z, z • _) (!(mnd_mor_unit f)) @ _) ;
           cbn ;
           rewrite id2_rwhisker ;
           rewrite id2_right ;
           apply linvunitor_lunitor).
      - abstract
          (cbn ;
           pose (mnd_mor_mu f) as p ;
           cbn in p ;
           rewrite !vassocl ;
           refine (maponpaths (λ z, _ • z) (vassocr _ _ _) @ _) ;
           refine (maponpaths (λ z, _ • (z • _)) (!p) @ _) ; clear p ;
           rewrite !vassocr ;
           rewrite rassociator_lassociator ;
           rewrite id2_left ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite !vassocr ;
           rewrite lunitor_triangle ;
           rewrite <- vcomp_lunitor ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite lunitor_triangle ;
           apply idpath).
    Defined.

    Definition hom_to_eilenberg_moore_mor
               {f g : mnd_incl B x --> m}
               (α : f ==> g)
      : hom_to_eilenberg_moore_ob f --> hom_to_eilenberg_moore_ob g.
    Proof.
      use make_mor_eilenberg_moore.
      - exact (cell_of_mnd_cell α).
      - abstract
          (cbn ;
           rewrite !vassocl ;
           rewrite <- vcomp_lunitor ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           exact (mnd_cell_endo α)).
    Defined.

    Definition hom_to_eilenberg_moore_data
      : functor_data
          (hom (mnd_incl B x) m)
          (eilenberg_moore_cat (mnd_to_cat_Monad m x)).
    Proof.
      use make_functor_data.
      - exact hom_to_eilenberg_moore_ob.
      - exact (λ _ _ α, hom_to_eilenberg_moore_mor α).
    Defined.

    Definition hom_to_eilenberg_moore_is_functor
      : is_functor hom_to_eilenberg_moore_data.
    Proof.
      split.
      - intro f.
        use eq_mor_eilenberg_moore ; cbn.
        apply idpath.
      - intros f g h α β.
        use eq_mor_eilenberg_moore ; cbn.
        apply idpath.
    Qed.

    Definition hom_to_eilenberg_moore
      : hom (mnd_incl B x) m
        ⟶
        eilenberg_moore_cat (mnd_to_cat_Monad m x).
    Proof.
      use make_functor.
      - exact hom_to_eilenberg_moore_data.
      - exact hom_to_eilenberg_moore_is_functor.
    Defined.

    Definition hom_to_eilenberg_moore_unit_data
      : nat_trans_data
          (functor_identity _)
          (eilenberg_moore_to_hom ∙ hom_to_eilenberg_moore).
    Proof.
      intro f.
      use make_mor_eilenberg_moore.
      - exact (id2 _).
      - abstract
          (cbn ;
           rewrite id2_rwhisker ;
           rewrite id2_left, id2_right ;
           rewrite !vassocl ;
           rewrite linvunitor_lunitor ;
           rewrite id2_right ;
           apply idpath).
    Defined.

    Definition hom_to_eilenberg_moore_unit_is_nat_trans
      : is_nat_trans _ _ hom_to_eilenberg_moore_unit_data.
    Proof.
      intros f g α.
      use eq_mor_eilenberg_moore ; cbn.
      rewrite id2_left, id2_right.
      apply idpath.
    Qed.

    Definition hom_to_eilenberg_moore_unit
      : functor_identity _ ⟹ eilenberg_moore_to_hom ∙ hom_to_eilenberg_moore.
    Proof.
      use make_nat_trans.
      - exact hom_to_eilenberg_moore_unit_data.
      - exact hom_to_eilenberg_moore_unit_is_nat_trans.
    Defined.

    Definition is_z_iso_hom_to_eilenberg_moore_unit
               (f : eilenberg_moore_cat (mnd_to_cat_Monad m x))
      : is_z_isomorphism (hom_to_eilenberg_moore_unit f).
    Proof.
      use is_z_iso_eilenberg_moore.
      use is_inv2cell_to_is_z_iso.
      cbn.
      is_iso.
    Defined.

    Definition hom_to_eilenberg_moore_counit_data
      : nat_trans_data
          (hom_to_eilenberg_moore ∙ eilenberg_moore_to_hom)
          (functor_identity _).
    Proof.
      intro f.
      use make_mnd_cell.
      - exact (id2 _).
      - abstract
          (unfold is_mnd_cell ;
           cbn ;
           rewrite id2_rwhisker, lwhisker_id2 ;
           rewrite id2_left, id2_right ;
           rewrite !vassocl ;
           rewrite lunitor_linvunitor ;
           apply id2_right).
    Defined.

    Definition hom_to_eilenberg_moore_counit_is_nat_trans
      : is_nat_trans _ _ hom_to_eilenberg_moore_counit_data.
    Proof.
      intros f g α.
      use eq_mnd_cell ; cbn.
      rewrite id2_left, id2_right.
      apply idpath.
    Qed.

    Definition hom_to_eilenberg_moore_counit
      : hom_to_eilenberg_moore ∙ eilenberg_moore_to_hom ⟹ functor_identity _.
    Proof.
      use make_nat_trans.
      - exact hom_to_eilenberg_moore_counit_data.
      - exact hom_to_eilenberg_moore_counit_is_nat_trans.
    Defined.

    Definition is_z_iso_hom_to_eilenberg_moore_counit
               (f : mnd_incl B x --> m)
      : is_z_isomorphism (hom_to_eilenberg_moore_counit f).
    Proof.
      use is_inv2cell_to_is_z_iso.
      use is_invertible_mnd_2cell.
      cbn.
      is_iso.
    Defined.
  End EilenbergMooreEquivalence.

  Definition eilenberg_moore_equiv_mnd_incl
             (x : B)
    : equivalence_of_cats
        (eilenberg_moore_cat (mnd_to_cat_Monad m x))
        (hom (mnd_incl B x) m).
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact (eilenberg_moore_to_hom x).
      + exact (hom_to_eilenberg_moore x).
      + exact (hom_to_eilenberg_moore_unit x).
      + exact (hom_to_eilenberg_moore_counit x).
    - split.
      + exact (is_z_iso_hom_to_eilenberg_moore_unit x).
      + exact (is_z_iso_hom_to_eilenberg_moore_counit x).
  Defined.

  Definition eilenberg_moore_adj_equiv_mnd_incl
             (x : B)
    : adj_equivalence_of_cats (eilenberg_moore_to_hom x)
    := adjointificiation (eilenberg_moore_equiv_mnd_incl x).

  Definition eilenberg_moore_adj_mnd_incl_nat_trans
             (e : em_cone)
             (x : B)
    : is_em_universal_em_cone_functor e x ∙ eilenberg_moore_to_hom x
      ⟹
      em_hom_functor e x.
  Proof.
    use make_nat_trans.
    - intro f.
      use make_mnd_cell.
      + apply id2.
      + abstract
          (unfold is_mnd_cell ; cbn ;
           rewrite id2_rwhisker, lwhisker_id2 ;
           rewrite id2_left, id2_right ;
           rewrite <- !lwhisker_vcomp ;
           rewrite !vassocl ;
           apply idpath).
    - abstract
        (intros f g α ;
         use eq_mnd_cell ;
         cbn ;
         rewrite id2_left, id2_right ;
         apply idpath).
  Defined.

  Definition eilenberg_moore_adj_mnd_incl_nat_z_iso
             (e : em_cone)
             (x : B)
    : nat_z_iso
        (is_em_universal_em_cone_functor e x ∙ eilenberg_moore_to_hom x)
        (em_hom_functor e x).
  Proof.
    use make_nat_z_iso.
    - exact (eilenberg_moore_adj_mnd_incl_nat_trans e x).
    - intro f.
      use is_inv2cell_to_is_z_iso.
      use is_invertible_mnd_2cell.
      cbn.
      is_iso.
  Defined.

  Definition is_universal_em_cone_weq_is_em_universal_em_cone
             (HB_2_1 : is_univalent_2_1 B)
             (e : em_cone)
    : is_universal_em_cone e ≃ is_em_universal_em_cone e.
  Proof.
    use weqimplimpl.
    - intros He x.
      use (two_out_of_three_first
             (is_em_universal_em_cone_functor e x)
             (eilenberg_moore_to_hom x)
             (em_hom_functor e x)
             (eilenberg_moore_adj_mnd_incl_nat_z_iso e x)).
      + apply eilenberg_moore_adj_equiv_mnd_incl.
      + exact (He x).
    - intros He x.
      use (two_out_of_three_comp
             (is_em_universal_em_cone_functor e x)
             (eilenberg_moore_to_hom x)
             (em_hom_functor e x)
             (eilenberg_moore_adj_mnd_incl_nat_z_iso e x)).
      + exact (He x).
      + apply eilenberg_moore_adj_equiv_mnd_incl.
    - apply isaprop_is_universal_em_cone.
      exact HB_2_1.
    - apply isaprop_is_em_universal_em_cone.
      exact HB_2_1.
  Defined.
End EMObject.

(**
 6. Bicategories with Eilenberg-Moore objects
 *)
Definition bicat_has_em
           (B : bicat)
  : UU
  := ∏ (m : mnd B),
     ∑ (e : em_cone m), has_em_ump m e.
