(************************************************************************************

 Local equivalences and monads

 One core theorem in the formal theory of monads is about the interaction between a
 duality involution and monads. More specifically, Theorem 12 in the paper 'The formal
 theory of monads' by Ross Street says that whenever a bicategory `B` has a duality
 involution and Eilenberg-Moore objects, then the bicategory `B^co` (2-cells reversed)
 also has Eilenberg-Moore objects. If we instantiate this theorem to the bicategory
 of categories (whose duality involution is given by the opposite category), then we
 see that the Eilenberg-Moore category for a comonad can be constructed via the
 Eilenberg-Moore category for a monad. Concretely, if we have a comonad `C` on a
 category `C`, then we obtain a monad `M` on the opposite category `C^op`.

 One of the intermediate steps of this theorem is proving the universal property of
 the Eilenberg-Moore object. To do so, we show that the natural functor between the
 hom-categories is an adjoint equivalence. As an intermediate step, we construct an
 adjoint equivalence between `hom (mnd_incl B₂ (F x)) (psfunctor_on_monad F m)`
 and `hom (mnd_incl B₁ x) m`.

 When we use this theorem, we have a duality involution. Since every duality
 involution also is a local equivalence, all the material in this file can be reused.

 References
 - The formal theory of monads, Ross Street

 Contents
 1. Action on objects
 2. Action on morphisms
 3. The functor between the hom categories
 4. The functor is faithful
 5. The functor is full
 6. The functor is essentially surjective
 7. The adjoint equivalence

 ************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.Examples.PsfunctorOnMonad.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Properties.
Require Import UniMath.Bicategories.PseudoFunctors.LocalEquivalenceProperties.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.

Local Open Scope cat.

Opaque local_equivalence_unit_inv2cell
  local_equivalence_counit_inv2cell
  local_equivalence_inv_onecell_comp
  local_equivalence_inv_twocell.

Section LocalEquivalenceMonad.
  Context {B₁ B₂ : bicat}
          (HB₁ : is_univalent_2_1 B₁)
          (HB₂ : is_univalent_2_1 B₂)
          {F : psfunctor B₁ B₂}
          (HF : local_equivalence HB₁ HB₂ F)
          (m : mnd B₁)
          (x : B₁).

  Let Fm : mnd B₂ := psfunctor_on_mnd F m.

  (** * 1. Action on objects *)
  Section Ob.
    Context (f : mnd_incl B₂ (F x) --> Fm).

    Definition local_equivalence_mnd_ob_data
      : mnd_mor_data (mnd_incl B₁ x) m.
    Proof.
      use make_mnd_mor_data.
      - exact (local_equivalence_inv_onecell HF (mor_of_mnd_mor f)).
      - exact ((_ ◃ local_equivalence_unit_inv2cell HF _)
               • (local_equivalence_inv_onecell_comp HF _ _)^-1
               • (local_equivalence_inv_twocell HF (mnd_mor_endo f • lunitor _))
               • linvunitor _).
    Defined.

    Proposition local_equivalence_mnd_ob_laws
      : mnd_mor_laws local_equivalence_mnd_ob_data.
    Proof.
      split.
      - cbn.
        rewrite id2_rwhisker.
        rewrite id2_right.
        refine (!(id2_left _) @ _).
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite <- local_equivalence_inv_twocell_id.
        rewrite <- linvunitor_lunitor.
        rewrite !local_equivalence_inv_twocell_comp.
        rewrite !vassocr.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (_ @ mnd_mor_unit f).
          cbn.
          rewrite id2_rwhisker.
          rewrite id2_right.
          apply idpath.
        }
        cbn -[psfunctor_id].
        rewrite !local_equivalence_inv_twocell_comp.
        rewrite local_equivalence_twocell_rinvunitor.
        apply maponpaths_2.
        rewrite !vassocl.
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !lwhisker_vcomp.
          apply maponpaths.
          rewrite !vassocl.
          rewrite local_equivalence_unit_natural.
          apply idpath.
        }
        etrans.
        {
          apply maponpaths.
          rewrite <- !lwhisker_vcomp.
          rewrite !vassocl.
          do 2 apply maponpaths.
          rewrite <- local_equivalence_twocell_lwhisker_inv.
          apply idpath.
        }
        rewrite <- lwhisker_vcomp.
        rewrite local_equivalence_inv_twocell_comp.
        rewrite !vassocr.
        apply maponpaths_2.
        use vcomp_move_R_Mp ; [ is_iso | ].
        cbn -[psfunctor_id].
        rewrite local_equivalence_twocell_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite lwhisker_vcomp.
        apply maponpaths.
        rewrite !vassocl.
        rewrite vcomp_linv.
        apply id2_right.
      - cbn -[psfunctor_comp].
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite lunitor_triangle.
          rewrite vcomp_lunitor.
          apply idpath.
        }
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          do 3 apply maponpaths_2.
          rewrite <- lunitor_triangle.
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          apply id2_left.
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
        rewrite !local_equivalence_inv_twocell_comp.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite <- !rwhisker_vcomp.
          rewrite !vassocl.
          do 2 apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite <- local_equivalence_twocell_rwhisker_inv.
            rewrite !vassocl.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite <- local_equivalence_twocell_rwhisker_inv.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          do 5 apply maponpaths.
          rewrite <- !local_equivalence_inv_twocell_comp.
          apply maponpaths.
          rewrite !vassocr.
          pose (p := mnd_mor_mu f).
          cbn -[psfunctor_comp] in p.
          rewrite !vassocl in p.
          rewrite lunitor_triangle in p.
          rewrite vcomp_lunitor in p.
          rewrite <- lunitor_triangle in p.
          rewrite !vassocl in p.
          rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) in p.
          rewrite rassociator_lassociator in p.
          rewrite id2_left in p.
          pose (q := maponpaths (λ z, rassociator _ _ _ • z) p).
          cbn -[psfunctor_comp] in q.
          rewrite !vassocr in q.
          rewrite rassociator_lassociator in q.
          rewrite id2_left in q.
          exact q.
        }
        rewrite !local_equivalence_inv_twocell_comp.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite <- local_equivalence_twocell_rassociator_inv.
          rewrite !vassocl.
          apply idpath.
        }
        etrans.
        {
          rewrite !vassocr.
          rewrite <- lwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rwhisker_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocl.
        rewrite local_equivalence_twocell_lwhisker_inv.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !lwhisker_vcomp.
        apply maponpaths.
        rewrite !vassocl.
        rewrite local_equivalence_unit_natural.
        rewrite local_equivalence_inv_twocell_comp.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        (** Here we use how `local_equivalence_inv_onecell_comp` is defined *)
        Transparent local_equivalence_inv_onecell_comp.
        cbn -[psfunctor_comp].
        rewrite !vassocl.
        rewrite <- local_equivalence_inv_twocell_comp.
        etrans.
        {
          do 4 apply maponpaths.
          rewrite !vassocl.
          rewrite <- !local_equivalence_unit_triangle_inv.
          cbn -[psfunctor_comp].
          rewrite <- psfunctor_rwhisker.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          rewrite <- psfunctor_lwhisker.
          rewrite !vassocr.
          rewrite vcomp_linv.
          apply id2_left.
        }
        rewrite <- psfunctor_vcomp.
        rewrite <- local_equivalence_unit_natural.
        rewrite !vassocr.
        refine (_ @ id2_left _).
        apply maponpaths_2.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          rewrite rwhisker_vcomp.
          rewrite vcomp_rinv.
          rewrite id2_rwhisker.
          apply id2_right.
        }
        rewrite lwhisker_vcomp.
        rewrite vcomp_rinv.
        apply lwhisker_id2.
    Qed.

    Opaque local_equivalence_inv_onecell_comp.

    Definition local_equivalence_mnd_ob
      : mnd_incl B₁ x --> m.
    Proof.
      use make_mnd_mor.
      - exact local_equivalence_mnd_ob_data.
      - exact local_equivalence_mnd_ob_laws.
    Defined.
  End Ob.

  (** * 2. Action on morphisms *)
  Section Mor.
    Context {f g : mnd_incl B₂ (F x) --> Fm}
            (τ : f ==> g).

    Definition local_equivalence_mnd_data_mor_data
      : mnd_cell_data
          (local_equivalence_mnd_ob f)
          (local_equivalence_mnd_ob g)
      := local_equivalence_inv_twocell HF (cell_of_mnd_cell τ).

    Proposition local_equivalence_mnd_data_mor_laws
      : is_mnd_cell local_equivalence_mnd_data_mor_data.
    Proof.
      unfold is_mnd_cell ; cbn ; unfold local_equivalence_mnd_data_mor_data.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite lwhisker_hcomp.
        rewrite <- linvunitor_natural.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- local_equivalence_inv_twocell_comp.
      rewrite !vassocl.
      rewrite <- vcomp_lunitor.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (mnd_cell_endo τ).
        }
        rewrite !vassocl.
        apply local_equivalence_inv_twocell_comp.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      use vcomp_move_R_pM ; [ is_iso | ].
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn.
      rewrite local_equivalence_twocell_rwhisker.
      apply idpath.
    Qed.

    Definition local_equivalence_mnd_data_mor
      : local_equivalence_mnd_ob f ==> local_equivalence_mnd_ob g.
    Proof.
      use make_mnd_cell.
      - exact local_equivalence_mnd_data_mor_data.
      - exact local_equivalence_mnd_data_mor_laws.
    Defined.
  End Mor.

  Arguments local_equivalence_mnd_data_mor_data {f g} τ /.

  (** * 3. The functor *)
  Definition local_equivalence_mnd_data
    : functor_data
        (hom (mnd_incl B₂ (F x)) Fm)
        (hom (mnd_incl B₁ x) m).
  Proof.
    use make_functor_data.
    - exact local_equivalence_mnd_ob.
    - exact @local_equivalence_mnd_data_mor.
  Defined.

  Proposition local_equivalence_mnd_laws
    : is_functor local_equivalence_mnd_data.
  Proof.
    split.
    - intros f.
      use eq_mnd_cell ; cbn.
      apply local_equivalence_inv_twocell_id.
    - intros f g h τ θ.
      use eq_mnd_cell ; cbn.
      apply local_equivalence_inv_twocell_comp.
  Qed.

  Definition local_equivalence_mnd
    : hom (mnd_incl B₂ (F x)) Fm ⟶ hom (mnd_incl B₁ x) m.
  Proof.
    use make_functor.
    - exact local_equivalence_mnd_data.
    - exact local_equivalence_mnd_laws.
  Defined.

  (** * 4. The functor is faithful *)
  Proposition faithful_local_equivalence_mnd
    : faithful local_equivalence_mnd.
  Proof.
    intros f g τ.
    use invproofirrelevance.
    intros θ₁ θ₂.
    induction θ₁ as [ θ₁ p₁ ].
    induction θ₂ as [ θ₂ p₂ ].
    use subtypePath.
    {
      intro.
      apply cellset_property.
    }
    cbn ; cbn in p₁, p₂.
    use eq_mnd_cell.
    use (vcomp_lcancel (local_equivalence_counit_inv2cell HF _)).
    {
      apply property_from_invertible_2cell.
    }
    use (vcomp_rcancel ((local_equivalence_counit_inv2cell HF _)^-1)).
    {
      is_iso.
    }
    rewrite <- !psfunctor_local_equivalence_inv_twocell.
    apply maponpaths.
    exact (maponpaths cell_of_mnd_cell (p₁ @ !p₂)).
  Qed.

  (** * 5. The functor is full *)
  Section Fullness.
    Context {f g : mnd_incl B₂ (F x) --> Fm}
            (τ : local_equivalence_mnd f --> local_equivalence_mnd g).

    Definition full_local_equivalence_mnd_cell_data
      : mnd_cell_data f g
      := (local_equivalence_counit_inv2cell HF (mor_of_mnd_mor f))^-1
         • ##F (cell_of_mnd_cell τ)
         • local_equivalence_counit_inv2cell HF (mor_of_mnd_mor g).

    Arguments full_local_equivalence_mnd_cell_data /.

    Proposition full_local_equivalence_mnd_cell_laws
      : is_mnd_cell full_local_equivalence_mnd_cell_data.
    Proof.
      unfold is_mnd_cell ; cbn.
      pose (maponpaths (λ z, z • lunitor _) (mnd_cell_endo τ)) as p.
      cbn in p.
      rewrite !vassocl in p.
      rewrite linvunitor_lunitor in p.
      rewrite id2_right in p.
      rewrite vcomp_lunitor in p.
      rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)) in p.
      rewrite linvunitor_lunitor in p.
      rewrite id2_left in p.
      rewrite !vassocr in p.
      rewrite vcomp_whisker in p.
      rewrite !vassocl in p.
      pose (maponpaths
              (λ z, (_ ◃ (local_equivalence_unit_inv2cell HF (endo_of_mnd m))^-1) • z)
              p)
        as q.
      cbn in q.
      rewrite !vassocr in q.
      clear p.
      rewrite !lwhisker_vcomp in q.
      rewrite !vcomp_linv in q.
      rewrite !lwhisker_id2 in q.
      rewrite !id2_left in q.
      rewrite !vassocl in q.
      use (vcomp_rcancel (lunitor _)).
      {
        is_iso.
      }
      rewrite !vassocl.
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite <- local_equivalence_counit_natural_alt.
        apply idpath.
      }
      rewrite !vassocl.
      pose (maponpaths
              (λ z, local_equivalence_inv_onecell_comp _ _ _ • z)
              q)
        as r.
      cbn in r.
      rewrite !vassocr in r.
      rewrite vcomp_rinv in r.
      rewrite id2_left in r.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- psfunctor_vcomp.
        rewrite r.
        apply idpath.
      }
      clear q r.
      rewrite !vassocr.
      etrans.
      {
        rewrite !psfunctor_vcomp.
        rewrite !vassocl.
        rewrite local_equivalence_counit_natural.
        apply idpath.
      }
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        Transparent local_equivalence_inv_onecell_comp.
        cbn -[psfunctor_comp].
        rewrite psfunctor_vcomp.
        rewrite !vassocl.
        rewrite local_equivalence_counit_natural.
        rewrite !vassocr.
        rewrite local_equivalence_triangle1.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        cbn -[psfunctor_comp].
        rewrite !psfunctor_vcomp.
        rewrite !vassocr.
        rewrite local_equivalence_counit_natural_alt.
        rewrite !vassocl.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !vassocr.
          rewrite local_equivalence_triangle1_inv.
          apply id2_left.
        }
        rewrite psfunctor_rwhisker.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_rinv.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      apply id2_right.
    Qed.

    Opaque local_equivalence_inv_onecell_comp.

    Definition full_local_equivalence_mnd_cell
      : f ==> g.
    Proof.
      use make_mnd_cell.
      - exact full_local_equivalence_mnd_cell_data.
      - exact full_local_equivalence_mnd_cell_laws.
    Defined.

    Proposition full_local_equivalence_mnd_eq
      : local_equivalence_mnd_data_mor full_local_equivalence_mnd_cell = τ.
    Proof.
      use eq_mnd_cell ; cbn.
      rewrite !vassocl.
      rewrite !local_equivalence_inv_twocell_comp.
      rewrite local_equivalence_counit_triangle.
      rewrite <- local_equivalence_unit_natural_alt.
      rewrite !vassocr.
      refine (_ @ id2_left _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (local_equivalence_counit_triangle_inv HF (mor_of_mnd_mor f)).
      }
      apply vcomp_rinv.
    Qed.
  End Fullness.

  Proposition full_local_equivalence_mnd
    : full local_equivalence_mnd.
  Proof.
    intros f g τ.
    simple refine (hinhpr (_ ,, _)).
    - exact (full_local_equivalence_mnd_cell τ).
    - exact (full_local_equivalence_mnd_eq τ).
  Qed.

  Proposition fully_faithful_local_equivalence_mnd
    : fully_faithful local_equivalence_mnd.
  Proof.
    use full_and_faithful_implies_fully_faithful.
    split.
    - exact full_local_equivalence_mnd.
    - exact faithful_local_equivalence_mnd.
  Qed.

  (** * 6. The functor is essentially surjective *)
  Section EssentiallySurjective.
    Context (f : mnd_incl B₁ x --> m).

    Definition essentially_surjective_local_equivalence_mnd_inv_data
      : mnd_mor_data (mnd_incl B₂ (F x)) Fm.
    Proof.
      use make_mnd_mor_data.
      - exact (#F (mor_of_mnd_mor f)).
      - exact (psfunctor_comp F _ _
               • ##F(mnd_mor_endo f)
               • (psfunctor_comp F _ _)^-1
               • ((psfunctor_id F _)^-1 ▹ _)).
    Defined.

    Proposition essentially_surjective_local_equivalence_mnd_inv_laws
      : mnd_mor_laws essentially_surjective_local_equivalence_mnd_inv_data.
    Proof.
      split.
      - cbn -[psfunctor_id psfunctor_comp].
        rewrite id2_rwhisker, id2_right.
        refine (!_).
        etrans.
        {
          rewrite <- lwhisker_vcomp.
          rewrite !vassocl.
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite <- psfunctor_lwhisker.
            rewrite !vassocl.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite <- psfunctor_rinvunitor.
          rewrite <- !psfunctor_vcomp.
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (!(mnd_mor_unit f)).
        }
        cbn -[psfunctor_id psfunctor_comp].
        rewrite id2_rwhisker, id2_right.
        rewrite !vassocl.
        use vcomp_move_R_Mp ; [ is_iso | ].
        cbn -[psfunctor_id psfunctor_comp].
        rewrite !vassocr.
        rewrite <- psfunctor_linvunitor.
        apply idpath.
      - cbn -[psfunctor_id psfunctor_comp].
        rewrite <- !rwhisker_vcomp.
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- psfunctor_lwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          do 2 apply maponpaths_2.
          rewrite <- psfunctor_vcomp.
          apply maponpaths.
          exact (!(mnd_mor_mu f)).
        }
        rewrite !psfunctor_vcomp.
        etrans.
        {
          rewrite !vassocr.
          do 7 apply maponpaths_2.
          rewrite psfunctor_lassociator.
          apply idpath.
        }
        rewrite !vassocl.
        do 2 apply maponpaths.
        etrans.
        {
          rewrite !vassocr.
          rewrite psfunctor_rwhisker.
          rewrite !vassocl.
          apply idpath.
        }
        apply maponpaths.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn -[psfunctor_id psfunctor_comp].
        etrans.
        {
          rewrite !vassocr.
          rewrite psfunctor_rassociator.
          rewrite !vassocl.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite rwhisker_rwhisker_alt.
          rewrite !vassocl.
          apply idpath.
        }
        apply maponpaths.
        etrans.
        {
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply idpath.
        }
        apply maponpaths.
        etrans.
        {
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite psfunctor_lwhisker.
          rewrite !vassocl.
          apply idpath.
        }
        apply maponpaths.
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply idpath.
        }
        use vcomp_move_R_pM ; [ is_iso | ].
        cbn -[psfunctor_id psfunctor_comp].
        etrans.
        {
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          rewrite rwhisker_lwhisker.
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite !vassocr.
          rewrite psfunctor_lassociator.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocl.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite psfunctor_rwhisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_rinv.
          apply id2_left.
        }
        rewrite !rwhisker_vcomp.
        apply maponpaths.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn -[psfunctor_id psfunctor_comp].
        etrans.
        {
          rewrite !vassocr.
          rewrite <- psfunctor_lunitor.
          apply idpath.
        }
        rewrite vcomp_lunitor.
        apply idpath.
    Qed.

    Definition essentially_surjective_local_equivalence_mnd_inv
      : mnd_incl B₂ (F x) --> Fm.
    Proof.
      use make_mnd_mor.
      - exact essentially_surjective_local_equivalence_mnd_inv_data.
      - exact essentially_surjective_local_equivalence_mnd_inv_laws.
    Defined.

    Definition essentially_surjective_local_equivalence_mnd_cell_data
      : mnd_cell_data
          (local_equivalence_mnd essentially_surjective_local_equivalence_mnd_inv)
          f
      := (local_equivalence_unit_inv2cell HF (mor_of_mnd_mor f))^-1.

    Arguments essentially_surjective_local_equivalence_mnd_cell_data /.

    Proposition essentially_surjective_local_equivalence_mnd_cell_laws
      : is_mnd_cell essentially_surjective_local_equivalence_mnd_cell_data.
    Proof.
      unfold is_mnd_cell.
      cbn -[psfunctor_id psfunctor_comp].
      rewrite !vassocl.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite lwhisker_hcomp.
        rewrite <- linvunitor_natural.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        do 3 apply maponpaths.
        rewrite psfunctor_lunitor.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite vcomp_linv.
          rewrite id2_rwhisker.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
      }
      Transparent local_equivalence_inv_onecell_comp.
      cbn -[psfunctor_comp].
      Opaque local_equivalence_inv_onecell_comp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite <- local_equivalence_inv_twocell_comp.
        apply maponpaths.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite <- !local_equivalence_unit_triangle_inv.
        cbn -[psfunctor_comp].
        rewrite !vassocl.
        rewrite <- psfunctor_rwhisker.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite <- psfunctor_lwhisker.
        rewrite !vassocr.
        rewrite vcomp_linv.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !local_equivalence_inv_twocell_comp.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- local_equivalence_inv_twocell_comp.
        rewrite <- psfunctor_vcomp.
        rewrite <- local_equivalence_unit_natural_alt.
        rewrite !vassocl.
        rewrite lunitor_linvunitor.
        rewrite id2_right.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- local_equivalence_inv_twocell_comp.
          rewrite <- psfunctor_vcomp.
          rewrite <- local_equivalence_unit_natural_alt.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite vcomp_rinv.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_left.
    Qed.

    Definition essentially_surjective_local_equivalence_mnd_cell
      : local_equivalence_mnd essentially_surjective_local_equivalence_mnd_inv ==> f.
    Proof.
      use make_mnd_cell.
      - exact essentially_surjective_local_equivalence_mnd_cell_data.
      - exact essentially_surjective_local_equivalence_mnd_cell_laws.
    Defined.

    Definition essentially_surjective_local_equivalence_mnd_inv2cell
      : invertible_2cell
          (local_equivalence_mnd
             essentially_surjective_local_equivalence_mnd_inv)
          f.
    Proof.
      use make_invertible_2cell.
      - exact essentially_surjective_local_equivalence_mnd_cell.
      - use is_invertible_mnd_2cell.
        cbn.
        unfold essentially_surjective_local_equivalence_mnd_cell_data.
        is_iso.
    Defined.
  End EssentiallySurjective.

  Proposition essentially_surjective_local_equivalence_mnd
    : essentially_surjective local_equivalence_mnd.
  Proof.
    intros f.
    simple refine (hinhpr (_ ,, _)).
    - exact (essentially_surjective_local_equivalence_mnd_inv f).
    - use inv2cell_to_z_iso.
      exact (essentially_surjective_local_equivalence_mnd_inv2cell f).
  Defined.

  (** * 7. The adjoint equivalence *)
  Definition adj_equivalence_of_cats_local_equivalence_mnd
    : adj_equivalence_of_cats local_equivalence_mnd.
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univ_hom.
      use is_univalent_2_1_mnd.
      exact HB₂.
    - exact fully_faithful_local_equivalence_mnd.
    - exact essentially_surjective_local_equivalence_mnd.
  Defined.
End LocalEquivalenceMonad.
