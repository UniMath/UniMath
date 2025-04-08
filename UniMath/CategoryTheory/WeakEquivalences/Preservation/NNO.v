(**
   In this file, we show that an arbitrary weak equivalence F : C -> D preserves a natural numbers object.
 *)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.

Local Open Scope cat.

Section WeakEquivalencesPreserveNNOs.

  Context {C D : category}
    {F : C ⟶ D} (Fw : is_weak_equiv F)
    {T_C : Terminal C} (N_C : NNO T_C)
    {d : D}
    (z_d : D⟦F T_C, d⟧)
    (s_d : D⟦d, d⟧)
    {c : C}
    (i : z_iso (F c) d).

  Let z_c : C⟦T_C, c⟧
      := fully_faithful_inv_hom (pr2 Fw) _ _ (z_d · z_iso_inv i).
  Let s_c : C⟦c, c⟧
      := fully_faithful_inv_hom (pr2 Fw) _ _ (i · s_d · z_iso_inv i).
  Let ext_c : C⟦N_C, c⟧ := NNO_mor _ N_C z_c s_c.
  Let ext_d : D⟦F N_C, d⟧ := #F ext_c · i.

  Lemma weak_equiv_preserves_NNO_zero
    : # F (zeroNNO T_C N_C) · ext_d = z_d.
  Proof.
    refine (assoc _ _ _ @ _).
    etrans. {
      apply maponpaths_2.
      apply pathsinv0, functor_comp.
    }
    etrans. {
      apply maponpaths_2, maponpaths.
      exact (NNO_mor_Z _ N_C z_c s_c).
    }
    etrans. {
      apply maponpaths_2.
      apply functor_on_fully_faithful_inv_hom.
    }
    refine (assoc' _ _ _ @ _).
    refine (_ @ id_right _).
    apply maponpaths.
    apply z_iso_after_z_iso_inv.
  Qed.

  Lemma weak_equiv_preserves_NNO_mult
    : # F (sucNNO T_C N_C) · ext_d = ext_d · s_d.
  Proof.
    refine (assoc _ _ _ @ _).
    etrans. {
      apply maponpaths_2.
      apply pathsinv0, functor_comp.
    }
    etrans. {
      apply maponpaths_2, maponpaths.
      exact (NNO_mor_S _ N_C z_c s_c).
    }

    etrans. {
      apply maponpaths_2.
      rewrite functor_comp.
      apply maponpaths.
      apply functor_on_fully_faithful_inv_hom.
    }
    rewrite ! assoc'.
    etrans. {
      do 3 apply maponpaths.
      apply z_iso_after_z_iso_inv.
    }
    rewrite id_right.
    now rewrite assoc.
  Qed.

  Lemma weak_equiv_preserves_NNO_uvp_commutation_zero
    (ϕ : ∑ u : D ⟦ F N_C, d ⟧, # F (zeroNNO T_C N_C) · u = z_d × # F (sucNNO T_C N_C) · u = u · s_d)
    : zeroNNO T_C N_C
        · fully_faithful_inv_hom (pr2 Fw) _ _ (pr1 ϕ · z_iso_inv i)
      = z_c.
  Proof.
    apply (faithful_reflects_morphism_equality _ (pr2 Fw)).
    etrans.
    2: { apply pathsinv0, functor_on_fully_faithful_inv_hom. }
    etrans. { apply functor_comp. }
    etrans. { apply maponpaths, functor_on_fully_faithful_inv_hom. }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    exact (pr12 ϕ).
  Qed.

  Lemma weak_equiv_preserves_NNO_uvp_commutation_mult
    (ϕ : ∑ u : D ⟦ F N_C, d ⟧, # F (zeroNNO T_C N_C) · u = z_d × # F (sucNNO T_C N_C) · u = u · s_d)
    : sucNNO T_C N_C · fully_faithful_inv_hom (pr2 Fw) _ _ (pr1 ϕ · z_iso_inv i)
      = fully_faithful_inv_hom (pr2 Fw) _ _ (pr1 ϕ · z_iso_inv i) · s_c.
  Proof.
    apply (faithful_reflects_morphism_equality _ (pr2 Fw)).
    etrans. { apply functor_comp. }
    etrans.
    2: { apply pathsinv0, functor_comp. }
    etrans.
    2: { apply maponpaths_2, pathsinv0, functor_on_fully_faithful_inv_hom. }
    etrans.
    2: { apply maponpaths, pathsinv0, functor_on_fully_faithful_inv_hom. }
    etrans. { apply maponpaths, functor_on_fully_faithful_inv_hom. }
    rewrite ! assoc.
    apply maponpaths_2.
    etrans. { apply (pr22 ϕ). }
    rewrite ! assoc'.
    apply maponpaths.
    refine (! id_left _ @ _ @ assoc' _ _ _).
    apply maponpaths_2.
    apply pathsinv0, z_iso_after_z_iso_inv.
  Qed.

  Lemma weak_equiv_preserves_NNO_uvp_uniqueness
    : isaprop (∑ u : D ⟦ F N_C, d ⟧,
            # F (zeroNNO T_C N_C) · u = z_d × # F (sucNNO T_C N_C) · u = u · s_d).
  Proof.
    use invproofirrelevance.
    intros ϕ₁ ϕ₂.
    use subtypePath.
    { intro ; apply isapropdirprod ; apply homset_property. }
    use (cancel_z_iso _ _ (z_iso_inv i)).
    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).
    apply maponpaths.

    use (NNO_mor_unique _ N_C z_c s_c).
    - apply weak_equiv_preserves_NNO_uvp_commutation_zero.
    - apply weak_equiv_preserves_NNO_uvp_commutation_zero.
    - apply weak_equiv_preserves_NNO_uvp_commutation_mult.
    - apply weak_equiv_preserves_NNO_uvp_commutation_mult.
  Qed.

  Corollary weak_equiv_preserves_NNO_uvp
    : ∃! u : D ⟦ F N_C, d ⟧, # F (zeroNNO T_C N_C) · u = z_d × # F (sucNNO T_C N_C) · u = u · s_d.
  Proof.
    use iscontraprop1.
    { apply weak_equiv_preserves_NNO_uvp_uniqueness. }
    simple refine (_ ,, _ ,, _).
    - exact ext_d.
    - exact weak_equiv_preserves_NNO_zero.
    - exact weak_equiv_preserves_NNO_mult.
  Defined.

End WeakEquivalencesPreserveNNOs.

Proposition weak_equiv_preserves_NNO
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  : preserves_NNO (weak_equiv_preserves_terminal _ Fw).
Proof.
  intros T_C N_C d s_d z_d.

  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw d)).
  intros [c i].

  exact (weak_equiv_preserves_NNO_uvp Fw N_C s_d z_d i).
Qed.

Corollary weak_equiv_creates_NNO
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  {T : Terminal C}
  (N : NNO T)
  : NNO (weak_equiv_creates_terminal Fw T).
Proof.
  exact (make_NNO _ _ _ _ (weak_equiv_preserves_NNO Fw _ N)).
Defined.

Corollary weak_equiv_creates_NNO'
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  {T : Terminal C}
  (N : NNO T)
  (T' : Terminal D)
  : NNO T'.
Proof.
  set (N' := weak_equiv_creates_NNO Fw N).
  exact (NNO_transport_along_terminal _ _ N').
Defined.
