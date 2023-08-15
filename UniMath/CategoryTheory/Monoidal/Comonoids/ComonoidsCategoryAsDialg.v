(**
In this file, the symmetric monoidal category of comonoids internal to a monoidal category is defined.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Sigma.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.

Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Comonoids.

Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SymmetricMonoidalDialgebras.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsMonoidal.

Local Open Scope cat.

Import MonoidalNotations.

Section DiagFunctor.

  Context (V : sym_monoidal_cat).

  Notation "x ⊗ y" := (monoidal_cat_tensor_pt x y).
  Notation "f ⊗⊗ g" := (monoidal_cat_tensor_mor f g) (at level 31).

  Definition diag_functor_data
    : functor_data V V.
  Proof.
    use make_functor_data.
    - exact (λ x, x ⊗ x).
    - exact (λ _ _ f, f ⊗⊗ f).
  Defined.

  Lemma diag_is_functor
    : is_functor diag_functor_data.
  Proof.
    split ; intro ; intros.
    - apply (bifunctor_distributes_over_id (F := V)) ; apply (pr21 V).
    - apply (bifunctor_distributes_over_comp (F := V)) ; apply (pr21 V).
  Qed.

  Definition diag_functor
    : functor V V.
  Proof.
    exists diag_functor_data.
    exact diag_is_functor.
  Defined.

  Definition diag_preserves_tensor_data
    : preserves_tensordata V V diag_functor.
  Proof.
    exact (λ x y, rearrange_prod (pr2 V) x x y y).
  Defined.

  Definition diag_preserves_unit
    : preserves_unit V V diag_functor.
  Proof.
    exact (luinv^{V}_{I_{V}}).
  Defined.

  Definition diag_functor_fmonoidal_data
    : fmonoidal_data V V diag_functor.
  Proof.
    exists diag_preserves_tensor_data.
    exact diag_preserves_unit.
  Defined.

  Lemma diag_functor_fmonoidal_nat_left
    : preserves_tensor_nat_left (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
  Proof.
    intros y x1 x2 f.
    apply pathsinv0.
    refine (_ @ precompose_rearrange_prod (pr2 V) (identity y) (identity y) f f @ _).
    - now rewrite (when_bifunctor_becomes_leftwhiskering V).
    - rewrite <- (when_bifunctor_becomes_leftwhiskering V).
      rewrite (bifunctor_distributes_over_id (F := V)) ; try (apply (pr21 V)).
      apply idpath.
  Qed.

  Lemma diag_functor_fmonoidal_nat_right
    : preserves_tensor_nat_right (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
  Proof.
    intros x1 x2 y f.
    apply pathsinv0.
    refine (_ @ precompose_rearrange_prod (pr2 V) f f (identity y) (identity y) @ _).
    - now rewrite (when_bifunctor_becomes_rightwhiskering V).
    - rewrite <- (when_bifunctor_becomes_rightwhiskering V).
      rewrite (bifunctor_distributes_over_id (F := V)) ; try (apply (pr21 V)).
      apply idpath.
  Qed.

  Lemma diag_functor_fmonoidal_assoc
    : preserves_associativity (fmonoidal_preservestensordata diag_functor_fmonoidal_data).
  Proof.
    intros x y z.
    refine (_ @ rearrange_hexagon'_3 (pr2 V) x y z @ _).
    - now rewrite (when_bifunctor_becomes_rightwhiskering V).
    - now rewrite (when_bifunctor_becomes_leftwhiskering V).
  Qed.

  Lemma diag_functor_fmonoidal_leftunitality
    : preserves_leftunitality
        (fmonoidal_preservestensordata diag_functor_fmonoidal_data)
        (fmonoidal_preservesunit diag_functor_fmonoidal_data).
  Proof.
    intro x.

    etrans. {
      apply maponpaths.
      apply (! precompose_rearrange_prod_with_lunitors_on_right (pr2 V) x x).
    }
    etrans. {
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply rearrange_prod_is_z_isomorphism.
    }
    rewrite id_right.
    etrans. {
      apply maponpaths_2.
      rewrite <- (bifunctor_rightcomp V).
      apply maponpaths.
      apply (pr2 (monoidal_leftunitorisolaw V _)).
    }
    rewrite (bifunctor_rightid V).
    apply id_left.
  Qed.

  Lemma diag_functor_fmonoidal_rightunitality
    : preserves_rightunitality
        (fmonoidal_preservestensordata diag_functor_fmonoidal_data)
        (fmonoidal_preservesunit diag_functor_fmonoidal_data).
  Proof.
    intro x.
    cbn.
    unfold diag_preserves_unit.
    unfold diag_preserves_tensor_data.
    etrans. {
      apply maponpaths.
      apply (! precompose_rearrange_prod_with_lunitors_and_runitor (pr2 V) x x).
    }
    etrans. {
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply rearrange_prod_is_z_isomorphism.
    }
    rewrite id_right.
    etrans. {
      apply maponpaths_2.
      rewrite <- (bifunctor_leftcomp V).
      apply maponpaths.
      apply (pr2 (monoidal_leftunitorisolaw V _)).
    }
    rewrite (bifunctor_leftid V).
    apply id_left.
  Qed.

  Lemma diag_functor_fmonoidal_laxlaws
    : fmonoidal_laxlaws diag_functor_fmonoidal_data.
  Proof.
    repeat split.
    - exact diag_functor_fmonoidal_nat_left.
    - exact diag_functor_fmonoidal_nat_right.
    - exact diag_functor_fmonoidal_assoc.
    - exact diag_functor_fmonoidal_leftunitality.
    - exact diag_functor_fmonoidal_rightunitality.
  Qed.

  Definition diag_functor_fmonoidal_lax
    : fmonoidal_lax V V diag_functor.
  Proof.
    exists diag_functor_fmonoidal_data.
    exact diag_functor_fmonoidal_laxlaws.
  Defined.

  Definition diag_functor_is_strong_fmonoidal
    :  fmonoidal_stronglaws
         (fmonoidal_preservestensordata diag_functor_fmonoidal_lax)
         (fmonoidal_preservesunit diag_functor_fmonoidal_lax).
  Proof.
    unfold fmonoidal_stronglaws.
    split.
    - intro ; intro.
      apply rearrange_prod_is_z_isomorphism.
    - refine (_ ,, _).
      split ; apply (monoidal_leftunitorisolaw V I_{V}).
  Defined.

  Definition diag_functor_fmonoidal
    : fmonoidal V V diag_functor.
  Proof.
    exists diag_functor_fmonoidal_lax.
    exact diag_functor_is_strong_fmonoidal.
  Defined.

  Definition diag_functor_is_symmetric
    : is_symmetric_monoidal_functor (pr2 V) (pr2 V) diag_functor_fmonoidal.
  Proof.
    intro ; intro.
    apply pathsinv0.
    apply (rearrange_commute_with_swap (pr2 V)).
  Defined.

End DiagFunctor.

Section ConstantFunctor.

  Context (V : sym_monoidal_cat).

  Notation "x ⊗ y" := (monoidal_cat_tensor_pt x y).
  Notation "f ⊗⊗ g" := (monoidal_cat_tensor_mor f g) (at level 31).

  Context {x : V} (m : monoid V x).

  Definition constant_functor_fmonoidal_data
    : fmonoidal_data V V (constant_functor _ _ x).
  Proof.
    use tpair.
    - intros ? ?.
      apply m.
    - apply m.
  Defined.

  Lemma constant_functor_fmonoidal_laxlaws
    : fmonoidal_laxlaws constant_functor_fmonoidal_data.
  Proof.
    repeat split ; (intro ; intros ; rewrite id_right).
    - rewrite (bifunctor_leftid V).
      apply id_left.
    - rewrite (bifunctor_rightid V).
      apply id_left.
    - apply pathsinv0, (monoid_to_assoc_law V m).
    - apply (monoid_to_unit_left_law V m).
    - apply (monoid_to_unit_right_law V m).
  Qed.

  Definition constant_functor_fmonoidal_lax
    : fmonoidal_lax V V (constant_functor _ _ x).
  Proof.
    exists constant_functor_fmonoidal_data.
    exact constant_functor_fmonoidal_laxlaws.
  Defined.

  Context (comul_iso : Isos.is_z_isomorphism (pr11 m))
    (counit_iso : Isos.is_z_isomorphism (pr21 m)).
  Definition constant_functor_fmonoidal_strong
    :   fmonoidal_stronglaws
          (fmonoidal_preservestensordata constant_functor_fmonoidal_lax)
          (fmonoidal_preservesunit constant_functor_fmonoidal_lax).
  Proof.
    split.
    - intro ; intro.
      apply comul_iso.
    - apply counit_iso.
  Defined.

  Definition constant_functor_fmonoidal
    : fmonoidal V V (constant_functor _ _ x).
  Proof.
    exists constant_functor_fmonoidal_lax.
    exact constant_functor_fmonoidal_strong.
  Defined.

  Definition constant_functor_is_symmetric
               (m_is_comm : (pr12 V) x x · pr11 m = pr11 m)
    : is_symmetric_monoidal_functor (pr2 V) (pr2 V) constant_functor_fmonoidal.
  Proof.
    intro ; intro.
    rewrite id_right.
    apply m_is_comm.
  Defined.

End ConstantFunctor.

Section ComonoidsAsDialg.

  Context (V : sym_monoidal_cat).

  Notation "x ⊗ y" := (monoidal_cat_tensor_pt x y).
  Notation "f ⊗⊗ g" := (monoidal_cat_tensor_mor f g) (at level 31).

  Let V_comult
      := dialgebra_disp_monoidal (identity_fmonoidal V) (diag_functor_fmonoidal V).

  Definition unit_monoid
    : monoid V (monoidal_unit V).
  Proof.
    use tpair.
    - exists (monoidal_leftunitordata V (monoidal_unit V)).
      exact (identity (monoidal_unit V)).
    - refine (_ ,, _ ,, _).
      + etrans. {
          apply maponpaths_2.
          apply (bifunctor_rightid V).
        }
        apply id_left.
      + etrans. {
          apply maponpaths_2.
          apply (bifunctor_leftid V).
        }
        refine (id_left _ @ _).
        apply unitors_coincide_on_unit.
      + etrans. {
          apply maponpaths_2.
          refine (_ @ associator_before_lwhisker_with_lu V).
          apply maponpaths.
          apply pathsinv0,
            (when_bifunctor_becomes_leftwhiskering V).
        }
        apply maponpaths_2.
        apply (when_bifunctor_becomes_rightwhiskering V).
  Defined.


  Definition V_counit
    : disp_monoidal (dialgebra_disp_cat (functor_identity V) (constant_functor _ _ I_{V})) V.
  Proof.
    use (dialgebra_disp_monoidal (identity_fmonoidal V)
           (constant_functor_fmonoidal V unit_monoid _ _)).
    - refine (_ ,, _).
      apply (monoidal_leftunitorisolaw V).
    - apply Isos.identity_is_z_iso.
  Defined.

  Local Definition Dialg_prod_dirprod
    : disp_cat _
    := dirprod_disp_cat
         (dialgebra_disp_cat (functor_identity V) (diag_functor V))
         (dialgebra_disp_cat (functor_identity V) (constant_functor _ _ I_{V})).

  Definition V_comonoid_data
    : disp_monoidal Dialg_prod_dirprod V
      := dirprod_disp_cat_monoidal
           V_comult V_counit
           (is_locally_propositional_dialgebra_disp_cat
              (functor_identity V)
              (diag_functor V))
           (is_locally_propositional_dialgebra_disp_cat
              (functor_identity V)
              (constant_functor _ _ I_{V})).

  Definition V_comult_symm
    : disp_symmetric V_comult (pr2 V).
  Proof.
    use (dialgebra_disp_symmetric_monoidal).
    - exact (pr2 V).
    - apply is_symmetric_monoidal_identity.
    - apply diag_functor_is_symmetric.
  Defined.

  Definition V_counit_symm
    : disp_symmetric V_counit (pr2 V).
  Proof.
    use (dialgebra_disp_symmetric_monoidal).
    - exact (pr2 V).
    - apply is_symmetric_monoidal_identity.
    - (* the unit monoid is commutative *)
      apply constant_functor_is_symmetric.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply sym_mon_braiding_id.
  Defined.

  Definition V_comonoid_symm
    : disp_symmetric V_comonoid_data (pr2 V).
  Proof.
    use dirprod_disp_cat_symmetric_monoidal.
    - exact V_comult_symm.
    - exact V_counit_symm.
  Defined.

  Definition comonoid_laws_disp_cat
    : disp_cat (total_category Dialg_prod_dirprod).
  Proof.
    exact (disp_full_sub _ (λ x : total_category Dialg_prod_dirprod, comonoid_laws V (pr2 x))).
  Defined.

  Definition tensor_comonoid_laws
    {x y : total_category Dialg_prod_dirprod}
    (mx : comonoid_laws V (pr2 x))
    (my : comonoid_laws V (pr2 y))
    : comonoid_laws V (pr2 (x ⊗_{ total_monoidal V_comonoid_data} y)).
  Proof.
    repeat split.
    - refine (_ @ tensor_of_comonoids_laws_unit_left V (_,,mx) (_,,my)).
      cbn.
      unfold dialgebra_disp_tensor_op.
      cbn.
      unfold comonoid_data_comultiplication.
      cbn.
      now rewrite ! id_left.
    - refine (_ @ tensor_of_comonoids_laws_unit_right V (_,,mx) (_,,my)).
      cbn.
      unfold dialgebra_disp_tensor_op.
      cbn.
      unfold comonoid_data_comultiplication.
      cbn.
      now rewrite ! id_left.
    - refine (_ @ tensor_of_comonoids_laws_assoc V (_,,mx) (_,,my) @ _).
      + apply maponpaths_2.
        cbn.
        unfold dialgebra_disp_tensor_op.
        cbn.
        rewrite ! id_left.
        now rewrite ! assoc'.
      + cbn.
        unfold comonoid_data_comultiplication.
        unfold dialgebra_disp_tensor_op.
        cbn.
        rewrite ! id_left.
        now rewrite ! assoc'.
  Qed.

  Definition comonoid_laws_disp_cat_monoidal
    : disp_monoidal comonoid_laws_disp_cat (total_monoidal V_comonoid_data).
  Proof.
    apply disp_monoidal_fullsub.
    - refine (_ ,, _ ,, _).
      + unfold comonoid_laws_unit_left.
        cbn.
        unfold dialgebra_disp_unit.
        rewrite ! id_left.
        rewrite (bifunctor_rightid V).
        rewrite id_right.
        apply monoidal_leftunitorisolaw.
      + unfold comonoid_laws_unit_right.
        cbn.
        unfold dialgebra_disp_unit.
        rewrite ! id_left.
        rewrite (bifunctor_leftid V).
        rewrite id_right.
        unfold fmonoidal_preservesunit.
        cbn.
        unfold diag_preserves_unit.
        rewrite <- unitors_coincide_on_unit.
        apply monoidal_leftunitorisolaw.
      + unfold comonoid_laws_assoc.
        cbn.
        unfold dialgebra_disp_unit.
        cbn.
        unfold diag_preserves_unit.
        rewrite ! id_left.
        rewrite assoc'.
        apply maponpaths.
        apply lunitorinv_preserves_leftwhiskering_with_unit.
    - intros x y mx my.
      apply (tensor_comonoid_laws mx my).
  Defined.

  Definition comonoid_laws_disp_cat_sym_monoidal
    : disp_symmetric comonoid_laws_disp_cat_monoidal (total_symmetric _ V_comonoid_symm)
    := disp_symmetric_fullsub _ _ _ _ _.

  Definition comonoids_disp_cat
    := sigma_disp_cat comonoid_laws_disp_cat.

  Definition comonoids_disp_monoidal
    : disp_monoidal comonoids_disp_cat V.
  Proof.
    use sigma_disp_cat_monoidal.
    - exact V_comonoid_data.
    - exact comonoid_laws_disp_cat_monoidal.
    - intro ; intros ; apply isapropunit.
  Defined.

  Definition comonoids_disp_symmetric
    : disp_symmetric comonoids_disp_monoidal (pr2 V).
  Proof.
    use sigma_disp_cat_monoidal_symmetric.
    - exact V_comonoid_symm.
    - exact comonoid_laws_disp_cat_sym_monoidal.
  Defined.

  Definition sym_monoidal_cat_comonoids : sym_monoidal_cat.
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact (total_category comonoids_disp_cat).
    - exact (total_monoidal comonoids_disp_monoidal).
    - exact (total_symmetric _ comonoids_disp_symmetric).
  Defined.

  Lemma cat_comonoids_is_locally_propositional
    : locally_propositional comonoids_disp_cat.
  Proof.
    intro ; intros.
    use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
    apply (isaprop_total2 (_ ,, homset_property _ _ _ _ _) (λ _ , _ ,, homset_property _ _ _ _ _)).
  Qed.

End ComonoidsAsDialg.

Section CommutativeComonoids.

  Context (V : sym_monoidal_cat).

  Notation "x ⊗ y" := (monoidal_cat_tensor_pt x y).
  Notation "f ⊗⊗ g" := (monoidal_cat_tensor_mor f g) (at level 31).

  Definition commutative_law_comonoids_disp_cat
    : disp_cat (total_category (comonoids_disp_cat V)).
  Proof.
    exact (disp_full_sub _
             (λ x : total_category (comonoids_disp_cat V),
                 is_commutative (pr2 V) (pr2 x))).
  Defined.

  Definition commutative_law_comonoids_disp_monoidal
    : disp_monoidal commutative_law_comonoids_disp_cat (pr1 (sym_monoidal_cat_comonoids V)).
  Proof.
    use disp_monoidal_fullsub.
    - etrans. {
        apply maponpaths.
        apply sym_mon_braiding_id.
      }
      apply id_right.
    - cbn.
      intros x y mx my.
      refine (_ @ tensor_of_comm_comonoids V mx my @ _).
      + apply maponpaths_2.
        unfold dialgebra_disp_tensor_op.
        cbn.
        now rewrite id_left.
      + cbn.
        unfold dialgebra_disp_tensor_op.
        cbn.
        now rewrite id_left.
  Defined.

  Definition commutative_law_comonoids_disp_symmetric
    : disp_symmetric commutative_law_comonoids_disp_monoidal (pr2 (sym_monoidal_cat_comonoids V)).
  Proof.
    apply disp_symmetric_fullsub.
  Defined.

  Definition commutative_comonoids_disp_cat
    := sigma_disp_cat commutative_law_comonoids_disp_cat.

  Definition commutative_comonoids_disp_monoidal
    : disp_monoidal commutative_comonoids_disp_cat V.
  Proof.
    use sigma_disp_cat_monoidal.
    - apply comonoids_disp_monoidal.
    - apply commutative_law_comonoids_disp_monoidal.
    - intro ; intros ; apply isapropunit.
  Defined.

  Definition commutative_comonoids_disp_symmetric
    : disp_symmetric commutative_comonoids_disp_monoidal (pr2 V).
  Proof.
    use sigma_disp_cat_monoidal_symmetric.
    - apply comonoids_disp_symmetric.
    - exact commutative_law_comonoids_disp_symmetric.
  Defined.

  Definition sym_monoidal_cat_commutative_comonoids : sym_monoidal_cat.
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact (total_category commutative_comonoids_disp_cat).
    - exact (total_monoidal commutative_comonoids_disp_monoidal).
    - exact (total_symmetric _ commutative_comonoids_disp_symmetric).
  Defined.

  Lemma cat_commutative_comonoids_is_locally_propositional
    : locally_propositional commutative_comonoids_disp_cat.
  Proof.
    intro ; intros.
    use (isaprop_total2 (_ ,, _) (λ _ , _ ,, isapropunit)).
    apply cat_comonoids_is_locally_propositional.
  Qed.

End CommutativeComonoids.
