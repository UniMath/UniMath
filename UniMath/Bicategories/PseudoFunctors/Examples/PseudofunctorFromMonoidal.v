(**

Construction of a pseudofunctor from a strong monoidal functor - between the bicategories (trivially) generated from the monoidal categories.

Author: Ralph Matthes 2021

*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicategoryFromMonoidal.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

Section monoidal_functor_to_psfunctor.

  Context (M N : monoidal_precat).
  Context (hsM : has_homsets (monoidal_precat_precat M)).
  Context (hsN : has_homsets (monoidal_precat_precat N)).

  Local Definition M_as_bicat := bicat_from_monoidal M hsM.
  Local Definition N_as_bicat := bicat_from_monoidal N hsN.

  Context (strF : strong_monoidal_functor M N).

  Local Definition F : functor (monoidal_precat_precat M) (monoidal_precat_precat N) := pr11 strF.
  Local Definition ε_F := pr121 strF.
  Local Definition μ_F : monoidal_functor_map M N F := pr1(pr2(pr2(pr1 strF))).
  Local Definition F_unital := pr2(pr2(pr2(pr1 strF))).
  Local Definition F_associative := pr1(pr2(pr2(pr2(pr1 strF)))).

Definition monoidal_functor_to_psfunctor_map_data: psfunctor_data M_as_bicat N_as_bicat.
Proof.
  use make_psfunctor_data.
  - cbn. exact (fun x => x).
  - intros a b. cbn.
    exact (functor_on_objects F).
  - intros a b f g. cbn.
    exact (functor_on_morphisms F).
  - intros a. cbn. exact ε_F.
  - intros a b c f g. cbn. apply (μ_F (f,g)).
Defined.

Definition monoidal_functor_to_psfunctor_map_laws: psfunctor_laws monoidal_functor_to_psfunctor_map_data.
Proof.
  repeat split; red; cbn.
  - intros H0 H1 a. apply functor_id.
  - intros H0 H1 a b c f g. apply functor_comp.
  - intros H0 H1 a. apply (pr2 F_unital).
  - intros H0 H1 a. apply (pr2 F_unital a).
  - intros H0 H1 H2 H3 a b c.
    do 2 rewrite <- assoc. apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ (nat_z_iso_pointwise_z_iso (monoidal_precat_associator N) ((F a, F b), F c))).
    do 2 rewrite assoc.
    etrans.
    2: { apply maponpaths. apply functor_on_inv_from_z_iso'. }
    apply z_iso_inv_on_left.
    cbn.
    apply pathsinv0.
    apply F_associative.
  - intros H0 H1 H2 a b1 b2 g. red in g.
    apply pathsinv0.
    assert (Heq := nat_trans_ax μ_F (a,,b1) (a,,b2) (id a,,g)).
    cbn in Heq.
    rewrite functor_id in Heq.
    exact Heq.
  - intros H0 H1 H2 a1 a2 b f.
    apply pathsinv0.
    assert (Heq := nat_trans_ax μ_F (a1,,b) (a2,,b) (f,,id b)).
    cbn in Heq.
    rewrite functor_id in Heq.
    exact Heq.
Defined.

Definition monoidal_functor_to_psfunctor: psfunctor M_as_bicat N_as_bicat.
Proof.
  use make_psfunctor.
    - exact (monoidal_functor_to_psfunctor_map_data).
    - exact (monoidal_functor_to_psfunctor_map_laws).
    - split ; red; cbn.
      + intros H0. unfold two_cells_from_monoidal.
        exists (inv_from_z_iso (_,,pr12 strF)).
        fold ε_F.
        exact (pr2 (pr12 strF)).
      + intros H0 H1 H2 a b. unfold two_cells_from_monoidal.
        exists (nat_z_iso_to_trans_inv (make_nat_z_iso _ _ μ_F (pr22 strF)) (a,,b)).
        exact (pr2 (pr22 strF (a,,b))).
Defined.

End monoidal_functor_to_psfunctor.

(** *** Going into the opposite direction *)
(** We fix two bicategories and a pseudofunctor between them and an object in the domain bicategory.
    This gives rise to a strong monoidal functor between the associated monoidal categories of endomorphisms
    for the fixed object and its image.
*)

Section psfunctor_to_monoidal_functor.

Local Open Scope bicategory_scope.
Import Bicat.Notations.

Context {C : bicat}.
Context (c0: ob C).
Context {D : bicat}.
Context (psF: psfunctor C D).

Local Definition d0 := psF c0.
Local Definition M := monoidal_precat_from_prebicat_and_ob c0.
Local Definition N := monoidal_precat_from_prebicat_and_ob d0.

Definition psfunctor_to_lax_monoidal_functor: lax_monoidal_functor M N.
Proof.
  use tpair.
  - use make_functor.
    + use make_functor_data.
      * cbn. intro f. exact (# psF f).
      * intros a b f. red in f. cbn in f.
        cbn. exact (##psF f).
    + split; red; cbn.
      * intros a. apply psF.
      * intros a b c f g. apply psF.
  - cbn.
    exists (psfunctor_id psF c0).
    use tpair.
    + use make_nat_trans.
      * red. cbn. intro fg.
        exact (psfunctor_comp psF (pr1 fg) (pr2 fg)).
      * red. cbn. intros gh gh' αβ.
        red in αβ. cbn in αβ.
        change (## psF (pr2 αβ) ⋆⋆ ## psF (pr1 αβ) • psfunctor_comp psF (pr1 gh') (pr2 gh') =
                psfunctor_comp psF (pr1 gh) (pr2 gh) • ## psF (pr2 αβ ⋆⋆ pr1 αβ)).
        apply pathsinv0.
        apply (psfunctor_comp_natural psF).
    + split.
      * red. cbn. intros x y z. unfold rassociator_fun'. cbn.
        assert (Hyp := psfunctor_rassociator psF x y z).
        change ((id₂ (# psF z) ⋆⋆  psfunctor_comp psF x y • psfunctor_comp psF (x · y) z)
                  • ## psF (rassociator x y z) =
                (rassociator (# psF x) (# psF y) (# psF z) •  psfunctor_comp psF y z ⋆⋆ id₂ (# psF x))
                  •  psfunctor_comp psF x (y · z)).
        rewrite hcomp_identity_right.
        rewrite hcomp_identity_left.
        exact Hyp.
      * red. cbn. intro x.
        split.
        -- change (lunitor (# psF x) =
                   (id₂ (# psF x) ⋆⋆ psfunctor_id psF c0 • psfunctor_comp psF (id₁ c0) x)
                     • ## psF (lunitor x)).
           rewrite hcomp_identity_right.
           apply psfunctor_lunitor.
        -- change (runitor (# psF x) =
                   (psfunctor_id psF c0 ⋆⋆ id₂ (# psF x) • psfunctor_comp psF x (id₁ c0))
                     • ## psF (runitor x)).
           rewrite hcomp_identity_left.
           apply psfunctor_runitor.
Defined.

Definition psfunctor_to_monoidal_functor: strong_monoidal_functor M N.
Proof.
  exists psfunctor_to_lax_monoidal_functor.
  split.
  - exact (pr2 (psfunctor_id psF c0)).
  - intro c. exact (pr2 (psfunctor_comp psF (pr1 c) (pr2 c))).
Defined.


End psfunctor_to_monoidal_functor.
