(**

- Construction of a pseudofunctor from a strong monoidal functor - between the bicategories (trivially)
  generated from the monoidal categories.
- And the opposite direction: We fix two bicategories and a pseudofunctor between them and an object in
  the domain bicategory. This gives rise to a strong monoidal functor between the associated monoidal
  categories of endomorphisms for the fixed object and its image.

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
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFromBicategory.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicategoryFromMonoidal.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

Section monoidal_functor_to_psfunctor.

  Context (M N : monoidal_cat).

  Local Definition M_as_bicat := bicat_from_monoidal M.
  Local Definition N_as_bicat := bicat_from_monoidal N.

  Context (smF : strong_monoidal_functor M N).

Definition monoidal_functor_to_psfunctor_map_data: psfunctor_data M_as_bicat N_as_bicat.
Proof.
  use make_psfunctor_data.
  - cbn. exact (fun x => x).
  - intros a b. cbn.
    exact (functor_on_objects smF).
  - intros a b f g. cbn.
    exact (functor_on_morphisms smF).
  - intros a. cbn. exact (lax_monoidal_functor_ϵ smF).
  - intros a b c f g. cbn. apply (lax_monoidal_functor_μ smF (f,g)).
Defined.

Definition monoidal_functor_to_psfunctor_map_laws: psfunctor_laws monoidal_functor_to_psfunctor_map_data.
Proof.
  repeat split; red; cbn.
  - intros H0 H1 a. apply functor_id.
  - intros H0 H1 a b c f g. apply functor_comp.
  - intros H0 H1 a. apply lax_monoidal_functor_unital.
  - intros H0 H1 a. apply (lax_monoidal_functor_unital smF a).
  - intros H0 H1 H2 H3 a b c.
    do 2 rewrite <- assoc. apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ (nat_z_iso_pointwise_z_iso (monoidal_cat_associator N) ((smF a, smF b), smF c))).
    do 2 rewrite assoc.
    etrans.
    2: { apply maponpaths. apply functor_on_inv_from_z_iso'. }
    apply z_iso_inv_on_left.
    cbn.
    apply pathsinv0.
    apply lax_monoidal_functor_assoc.
  - intros H0 H1 H2 a b1 b2 g. red in g.
    apply pathsinv0.
    assert (Heq := nat_trans_ax (lax_monoidal_functor_μ smF) (a,,b1) (a,,b2) (id a,,g)).
    cbn in Heq.
    rewrite functor_id in Heq.
    exact Heq.
  - intros H0 H1 H2 a1 a2 b f.
    apply pathsinv0.
    assert (Heq := nat_trans_ax (lax_monoidal_functor_μ smF) (a1,,b) (a2,,b) (f,,id b)).
    cbn in Heq.
    rewrite functor_id in Heq.
    exact Heq.
Qed.

Definition monoidal_functor_to_psfunctor: psfunctor M_as_bicat N_as_bicat.
Proof.
  use make_psfunctor.
    - exact (monoidal_functor_to_psfunctor_map_data).
    - exact (monoidal_functor_to_psfunctor_map_laws).
    - split ; red; cbn.
      + intros H0. unfold two_cells_from_monoidal.
        exists (strong_monoidal_functor_ϵ_inv smF).
        exact (pr2 (strong_monoidal_functor_ϵ_is_z_iso smF)).
      + intros H0 H1 H2 a b. unfold two_cells_from_monoidal.
        exists (strong_monoidal_functor_μ_inv smF (a,,b)).
        exact (pr2 (strong_monoidal_functor_μ_is_nat_z_iso smF (a,,b))).
Defined.

End monoidal_functor_to_psfunctor.

(** *** Going into the opposite direction *)
(** see the description in the file header *)

Section psfunctor_to_monoidal_functor.

Local Open Scope bicategory_scope.
Import Bicat.Notations.

Context {C : bicat}.
Context (c0: ob C).
Context {D : bicat}.
Context (psF: psfunctor C D).

Local Definition d0 : D := psF c0.
Local Definition M : monoidal_cat := monoidal_cat_from_bicat_and_ob c0.
Local Definition N : monoidal_cat := monoidal_cat_from_bicat_and_ob d0.

Definition psfunctor_to_lax_monoidal_functor_data: functor_data M N.
Proof.
  use make_functor_data.
  - cbn. intro f. exact (# psF f).
  - intros a b f. red in f. cbn in f.
    cbn. exact (##psF f).
Defined.

Lemma psfunctor_to_lax_monoidal_functor_data_is_functor : is_functor psfunctor_to_lax_monoidal_functor_data.
Proof.
  split; red; cbn.
  - intros a. apply psF.
  - intros a b c f g. apply psF.
Qed.

Definition psfunctor_to_lax_monoidal_functor_functor : M ⟶ N.
Proof.
  use make_functor.
  - exact psfunctor_to_lax_monoidal_functor_data.
  - exact psfunctor_to_lax_monoidal_functor_data_is_functor.
Defined.

Local Definition auxμ : nat_trans_data (monoidal_functor_map_dom M N psfunctor_to_lax_monoidal_functor_functor)
                                       (monoidal_functor_map_codom M N psfunctor_to_lax_monoidal_functor_functor).
Proof.
  red. cbn. intro fg.
  exact (psfunctor_comp psF (pr1 fg) (pr2 fg)).
Defined.

Local Lemma auxμ_is_nat_trans: is_nat_trans _ _ auxμ.
Proof.
  red. cbn. intros gh gh' αβ.
  red in αβ. cbn in αβ.
  change (## psF (pr2 αβ) ⋆⋆ ## psF (pr1 αβ) • psfunctor_comp psF (pr1 gh') (pr2 gh') =
          psfunctor_comp psF (pr1 gh) (pr2 gh) • ## psF (pr2 αβ ⋆⋆ pr1 αβ)).
  apply pathsinv0.
  apply (psfunctor_comp_natural psF).
Qed.

Local Definition μ : monoidal_functor_map M N psfunctor_to_lax_monoidal_functor_functor
  := (auxμ,, auxμ_is_nat_trans).

Lemma psfunctor_to_lax_monoidal_functor_laws :
  monoidal_functor_associativity M N psfunctor_to_lax_monoidal_functor_functor μ
  × monoidal_functor_unitality M N psfunctor_to_lax_monoidal_functor_functor (pr1(psfunctor_id psF c0)) μ.
Proof.
  split.
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
Qed.

Definition psfunctor_to_lax_monoidal_functor: lax_monoidal_functor M N.
Proof.
  exists psfunctor_to_lax_monoidal_functor_functor.
  cbn.
    exists (psfunctor_id psF c0).
    exists μ.
    exact psfunctor_to_lax_monoidal_functor_laws.
Defined.

Definition psfunctor_to_monoidal_functor: strong_monoidal_functor M N.
Proof.
  exists psfunctor_to_lax_monoidal_functor.
  split.
  - exact (pr2 (psfunctor_id psF c0)).
  - intro c. exact (pr2 (psfunctor_comp psF (pr1 c) (pr2 c))).
Defined.


End psfunctor_to_monoidal_functor.
