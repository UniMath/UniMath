Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CodomainFibs.
Require Import UniMath.Bicategories.Colimits.Pullback.

Local Open Scope cat.

(**
The codomain displayed bicategory has a cleaving
 *)
Definition TODO {A : UU} : A.
Admitted.

Section CodomainFibsCleaving.
  Context (B : bicat)
          (pb_B : has_pb B).

  Definition test
             {x y : B}
             {f g : x --> y}
             {γ : f ==> g}
             {hx : cod_sfibs B x}
             {hy : cod_sfibs B y}
             {hf : hx -->[ f ] hy}
             {hg : hx -->[ g ] hy}
             (hγ : hf ==>[ γ ] hg)
    : is_cartesian_2cell (cod_sfibs B) hγ.
  Proof.
    intros h hh α ββ.
    use iscontraprop1.
    - admit.
    - simple refine (_ ,, _).
      * use make_cell_of_internal_sfib_over.
        ** cbn in h, hh, α, ββ.
           induction hh as [ hh₁ [ hh₂ hh₃ ] ].
           induction ββ as [ ββ₁ ββ₂ ].
           cbn in ββ₁.
           cbn.
           refine (ββ₁ • _).

  Section LocalCleaving.
    Context {x y : B}
            {hx : cod_sfibs B x}
            {hy : cod_sfibs B y}
            {f g : x --> y}
            (hf : hx -->[ g] hy)
            (γ : f ==> g).

    Definition lift_of_local_cleaving_mor
      : hx -->[ f ] hy.
    Proof.
      pose (pr122 hy (pr1 hx) (pr12 hx · f) (pr1 hf) ((pr12 hx ◃ γ) • pr22 hf)) as ℓ.
      use make_mor_of_internal_sfib_over.
      - exact (pr1 ℓ).
      - intros z φ ψ ζ Hζ.
        apply TODO.
      - exact (inv_of_invertible_2cell (pr122 ℓ)).
    Defined.

    Definition lift_of_local_cleaving_cell
      : lift_of_local_cleaving_mor ==>[ γ ] hf.
    Proof.
      pose (pr122 hy (pr1 hx) (pr12 hx · f) (pr1 hf) ((pr12 hx ◃ γ) • pr22 hf)) as ℓ.
      use make_cell_of_internal_sfib_over.
      - apply ℓ.
      - unfold cell_of_internal_sfib_over_homot.
        simpl.
        pose (pr2 (pr222 ℓ)) as p.
        cbn in p.
        etrans.
        {
          apply maponpaths.
          exact p.
        }
        cbn in hf.
        use vcomp_move_R_pM ; [ is_iso | ].
        apply idpath.
    Defined.

    Definition lift_of_local_cleaving_is_cartesian
      : is_cartesian_2cell (cod_sfibs B) lift_of_local_cleaving_cell.
    Proof.
      intros h hh ζ ββ ; simpl.
      use iscontraprop1.
      - use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath ; [ intro ; apply cod_sfibs | ].
        cbn in φ₁, φ₂.
        pose (r := maponpaths pr1 (pr2 φ₁ @ !(pr2 φ₂))).
        cbn in r.
        apply TODO.
      - simple refine (_ ,, _).
        + use make_cell_of_internal_sfib_over.
          * apply TODO.
          * apply TODO.
        + apply TODO.
    Defined.

    Definition lift_of_local_cleaving
      : cartesian_lift_2cell (cod_sfibs B) hf γ.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact lift_of_local_cleaving_mor.
      - exact lift_of_local_cleaving_cell.
      - exact lift_of_local_cleaving_is_cartesian.
    Defined.
  End LocalCleaving.

  Definition cod_sfibs_local_cleaving
    : local_cleaving (cod_sfibs B).
  Proof.
    intros x y hx hy f g hf γ.
    exact (lift_of_local_cleaving hf γ).
  Defined.

  Definition cod_sfibs_global_cleaving
    : global_cleaving (cod_sfibs B).
  Proof.
  Admitted.

  Definition cod_sfibs_lwhisker_cartesian
    : lwhisker_cartesian (cod_sfibs B).
  Proof.
  Admitted.

  Definition cod_sfibs_rwhisker_cartesian
    : rwhisker_cartesian (cod_sfibs B).
  Proof.
  Admitted.

  Definition cod_sfibs_cleaving_of_bicats
    : cleaving_of_bicats (cod_sfibs B).
  Proof.
    repeat split.
    - exact cod_sfibs_local_cleaving.
    - exact cod_sfibs_global_cleaving.
    - exact cod_sfibs_lwhisker_cartesian.
    - exact cod_sfibs_rwhisker_cartesian.
  Defined.
End CodomainFibsCleaving.
