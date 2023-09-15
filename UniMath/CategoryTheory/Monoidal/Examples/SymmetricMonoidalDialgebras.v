(** **********************************************************

Contents :

- constructs a displayed symmetric monoidal category that is displayed
  over the monoidal dialgebras, its total category is called the
  symmetric monoidal dialgebras

 ************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section FixTwoSymmetricMonoidalFunctors.

  Import BifunctorNotations.
  Import MonoidalNotations.
  Import DisplayedBifunctorNotations.
  Import DisplayedMonoidalNotations.

  Context {A B : category}
          {V : monoidal A} {W : monoidal B}
          {HV : symmetric V} {HW : symmetric W}
          {F G : A ⟶ B}
          {Fm : fmonoidal V W F} {Gm : fmonoidal_lax V W G}
          (Fs : is_symmetric_monoidal_functor HV HW Fm)
          (Gs : is_symmetric_monoidal_functor HV HW Gm).

  Local Definition base_mon_disp : disp_monoidal (dialgebra_disp_cat F G) V :=
    dialgebra_disp_monoidal Fm Gm.

  Lemma dialgebra_disp_symmetric_data : disp_symmetric_data base_mon_disp HV.
  Proof.
    intros x y xx yy.
    red in xx, yy. cbn in xx, yy.
    cbn.
    unfold dialgebra_disp_tensor_op.
    repeat rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (_,,fmonoidal_preservestensorstrongly Fm x y)).
    etrans.
    { apply maponpaths.
      apply pathsinv0, Gs. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    cbn.
    etrans.
    2: { do 2 apply cancel_postcomposition.
         exact (Fs x y).
    }
    etrans.
    2: { apply cancel_postcomposition.
         rewrite assoc'.
         apply maponpaths.
         apply pathsinv0, (z_iso_inv_after_z_iso (_ ,, fmonoidal_preservestensorstrongly Fm y x)). }
    rewrite id_right.
    apply (tensor_sym_mon_braiding (((B,,W):monoidal_cat),,HW)).
  Qed.

  Definition dialgebra_disp_symmetric_monoidal : disp_symmetric base_mon_disp HV.
  Proof.
    use make_disp_symmetric_locally_propositional.
    - apply is_locally_propositional_dialgebra_disp_cat.
    - exact dialgebra_disp_symmetric_data.
  Defined.

  Definition dialgebra_symmetric_monoidal : symmetric (dialgebra_monoidal Fm Gm)
    := total_symmetric base_mon_disp dialgebra_disp_symmetric_monoidal.


End FixTwoSymmetricMonoidalFunctors.
