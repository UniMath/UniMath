Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.

Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.AlgebraMap.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.

Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Monads.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.KleisliTriple.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Section Monad_of_Kleisli_Data.

Context {x : category} (k : kleisli_triple_data_on_cat x).

Local Definition unit_kleisli_data : ∏ a : x, x ⟦ a, pr1 k a ⟧
  := unit_kt k.

Local Lemma unit_kleisli_natural
  : is_nat_trans (functor_identity_data x)
                 (functor_data_of_kleisli_triple k)
                 unit_kleisli_data.
Proof.
  intros a b f. cbn.
  symmetry.
  apply (unit_bind k).
Qed.

Definition unit_kleisli
  : functor_identity_data x ⟹ functor_of_kleisli_triple k.
Proof.
   use make_nat_trans.
   - exact unit_kleisli_data.
   - exact unit_kleisli_natural.
Defined.

Local Definition mu_kleisli_data (a : x) : x ⟦ k (k a), k a ⟧
  := bind_kt k (identity (k a)).

Local Lemma mu_kleisli_natural
  : is_nat_trans (functor_composite_data (functor_of_kleisli_triple k)
                                         (functor_of_kleisli_triple k))
                 (functor_of_kleisli_triple k) mu_kleisli_data.
Proof.
  unfold mu_kleisli_data.
  intros a b f. cbn.
  do 2 rewrite (bind_bind k).
  apply maponpaths.
  rewrite assoc'.
  rewrite (unit_bind k).
  rewrite id_left.
  apply id_right.
Qed.

Definition mu_kleisli
  : functor_composite_data (functor_of_kleisli_triple k)
                           (functor_of_kleisli_triple k)
    ⟹
    functor_of_kleisli_triple k.
Proof.
  use make_nat_trans.
  - exact mu_kleisli_data.
  - exact mu_kleisli_natural.
Defined.

End Monad_of_Kleisli_Data.

Section Monad_of_Kleisli_Data.

Context {x : univalent_category} (k : kleisli_triple_data_on_cat x).

Local Definition unit_mu_kleisli_data
  : add_unit_mu bicat_of_cats (ps_id_functor bicat_of_cats x)
  := (functor_of_kleisli_triple k,,
      make_dirprod (unit_kleisli k)
      (mu_kleisli k)).

Local Lemma unit_mu_kleisli_laws
  : disp_fullsubbicat (lawless_monad bicat_of_cats)
                      (monad_laws bicat_of_cats)
                      (ps_id_functor bicat_of_cats x,, unit_mu_kleisli_data).
Proof.
  cbn.
  repeat apply make_dirprod; cbn;
    (apply nat_trans_eq;
     [ apply x
     | cbn; intro a; unfold unit_kleisli_data, mu_kleisli_data;
       repeat rewrite id_left;
       repeat rewrite (bind_bind k) ]).
  - etrans.
    { apply maponpaths.
      rewrite assoc'.
      rewrite (unit_bind k).
      apply id_right.
    }
    apply (bind_unit k).
  - apply (unit_bind k).
  - apply maponpaths.
    rewrite id_left.
    rewrite assoc'.
    rewrite (unit_bind k).
    symmetry.
    apply id_right.
Qed.

Definition unit_mu_kleisli
  : disp_monad bicat_of_cats (ps_id_functor bicat_of_cats x)
  := (unit_mu_kleisli_data,, unit_mu_kleisli_laws).

End Monad_of_Kleisli_Data.

Definition Ktriple_to_Monad_data
  : disp_psfunctor_data kleisli_triple_disp_bicat
                        (disp_monad bicat_of_cats)
                        (ps_id_functor bicat_of_cats).
Proof.
  use make_disp_psfunctor_data.
  - exact @unit_mu_kleisli.
  - simpl.
    intros x y f kx ky kf.
    apply make_dirprod.
    2: { exact tt. }
    use tpair.
    + pose (pr1 kf) as c.
      use make_invertible_2cell.
      * use
      inv_from_iso
      refine (comp_of_invertible_2cell (g:=f:bicat_of_cats⟦_,_⟧) _ _).
      use make_invertible_2cell.
      Search functor_comp "right".
      Search (functor_comp (functor_identity _) ?f ==> ?f).
      Search (invertible_2cell (functor_identity · ?f) ?f).


refine (comp_of_invertible_2cell _ _).
      Search invertible_2cell "comp".

Definition Ktriple_to_Monad
  : disp_psfunctor kleisli_triple_disp_bicat
                   (disp_monad bicat_of_cats)
                   (ps_id_functor bicat_of_cats).
Proof.
  use tpair.
