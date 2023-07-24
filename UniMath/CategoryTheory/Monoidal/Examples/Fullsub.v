(*********************************************************************************

 Full subcategories of monoidal categories

Given a full subcategory of a monoidal category, that is closed under the unit and the tensor product, the subcategory inherits the monoidal structure [disp_monoidal_fullsub].
Furthermore, if the monoidal category is carries a braiding (or symmetric braiding), it also restricts to the full sub [disp_braiding_fullsub, disp_symmetric_fullsub]

 *********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.

Require Import UniMath.CategoryTheory.Monoidal.Displayed.TransportLemmas.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.
Import MonoidalNotations.
Import DisplayedBifunctorNotations.
Import DisplayedMonoidalNotations.

Section FullSubOfMonoidal.

  Context {C : category}
    (M : monoidal C)
    (P : C → hProp).

  Context
    (P_u : P (monoidal_unit M))
      (P_t :  ∏ x y : C, P x → P y → P (x ⊗_{ M} y)).

  Definition disp_monoidal_tensor_data_fullsub
    : disp_bifunctor_data M (disp_full_sub C P) (disp_full_sub C P) (disp_full_sub C P).
  Proof.
    simple refine (_ ,, _).
    - exact P_t.
    - split ; intro ; intros ; exact tt.
  Defined.

  Lemma disp_monoidal_tensor_is_tensor_fullsub
    :  is_disp_bifunctor disp_monoidal_tensor_data_fullsub.
  Proof.
    repeat split ; intro ; intros ; apply isapropunit.
  Qed.

  Definition disp_monoidal_tensor_fullsub
    : disp_tensor (disp_full_sub C P) M.
  Proof.
    exists disp_monoidal_tensor_data_fullsub.
    exact disp_monoidal_tensor_is_tensor_fullsub.
  Defined.

  Definition disp_monoidal_data_fullsub
    : disp_monoidal_data (disp_full_sub C P) M.
  Proof.
    unfold disp_monoidal_data.
    exists disp_monoidal_tensor_fullsub.
    exists P_u.
    repeat (use tpair) ; intro ; intros ; exact tt.
  Defined.

  Lemma disp_monoidal_laws_fullsub
    : disp_monoidal_laws disp_monoidal_data_fullsub.
  Proof.
    repeat split ; try (intro ; intros) ; apply isapropunit.
  Qed.

  Definition disp_monoidal_fullsub
    : disp_monoidal (disp_full_sub C P) M
    := _ ,, disp_monoidal_laws_fullsub.

  Definition disp_braiding_fullsub
    (B : braiding M)
    : disp_braiding disp_monoidal_fullsub B.
  Proof.
    simple refine (_ ,, _ ,, _).
    - intro ; intros ; exact tt.
    - intro ; intros ; exact tt.
    - abstract (repeat split ; try (intro ; intros) ; apply isapropunit).
  Defined.

  Definition disp_symmetric_fullsub
    (B : symmetric M)
    : disp_symmetric disp_monoidal_fullsub B.
  Proof.
    simple refine (_ ,, _).
    - intro ; intros ; exact tt.
    - abstract (repeat split ; try (intro ; intros) ; apply isapropunit).
  Defined.

End FullSubOfMonoidal.
