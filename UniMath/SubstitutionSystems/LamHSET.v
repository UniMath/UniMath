
Section set_instances.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.polynomialfunctors.

Let Lam_S : Signature _ _ := Lam_Sig HSET has_homsets_HSET TerminalHSET CoproductsHSET ProductsHSET.

Local Notation "'EndHSET'":= ([HSET, HSET, has_homsets_HSET]) .

Let hsEndC : has_homsets EndHSET := functor_category_has_homsets _ _ has_homsets_HSET.

Lemma Lam_Initial_HSET : Initial (precategory_FunctorAlg (Id_H _ _ CoproductsHSET Lam_S) hsEndC).
Proof.
use colimAlgInitial.
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_sum_of_functors.
  + apply (Products_functor_precat _ _ ProductsHSET).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor; apply functor_category_has_homsets.
  + apply is_omega_cocont_Lam.
    * apply (has_exponentials_functor_HSET _ has_homsets_HSET).
    * apply cats_LimsHSET.
- apply (Initial_functor_precat _ _ InitialHSET).
- apply ColimsFunctorCategory; apply ColimsHSET.
Defined.

Lemma KanExt_HSET : ∀ Z : precategory_Ptd HSET has_homsets_HSET,
   RightKanExtension.GlobalRightKanExtensionExists HSET HSET
     (U Z) HSET has_homsets_HSET has_homsets_HSET.
Proof.
intro Z.
apply RightKanExtension_from_limits.
apply cats_LimsHSET.
Defined.

Definition LamHSS_Initial_HSET : Initial (hss_precategory CoproductsHSET Lam_S).
Proof.
  apply InitialHSS.
  - apply KanExt_HSET.
  - apply Lam_Initial_HSET.
Defined.

End set_instances.
