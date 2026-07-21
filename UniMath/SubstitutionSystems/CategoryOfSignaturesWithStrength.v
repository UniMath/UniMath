Require Import UniMath.Foundations.All.

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.

Require Import UniMath.CategoryTheory.coslicecat.

Require Import UniMath.SubstitutionSystems.SigmaMonoids.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section CategoryOfSignaturesWithStrength.
  Context {V : category} (Mon_V : monoidal V).

  Definition pointedtensorialstrength_disp_cat_ob_mor
    : disp_cat_ob_mor [V, V].
  Proof.
    use tpair; cbn.
    - exact (pointedtensorialstrength Mon_V).
    - intros H H' θ θ' α; exact (is_linear_nat_trans θ θ' α).
  Defined.

  Lemma pointedtensorialstrength_disp_cat_id_comp
    : disp_cat_id_comp [V,V] pointedtensorialstrength_disp_cat_ob_mor.
  Proof.
    split; cbn.
    - intros ? ?; use is_linear_nat_trans_identity.
    - intros ? ? ? ? ? ? ? ?; use is_linear_nat_trans_comp.
  Qed.

  Definition pointedtensorialstrength_disp_cat_data : disp_cat_data [V, V]
    := pointedtensorialstrength_disp_cat_ob_mor ,, 
        pointedtensorialstrength_disp_cat_id_comp.

  Lemma pointedtensorialstrength_disp_cat_axioms 
    : disp_cat_axioms [V , V] pointedtensorialstrength_disp_cat_data.
  Proof.
    repeat split; cbn.
    - intros; use proofirrelevance; use isaprop_is_linear_nat_trans.
    - intros; use proofirrelevance; use isaprop_is_linear_nat_trans.
    - intros; use proofirrelevance; use isaprop_is_linear_nat_trans.
    - intros; use isasetaprop; use isaprop_is_linear_nat_trans.
  Qed.

  Definition pointedtensorialstrength_disp_cat : disp_cat [V, V] 
    := pointedtensorialstrength_disp_cat_data ,,
        pointedtensorialstrength_disp_cat_axioms.

  Definition pointedtensorialstrength_cat : category
    := total_category pointedtensorialstrength_disp_cat.

End CategoryOfSignaturesWithStrength.

  




