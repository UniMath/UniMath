(**

the notion of strong monads w.r.t. monoidal actions (a generalization of the notion w.r.t. a monad

see https://ncatlab.org/nlab/show/strong+monad for a general bicategorical formulation and for the one w.r.t. a monad,
the present notion is intermediately abstract/general and only sketched on that page

author: Ralph Matthes 2022

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section A.

Context {V : category} {Mon_V : monoidal V} {C : category} (Act : actegory Mon_V C).

Definition actionbasedstrongmonads_cat_disp : disp_cat (category_Monad C).
Proof.
  use tpair.
  - use tpair.
    + use make_disp_cat_ob_mor.
      * intro M.
        exact (∑ Ml : lineator Mon_V Act Act (M: Monad C), is_linear_nat_trans (identity_lineator Mon_V Act) Ml (η (M: Monad C)) ×
                                                           is_linear_nat_trans (comp_lineator Mon_V Ml Ml) Ml (μ (M: Monad C))).
      * intros M N [Ml islinM] [Nl islinN] α.
        exact (is_linear_nat_trans Ml Nl (nat_trans_from_monad_mor _ _ _ α)).
    + split.
      * intros M [Ml [islinMη islimMμ]]. cbn.
        apply is_linear_nat_trans_identity.
      * intros M N O α α' Mll Nll Oll islntα islntβ.
        exact (is_linear_nat_trans_comp (pr1 Mll) (pr1 Nll) (pr1 Oll) islntα islntβ).
  - repeat split; intros; try apply isaprop_is_linear_nat_trans.
    apply isasetaprop; apply isaprop_is_linear_nat_trans.
Defined.

Definition actionbasedstrongmonads_cat_total : category := total_category actionbasedstrongmonads_cat_disp.

End A.
