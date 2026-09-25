(**

 Parameterized NNOs from ordinary NNOs

 We show that in a Cartesian closed category, every NNO is a parameterized NNO. The
 object and maps stay the same, and the only work lies in deriving the parameterized
 recursion principle. The idea here is to define a recursive map from the NNO to an
 exponential instead.

 Content
 1. Parameterized recursion
 2. Parameterized NNOs from NNOs

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.Exponentials.

Local Open Scope cat.

Section ParameterizedNNOFromNNO.
  Context {C : category}
          (T : Terminal C)
          (BP : BinProducts C)
          (N : NNO T)
          (E : Exponentials BP).

  (** * 1. Parameterized recursion *)
  Section Recursion.
    Context {b y : C}
            (zy : b --> y)
            (sy : y --> y).

    Definition parameterized_NNO_from_NNO_rec_exp
      : N --> exp (E b) y.
    Proof.
      use NNO_mor.
      - use exp_lam.
        exact (BinProductPr1 _ _ · zy).
      - use exp_lam.
        exact (exp_eval (E b) y · sy).
    Defined.

    Definition parameterized_NNO_from_NNO_rec
      : BP b N --> y
      := BinProductOfArrows _ _ _ (identity _) parameterized_NNO_from_NNO_rec_exp
         · exp_eval (E b) y.

    Proposition parameterized_NNO_from_NNO_rec_Z
      : BinProductArrow C (BP b N) (identity b) (TerminalArrow T b · zeroNNO T N)
        · parameterized_NNO_from_NNO_rec
        =
        zy.
    Proof.
      unfold parameterized_NNO_from_NNO_rec.
      rewrite assoc.
      rewrite postcompWithBinProductArrow.
      unfold parameterized_NNO_from_NNO_rec_exp.
      rewrite !assoc'.
      rewrite NNO_mor_Z.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (postcompWithBinProductArrow _ (BP _ _) (BP _ _)).
      }
      rewrite !assoc'.
      rewrite exp_beta.
      rewrite assoc.
      rewrite BinProductPr1Commutes.
      apply id_left.
    Qed.

    Proposition parameterized_NNO_from_NNO_rec_S
      : BinProductOfArrows C (BP b N) (BP b N) (identity b) (sucNNO T N)
        · parameterized_NNO_from_NNO_rec
        =
        parameterized_NNO_from_NNO_rec · sy.
    Proof.
      unfold parameterized_NNO_from_NNO_rec.
      rewrite assoc.
      rewrite BinProductOfArrows_comp.
      unfold parameterized_NNO_from_NNO_rec_exp.
      rewrite NNO_mor_S.
      rewrite <- BinProductOfArrows_comp.
      rewrite !assoc'.
      apply maponpaths.
      rewrite exp_beta.
      apply idpath.
    Qed.

    Proposition parameterized_NNO_from_NNO_rec_unique
                {f : BP b N --> y}
                (qz : BinProductArrow
                        C (BP b N)
                        (identity b)
                        (TerminalArrow T b · zeroNNO T N)
                      · f
                      =
                      zy)
                (qs : BinProductOfArrows C _ _ (identity b) (sucNNO T N) · f
                      =
                      f · sy)
      : f = parameterized_NNO_from_NNO_rec.
    Proof.
      unfold parameterized_NNO_from_NNO_rec.
      refine (!(exp_beta (E b) _) @ _ @ exp_beta (E b) _).
      apply maponpaths_2.
      apply maponpaths.
      use NNO_mor_unique.
      - use exp_lam.
        exact (BinProductPr1 _ _ · zy).
      - use exp_lam.
        exact (exp_eval (E b) y · sy).
      - use exp_funext.
        intros a h.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (!(id_left _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        rewrite !assoc.
        rewrite BinProductOfArrowsPr1.
        rewrite <- qz.
        rewrite !assoc.
        apply maponpaths_2.
        use BinProductArrowsEq.
        + rewrite !assoc'.
          rewrite BinProductPr1Commutes.
          rewrite id_right.
          rewrite BinProductOfArrowsPr1.
          apply idpath.
        + rewrite !assoc'.
          rewrite BinProductPr2Commutes.
          rewrite BinProductOfArrowsPr2.
          rewrite !assoc.
          apply maponpaths_2.
          apply TerminalArrowEq.
      - use exp_funext.
        intros a h.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        unfold parameterized_NNO_from_NNO_rec_exp.
        rewrite !assoc.
        rewrite BinProductOfArrows_comp.
        rewrite NNO_mor_Z.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (!(id_left _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (!(id_left _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        apply idpath.
      - use exp_funext.
        intros a h.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          exact (!(id_right _)).
        }
        etrans.
        {
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (!(id_left _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite exp_beta.
          exact (!qs).
        }
        rewrite !assoc.
        rewrite BinProductOfArrows_comp.
        rewrite id_left, id_right.
        apply idpath.
      - use exp_funext.
        intros a h.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        unfold parameterized_NNO_from_NNO_rec_exp.
        rewrite !assoc.
        rewrite BinProductOfArrows_comp.
        rewrite NNO_mor_S.
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite exp_beta.
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          exact (!(id_right _)).
        }
        etrans.
        {
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (!(id_left _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite exp_beta.
          apply idpath.
        }
        rewrite !assoc.
        rewrite BinProductOfArrows_comp.
        rewrite id_left, id_right.
        apply idpath.
    Qed.
  End Recursion.

  (** * 2. Parameterized NNOs from NNOs *)
  Definition parameterized_NNO_from_NNO
    : parameterized_NNO T BP.
  Proof.
    use make_parameterized_NNO.
    - exact N.
    - exact (zeroNNO _ N).
    - exact (sucNNO _ N).
    - intros b y zy sy.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (parameterized_NNO_from_NNO_rec zy sy).
        * apply parameterized_NNO_from_NNO_rec_Z.
        * apply parameterized_NNO_from_NNO_rec_S.
      + abstract
          (intros [ f [ qz qs ]] ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           cbn ;
           exact (parameterized_NNO_from_NNO_rec_unique zy sy qz qs)).
  Defined.
End ParameterizedNNOFromNNO.
