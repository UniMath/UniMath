(** * Cartesian monoidal categories *)

(** ** Contents

 - Every category with finite products is monoidal
 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.


Section CartesianMonoidal.
  Context {C : category}.
  Context (T : Terminal C).
  Context (BC : BinProducts C).

  Definition cartesian_left_unitor :
    left_unitor (binproduct_functor BC) T.
  Proof.
    use tpair.
    - (** left unitor natural transformation *)
      use make_nat_trans.
      + (** [nat_trans_data] *)
        intros x; cbn.
        use make_iso; [|apply terminal_binprod_unit_l].
      + (** [is_nat_trans] *)
        (** The diagram:
            <<
              T × y -----> y
                |          |
                V          V
              T × z -----> z
            >>
         *)
        intros x y f.
        unfold terminal_binprod_unit_l; cbn.
        apply BinProductOfArrowsPr2.
    - (** left unitor is a natural isomorphism *)
      intro x; unfold is_nat_iso; cbn.
      apply is_z_iso_from_is_iso.
      apply terminal_binprod_unit_l.
  Defined.

  Definition cartesian_right_unitor :
    right_unitor (binproduct_functor BC) T.
  Proof.
    use tpair.
    - (** right unitor natural transformation *)
      use make_nat_trans.
      + (** [nat_trans_data] *)
        intros x; cbn.
        use make_iso; [|apply terminal_binprod_unit_r].
      + (** [is_nat_trans] *)
        intros x y f.
        unfold terminal_binprod_unit_r; cbn.
        apply BinProductOfArrowsPr1.
    - (** right unitor is a natural isomorphism *)
      intro x; unfold is_nat_iso; cbn.
      apply is_z_iso_from_is_iso.
      apply terminal_binprod_unit_r.
  Defined.

  (** TODO: from LatticeObject *)
  Local Notation "c '⊗' d" := (BinProductObject C (BC c d)) : cat.
  Local Notation "f '××' g" := (BinProductOfArrows _ _ _ f g) (at level 80) : cat.
  Local Open Scope cat.
  (* Local Notation "π1[ ( x ) ⊗ ( y ) ]" := (BinProductPr1 _ (BC x y)). *)
  (* Local Notation "π2[ ( x ) ⊗ ( y ) ]" := (BinProductPr2 _ (BC x y)). *)

  Local Lemma f_equal_2 :
    forall {A B C : UU} (f : A -> B -> C) (a a' : A) (b b' : B),
      a = a' -> b = b' -> f a b = f a' b'.
  Proof.
    do 8 intro; intros eq1 eq2.
    abstract (rewrite eq1; rewrite eq2; reflexivity).
  Defined.

  Lemma cartesian_monoidal : monoidal_cat.
  Proof.
    use mk_monoidal_cat.
    - exact C.
    - (** Tensor functor [C ⊠ C ⟶ C] *)
      apply binproduct_functor; assumption.
    - (** Identity object [I : C] *)
      exact T.
    - (** [left_unitor] : [T × y -> y] *)
      exact cartesian_left_unitor.
    - (** [right_unitor] : [y × T -> y] *)
      exact cartesian_right_unitor.
    - (** [associator] *)
      use make_nat_z_iso.
      + use make_nat_trans.
        * intros x.
          apply binprod_assoc_l.
        * intros x y f; cbn.
          unfold binprod_assoc_l.
          abstract(
            do 2 rewrite precompWithBinProductArrow;
            rewrite !assoc, !BinProductOfArrowsPr1, BinProductOfArrowsPr2;
            rewrite !assoc', BinProductOfArrowsPr1, BinProductOfArrowsPr2;
            do 2 rewrite postcompWithBinProductArrow;
            do 2 rewrite assoc;
            reflexivity
          ).
      + intros bp.
        use make_is_z_isomorphism.
        * apply binprod_assoc_r.
        * apply assoc_l_qinv_assoc_r.
    - intros a b; cbn.
      unfold binprod_assoc_l.
      rewrite postcompWithBinProductArrow.
      unfold BinProductOfArrows; cbn.
      rewrite BinProductPr2Commutes.
      do 2 rewrite id_right.
      reflexivity.
    - unfold pentagon_eq; cbn; intros a b c d.
      unfold binprod_assoc_l; cbn.
      repeat (rewrite assoc || rewrite BinProdPr1Commutes).
      repeat (rewrite <- assoc || rewrite BinProdPr2Commutes).
      repeat rewrite postcompWithBinProductArrow.
      repeat rewrite precompWithBinProductArrow.

      (* Now they both have the form:
          [BinProductArrow C (BC a (b ⊗ (c ⊗ d))) f g],
          so we can split into cases. *)
      apply f_equal_2.

      + rewrite assoc, BinProductPr1Commutes.
        rewrite !assoc, BinProductOfArrowsPr1.
        rewrite !assoc'.
        apply cancel_precomposition.
        rewrite assoc, BinProductPr1Commutes, id_right.
        reflexivity.
      + apply f_equal_2.
        * rewrite assoc, BinProductPr1Commutes.
          rewrite assoc, precompWithBinProductArrow.
          rewrite assoc, BinProductPr1Commutes.
          rewrite assoc, BinProductOfArrowsPr1.
          rewrite !assoc'.
          apply cancel_precomposition.
          rewrite assoc.
          rewrite BinProductPr2Commutes, BinProductPr1Commutes.
          reflexivity.
        * rewrite assoc, BinProductPr2Commutes.
          rewrite assoc, BinProductPr2Commutes.
          apply f_equal_2.
          -- repeat rewrite precompWithBinProductArrow.
             rewrite assoc, BinProductPr1Commutes, BinProductOfArrowsPr1.
             rewrite !assoc'.
             apply cancel_precomposition.
             rewrite assoc, BinProductPr2Commutes, BinProductPr2Commutes.
             reflexivity.
          -- repeat rewrite precompWithBinProductArrow.
             rewrite BinProductOfArrowsPr2.
             rewrite id_right.
             reflexivity.
  Defined.
End CartesianMonoidal.
