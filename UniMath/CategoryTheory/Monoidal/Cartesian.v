(** * Cartesian monoidal categories *)

(** ** Contents

 - Every category with finite products is monoidal
 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.


Section CartesianMonoidal.
  Context {C : precategory}.
  Context (T : Terminal C).
  Context (BC : BinProducts C).
  Context (hsC : has_homsets C).

  Definition cartesian_left_unitor :
    nat_iso (I_pretensor (binproduct_functor BC) T) (functor_identity C).
  Proof.
    use tpair.
    - (** left unitor natural transformation *)
      use mk_nat_trans.
      + (** [nat_trans_data] *)
        intros x; cbn.
        use mk_iso; [|apply terminal_binprod_unit_l].
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
      apply terminal_binprod_unit_l.
  Defined.

  Definition cartesian_right_unitor :
    nat_iso (I_posttensor (binproduct_functor BC) T) (functor_identity C).
  Proof.
    use tpair.
    - (** right unitor natural transformation *)
      use mk_nat_trans.
      + (** [nat_trans_data] *)
        intros x; cbn.
        use mk_iso; [|apply terminal_binprod_unit_r].
      + (** [is_nat_trans] *)
        intros x y f.
        unfold terminal_binprod_unit_r; cbn.
        apply BinProductOfArrowsPr1.
    - (** right unitor is a natural isomorphism *)
      intro x; unfold is_nat_iso; cbn.
      apply terminal_binprod_unit_r.
  Defined.

  (** TODO: from LatticeObject *)
  Local Notation "c '⊗' d" := (BinProductObject C (BC c d)) : cat.
  Local Notation "f '××' g" := (BinProductOfArrows _ _ _ f g) (at level 80) : cat.
  Local Open Scope cat.
  (* Local Notation "π1[ ( x ) ⊗ ( y ) ]" := (BinProductPr1 _ (BC x y)). *)
  (* Local Notation "π2[ ( x ) ⊗ ( y ) ]" := (BinProductPr2 _ (BC x y)). *)

  Hint Resolve BinProductArrow : binprod.
  Hint Resolve BinProductPr1 : binprod.
  Hint Resolve BinProductPr2 : binprod.
  Hint Resolve compose : binprod.

  (** The behavior of eauto here is to [apply] the above hints until successful *)
  Definition binprod_assoc_r {x y z} : C⟦x ⊗ (y ⊗ z), (x ⊗ y) ⊗ z⟧.
  Proof.
    eauto with binprod.
  Defined.

  Definition binprod_assoc_l {x y z} : C⟦(x ⊗ y) ⊗ z, x ⊗ (y ⊗ z)⟧.
  Proof.
    eauto with binprod.
  Defined.

  (* Equalities for which it almost always pays to rewrite forward *)
  Hint Rewrite BinProductPr1Commutes : binprod.
  Hint Rewrite BinProductPr2Commutes : binprod.
  Hint Rewrite BinProductOfArrowsPr1 : binprod.
  Hint Rewrite BinProductOfArrowsPr2 : binprod.

  Lemma assoc_l_qinv_assoc_r {x y z : C} :
    is_inverse_in_precat (@binprod_assoc_l x y z) (@binprod_assoc_r x y z).
  Proof.
    unfold is_inverse_in_precat.
    split.
    - unfold binprod_assoc_l, binprod_assoc_r.
      do 2 rewrite precompWithBinProductArrow.
      repeat ( rewrite assoc || autorewrite with binprod ).
      refine (_ @ !BinProductArrowEta _ _ _ _ _ (id (x ⊗ y ⊗ z))).
      do 2 rewrite id_left.
      apply (maponpaths (fun f => BinProductArrow _ _ f _)).
      exact (! BinProductArrowEta _ _ _ _ _ (BinProductPr1 _ _)).
    - unfold binprod_assoc_l, binprod_assoc_r.
      do 2 rewrite precompWithBinProductArrow.
      repeat ( rewrite assoc || autorewrite with binprod ).
      refine (_ @ !BinProductArrowEta _ _ _ _ _ (id (x ⊗ (y ⊗ z)))).
      do 2 rewrite id_left.
      apply (maponpaths (fun f => BinProductArrow _ _ _ f)).
      exact (! BinProductArrowEta _ _ _ _ _ (BinProductPr2 _ _)).
  Qed.

  Local Lemma f_equal_2 :
    forall {A B C : UU} (f : A -> B -> C) (a a' : A) (b b' : B),
      a = a' -> b = b' -> f a b = f a' b'.
  Proof.
    do 8 intro; intros eq1 eq2.
    abstract (rewrite eq1; rewrite eq2; auto).
  Defined.

  Lemma cartesian_monoidal : monoidal_precat_structure C.
  Proof.
    use mk_monoidal_precat_structure.
    - (** Tensor functor [C ⊠ C ⟶ C] *)
      apply binproduct_functor; assumption.
    - (** Identity object [I : C] *)
      exact T.
    - (** [left_unitor] : [T × y -> y] *)
      exact cartesian_left_unitor.
    - (** [right_unitor] : [y × T -> y] *)
      exact cartesian_right_unitor.
    - (** [associator] *)
      unfold associator.
      use tpair.
      + use mk_nat_trans.
        * intros x.
          apply binprod_assoc_l.
        * intros x y f; cbn.
          unfold binprod_assoc_l.

          abstract ((** Rewrite the LHS *)
                    do 2 rewrite precompWithBinProductArrow;
                    do 4 (rewrite assoc || autorewrite with binprod);
                    do 4 (rewrite <- assoc || autorewrite with binprod);

                    (** Rewrite the RHS *)
                    do 2 rewrite postcompWithBinProductArrow;
                    do 2 rewrite assoc;
                    reflexivity).
      + intros bp.
        use is_iso_qinv.
        * apply binprod_assoc_r.
        * apply assoc_l_qinv_assoc_r.
   - unfold triangle_eq; intros a b; cbn.
     unfold binprod_assoc_l.
     rewrite postcompWithBinProductArrow.
     unfold BinProductOfArrows; cbn.
     autorewrite with binprod.
     do 2 rewrite id_right.
     reflexivity.
   - unfold pentagon_eq; cbn; intros a b c d.

     unfold binprod_assoc_l; cbn.
     repeat (rewrite assoc   || rewrite BinProdPr1Commutes).
     repeat (rewrite <- assoc || rewrite BinProdPr2Commutes).
     repeat rewrite postcompWithBinProductArrow.
     repeat rewrite precompWithBinProductArrow.

     (* Now they both have the form:
        [BinProductArrow C (BC a (b ⊗ (c ⊗ d))) f g],
        so we can split into cases. *)
     apply f_equal_2.

     + repeat (rewrite assoc   || autorewrite with binprod).
       repeat rewrite <- assoc.
       apply (maponpaths (fun f => BinProductPr1 C _ · f)).
       repeat (rewrite assoc   || autorewrite with binprod).
       rewrite id_right.
       reflexivity.
     + apply f_equal_2.
       * repeat (rewrite assoc   || autorewrite with binprod).
         rewrite precompWithBinProductArrow.
         repeat (rewrite assoc   || autorewrite with binprod).
         repeat rewrite <- assoc.
         apply (maponpaths (fun f => BinProductPr1 C _ · f)).
         repeat (rewrite assoc   || autorewrite with binprod).
         reflexivity.
       * repeat (rewrite assoc   || autorewrite with binprod).
         apply f_equal_2.
         -- repeat rewrite precompWithBinProductArrow.
            repeat (rewrite assoc   || autorewrite with binprod).
            repeat rewrite <- assoc.
            apply (maponpaths (fun f => BinProductPr1 C _ · f)).
            repeat rewrite assoc.
            autorewrite with binprod.
            reflexivity.
         -- repeat rewrite precompWithBinProductArrow.
            repeat (rewrite assoc   || autorewrite with binprod).
            rewrite id_right.
            reflexivity.
  Defined.
End CartesianMonoidal.