(** Constructs the bicategory of actions, strong action-based functors and their natural transformations

The construction goes through a displayed bicategory over the bicategoy of (small) categories.

Author: Ralph Matthes 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.Actions.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrength.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrongFunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.


Local Open Scope cat.
Local Open Scope mor_disp_scope.


(* TODO: factor out proof, upstream the definition *)
Definition categoryBinProduct (C C' : category) : category.
Proof.
  exists (C ⊠ C').
  intros a b. apply isasetdirprod.
  - apply C.
  - apply C'.
Defined.

Notation "C ⊠ C'" := (categoryBinProduct C C').

Section DispCartProdOfCats.

  Context {C C' : category}
          (D : disp_cat C)
          (D' : disp_cat C').

  Definition disp_binprod_ob_mor : disp_cat_ob_mor (C ⊠ C').
  Proof.
    use tpair.
    - intro cc'. exact (D (pr1 cc') × D' (pr2 cc')).
    - intros aa' bb' xx' yy' fg.
      exact ( (pr1 xx' -->[ pr1 fg ] pr1 yy') × (pr2 xx' -->[ pr2 fg ] pr2 yy' )).
  Defined.

  Definition disp_binprod_id_comp : disp_cat_id_comp _ disp_binprod_ob_mor.
  Proof.
    use tpair.
    - intros x xx.
      use tpair.
      * apply id_disp.
      * apply id_disp.
    - intros aa' bb' cc' ff' gg'  xx' yy' zz' hh' ii'.
      use tpair.
      * apply (comp_disp (pr1 hh') (pr1 ii')).
      * apply (comp_disp (pr2 hh') (pr2 ii')).
  Defined.


  Definition disp_binprod_data : disp_cat_data (C ⊠ C')
    := disp_binprod_ob_mor ,,  disp_binprod_id_comp.


  Lemma disp_binprod_transportf_pr1 (a b : C) (f g : a --> b)
        (a' b' : C') (f' g' : a' --> b')
        (x : D a) (y : D b) (x' : D' a') (y' : D' b')
        (ff : x -->[f] y) (ff' : x' -->[f'] y')
        (e : precatbinprodmor f f' = precatbinprodmor g g')
    : transportf (mor_disp _ _) (maponpaths pr1 e) ff
      =
      pr1 (transportf (@mor_disp _ disp_binprod_data (a,,a') _ (x,, x') (_,, _)) e (ff,, ff')) .
  Proof.
    induction e.
    apply idpath.
  Qed.


  Lemma disp_binprod_transportf_pr2 (a b : C) (f g : a --> b)
        (a' b' : C') (f' g' : a' --> b')
        (x : D a) (y : D b) (x' : D' a') (y' : D' b')
        (ff : x -->[f] y) (ff' : x' -->[f'] y')
        (e : precatbinprodmor f f' = precatbinprodmor g g')
    : transportf (mor_disp _ _) (maponpaths (dirprod_pr2) e) ff'
      =
      pr2 (transportf (@mor_disp _ disp_binprod_data (a,,a') _ (x,, x') (_,, _)) e (ff,, ff')) .
  Proof.
    induction e.
    apply idpath.
  Qed.


  Lemma disp_binprod_axioms : disp_cat_axioms _ disp_binprod_data.
  Proof.
    repeat split.
    - intros [a a'] [b b'] [f f'] [x x'] [y y'] [ff ff'].
      simpl in *.
      apply dirprodeq.
      * simpl in *.
        etrans.
        apply id_left_disp.
        etrans. 2: { apply disp_binprod_transportf_pr1. }.
        apply transportf_paths.
        apply C.
      * simpl in *.
        etrans. apply id_left_disp.
        etrans. 2: { apply disp_binprod_transportf_pr2. }.
        apply transportf_paths.
        apply C'.
    - intros [a a'] [b b'] [f f'] [x x'] [y y'] [ff ff'].
      simpl in *.
      apply dirprodeq.
      * simpl in *.
        etrans.
        apply id_right_disp.
        etrans. 2: { apply disp_binprod_transportf_pr1. }.
        apply transportf_paths.
        apply C.
      * simpl in *.
        etrans. apply id_right_disp.
        etrans. 2: { apply disp_binprod_transportf_pr2. }.
        apply transportf_paths.
        apply C'.
    - intros [a a'] [b b'] [c c'] [d d'] [f f'] [g g'] [h h'] [x x'] [y y'] [z z']
             [w w'] [u u'] [v v'] [r r'].
      simpl in *.
      apply dirprodeq.
      * simpl.
        etrans. apply assoc_disp.
        etrans. 2: { apply disp_binprod_transportf_pr1. }.
        apply transportf_paths.
        apply C.
      * simpl.
        etrans. apply assoc_disp.
        etrans. 2: { apply disp_binprod_transportf_pr2. }.
        apply transportf_paths.
        apply C'.
    - intros.
      apply isasetdirprod.
      * apply D.
      * apply D'.
  Qed.

  Definition disp_binprod : disp_cat (C ⊠ C')
    :=  disp_binprod_data ,,  disp_binprod_axioms.

End DispCartProdOfCats.

Notation "D ⊠⊠ D'" := (disp_binprod D D') (at level 60).


Lemma disp_binprod_transportf (C C' : category) (D : disp_cat C) (D' : disp_cat C')
      (a b : C) (a' b' : C') (f g : a --> b) (f' g' : a' --> b')
      (x : D a) (y : D b) (x' : D' a') (y' : D' b')
      (ff : x -->[f] y) (ff' : x' -->[f'] y')
      (e : (f,,f') = (g,, g'))
  : transportf (@mor_disp (C ⊠ C') (disp_binprod D D') (a,,a') (b,,b') (x,,x') (y,,y')) e (ff,, ff')  =
      transportf (mor_disp _ _ ) (maponpaths pr1 e) ff ,, transportf (mor_disp _ _ )  (maponpaths (dirprod_pr2) e) ff'.
Proof.
  induction e.
  apply idpath.
Qed.

Section DispCartProdOfFunctors.

  Context {A A' C C' : category}
          {F : functor A C}
          {F' : functor A' C'}
          {D : disp_cat A}
          {D' : disp_cat A'}
          {E : disp_cat C}
          {E' : disp_cat C'}
          (G : disp_functor F D E)
          (G' : disp_functor F' D' E').

  Definition disp_pair_functor_data
    : disp_functor_data (pair_functor F F') (D ⊠⊠ D') (E ⊠⊠ E').
  Proof.
    use tpair.
    - intros aa' dd'.
      use tpair.
      + use G. apply (pr1 dd').
      + use G'. apply (pr2 dd').
    - cbn. intros aa' aa'' xx' yy' ff' gg'.
      use tpair.
      + apply #G. apply (pr1 gg').
      +  apply #G'. apply (pr2 gg').
  Defined.

  Lemma disp_pair_functor_axioms :
    @disp_functor_axioms (A ⊠ A') (C ⊠ C') (pair_functor F F') _ _ disp_pair_functor_data.
  Proof.
    split.
    - intros [a a'] [d d'].
      apply pathsinv0.
      etrans. { apply disp_binprod_transportf. }
      cbn.
      apply dirprodeq; cbn.
      + apply pathsinv0.
        etrans. apply disp_functor_id.
        apply transportf_paths. apply C.
      + apply pathsinv0.
        etrans. apply disp_functor_id.
        apply transportf_paths. apply C'.
    - intros [a a'] [b b'] [c c'] [w w'] [x x'] [y y'] [f f'] [g g'] [ff ff'] [gg gg'].
      cbn in *.
      apply pathsinv0.
      etrans. { apply disp_binprod_transportf. }
      apply pathsinv0.
      apply dirprodeq; cbn.
      + etrans. apply disp_functor_comp.
        apply transportf_paths. apply C.
      + etrans. apply disp_functor_comp.
        apply transportf_paths. apply C'.
  Qed.

  Definition disp_pair_functor :
    @disp_functor (A ⊠ A') (C ⊠ C')  (pair_functor F F') (D ⊠⊠ D') (E ⊠⊠ E')
    :=  disp_pair_functor_data ,, disp_pair_functor_axioms.

End DispCartProdOfFunctors.

Section DispAssocFunctors.

  Context (A B C : category)
          (DA : disp_cat A)
          (DB : disp_cat B)
          (DC : disp_cat C).

  Definition disp_assoc_data :
    disp_functor_data (precategory_binproduct_assoc A B C)
                      (DA ⊠⊠ (DB ⊠⊠ DC))
                      ((DA ⊠⊠ DB) ⊠⊠ DC).
  Proof.
    use tpair.
    - intros abc dabc.
      exact ( (pr1 dabc,,pr12 dabc) ,, pr22 dabc).
    - intros abc abc' xx yy f g.
      exact ( (pr1 g,,pr12 g) ,, pr22 g).
  Defined.

  (* Type error - due to precategory vs category?
  Lemma disp_assoc_axioms : disp_functor_axioms disp_assoc_data.
  Abort.
   *)

Definition displayed_tensor {C : category}
           (tensor : C ⊠ C ⟶ C)
           (D : disp_cat C)
  : UU
  := disp_functor tensor (disp_binprod D D) D.


Section FixDispTensor.

  Context {C : category}
          (tensor : C ⊠ C ⟶ C)
          {D : disp_cat C}
          (disp_tensor : displayed_tensor tensor D).

  Let al : functor _ _ := assoc_left tensor.
  Let ar : functor _ _ := assoc_right tensor.

  Definition disp_assoc_left : @disp_functor ((C ⊠ C) ⊠ C) C al  ((D ⊠⊠ D) ⊠⊠ D) D .
  Proof.
    use disp_functor_composite.
    - use (disp_binprod D D).
    - use disp_pair_functor.
      + use disp_tensor.
      + use disp_functor_identity.
    - use disp_tensor.
  Defined.


  (* TODO: why unassoc? *)
  Definition disp_category_binproduct_unassoc



  (* Should work modulo changes in proof once [ar] is correct.
  Definition disp_assoc_right : @disp_functor (C ⊠ (C ⊠ C)) C ar  (D ⊠⊠ (D ⊠⊠ D)) D .
  Proof.
    use disp_functor_composite.
    - use (disp_binprod D D).
    - use disp_pair_functor.
      + use disp_tensor.
      + use disp_functor_identity.
    - use disp_tensor.
  Defined.
*)



End FixDispTensor.
