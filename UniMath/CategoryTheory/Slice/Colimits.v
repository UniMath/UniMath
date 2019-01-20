(** * Colimits in slice categories *)

(** ** Contents

  - Colimits in slice categories ([slice_precat_colims])

  - Binary coproducts in slice categories of categories with binary
    coproducts ([BinCoproducts_slice_precat])

  - Coproducts in slice categories of categories with coproducts
    ([Coproducts_slice_precat])

  - Initial object in slice categories with initial object
    ([Initial_slice_precat])
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
(* Require Import UniMath.CategoryTheory.Core.NaturalTransformations. *)

Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import UniMath.CategoryTheory.Slice.Core.

Local Open Scope cat.

(** ** Colimits in slice categories ([slice_precat_colims]) *)

Section slicecat_colimits.

Context (g : graph) {C : precategory} (hsC : has_homsets C) (x : C).

Local Notation "C / X" := (slice_precat C X hsC).

Let U : functor (C / x) C := slicecat_to_cat hsC x.

Lemma slice_precat_isColimCocone (d : diagram g (C / x)) (a : C / x)
  (cc : cocone d a)
  (H : isColimCocone (mapdiagram U d) (U a) (mapcocone U d cc)) :
  isColimCocone d a cc.
Proof.
set (CC := mk_ColimCocone _ _ _ H).
intros y ccy.
use unique_exists.
+ use tpair; simpl.
  * apply (colimArrow CC), (mapcocone U _ ccy).
  * abstract (apply pathsinv0;
              eapply pathscomp0; [apply (postcompWithColimArrow _ CC (pr1 y) (mapcocone U d ccy))|];
              apply pathsinv0, (colimArrowUnique CC); intros u; simpl;
              eapply pathscomp0; [apply (!(pr2 (coconeIn cc u)))|];
              apply (pr2 (coconeIn ccy u))).
+ abstract (intros u; apply subtypeEquality; [intros xx; apply hsC|]; simpl;
            apply (colimArrowCommutes CC)).
+ abstract (intros f; simpl; apply impred; intro u; apply has_homsets_slice_precat).
+ abstract (intros f; simpl; intros Hf;
            apply eq_mor_slicecat; simpl;
            apply (colimArrowUnique CC); intro u; cbn;
            rewrite <- (Hf u); apply idpath).
Defined.

Lemma slice_precat_ColimCocone (d : diagram g (C / x))
  (H : ColimCocone (mapdiagram U d)) :
  ColimCocone d.
Proof.
use mk_ColimCocone.
- use tpair.
  + apply (colim H).
  + apply colimArrow.
    use mk_cocone.
    * intro v; apply (pr2 (dob d v)).
    * abstract (intros u v e; apply (! pr2 (dmor d e))).
- use mk_cocone.
  + intro v; simpl.
    use tpair; simpl.
    * apply (colimIn H v).
    * abstract (apply pathsinv0, (colimArrowCommutes H)).
  + abstract (intros u v e; apply eq_mor_slicecat, (coconeInCommutes (colimCocone H))).
- intros y ccy.
  use unique_exists.
  + use tpair; simpl.
    * apply colimArrow, (mapcocone U _ ccy).
    * abstract (apply pathsinv0, colimArrowUnique; intros v; simpl; rewrite assoc;
                eapply pathscomp0;
                  [apply cancel_postcomposition,
                        (colimArrowCommutes H _ (mapcocone U _ ccy) v)|];
                induction ccy as [f Hf]; simpl; apply (! pr2 (f v))).
  + abstract (intro v; apply eq_mor_slicecat; simpl;
              apply (colimArrowCommutes _ _ (mapcocone U d ccy))).
  + abstract (simpl; intros f; apply impred; intro v; apply has_homsets_slice_precat).
  + abstract (intros f Hf; apply eq_mor_slicecat; simpl in *; apply colimArrowUnique;
              intros v; apply (maponpaths pr1 (Hf v))).
Defined.

End slicecat_colimits.

Lemma slice_precat_colims_of_shape {C : precategory} (hsC : has_homsets C)
  {g : graph} (x : C) (CC : Colims_of_shape g C) :
  Colims_of_shape g (slice_precat C x hsC).
Proof.
intros y; apply slice_precat_ColimCocone, CC.
Defined.

Lemma slice_precat_colims {C : precategory} (hsC : has_homsets C) (x : C) (CC : Colims C) :
  Colims (slice_precat C x hsC).
Proof.
intros g d; apply slice_precat_ColimCocone, CC.
Defined.

(** ** Binary coproducts in slice categories of categories with binary coproducts *)

Section slicecat_bincoproducts.

Context {C : precategory} (hsC : has_homsets C) (BC : BinCoproducts C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma BinCoproducts_slice_precat (x : C) : BinCoproducts (C / x).
Proof.
intros a b.
use mk_BinCoproduct.
+ exists (BinCoproductObject _ (BC (pr1 a) (pr1 b))).
  apply (BinCoproductArrow _ _ (pr2 a) (pr2 b)).
+ use tpair.
  - apply BinCoproductIn1.
  - abstract (cbn; rewrite BinCoproductIn1Commutes; apply idpath).
+ use tpair.
  - apply BinCoproductIn2.
  - abstract (cbn; rewrite BinCoproductIn2Commutes; apply idpath).
+ intros c f g.
  use unique_exists.
  - exists (BinCoproductArrow _ _ (pr1 f) (pr1 g)).
    abstract (apply pathsinv0, BinCoproductArrowUnique;
      [ rewrite assoc, (BinCoproductIn1Commutes C _ _ (BC (pr1 a) (pr1 b))), (pr2 f); apply idpath
      | rewrite assoc, (BinCoproductIn2Commutes C _ _ (BC (pr1 a) (pr1 b))), (pr2 g)]; apply idpath).
  - abstract (split; apply eq_mor_slicecat; simpl;
             [ apply BinCoproductIn1Commutes | apply BinCoproductIn2Commutes ]).
  - abstract (intros y; apply isapropdirprod; apply has_homsets_slice_precat).
  - abstract (intros y [<- <-]; apply eq_mor_slicecat, BinCoproductArrowUnique; apply idpath).
Defined.

End slicecat_bincoproducts.

(** ** Coproducts in slice categories of categories with coproducts *)

Section slicecat_coproducts.

Context {C : precategory} (hsC : has_homsets C) (I : UU) (BC : Coproducts I C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma Coproducts_slice_precat (x : C) : Coproducts I (C / x).
Proof.
intros a.
use mk_Coproduct.
+ exists (CoproductObject _ _ (BC (λ i, pr1 (a i)))).
  apply CoproductArrow; intro i; apply (pr2 (a i)).
+ intro i; use tpair; simpl.
  - apply (CoproductIn I C (BC (λ i, pr1 (a i))) i).
  - abstract (rewrite (CoproductInCommutes I C _ (BC (λ i, pr1 (a i)))); apply idpath).
+ intros c f.
  use unique_exists.
  - exists (CoproductArrow _ _ _ (λ i, pr1 (f i))).
    abstract (simpl; apply pathsinv0, CoproductArrowUnique; intro i;
              rewrite assoc, (CoproductInCommutes _ _ _ (BC (λ i, pr1 (a i)))), (pr2 (f i)); apply idpath).
  - abstract (intros i;
              apply eq_mor_slicecat, (CoproductInCommutes _ _ _ (BC (λ i0 : I, pr1 (a i0))))).
  - abstract (intros y; apply impred; intro i; apply has_homsets_slice_precat).
  - abstract (simpl; intros y Hy;
              apply eq_mor_slicecat, CoproductArrowUnique;
              intros i; apply (maponpaths pr1 (Hy i))).
Defined.

End slicecat_coproducts.

(** ** Initial object *)

Section slicecat_initial.

Context {C : precategory} (hsC : has_homsets C) (IC : Initial C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma Initial_slice_precat (x : C) : Initial (C / x).
Proof.
use mk_Initial.
- use tpair.
  + apply (InitialObject IC).
  + apply InitialArrow.
- intros y.
  use unique_exists; simpl.
  * apply InitialArrow.
  * abstract (apply pathsinv0, InitialArrowUnique).
  * abstract (intros f; apply hsC).
  * abstract (intros f Hf; apply InitialArrowUnique).
Defined.

End slicecat_initial.