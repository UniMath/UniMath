(***** Displayed Category of Algebras over a Signature *****)

Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.Algebra.Universal.

Section algebras.

  Context (sigma : signature).

  Definition algebras_disp :disp_cat SET.
  Proof.
    use disp_struct.
    - exact (λ A:hSet, ∏ (nm : names sigma),  Vector A (arity nm) → A).
    - cbn. intros. exact (@ishom sigma (make_algebra x X) (make_algebra y X0) X1).
    - cbn. intros A B opA opB f prpt1 prpt2.
      use iscontraprop1.
      + assert (T : isaset (@ishom sigma (make_algebra A opA)(make_algebra B opB) f)).
        { apply isasetaprop. use isapropishom.
        }
        apply T.
      + apply isapropishom.
    - cbn. intros. apply ishomidfun.
    - cbn. intros A B C opA opB opC. intros f g ishomf ishomg.
      exact (ishomcomp (make_hom ishomf) (make_hom ishomg)).
  Defined.

  Lemma is_univalent_algebras_disp : is_univalent_disp algebras_disp.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - intro A. cbn. use impred_isaset. intro nm. cbn.
      use isaset_set_fun_space.
    - cbn. intros A op1 op2 ishomid1 ishomid2. use funextsec. intro nm. use funextfun. intro vec.
      unfold ishom in *. cbn in *. set (H1:= ishomid1 nm vec). rewrite vector_map_id in H1.
      apply H1.
  Qed.

  Definition category_algebras : category := total_category algebras_disp.

  Lemma is_univalent_category_algebras : is_univalent category_algebras.
  Proof.
    exact (@is_univalent_total_category SET algebras_disp (is_univalent_HSET) is_univalent_algebras_disp).
  Qed.

End algebras.

Lemma isinitial_termalgebra (sigma :signature) : Initial (category_algebras sigma).
Proof.
  exact (term_algebra sigma ,, iscontrhomsfromterm).
Defined.
