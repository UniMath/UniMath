(** * Displayed category of varieties over a theory *)

Require Import UniMath.Foundations.All.

Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.

Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Universal.Equations.
Require Import UniMath.Algebra.Universal.CatAlgebras.

Notation "'theory'" := eqsignature. (* isn't it a standard name? *)
Context (sigma : theory).

Definition varieties_disp : disp_cat SET.
Proof.
  use disp_struct.
  - cbn; intro A.
    exact (∑ (op :  ∏ (nm : names sigma),  Vector A (arity nm) → A),
           ∏ e : eqs sigma, holds (make_algebra A op) (geteq e)).
  - cbn; intros a b [opa iseqa] [opb iseqb] f.
    exact (@ishom sigma (make_algebra a opa) (make_algebra b opb) f).
  - cbn. intros A B [opA iseqA] [opB iseqB] f prpt1 prpt2.
    use iscontraprop1.
    + assert (T : isaset (@ishom sigma (make_algebra A opA)(make_algebra B opB) f)).
      { apply isasetaprop. use isapropishom.
      }
      apply T.
    + apply isapropishom.
  - cbn. intros. apply ishomidfun.
  - cbn. intros A B C prpA prpB prpC. intros f g ishomf ishomg.
    exact (ishomcomp (make_hom ishomf) (make_hom ishomg)).
Defined.

Lemma is_univalent_varieties_disp : is_univalent_disp varieties_disp.
Proof.
  use is_univalent_disp_from_SIP_data.
  - cbn; intro A. apply isaset_total2.
    * apply impred_isaset. cbn; intro nm; use isaset_set_fun_space.
    * cbn; intros. apply impred_isaset. cbn; intro sys. apply impred_isaset; cbn. intro t.
      apply isasetaprop. apply A.
  - cbn; intros A [opA iseqA][op'A iseq'A]. intros i i'.
    use total2_paths2_f.
    * use funextsec. intro nm. use funextfun. intro v.
      unfold ishom in *. cbn in *. set (H1:= i nm v). rewrite vector_map_id in H1.
      apply H1.
    * cbn. apply funextsec; cbn; intro e. apply funextsec; intro f. apply A.
Qed.

Definition category_varieties : category := total_category varieties_disp.

Lemma is_univalent_category_varieties : is_univalent category_varieties.
Proof.
  exact (@is_univalent_total_category SET varieties_disp (is_univalent_HSET) is_univalent_varieties_disp).
Qed.
