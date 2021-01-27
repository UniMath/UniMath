(** * The univalent category of equational algebras over an equational specification. *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Algebra.Universal.Equations.
Require Import UniMath.Algebra.Universal.EqAlgebras.

Require Import UniMath.CategoryTheory.categories.Universal_Algebra.Algebras.

Context (σ : eqspec).

Local Open Scope sorted_scope.

Definition eqalg_disp : disp_cat (category_algebras σ).
Proof.
  use disp_full_sub.
  exact (λ A, is_eqalgebra A).
Defined.

Lemma is_univalent_eqalg_disp : is_univalent_disp eqalg_disp.
Proof.
  use disp_full_sub_univalent.
  cbn.
  intros A isT isT'.
  use impred_isaprop.
  intro eq.
  use impred_isaprop.
  intro eq'.
  cbn.
  intros p p'.
  apply (pr1 A).
Qed.

Definition category_eqalgebras : category := total_category eqalg_disp.

Lemma is_univalent_category_eqalgebras : is_univalent category_eqalgebras.
Proof.
  exact (@is_univalent_total_category
           (category_algebras σ) eqalg_disp (is_univalent_category_algebras σ) is_univalent_eqalg_disp).
Qed.

(* Alternative version, kept here for comparison purposes.  *)

(*
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.

Definition eqalg_disp : disp_cat (shSet_category σ).
Proof.
  use disp_cat_from_SIP_data.
  - cbn; intro A.
    exact (∑ ops: (∏ nm: names σ, A⋆ (arity nm) → A (sort nm)),
            (∏ e : equations σ, holds (make_algebra A ops) (geteq e))).
  - cbn. intros a b [opa iseqa] [opb iseqb] f.
    exact (@ishom σ (make_algebra a opa) (make_algebra b opb) f).
  - intros. apply isapropishom.
  - cbn. intros. apply ishomid.
  - cbn. intros A B C prpA prpB prpC. intros f g ishomf ishomg.
    exact (ishomcomp (make_hom ishomf) (make_hom ishomg)).
Defined.

Lemma is_univalent_eqalg_disp : is_univalent_disp eqalg_disp.
Proof.
  use is_univalent_disp_from_SIP_data.
  - cbn; intro A. apply isaset_total2.
    * apply impred_isaset. cbn; intro nm; use isaset_set_fun_space.
    * cbn; intros. apply impred_isaset. cbn; intro sys. apply impred_isaset; cbn. intro t.
      apply isasetaprop. apply A.
  - cbn; intros A [opA iseqA][op'A iseq'A]. intros i i'.
    use total2_paths2_f.
    * use funextsec. intro nm. use funextfun. intro v.
      unfold ishom in *. cbn in *. set (H1 := i nm v).
      eapply pathscomp0.
      exact H1.
      apply maponpaths.
      apply staridfun.
    * cbn. apply funextsec; cbn; intro e. apply funextsec; intro f. apply A.
Qed.

Definition category_eqalgebras : category := total_category eqalg_disp.

Lemma is_univalent_category_eqalgebras : is_univalent category_eqalgebras.
Proof.
  exact (@is_univalent_total_category (shSet_category σ) eqalg_disp
           (is_univalent_shSet_category σ) is_univalent_eqalg_disp).
Qed. 
*)
