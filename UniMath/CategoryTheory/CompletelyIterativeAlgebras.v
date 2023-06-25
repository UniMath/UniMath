(** ****************************************************************

Completely iterative algebras according to Stefan Milius, Completely iterative algebras and completely iterative monads, https://doi.org/10.1016/j.ic.2004.05.003

Ralph Matthes, June 2023

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.

Local Open Scope cat.

Section FixAFunctor.

  Context {C : category} (CP : BinCoproducts C) (F : functor C C).

  (** As does Stefan Milius, we use the abbreviation cia for completely iterative algebras. *)
  Definition cia_characteristic_formula (X : algebra_ob F) {x : C}
    (e : x --> CP (F x) (alg_carrier _ X)) (h : x --> alg_carrier _ X) : UU :=
    h = e ·
          BinCoproductOfArrows _ (CP _ _) (CP _ _) (#F h) (identity _) ·
          (BinCoproductArrow (CP _ _) (alg_map _ X) (identity _)).

  (** [e] is called a "flat equation morphism" *)

  Lemma isaprop_cia_characteristic_formula (X : algebra_ob F) {x : C}
    (e : x --> CP (F x) (alg_carrier _ X)) (h : x --> alg_carrier _ X) : isaprop (cia_characteristic_formula X e h).
  Proof.
    apply C.
  Qed.

  Definition cia (X : algebra_ob F) : UU :=
    ∏ (x : C) (e : x --> CP (F x) (alg_carrier _ X)), ∃! h : x --> alg_carrier _ X,
        cia_characteristic_formula X e h.

(** The following is a more modular proof for Example 2.5(iii) in Milius' article
    since we directly use primitive corecursion.
 *)


  Section cia_from_final_coalgebra.

    Context  (X : coalgebra_ob F) (isTerminalX : isTerminal (CoAlg_category F) X).

    Local Definition Xinv : algebra_ob F.
    Proof.
      exists (coalg_carrier _ X).
      exact (inv_from_z_iso (finalcoalgebra_z_iso _ _ _ isTerminalX)).
    Defined.

    Local Definition ϕ_for_cia (x : C) (e : x --> CP (F x) (alg_carrier _ Xinv)) :
      x --> F(CP x (alg_carrier _ Xinv)).
    Proof.
      simple refine (e · _).
      apply (BinCoproductArrow (CP _ _)).
      - apply #F.
        apply BinCoproductIn1.
      - simple refine ((coalg_map _ X) · _).
        apply #F.
        apply BinCoproductIn2.
    Defined.

    Lemma ϕ_for_cia_has_equivalent_characteristic_formula
      (x : C) (e : x --> CP (F x) (alg_carrier _ Xinv)) (h : C ⟦ x, alg_carrier F Xinv ⟧) :
      primitive_corecursion_characteristic_formula CP (ϕ_for_cia x e) h ≃
        cia_characteristic_formula Xinv e h.
    Proof.
      apply weqimplimpl.
      - intro H.
        red in H; red.
        apply pathsinv0 in H.
        apply (z_iso_inv_on_left _ _ _ _ (finalcoalgebra_z_iso _ _ _ isTerminalX)) in H.
        etrans; [ exact H |].
        clear H.
        unfold ϕ_for_cia.
        repeat rewrite assoc'.
        apply maponpaths.
        cbn.
        rewrite postcompWithBinCoproductArrow.
        rewrite precompWithBinCoproductArrow.
        rewrite id_left.
        apply maponpaths_12.
        + rewrite assoc.
          rewrite <- functor_comp.
          rewrite BinCoproductIn1Commutes.
          apply idpath.
        + etrans.
          { rewrite assoc.
            apply cancel_postcomposition.
            rewrite assoc'.
            apply maponpaths.
            rewrite <- functor_comp.
            rewrite BinCoproductIn2Commutes.
            apply functor_id.
          }
          rewrite id_right.
          apply αα'_idA.
      - intro H.
        red in H; red.
        etrans.
        { apply cancel_postcomposition.
          exact H. }
        clear H.
        unfold ϕ_for_cia.
        repeat rewrite assoc'.
        apply maponpaths.
        cbn.
        do 2 rewrite postcompWithBinCoproductArrow.
        rewrite precompWithBinCoproductArrow.
        do 2 rewrite id_left.
        apply maponpaths_12.
        + rewrite <- functor_comp.
          rewrite BinCoproductIn1Commutes.
          etrans.
          { apply maponpaths.
            apply α'α_idFA. }
          apply id_right.
        + rewrite assoc'.
          rewrite <- functor_comp.
          rewrite BinCoproductIn2Commutes.
          rewrite functor_id.
          apply pathsinv0, id_right.
      - apply C.
      - apply isaprop_cia_characteristic_formula.
    Qed.

    Definition cia_from_final_coalgebra : cia Xinv.
    Proof.
      intros x e.
      simple refine (iscontrretract _ _ _ (primitive_corecursion CP isTerminalX (ϕ_for_cia x e))).
      - intros [h H].
        exists h.
        apply ϕ_for_cia_has_equivalent_characteristic_formula.
        assumption.
      - intros [h H].
        exists h.
        apply ϕ_for_cia_has_equivalent_characteristic_formula.
        assumption.
      - intros [h Hyp].
        use total2_paths_f.
        + apply idpath.
        + apply isaprop_cia_characteristic_formula.
    Qed.


  End cia_from_final_coalgebra.


End FixAFunctor.
