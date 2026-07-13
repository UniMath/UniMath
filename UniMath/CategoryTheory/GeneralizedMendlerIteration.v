Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Limits.Graphs.Initial.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.Chains.All.

Local Open Scope cat.

Section GeneralizedMendlerIteration.
  Context {C D : category}.
  Context (F : C ⟶ C) (L : C ⟶ D).
  Context (F_cocont : is_omega_cocont F).
  Context (L_cocont : is_omega_cocont L).
  Context (L_init : preserves_initial L).
  Context (O : Initial C).

  Let LO : Initial D := make_Initial (L O) (L_init _ (pr2 O)).

  Context (X : D).
  Context (Ψ : ∏ {c}, D⟦ L c, X ⟧ → D⟦ L (F c) , X ⟧).
  Context (Ψ_nat : ∏ c c' (q : L c --> X) (f : c' --> c), 
    Ψ c' (#L f · q) = #L (#F f) · Ψ c q).


  Let Fchain : chain C := initChain O F.
  Variable (CC : ColimCocone Fchain).

  Let LFchain : chain D :=  mapchain L Fchain.

  Let x : LO --> X := InitialArrow LO X.

  (* The following definition gives Ψ^n (x) *)
  Local Definition iterate_Ψ_x (n : ℕ) : D ⟦ L (iter_functor F n O), X ⟧.
  Proof.
    induction n; simpl.
    - exact x.
    - use Ψ; exact IHn.
  Defined.

  Local Lemma iterate_Ψ_x_is_cocone (n : ℕ)
    : dmor LFchain (idpath _) · iterate_Ψ_x (1 + n) = iterate_Ψ_x n.
  Proof.
    induction n.
    - use (InitialArrowUnique LO).
    - transitivity (iterate_Ψ_x (1 + n)); [|use idpath].
      cbn; rewrite <- Ψ_nat.
      use maponpaths.
      use IHn. 
  Qed.

  Local Definition iterate_Ψ_x_cocone : cocone LFchain X.
  Proof.
    use make_cocone.
    - use iterate_Ψ_x.
    - abstract (intros n m e; induction e; use iterate_Ψ_x_is_cocone).
  Defined.

  Let L_CC : ColimCocone LFchain
    := make_ColimCocone _ _ _ (L_cocont Fchain _ _ 
        (isColimCocone_from_ColimCocone CC)).


  Definition mendler_iteration_arrow : L (colim CC) --> X
    := colimArrow L_CC _ iterate_Ψ_x_cocone.

  Let r : F (colim CC) --> colim CC 
    := colim_algebra_mor _ F_cocont _.

  Let rinv : colim CC --> F (colim CC) 
    := colim_algebra_mor_inv _ F_cocont _.

  Local Lemma rinv_colimIn_commutes (n : ℕ)
    : colimIn CC (S n) · rinv = #F (colimIn CC n).
  Proof.
    assert (r · rinv = identity _) as H
    by exact (pr122 (colim_algebra_mor_iso _ F_cocont CC)).
    rewrite <- id_right, <- H, assoc.
    refine (!maponpaths (λ x, x · _) _).
    use colim_algebra_mor_commutes.
  Qed.

  Lemma mendler_iteration_arrow_commutes_lemma (n : ℕ)
    : #L (colimIn CC n) · #L rinv · Ψ _ mendler_iteration_arrow = iterate_Ψ_x n.
  Proof.
    destruct n.
    - use (InitialArrowUnique LO).
    - rewrite <- functor_comp, rinv_colimIn_commutes.
      etrans; [symmetry; use Ψ_nat|].
      use maponpaths.
      use (colimArrowCommutes L_CC).
  Qed.

  Proposition mendler_iteration_arrow_commutes
    : #L r · mendler_iteration_arrow = Ψ _ mendler_iteration_arrow.
  Proof.
    assert (r · rinv = identity _) as H
    by exact (pr122 (colim_algebra_mor_iso _ F_cocont CC)).
    rewrite <- id_left, <- functor_id, <- H, functor_comp, <- assoc.
    refine (!maponpaths _ _).
    use (colimArrowUnique L_CC). 
    intro; rewrite assoc; use mendler_iteration_arrow_commutes_lemma.
  Qed.


  Section Uniqueness.
    Context (h : L (colim CC) --> X).
    Context (h_commutes : #L r · h = Ψ _ h).

    Lemma mendler_iteration_unique_lemma (n : ℕ)
      : #L (colimIn CC n) · h = iterate_Ψ_x n.
    Proof.
      induction n.
      - use (InitialArrowUnique LO).
      - rewrite <- (colim_algebra_mor_commutes _ F_cocont CC), functor_comp, <- assoc; fold r.
        etrans; [refine (maponpaths _ _); use h_commutes|].
        rewrite <- Ψ_nat.
        use maponpaths.
        use IHn.
    Qed.

    Proposition mendler_iteration_unique
      : mendler_iteration_arrow = h.
    Proof.
      symmetry; use (colimArrowUnique L_CC).
      use mendler_iteration_unique_lemma.
    Qed.
  End Uniqueness.
End GeneralizedMendlerIteration.
