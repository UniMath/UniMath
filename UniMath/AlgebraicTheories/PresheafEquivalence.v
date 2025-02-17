(**************************************************************************************************

  The equivalence between presheaves on the monoid L1 and on the Lawvere theory L

  Let L be a λ-theory. The set L 1 of terms with one free variable form a monoid under substitution,
  with unit x1, which gives a one-object category [algebraic_theory_monoid_category] and we will
  denote this with L1. We also have a category [algebraic_theory_to_lawvere], with objects {0, 1, …}
  and morphisms from m to n given by (L n)^m. We will denote this with LL.

  The embedding L1 ↪ LL gives a precomposition functor on functor categories [LL, D] ⟶ [L1, D]. In
  this file, we will show that this functor is an equivalence.

  We first show that we have an equivalence F: R ≃ K between the Karoubi envelope K of L1 and the
  category of retracts R from Scott's representation theorem.
  Then, by Scott's representation theorem, we can embed LL into the Karoubi envelope K, sending n to
  F(U^n).
  The composition L1 ⟶ LL ⟶ K equals the embedding of L1 into its Karoubi envelope. Therefore, the
  precomposition [K, D] ⟶ [L1, D] is an equivalence.
  If D has colimits, the statements above suffice to show that the individual precompositions
  [K, D] ⟶ [LL, D] and [LL, D] ⟶ [L1, D] are equivalences, which concludes the proof.

  Contents
  1. The equivalence between R and K [algebraic_theory_retracts_equiv_karoubi]
  2. The fully faithful functor from LL to K [algebraic_theory_lawvere_to_karoubi]
  2.1. The isomorphism between the composed functor and the embedding from L1 to K
    [algebraic_theory_lawvere_to_karoubi_after_theory_monoid_to_lawvere]
  3. The equivalence [lawvere_theory_presheaf_equiv_monoid_presheaf]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryToLawvereTheory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryToMonoid.
Require Import UniMath.AlgebraicTheories.CategoryOfRetracts.
Require Import UniMath.AlgebraicTheories.Combinators.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.OriginalRepresentationTheorem.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.EquivalenceFromComp.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Retracts.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import Ltac2.Ltac2.

Local Open Scope algebraic_theories.
Local Open Scope stn.
Local Open Scope cat.
Local Open Scope lambda_calculus.

(** * 1. The equivalence between R and K *)

Section Karoubi.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).

  Definition algebraic_theory_karoubi
    : setcategory
    := set_karoubi_envelope (algebraic_theory_monoid_category L).

  Definition algebraic_theory_retracts_to_karoubi
    : R (n := 0) L Lβ ⟶ algebraic_theory_karoubi.
  Proof.
    refine '(make_functor _ _).
    - refine '(make_functor_data _ _).
      + intro A.
        refine '(make_karoubi_ob _ _ _ _).
        * exact tt.
        * exact (appx (A : R_ob L)).
        * abstract (
            refine '(subst_is_compose _ Lβ _ _ @ _);
            apply maponpaths;
            apply R_ob_idempotent
          ).
      + intros A B f.
        refine '(make_karoubi_mor _ _ _ _).
        * exact (appx (f : R_mor _ _ _)).
        * abstract (
            refine '(subst_is_compose _ Lβ _ _ @ _);
            apply maponpaths;
            apply (R_mor_is_mor_right _ Lβ)
          ).
        * abstract (
            refine '(subst_is_compose _ Lβ _ _ @ _);
            apply maponpaths;
            apply (R_mor_is_mor_left _ Lβ)
          ).
    - split.
      + abstract (
          intro x;
          now apply karoubi_mor_eq
        ).
      + abstract (
          intros A B C f g;
          apply karoubi_mor_eq;
          exact (!subst_is_compose _ Lβ _ _)
        ).
  Defined.

  Definition algebraic_theory_retracts_equiv_karoubi
    : adj_equiv (R (n := 0) L Lβ) algebraic_theory_karoubi.
  Proof.
    exists algebraic_theory_retracts_to_karoubi.
    apply rad_equivalence_of_cats'.
    - intros A B.
      refine '(isweq_iso _ _ _ _).
      + intro f.
        refine '(_ ,, _).
        * exact (abs ((f : karoubi_mor _ _ _) : _ ⟦_, _⟧)).
        * abstract (
            refine '(!maponpaths (λ x, x ∘ _ ∘ _) (functional_equation_eta Lβ (!R_ob_idempotent _ _)) @ _);
            refine '(maponpaths (λ x, x ∘ _) (compose_is_subst _ Lβ _ _) @ _);
            refine '(maponpaths (λ x, abs x ∘ _) (karoubi_mor_commutes_right _ f) @ _);
            refine '(!maponpaths (λ x, _ ∘ x) (functional_equation_eta Lβ (!R_ob_idempotent _ _)) @ _);
            refine '(compose_is_subst _ Lβ _ _ @ _);
            apply maponpaths;
            apply (karoubi_mor_commutes_left _ f)
          ).
      + abstract (
          intro f;
          apply R_mor_eq;
          exact (functional_equation_eta Lβ (!R_mor_is_mor _ _))
        ).
      + abstract (
          intro f;
          apply karoubi_mor_eq;
          apply Lβ
        ).
    - intro A.
      refine '((_ ,, _) ,, _).
      + exact (abs (karoubi_ob_idempotent _ A : _ ⟦_, _⟧)).
      + abstract (
          refine '(compose_is_subst _ Lβ _ _ @ _);
          apply maponpaths;
          exact (idempotent_is_idempotent (karoubi_ob_idempotent _ A))
        ).
      + refine '(make_z_iso _ _ _).
        * refine '(make_karoubi_mor _ _ _ _).
          -- exact (karoubi_ob_idempotent _ A : _ ⟦_, _⟧).
          -- abstract (
              refine '(_ @ idempotent_is_idempotent (karoubi_ob_idempotent _ A));
              apply (maponpaths (λ x, _ • x));
              apply funextfun;
              intro;
              apply Lβ
            ).
          -- abstract (exact (idempotent_is_idempotent (karoubi_ob_idempotent _ A))).
        * refine '(make_karoubi_mor _ _ _ _).
          -- exact (karoubi_ob_idempotent _ A : _ ⟦_, _⟧).
          -- abstract (exact (idempotent_is_idempotent (karoubi_ob_idempotent _ A))).
          -- abstract (
              refine '(_ @ idempotent_is_idempotent (karoubi_ob_idempotent _ A));
              apply (maponpaths (λ x, x • _));
              apply Lβ
            ).
        * abstract (
            refine '(make_is_inverse_in_precat _ _);
            apply karoubi_mor_eq;
            try (refine '(_ @ !Lβ _ _));
            exact (idempotent_is_idempotent (karoubi_ob_idempotent _ A))
          ).
  Defined.

End Karoubi.

(** * 2. The fully faithful functor from LL to K *)

Section Functors.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).

  Let φ
    : z_iso (E L Lβ) L
    := representation_theorem_iso L Lβ.

  Let Pn
    (n : nat)
    := bin_product_power
          (R (n := 0) L Lβ)
          (U L Lβ)
          (R_chosen_terminal L Lβ)
          (R_binproducts L Lβ)
          n.

  Definition algebraic_theory_lawvere_to_karoubi
    : (algebraic_theory_to_lawvere (L : algebraic_theory) : setcategory)
      ⟶ algebraic_theory_karoubi L.
  Proof.
    refine '(make_functor _ _).
    - refine '(make_functor_data _ _).
      + intro n.
        refine '(algebraic_theory_retracts_equiv_karoubi L Lβ _).
        exact (ProductObject _ _ (Pn n)).
      + intros m n f.
        apply (#(algebraic_theory_retracts_equiv_karoubi L Lβ)).
        apply ProductArrow.
        intro i.
        apply ((inv_from_z_iso φ : lambda_theory_morphism _ _) m).
        exact (f i).
    - split.
      + abstract (
          intro n;
          refine '(_ @ functor_id (algebraic_theory_retracts_equiv_karoubi _ _) _);
          apply (maponpaths (#(algebraic_theory_retracts_equiv_karoubi L Lβ)));
          refine '(!ProductArrowUnique _ _ _ _ _ _ _ _);
          intro i;
          refine '(id_left _ @ _);
          exact (!mor_var (inv_from_z_iso φ : lambda_theory_morphism _ _) i)
        ).
      + abstract (
          intros l m n f g;
          refine '(_ @ functor_comp (algebraic_theory_retracts_equiv_karoubi _ _) _ _);
          apply (maponpaths (#(algebraic_theory_retracts_equiv_karoubi L Lβ)));
          refine '(!ProductArrowUnique _ _ _ _ _ _ _ _);
          intro i;
          refine '(assoc' _ _ _ @ _);
          refine '(maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _);
          exact (!mor_subst (inv_from_z_iso φ : lambda_theory_morphism _ _) (g i) f)
        ).
  Defined.

  Lemma algebraic_theory_lawvere_to_karoubi_fully_faithful
    : fully_faithful algebraic_theory_lawvere_to_karoubi.
  Proof.
    intros m n.
    refine '(isweq_iso _ _ _ _).
    - intros f i.
      apply ((z_iso_mor φ : lambda_theory_morphism _ _) _).
      refine '(_ · ProductPr _ _ (Pn n) i).
      apply (weq_from_fully_faithful (fully_faithful_from_equivalence _ _ _
        (algebraic_theory_retracts_equiv_karoubi L Lβ))).
      exact f.
    - intro f.
      apply funextfun.
      intro i.
      refine '(_ @ maponpaths (λ (x : lambda_theory_morphism _ _), x _ _) (z_iso_after_z_iso_inv φ)).
      apply (maponpaths ((z_iso_mor φ : lambda_theory_morphism _ _) m)).
      refine '(maponpaths (λ x, x · _) (homotinvweqweq (weq_from_fully_faithful _ _ _) _) @ _).
      exact (ProductPrCommutes _ _ _ _ _ _ _).
    - intro f.
      refine '(_ @ homotweqinvweq (weq_from_fully_faithful (fully_faithful_from_equivalence _ _ _
        (algebraic_theory_retracts_equiv_karoubi L Lβ)) _ _) _).
      apply (maponpaths (# (algebraic_theory_retracts_equiv_karoubi L Lβ))).
      refine '(!ProductArrowUnique _ _ _ (Pn n) _ _ _ _).
      intro i.
      exact (!maponpaths (λ (x : lambda_theory_morphism _ _), x _ _) (z_iso_inv_after_z_iso φ)).
  Qed.

(** * 2.1. The isomorphism between the composed functor and the embedding from L1 to K *)

  Definition U_iso_algebraic_theory_to_unit
    : z_iso
      (algebraic_theory_retracts_to_karoubi L Lβ (U L Lβ))
      (karoubi_envelope_inclusion (algebraic_theory_monoid_category L) tt).
  Proof.
    refine '(make_z_iso _ _ _).
    - refine '(make_karoubi_mor _ _ _ _).
      + exact (karoubi_ob_idempotent _ (karoubi_envelope_inclusion (algebraic_theory_monoid_category L) tt)).
      + abstract (
          refine '(_ @ idempotent_is_idempotent _);
          apply (maponpaths (λ x, x · _));
          apply Lβ
        ).
      + abstract (apply idempotent_is_idempotent).
    - refine '(make_karoubi_mor _ _ _ _).
      + exact (karoubi_ob_idempotent _ (karoubi_envelope_inclusion (algebraic_theory_monoid_category L) tt)).
      + abstract (apply idempotent_is_idempotent).
      + abstract (
          refine '(_ @ idempotent_is_idempotent _);
          apply maponpaths;
          apply Lβ
        ).
    - refine '(make_is_inverse_in_precat _ _).
      + abstract (
          apply karoubi_mor_eq;
          refine '(_ @ !Lβ _ _);
          exact (var_subst _ _ _)
        ).
      + abstract (
          apply karoubi_mor_eq;
          exact (var_subst _ _ _)
        ).
  Defined.

  Definition algebraic_theory_lawvere_to_karoubi_after_theory_monoid_to_lawvere
    : z_iso
      (C := [_, _])
      (theory_monoid_to_lawvere L ∙ algebraic_theory_lawvere_to_karoubi)
      (karoubi_envelope_inclusion (algebraic_theory_monoid_category L)).
  Proof.
    pose (ψ := z_iso_comp
      (functor_on_z_iso (algebraic_theory_retracts_to_karoubi L Lβ) (make_z_iso' _
        (terminal_binprod_unit_l_z (R_chosen_terminal L Lβ) (R_binproducts _ _) (U L Lβ))))
      U_iso_algebraic_theory_to_unit).
    apply z_iso_is_nat_z_iso.
    refine '(make_nat_z_iso _ _ _ _).
    - refine '(make_nat_trans _ _ _ _).
      + intro t.
        exact ψ.
      + abstract (
          intros t1 t2 f;
          apply karoubi_mor_eq;
          refine '(_ @ maponpaths (λ x, x • _) (Lβ _ _));
          refine '(maponpaths (λ x, x • _) (var_subst _ _ _) @ _);
          refine '(subst_is_compose _ Lβ _ _ @ _);
          refine '(_ @ !maponpaths (λ x, _ • (λ _, x)) (var_subst _ _ _));
          refine '(_ @ !subst_is_compose _ Lβ (abs f) _);
          apply maponpaths;
          refine '(maponpaths (λ (x : R_mor _ _ _), (x : L 0)) (p2_commutes _ _ _ _ _ _ _) @ _);
          refine '(_ @ !abs_compose _ Lβ _ _);
          apply (maponpaths (λ x, abs (f • x)));
          apply funextfun;
          intro i;
          induction (!iscontr_uniqueness iscontrstn1 i);
          refine '(_ @ !maponpaths (λ x, app (inflate x) _) (abs_compose _ Lβ _ _));
          refine '(_ @ !maponpaths (λ x, app (inflate (abs x)) _) (var_subst _ _ _));
          refine '(!maponpaths (λ x, app x _) (inflate_n_π _ _) @ _);
          refine '(!maponpaths (λ x, app (inflate x) _) (functional_equation_eta Lβ (idpath π2)) @ _);
          exact (maponpaths (λ x, app (inflate (abs x)) _) (appx_to_app _))
        ).
    - intro t.
      induction t.
      exact (z_iso_is_z_isomorphism ψ).
  Defined.

End Functors.

(** * 3. The equivalence *)

Section Equivalence.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).
  Context (D : category).
  Context (HD : Colims D).

  Definition lawvere_theory_presheaf_equiv_monoid_presheaf
    : adj_equiv
      [(algebraic_theory_to_lawvere (L : algebraic_theory) : setcategory), D]
      [algebraic_theory_monoid_category L, D].
  Proof.
    refine '(_ ,, _).
    - exact (pre_comp_functor (theory_monoid_to_lawvere L)).
    - refine '(adjoint_equivalence_2_from_comp _ _ (algebraic_theory_lawvere_to_karoubi_fully_faithful L Lβ) _ HD _).
      apply (adj_equivalence_of_cats_closed_under_iso (pre_comp_functor_assoc _ _)).
      refine '(adj_equivalence_of_cats_closed_under_iso ((functor_on_z_iso
        (pre_comp_functor_functor _ _ _)
        (z_iso_inv (algebraic_theory_lawvere_to_karoubi_after_theory_monoid_to_lawvere _ _)))) _).
      exact (karoubi_pullback_equivalence _ _ HD).
  Defined.

End Equivalence.
