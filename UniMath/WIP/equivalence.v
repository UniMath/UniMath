Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryToLawvereTheory.
Require Import UniMath.AlgebraicTheories.CategoryOfRetracts.
Require Import UniMath.AlgebraicTheories.Combinators.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.CommonUtilities.KaroubiEnvelope.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.OriginalRepresentationTheorem.
Require Import UniMath.CategoryTheory.Categories.MonoidToCategory.
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

Section T1.

  Context (T : algebraic_theory).

  Definition T1_setwithbinop
    : setwithbinop.
  Proof.
    refine '(make_setwithbinop _ _).
    - exact (T 1).
    - intros f g.
      exact (f • (λ _, g)).
  Defined.

  Definition T1_unit
    : T1_setwithbinop
    := var (● 0 : stn 1).

  Lemma T1_isunit
    : isunit op T1_unit.
  Proof.
    apply make_isunit.
    - intro f.
      apply var_subst.
    - intro f.
      refine '(_ @ subst_var _ f).
      apply (maponpaths (λ x, f • x)).
      apply funextfun.
      intro.
      apply maponpaths.
      exact (!iscontr_uniqueness iscontrstn1 x).
  Qed.

  Definition T1_monoid
    : monoid.
  Proof.
    refine '(make_monoid _ _).
    - exact T1_setwithbinop.
    - apply make_ismonoidop.
      + abstract (exact (λ f g h, subst_subst _ f _ _)).
      + refine '(make_isunital _ _).
        * exact T1_unit.
        * exact T1_isunit.
  Defined.

  Definition T1
    : setcategory
    := monoid_to_category T1_monoid.

  Definition TT
    : setcategory
    := algebraic_theory_to_lawvere T.

  Definition T1bar
    : setcategory
    := set_karoubi_envelope T1.

  Definition i1
    : T1 ⟶ TT.
  Proof.
    refine '(make_functor _ _).
    - refine '(make_functor_data _ _).
      + intro.
        exact 1.
      + intros ? ? f.
        exact (λ _, f).
    - split.
      + intro.
        apply funextfun.
        intro t.
        apply (maponpaths var).
        apply proofirrelevancecontr.
        apply iscontrstn1.
      + intros ? ? ? f g.
        reflexivity.
  Defined.

  Lemma i1_fully_faithful
    : fully_faithful i1.
  Proof.
    intros ? ?.
    refine '(isweq_iso _ _ _ _).
    - intro f.
      exact (f (● 0)).
    - intro f.
      reflexivity.
    - intro f.
      apply funextfun.
      intro.
      apply (maponpaths f).
      apply proofirrelevancecontr.
      apply iscontrstn1.
  Qed.

End T1.

Section RL1bar.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).

  Lemma subst_is_compose
    (A B : L 0)
    : appx A • (λ _, appx B) = appx (A ∘ B).
  Proof.
    refine '(maponpaths (λ x, x • _) (appx_to_app _) @ _).
    refine '(maponpaths (λ x, _ • (λ _, x)) (appx_to_app _) @ _).
    refine '(subst_app _ _ _ _ @ _).
    refine '(maponpaths (λ x, (app x _)) (subst_inflate _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (var_subst _ _ _) @ !_).
    refine '(appx_to_app _ @ _).
    refine '(maponpaths (λ x, (app x _)) (inflate_compose _ _ _) @ _).
    refine '(app_compose _ Lβ _ _ _ @ _).
    apply (maponpaths (λ x, app (A • x) _)).
    apply funextfun.
    intro i.
    apply fromempty.
    apply (negstn0 i).
  Qed.

  Lemma compose_is_subst
    (A B : L 1)
    : abs A ∘ abs B = abs (A • (λ _, B)).
  Proof.
    refine '(_ @ maponpaths (λ x, abs (x • _)) (Lβ _ _)).
    refine '(_ @ maponpaths (λ x, abs (_ • (λ _, x))) (Lβ _ _)).
    refine '(_ @ !maponpaths _ (subst_is_compose _ _)).
    exact (maponpaths _ (!Lβ _ _)).
  Qed.

  Definition R_to_L1bar
    : R (n := 0) L Lβ ⟶ T1bar L.
  Proof.
    refine '(make_functor _ _).
    - refine '(make_functor_data _ _).
      + intro A.
        refine '(make_karoubi_ob _ _ _ _).
        * exact tt.
        * exact (appx (A : R_ob L)).
        * abstract (
            refine '(subst_is_compose _ _ @ _);
            apply maponpaths;
            apply R_ob_idempotent
          ).
      + intros A B f.
        refine '(make_karoubi_mor _ _ _ _).
        * exact (appx (f : R_mor _ _ _)).
        * abstract (
            refine '(subst_is_compose _ _ @ _);
            apply maponpaths;
            apply (R_mor_is_mor_right _ Lβ)
          ).
        * abstract (
            refine '(subst_is_compose _ _ @ _);
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
          exact (!subst_is_compose _ _)
        ).
  Defined.

  Lemma functional_equation_eta
    {x : L 0}
    {y : L 1}
    (Hx : x = abs y)
    : abs (appx x) = x.
  Proof.
    refine '(_ @ !Hx).
    refine '(_ @ maponpaths abs (Lβ _ _)).
    do 2 (apply maponpaths).
    exact Hx.
  Qed.

  Definition R_equiv_L1bar
    : adj_equiv (R (n := 0) L Lβ) (T1bar L).
  Proof.
    exists R_to_L1bar.
    apply rad_equivalence_of_cats'.
    - intros A B.
      refine '(isweq_iso _ _ _ _).
      + intro f.
        refine '(_ ,, _).
        * exact (abs ((f : karoubi_mor _ _ _) : T1 L ⟦_, _⟧)).
        * abstract (
            refine '(!maponpaths (λ x, x ∘ _ ∘ _) (functional_equation_eta (!R_ob_idempotent _ _)) @ _);
            refine '(maponpaths (λ x, x ∘ _) (compose_is_subst _ _) @ _);
            refine '(maponpaths (λ x, abs x ∘ _) (karoubi_mor_commutes_right _ f) @ _);
            refine '(!maponpaths (λ x, _ ∘ x) (functional_equation_eta (!R_ob_idempotent _ _)) @ _);
            refine '(compose_is_subst _ _ @ _);
            apply maponpaths;
            apply (karoubi_mor_commutes_left _ f)
          ).
      + abstract (
          intro f;
          apply R_mor_eq;
          exact (functional_equation_eta (!R_mor_is_mor _ _))
        ).
      + abstract (
          intro f;
          apply karoubi_mor_eq;
          apply Lβ
        ).
    - intro A.
      refine '((_ ,, _) ,, _).
      + exact (abs (karoubi_ob_idempotent _ A : T1 L ⟦_, _⟧)).
      + abstract (
          refine '(compose_is_subst _ _ @ _);
          apply maponpaths;
          exact (idempotent_is_idempotent (karoubi_ob_idempotent _ A))
        ).
      + refine '(make_z_iso _ _ _).
        * refine '(make_karoubi_mor _ _ _ _).
          -- exact (karoubi_ob_idempotent _ A : T1 L ⟦_, _⟧).
          -- abstract (
              refine '(_ @ idempotent_is_idempotent (karoubi_ob_idempotent _ A));
              apply (maponpaths (λ x, _ • x));
              apply funextfun;
              intro;
              apply Lβ
            ).
          -- abstract (exact (idempotent_is_idempotent (karoubi_ob_idempotent _ A))).
        * refine '(make_karoubi_mor _ _ _ _).
          -- exact (karoubi_ob_idempotent _ A : T1 L ⟦_, _⟧).
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

End RL1bar.

Section L1.

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

  Definition i2
    : TT L ⟶ T1bar L.
  Proof.
    refine '(make_functor _ _).
    - refine '(make_functor_data _ _).
      + intro n.
        refine '(R_equiv_L1bar L Lβ _).
        exact (ProductObject _ _ (Pn n)).
      + intros m n f.
        apply (#(R_equiv_L1bar L Lβ)).
        apply ProductArrow.
        intro i.
        apply ((inv_from_z_iso φ : lambda_theory_morphism _ _) m).
        exact (f i).
    - split.
      + abstract (
          intro n;
          refine '(_ @ functor_id (R_equiv_L1bar _ _) _);
          apply (maponpaths (#(R_equiv_L1bar L Lβ)));
          refine '(!ProductArrowUnique _ _ _ _ _ _ _ _);
          intro i;
          refine '(id_left _ @ _);
          exact (!mor_var (inv_from_z_iso φ : lambda_theory_morphism _ _) i)
        ).
      + abstract (
          intros l m n f g;
          refine '(_ @ functor_comp (R_equiv_L1bar _ _) _ _);
          apply (maponpaths (#(R_equiv_L1bar L Lβ)));
          refine '(!ProductArrowUnique _ _ _ _ _ _ _ _);
          intro i;
          refine '(assoc' _ _ _ @ _);
          refine '(maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _);
          exact (!mor_subst (inv_from_z_iso φ : lambda_theory_morphism _ _) (g i) f)
        ).
  Defined.

  Lemma i2_fully_faithful
    : fully_faithful i2.
  Proof.
    intros m n.
    refine '(isweq_iso _ _ _ _).
    - intros f i.
      apply ((z_iso_mor φ : lambda_theory_morphism _ _) _).
      refine '(_ · ProductPr _ _ (Pn n) i).
      apply (weq_from_fully_faithful (fully_faithful_from_equivalence _ _ _ (R_equiv_L1bar L Lβ))).
      exact f.
    - intro f.
      apply funextfun.
      intro i.
      refine '(_ @ maponpaths (λ (x : lambda_theory_morphism _ _), x _ _) (z_iso_after_z_iso_inv φ)).
      apply (maponpaths ((z_iso_mor φ : lambda_theory_morphism _ _) m)).
      refine '(maponpaths (λ x, x · _) (homotinvweqweq (weq_from_fully_faithful _ _ _) _) @ _).
      exact (ProductPrCommutes _ _ _ _ _ _ _).
    - intro f.
      refine '(_ @ homotweqinvweq (weq_from_fully_faithful (fully_faithful_from_equivalence _ _ _ (R_equiv_L1bar L Lβ)) _ _) _).
      apply (maponpaths (# (R_equiv_L1bar L Lβ))).
      refine '(!ProductArrowUnique _ _ _ (Pn n) _ _ _ _).
      intro i.
      exact (!maponpaths (λ (x : lambda_theory_morphism _ _), x _ _) (z_iso_inv_after_z_iso φ)).
  Qed.

  Definition U_iso_T1_unit
    : z_iso (R_to_L1bar L Lβ (U L Lβ)) (karoubi_envelope_inclusion (T1 L) tt).
  Proof.
    refine '(make_z_iso _ _ _).
    - refine '(make_karoubi_mor _ _ _ _).
      + exact (karoubi_ob_idempotent _ (karoubi_envelope_inclusion (T1 L) tt)).
      + abstract (
          refine '(_ @ idempotent_is_idempotent _);
          apply (maponpaths (λ x, x · _));
          apply Lβ
        ).
      + abstract (apply idempotent_is_idempotent).
    - refine '(make_karoubi_mor _ _ _ _).
      + exact (karoubi_ob_idempotent _ (karoubi_envelope_inclusion (T1 L) tt)).
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

  Definition i2_after_i1
    : z_iso (C := [_, _]) (i1 L ∙ i2) (karoubi_envelope_inclusion (T1 L)).
  Proof.
    pose (ψ := z_iso_comp
      (functor_on_z_iso (R_to_L1bar L Lβ) (make_z_iso' _
        (terminal_binprod_unit_l_z (R_chosen_terminal L Lβ) (R_binproducts _ _) (U L Lβ))))
      U_iso_T1_unit).
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
          refine '(!maponpaths (λ x, app (inflate x) _) (functional_equation_eta _ Lβ (idpath π2)) @ _);
          exact (maponpaths (λ x, app (inflate (abs x)) _) (appx_to_app _))
        ).
    - intro t.
      induction t.
      exact (z_iso_is_z_isomorphism ψ).
  Defined.

End L1.

Section Equivalence.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).
  Context (D : category).
  Context (HD : Colims D).

  Definition equivalence
    : adj_equiv [TT L, D] [T1 L, D].
  Proof.
    refine '(_ ,, _).
    - exact (pre_comp_functor (i1 L)).
    - refine '(adjoint_equivalence_2_from_comp _ _ (i2_fully_faithful L Lβ) _ HD _).
      apply (adj_equivalence_of_cats_closed_under_iso (pre_comp_functor_assoc _ _)).
      apply (adj_equivalence_of_cats_closed_under_iso ((functor_on_z_iso (pre_comp_functor_functor _ _ _) (z_iso_inv (i2_after_i1 _ _))))).
      exact (karoubi_pullback_equivalence _ _ HD).
  Defined.

End Equivalence.
