Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.Combinators.

Require Import Ltac2.Ltac2.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Section Category.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).

  Context {n : nat}.

  Definition R_ob : UU := ∑ (l : L n), l ∘ l = l.
  Coercion R_ob_to_L (A : R_ob) : L n := pr1 A.
  Definition R_ob_idempotent (A : R_ob) : A ∘ A = A := pr2 A.

  Definition R_mor (A B : R_ob) : UU := ∑ (f : L n), B ∘ f ∘ A = f.
  Coercion R_mor_to_L {A B : R_ob} (f : R_mor A B) : L n := pr1 f.
  Definition R_mor_is_mor {A B : R_ob} (f : R_mor A B) : B ∘ f ∘ A = f := pr2 f.

  Lemma R_mor_is_mor_left
    {A B : R_ob}
    (f : R_mor A B)
    : B ∘ f = f.
  Proof.
    refine '(!maponpaths _ (R_mor_is_mor _) @ _).
    refine '(compose_assoc _ Lβ _ _ _ @ _).
    refine '(maponpaths (λ x, x ∘ _) (compose_assoc _ Lβ _ _ _) @ _).
    refine '(maponpaths (λ x, x ∘ _ ∘ _) (R_ob_idempotent _) @ _).
    apply R_mor_is_mor.
  Qed.

  Lemma R_mor_is_mor_right
    {A B : R_ob}
    (f : R_mor A B)
    : f ∘ A = f.
  Proof.
    refine '(!maponpaths (λ x, x ∘ _) (R_mor_is_mor _) @ _).
    refine '(!compose_assoc _ Lβ _ _ _ @ _).
    refine '(maponpaths _ (R_ob_idempotent _) @ _).
    apply R_mor_is_mor.
  Qed.

  Lemma R_mor_eq
    {A B : R_ob}
    (f g : R_mor A B)
    (H : pr1 f = pr1 g)
    : f = g.
  Proof.
    apply subtypePath.
    - intro.
      apply setproperty.
    - apply H.
  Qed.

  Definition R : category.
  Proof.
    refine '(make_category _ _).
    - refine '(make_precategory _ _).
      + refine '(make_precategory_data _ _ _).
        * refine '(make_precategory_ob_mor _ _).
          -- exact R_ob.
          -- exact R_mor.
        * refine '(λ (A : R_ob), _).
          exists A.
          abstract (exact (maponpaths (λ x, x ∘ _) (R_ob_idempotent A) @ R_ob_idempotent A)).
        * refine '(λ (A B C : R_ob) (f g : R_mor _ _), _).
          exists (g ∘ f).
          abstract (
            refine '(maponpaths (λ x, x ∘ _) (compose_assoc _ Lβ _ _ _) @ _);
            refine '(!compose_assoc _ Lβ _ _ _ @ _);
            refine '(maponpaths (λ x, x ∘ _) _ @ maponpaths _ _) >
            [ apply R_mor_is_mor_left
            | apply R_mor_is_mor_right ]
          ).
      + abstract (
          apply make_is_precategory_one_assoc >
          [ intros A B f;
            apply R_mor_eq;
            apply R_mor_is_mor_right
          | intros A B f;
            apply R_mor_eq;
            apply R_mor_is_mor_left
          | intros A B C D f g h;
            apply R_mor_eq;
            symmetry;
            exact (compose_assoc _ Lβ _ _ _) ]
        ).
    - abstract (
        intros A B;
        apply isaset_total2 >
        [ apply setproperty
        | intro t;
          apply isasetaprop;
          apply setproperty ]
      ).
  Defined.

  Section Terminal.

    Definition terminal_term
      : L n
      := abs (abs (var (stnweq (inr tt)))).

    Definition terminal_compose
      (t : L n)
      : terminal_term ∘ t = terminal_term.
    Proof.
      refine '(maponpaths (λ x, (abs (app x _))) (inflate_abs _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (subst_subst _ _ _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (subst_abs _ _ _) @ _).
      refine '(maponpaths (λ x, (abs (abs x))) (var_subst _ _ _) @ _).
      exact (maponpaths (λ x, (abs (abs x))) (extend_tuple_inr _ _ _)).
    Qed.

    Definition terminal
      : R_ob
      := terminal_term ,, terminal_compose _.

    Section Arrow.

      Context (A : R_ob).

      Definition terminal_arrow_term
        : L n
        := terminal_term.

      Lemma terminal_arrow_is_mor
        : terminal ∘ terminal_arrow_term ∘ A = terminal_arrow_term.
      Proof.
        refine '(!compose_assoc _ Lβ _ _ _ @ _).
        apply terminal_compose.
      Qed.

      Definition terminal_arrow
        : R_mor A terminal
        := terminal_arrow_term ,, terminal_arrow_is_mor.

      Lemma terminal_arrow_unique
        (t : R_mor A terminal)
        : t = terminal_arrow.
      Proof.
        apply R_mor_eq.
        refine '(!R_mor_is_mor t @ _).
        refine '(!compose_assoc _ Lβ _ _ _ @ _).
        apply terminal_compose.
      Qed.

    End Arrow.

    Definition R_terminal
      : Terminal R.
    Proof.
      refine '(make_Terminal _ _).
      - exact terminal.
      - refine '(make_isTerminal _ _).
        intro A.
        refine '(make_iscontr _ _).
        + exact (terminal_arrow A).
        + apply terminal_arrow_unique.
    Defined.

  End Terminal.

  Section BinProducts.

    Context (A B : R_ob).

    Definition prod_term
      : L n
      := pair_arrow
        (A ∘ π1)
        (B ∘ π2).

    Lemma prod_idempotent
      : prod_term ∘ prod_term = prod_term.
    Proof.
      refine '(pair_arrow_compose _ Lβ _ _ _ @ _).
      refine '(maponpaths (λ x, pair_arrow x _) (!compose_assoc _ Lβ _ _ _) @ _).
      refine '(maponpaths (λ x, pair_arrow _ x) (!compose_assoc _ Lβ _ _ _) @ _).
      refine '(maponpaths (λ x, (pair_arrow (_ ∘ x) _)) ( π1_pair_arrow _ Lβ _ _) @ _).
      refine '(maponpaths (λ x, (pair_arrow _ (_ ∘ x))) ( π2_pair_arrow _ Lβ _ _) @ _).
      refine '(maponpaths (λ x, pair_arrow x _) (compose_assoc _ Lβ _ _ _) @ _).
      refine '(maponpaths (λ x, pair_arrow _ x) (compose_assoc _ Lβ _ _ _) @ _).
      refine '(maponpaths (λ x, pair_arrow (x ∘ _) _) (R_ob_idempotent A) @ _).
      exact (maponpaths (λ x, pair_arrow _ (x ∘ _)) (R_ob_idempotent B)).
    Qed.

    Definition prod
      : R_ob
      := prod_term ,, prod_idempotent.

    Definition p1_term
      : L n
      := A ∘ π1.

    Lemma p1_is_mor
      : A ∘ p1_term ∘ prod = p1_term.
    Proof.
      refine '(maponpaths (λ x, x ∘ _) (compose_assoc _ Lβ _ _ _) @ _).
      refine '(maponpaths (λ x, x ∘ _ ∘ _) (R_ob_idempotent _) @ _).
      refine '(!compose_assoc _ Lβ _ _ _ @ _).
      refine '(maponpaths _ ( π1_pair_arrow _ Lβ _ _ : _ = _ ∘ _) @ _).
      refine '(compose_assoc _ Lβ _ _ _ @ _).
      exact (maponpaths (λ x, x ∘ _) (R_ob_idempotent _)).
    Qed.

    Definition p1
      : R_mor prod A
      := p1_term ,, p1_is_mor.

    Definition p2_term
      : L n
      := B ∘ π2.

    Lemma p2_is_mor
      : B ∘ p2_term ∘ prod = p2_term.
    Proof.
      refine '(maponpaths (λ x, x ∘ _) (compose_assoc _ Lβ _ _ _) @ _).
      refine '(maponpaths (λ x, x ∘ _ ∘ _) (R_ob_idempotent _) @ _).
      refine '(!compose_assoc _ Lβ _ _ _ @ _).
      refine '(maponpaths _ ( π2_pair_arrow _ Lβ _ _ : _ = _ ∘ _) @ _).
      refine '(compose_assoc _ Lβ _ _ _ @ _).
      exact (maponpaths (λ x, x ∘ _) (R_ob_idempotent _)).
    Qed.

    Definition p2
      : R_mor prod B
      := p2_term ,, p2_is_mor.

    Section Arrow.

      Context (C : R_ob).
      Context (f : R_mor C A).
      Context (g : R_mor C B).

      Definition prod_arrow_term
        : L n
        := pair_arrow f g.

      Lemma prod_arrow_is_mor
        : prod ∘ prod_arrow_term ∘ C = prod_arrow_term.
      Proof.
        refine '(maponpaths (λ x, x ∘ _) (pair_arrow_compose _ Lβ _ _ _) @ _).
        refine '(maponpaths (λ x, pair_arrow x _ ∘ _) (!compose_assoc _ Lβ _ _ _) @ _).
        refine '(maponpaths (λ x, pair_arrow _ x ∘ _) (!compose_assoc _ Lβ _ _ _) @ _).
        refine '(maponpaths (λ x, pair_arrow (_ ∘ (_ ∘ pair_arrow x _)) _ ∘ _) (!R_mor_is_mor_left _) @ _).
        refine '(maponpaths (λ x, pair_arrow _ (_ ∘ (_ ∘ pair_arrow _ x)) ∘ _) (!R_mor_is_mor_left _) @ _).
        refine '(maponpaths (λ x, pair_arrow (_ ∘ x) _ ∘ _) ( π1_pair_arrow _ Lβ _ _ : _ = _ ∘ _) @ _).
        refine '(maponpaths (λ x, pair_arrow _ (_ ∘ x) ∘ _) ( π2_pair_arrow _ Lβ _ _ : _ = _ ∘ _) @ _).
        refine '(maponpaths (λ x, pair_arrow (_ ∘ x) _ ∘ _) (R_mor_is_mor_left _) @ _).
        refine '(maponpaths (λ x, pair_arrow x _ ∘ _) (R_mor_is_mor_left _) @ _).
        refine '(maponpaths (λ x, pair_arrow _ (_ ∘ x) ∘ _) (R_mor_is_mor_left _) @ _).
        refine '(maponpaths (λ x, pair_arrow _ x ∘ _) (R_mor_is_mor_left _) @ _).
        refine '(pair_arrow_compose _ Lβ _ _ _ @ _).
        refine '(maponpaths (λ x, pair_arrow x _) (R_mor_is_mor_right _) @ _).
        exact (maponpaths (λ x, pair_arrow _ x) (R_mor_is_mor_right _)).
      Qed.

      Definition prod_arrow
        : R_mor C prod
        := prod_arrow_term ,, prod_arrow_is_mor.

      From Ltac2 Require Import Pattern.

      Definition p1_commutes
        : (prod_arrow : R⟦_, _⟧) · p1 = f.
      Proof.
        apply R_mor_eq.
        refine '(maponpaths (λ x, _ ∘ pair_arrow x _) (!R_mor_is_mor_left _) @ _).
        refine '(!compose_assoc _ Lβ _ _ _ @ _).
        refine '(maponpaths (λ x, _ ∘ x) ( π1_pair_arrow _ Lβ _ _ : _ = _ ∘ _) @ _).
        refine '(maponpaths (λ x, _ ∘ x) (R_mor_is_mor_left _) @ _).
        exact (R_mor_is_mor_left _).
      Qed.

      Definition p2_commutes
        : (prod_arrow : R⟦_, _⟧) · p2 = g.
      Proof.
        apply R_mor_eq.
        refine '(maponpaths (λ x, _ ∘ pair_arrow _ x) (!R_mor_is_mor_left _) @ _).
        refine '(!compose_assoc _ Lβ _ _ _ @ _).
        refine '(maponpaths (λ x, _ ∘ x) ( π2_pair_arrow _ Lβ _ _ : _ = _ ∘ _) @ _).
        refine '(maponpaths (λ x, _ ∘ x) (R_mor_is_mor_left _) @ _).
        exact (R_mor_is_mor_left _).
      Qed.

      Lemma prod_arrow_unique
        (a': R ⟦ C, prod ⟧)
        (Ha': a' · p1 = f × a' · p2 = g)
        : a' = prod_arrow.
      Proof.
        apply R_mor_eq.
        refine '(!R_mor_is_mor_left a' @ _).
        refine '(pair_arrow_compose _ Lβ _ _ _ @ _).
        refine '(_ @ maponpaths (λ x, pair_arrow (R_mor_to_L x) _) (pr1 Ha')).
        exact (maponpaths (λ x, pair_arrow _ (R_mor_to_L x)) (pr2 Ha')).
      Qed.

    End Arrow.

    Definition R_binproduct
      : BinProduct R A B.
    Proof.
      refine '(make_BinProduct _ _ _ _ _ _ _).
      - exact prod.
      - exact p1.
      - exact p2.
      - refine '(make_isBinProduct _ _ _ _ _ _ _).
        intros C f g.
        refine '(unique_exists _ _ _ _).
        + exact (prod_arrow C f g).
        + split.
          * apply p1_commutes.
          * apply p2_commutes.
        + intro a.
          apply isapropdirprod;
            apply homset_property.
        + apply prod_arrow_unique.
    Defined.

  End BinProducts.

  Definition R_binproducts
    : BinProducts R.
  Proof.
    intros A B.
    apply R_binproduct.
  Defined.

  Section Exponentials.

    Section Object.

      Context (B C : R_ob).

      Definition exponential_term
        : L n
        := curry (ev C B).

      Lemma exponential_idempotent
        : exponential_term ∘ exponential_term = exponential_term.
      Proof.
        refine '(curry_compose _ Lβ _ _ @ _).
        refine '(maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_ev _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (inflate (abs (app (inflate x) _)))⟩))))) (inflate_ev _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app x _)))) (inflate_ev _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (inflate (abs (app x _)))⟩))))) (inflate_ev _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs x))) (app_ev _ Lβ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app (app _ (⟨_, (inflate (abs x))⟩)) _))))) ( app_ev _ Lβ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app x _))))) ( π2_pair _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ x)))))) ( π1_pair _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app x _))))) (inflate_abs _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ x)))) (beta_equality _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ x)))) (subst_subst _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ x)))) (subst_app _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app x _))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ x))))) (subst_app _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app x _))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) (subst_app _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ x)))))) (subst_app _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app (app x _) _)))))) (subst_π2 _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app (app _ x) _)))))) (subst_pair _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app x _))))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (subst_app _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) ( π2_pair _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app x _))))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ (app x _)))))))) (subst_π1 _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ (app _ x)))))))) (subst_pair _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) ( π1_pair _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app (x • _) _)))))) (extend_tuple_inl _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ (x • _)))))))) (extend_tuple_inr _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) (extend_tuple_inl _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (extend_tuple_inr _ _ _) @ _).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_ev _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app x _)))) (inflate_ev _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs x))) (app_ev _ Lβ _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app x _))))) ( π2_pair _ Lβ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ x)))))) ( π1_pair _ Lβ _ _)).
        refine '(_ @ maponpaths (λ x, (abs (abs (app (inflate (inflate x)) _)))) (R_ob_idempotent C)).
        refine '(_ @ maponpaths (λ x, (abs (abs (app _ (app _ (app (inflate (inflate x)) _)))))) (R_ob_idempotent B)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_compose _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app (inflate x) _)))))) (inflate_compose _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app x _)))) (inflate_compose _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) (inflate_compose _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs x))) (app_compose _ Lβ _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ x)))))) (app_compose _ Lβ _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app x _))))) (subst_subst _ _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app x _))))))) (subst_subst _ _ _ _)).
        refine '(
          maponpaths (λ x, (abs (abs (app _ (app (_ • x) _))))) _ @
          maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app (_ • x) _))))))) _
        );
          apply funextfun;
          intro i;
          refine '(maponpaths (λ x, x • _) (extend_tuple_inl _ _ _) @ _);
          refine '(var_subst _ _ _ @ _);
          refine '(extend_tuple_inl _ _ _ @ _);
          exact (!var_subst _ (stnweq (inl i)) _).
      Qed.

      Definition exponential_ob
        : R_ob
        := exponential_term ,, exponential_idempotent.

      Definition eval_term
        : L n
        := ev C B.

      Lemma eval_is_mor
        : C ∘ eval_term ∘ prod B exponential_ob = eval_term.
      Proof.
        refine '(!compose_assoc _ Lβ _ _ _ @ _).
        refine '(maponpaths (λ x, (_ ∘ x)) (ev_compose_pair_arrow _ Lβ _ _ _ _) @ _).
        refine '(compose_abs _ Lβ _ _ @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app (app x _) _))))) (inflate_compose _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app _ (app x _))))))) (inflate_compose _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app (app (x ∘ _) _) _))))) (inflate_curry _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app (app (_ ∘ x) _) _))))) (inflate_π2 _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app _ (app (_ ∘ x) _))))))) (inflate_π1 _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app (app ((curry x) ∘ _) _) _))))) (inflate_ev _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app (app x _) _))))) (curry_compose _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (beta_equality _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (subst_abs _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (beta_equality _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (subst_subst _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (subst_app _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ x))))) (subst_pair _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨x, _⟩)))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, x⟩)))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (subst_ev _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨(x • _), _⟩)))))) (extend_tuple_inr _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, x⟩)))))) (subst_app _ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app (ev x _) _))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app (ev _ x) _))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨x, _⟩)))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app x _)⟩)))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app _ x)⟩)))))) (subst_abs _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨x, _⟩)))))) (extend_tuple_inr _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app (x • _) _)⟩)))))) (extend_tuple_inl _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app _ (abs x))⟩)))))) (subst_abs _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app x _)⟩)))))) (subst_inflate _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app _ (abs (abs x)))⟩)))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app (x • _) _)⟩)))))) (extend_tuple_inr _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app _ (abs (abs x)))⟩)))))) (extend_tuple_inr _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app x _)⟩)))))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (⟨_, (app x _)⟩)))))) (extend_tuple_inl _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (app_ev _ Lβ _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app x _)))))) ( π2_pair _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app _ (app _ x))))))) ( π1_pair _ Lβ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app _ (app _ (app _ x)))))))) (app_compose _ Lβ _ _ _) @ _).
        refine '(_ @ maponpaths (λ x, (abs (app (inflate x) _))) (R_ob_idempotent _)).
        refine '(_ @ maponpaths (λ x, (abs (app (inflate (x ∘ _)) _))) (R_ob_idempotent _)).
        refine '(_ @ maponpaths (λ x, (abs (app _ (app _ (app (inflate x) _))))) (R_ob_idempotent _)).
        refine '(_ @ maponpaths (λ x, (abs (app _ (app _ (app (inflate (x ∘ _)) _))))) (R_ob_idempotent _)).
        refine '(_ @ !maponpaths (λ x, (abs (app x _))) (inflate_compose _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app x _))))) (inflate_compose _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app (x ∘ _) _))) (inflate_compose _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app (x ∘ _) _))))) (inflate_compose _ _ _)).
        do 2 (refine '(_ @ !maponpaths (λ x, (abs x)) (app_compose _ Lβ _ _ _))).
        do 2 (refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app _ x)))))) (app_compose _ Lβ _ _ _))).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app x _)))))) (beta_equality _ Lβ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app x _)))))) (subst_app _ _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app (app x _) _)))))) (var_subst _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app (app _ x) _)))))) (subst_abs _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app (app x _) _)))))) (extend_tuple_inr _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app (app _ (abs x)) _)))))) (subst_abs _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app (app _ (abs (abs x))) _)))))) (var_subst _ _ _)).
        refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app (app _ (abs (abs x))) _)))))) (extend_tuple_inr _ _ _)).
        refine '(
          maponpaths (λ x, (abs (app _ (app _ (app (_ • x) _))))) _ @
          maponpaths (λ x, (abs (app _ (app _ (app _ (app _ (app (_ • x) _))))))) _
        );
          apply funextfun;
          intro i;
          refine '(maponpaths (λ x, x • _) (extend_tuple_inl _ _ _) @ _);
          refine '(maponpaths (λ x, ((inflate x) • _)) (extend_tuple_inl _ _ _) @ _);
          refine '(subst_inflate _ _ _ @ _);
          refine '(var_subst _ _ _ @ _);
          exact (extend_tuple_inl _ _ _).
      Qed.

      Definition eval_mor
        : R_mor (prod B exponential_ob) C
        := eval_term ,, eval_is_mor.

      Section Lambda.

        Context (A : R_ob).
        Context (h : R_mor (prod B A) C).

        Definition lifted_term
          : L n
          := curry h.

        Lemma lifted_is_mor
          : exponential_ob ∘ lifted_term ∘ A = lifted_term.
        Proof.
          refine '(maponpaths (λ x, (x ∘ _)) (curry_compose _ Lβ _ _) @ _).
          refine '(abs_compose _ Lβ _ _ @ _).
          refine '(maponpaths (λ x, (abs x)) (subst_abs _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs x))) (subst_app _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_inflate _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ x)))) (subst_pair _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_inflate _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (var_subst _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (subst_inflate _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app x _)))) (subst_ev _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨x, _⟩))))) (extend_tuple_inr _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (subst_abs _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs x)⟩))))) (subst_app _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app x _))⟩))))) (subst_inflate _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ x))⟩))))) (subst_pair _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app x _))⟩))))) (subst_inflate _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨x, _⟩)))⟩))))) (var_subst _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨_, x⟩)))⟩))))) (var_subst _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨x, _⟩)))⟩))))) (extend_tuple_inr _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨_, x⟩)))⟩))))) (extend_tuple_inl _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨_, (inflate x)⟩)))⟩))))) (extend_tuple_inl _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨_, (inflate (inflate x))⟩)))⟩))))) (extend_tuple_inr _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨_, (inflate x)⟩)))⟩))))) (inflate_app _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨_, x⟩)))⟩))))) (inflate_app _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨_, (app _ (inflate x))⟩)))⟩))))) (inflate_var _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (abs (app _ (⟨_, (app _ x)⟩)))⟩))))) (inflate_var _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs x))) (app_ev_pair _ Lβ _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ x)))) (beta_equality _ Lβ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ x)))) (subst_app _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app x _))))) (subst_subst _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ x))))) (subst_pair _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (⟨x, _⟩)))))) (var_subst _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, x⟩)))))) (subst_app _ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (⟨x, _⟩)))))) (extend_tuple_inr _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, (app x _)⟩)))))) (subst_inflate _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, (app _ x)⟩)))))) (var_subst _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, (app x _)⟩)))))) (subst_inflate _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, (app _ x)⟩)))))) (extend_tuple_inl _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, (app x _)⟩)))))) (subst_inflate _ _ _) @ _).
          refine '(_ @ maponpaths (λ x, abs (abs (app (inflate (inflate x)) _))) (R_mor_is_mor h)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app x _)))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app ((inflate x) ∘ _) _)))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app (x ∘ _) _)))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, abs (abs x)) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (inflate x) _))))) (inflate_pair_arrow _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app x _))))) (inflate_pair_arrow _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (pair_arrow (inflate x) _) _))))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (pair_arrow _ (inflate x)) _))))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (pair_arrow x _) _))))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (pair_arrow _ x) _))))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (pair_arrow (_ ∘ (inflate x)) _) _))))) (inflate_π1 _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (pair_arrow _ (_ ∘ (inflate x))) _))))) (inflate_π2 _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (pair_arrow (_ ∘ x) _) _))))) (inflate_π1 _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (pair_arrow _ (_ ∘ x)) _))))) (inflate_π2 _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ x)))) (app_pair_arrow _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs x))) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (⟨x, _⟩)))))) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, x⟩)))))) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (⟨(app _ x), _⟩)))))) ( π1_pair _ Lβ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, (app _ x)⟩)))))) ( π2_pair _ Lβ _ _)).
          refine '(
            maponpaths (λ x, (abs (abs (app x _)))) _ @
            maponpaths (λ x, (abs (abs (app _ (app x _))))) _ @
            maponpaths (λ x, (abs (abs (app _ (app _ (⟨(app x _), _⟩)))))) _ @
            maponpaths (λ x, (abs (abs (app _ (app _ (⟨_, (app x _)⟩)))))) _
          );
            refine '(_ @ !(subst_subst _ _ _ _ : inflate (inflate _) = _));
            refine '(maponpaths (λ x, _ • x) _);
            apply funextfun;
            intro i;
            refine '(_ @ !inflate_var _ _).
          - refine '(extend_tuple_inl _ _ _ @ _).
            refine '(maponpaths (λ x, (inflate x)) (extend_tuple_inl _ _ _) @ _).
            exact (inflate_var _ _).
          - refine '(maponpaths (λ x, x • _) (extend_tuple_inl _ _ _) @ _).
            refine '(maponpaths (λ x, ((inflate x) • _)) (extend_tuple_inl _ _ _) @ _).
            refine '(subst_inflate _ _ _ @ _).
            refine '(subst_inflate L (extend_tuple _ _ _) _ @ _).
            refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
            refine '(var_subst _ _ _ @ _).
            exact (extend_tuple_inl _ _ _).
          - refine '(extend_tuple_inl _ _ _ @ _).
            refine '(maponpaths (λ x, (inflate x)) (extend_tuple_inl _ _ _) @ _).
            exact (inflate_var _ _).
          - exact (extend_tuple_inl _ _ _).
        Qed.

        Definition lifted_mor
          : R_mor A exponential_ob
          := lifted_term ,, lifted_is_mor.

        Lemma lifted_mor_commutes
          : h = # (constprod_functor1 R_binproducts B) lifted_mor · eval_mor.
        Proof.
          apply R_mor_eq.
          refine '(!R_mor_is_mor h @ _).
          refine '(compose_abs _ Lβ _ _ @ _).
          refine '(maponpaths (λ x, (abs (app x _))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (app _ (⟨(app x _), _⟩)))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (app _ (⟨_, (app x _)⟩)))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (app _ (⟨(app (_ ∘ x) _), _⟩)))) (inflate_π1 _) @ _).
          refine '(maponpaths (λ x, (abs (app _ (⟨_, (app (_ ∘ x) _)⟩)))) (inflate_π2 _) @ _).
          refine '(!maponpaths (λ x, (abs (app _ (⟨(app (inflate x ∘ _) _), _⟩)))) (R_ob_idempotent _) @ _).
          refine '(!maponpaths (λ x, (abs (app _ (⟨(app (inflate (x ∘ _) ∘ _) _), _⟩)))) (R_ob_idempotent _) @ _).
          refine '(maponpaths (λ x, (abs (app _ (⟨(app (x ∘ _) _), _⟩)))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (app _ (⟨(app ((x ∘ _) ∘ _) _), _⟩)))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs x)) (app_compose _ Lβ _ _ _) @ _).
          do 3 (refine '(maponpaths (λ x, (abs (app _ (app _ (⟨x, _⟩))))) (app_compose _ Lβ _ _ _) @ _)).
          refine '(maponpaths (λ x, (abs (app _ (app _ (⟨_, x⟩))))) (app_compose _ Lβ _ _ _) @ _).
          refine '(_ @ !ev_compose_pair_arrow _ Lβ _ _ _ _).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app (app (inflate x) _) _)))) (curry_compose _ Lβ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app (app x _) _)))) (inflate_abs _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app x _)))))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (beta_equality _ Lβ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app (_ ∘ x) _)))))) (inflate_compose _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (subst_subst _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (app _ (app (_ ∘ (_ ∘ x)) _)))))) (inflate_π1 _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (subst_abs _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ x))) (beta_equality _ Lβ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ x))) (subst_subst _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ x))) (subst_app _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ x)))) (subst_pair _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app x _)))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨x, _⟩))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, x⟩))))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨(x • _), _⟩))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, x⟩))))) (subst_app _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨x, _⟩))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app x _)⟩))))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ x)⟩))))) (subst_app _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨x, _⟩))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app x _))⟩))))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ x))⟩))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app x _))⟩))))) (subst_π2 _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ (x • _)))⟩))))) (extend_tuple_inl _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ x))⟩))))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ ((x • _) • _)))⟩))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ x))⟩))))) (subst_subst _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ x))⟩))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ (x • _)))⟩))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ x))⟩))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨_, (app _ (app _ x))⟩))))) (extend_tuple_inl _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨(app _ x), _⟩))))) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (app _ (app _ (⟨(app _ (app _ x)), _⟩))))) (app_compose _ Lβ _ _ _)).
          refine '(
            maponpaths (λ x, (abs (app _ (app (_ • x) _)))) _ @
            maponpaths (λ x, (abs (app _ (app _ (⟨_, (app (_ • x) _)⟩))))) _
          );
            apply funextfun;
            intro i;
            refine '(_ @ !maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _));
            refine '(_ @ !subst_inflate _ _ _);
            refine '(_ @ !subst_subst L (extend_tuple _ _ _) _ _);
            refine '(_ @ !maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _));
            refine '(_ @ !var_subst _ _ _);
            refine '(_ @ !maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _));
            refine '(_ @ !var_subst _ _ _);
            exact (!extend_tuple_inl _ _ _).
        Qed.

        Lemma lifted_mor_unique
          (lifted_mor' : R_mor A (exponential_ob))
          (H : h = # (constprod_functor1 R_binproducts B) lifted_mor' · eval_mor)
          : lifted_mor' = lifted_mor.
        Proof.
          apply R_mor_eq.
          refine '(!R_mor_is_mor _ @ _).
          refine '(!compose_assoc _ Lβ _ _ _ @ _).
          refine '(curry_compose _ Lβ _ _ @ _).
          refine '(maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_ev _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, x⟩))))) (inflate_app _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app x _)))) (inflate_ev _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (app _ x)⟩))))) (inflate_app _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (⟨_, (app _ (app _ x))⟩))))) (inflate_var _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs x))) (app_ev_pair _ Lβ _ _ _ _) @ _).
          refine '(!maponpaths (λ x, (abs (abs (app _ (app _ (app (inflate (inflate x)) _)))))) (R_ob_idempotent _) @ _).
          refine '(!maponpaths (λ x, (abs (abs (app _ (app _ (app (inflate (inflate (x ∘ _))) _)))))) (R_ob_idempotent _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app (inflate x) _)))))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app ((inflate x) ∘ _) _)))))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ (app (x ∘ _) _)))))) (inflate_compose _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ x))))) (app_compose _ Lβ _ _ _) @ _).
          refine '(maponpaths (λ x, (abs (abs (app _ (app _ x))))) (app_compose _ Lβ _ _ _) @ _).
          refine '(_ @ !maponpaths (λ x, curry (R_mor_to_L x)) H).
          refine '(_ @ !maponpaths (λ x, (curry x)) (ev_compose_pair_arrow _ Lβ _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app (inflate x) _)))) (inflate_abs _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app x _)))) (inflate_abs _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs x))) (beta_equality _ Lβ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs x))) (subst_subst _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs x))) (subst_subst _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs x))) (subst_app _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app x _)))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ x)))) (subst_app _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app x _))))) (subst_app _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ x))))) (subst_app _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app x _) _))))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app _ x) _))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ x)))))) (subst_app _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app x _) _))))) (subst_compose _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app _ (x • _)) _))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app x _))))))) (subst_inflate _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app _ x) _))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app x _))))))) (subst_compose _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ (x • _)))))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app _ (x • _)) _))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app _ x) _))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ (x • _)))))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app _ x) _))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (var_subst _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (extend_tuple_inr _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app (_ ∘ x) _) _))))) (subst_compose _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app (_ ∘ x) _))))))) (subst_compose _ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app (_ ∘ (_ ∘ x)) _) _))))) (subst_π2 _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app (_ ∘ (_ ∘ x)) _))))))) (subst_π1 _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app x _))))) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app _ x) _))))) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ x)))))) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ x))))))) (app_compose _ Lβ _ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app (app _ (app _ x)) _))))) ( π2_pair _ Lβ _ _)).
          refine '(_ @ !maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ (app _ x)))))))) ( π1_pair _ Lβ _ _)).
          refine '(
            maponpaths (λ x, (abs (abs (app x _)))) _ @
            maponpaths (λ x, (abs (abs (app _ (app (app x _) _))))) _ @
            maponpaths (λ x, (abs (abs (app _ (app (app _ (app x _)) _))))) _ @
            maponpaths (λ x, (abs (abs (app _ (app _ (app x _)))))) _ @
            maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app x _))))))) _  @
            maponpaths (λ x, (abs (abs (app _ (app _ (app _ (app _ (app x _)))))))) _
          );
            refine '((subst_subst _ _ _ _ : inflate (inflate _) = _) @ _);
            refine '(maponpaths (λ x, _ • x) _);
            apply funextfun;
            intro i;
            refine '(var_subst _ _ _ @ _);
            refine '(_ @ !maponpaths (λ x, x • _) (extend_tuple_inl _ _ _));
            refine '(_ @ !var_subst _ _ _);
            refine '(_ @ !maponpaths (λ x, x • _) (extend_tuple_inl _ _ _));
            refine '(_ @ !var_subst _ _ _);
            exact (!extend_tuple_inl _ _ _).
        Qed.

      End Lambda.

    End Object.

    Definition R_exponentials
      : Exponentials R_binproducts.
    Proof.
      intro B.
      refine '(left_adjoint_from_partial _ _ _ _).
      - exact (exponential_ob B).
      - exact (eval_mor B).
      - intros C A h.
        refine '(unique_exists _ _ _ _).
        + exact (lifted_mor B C A h).
        + exact (lifted_mor_commutes B C A h).
        + intro y.
          apply homset_property.
        + apply lifted_mor_unique.
    Defined.

  End Exponentials.

  Section Endomorphism.

    Definition U_term
      : L n
      := abs (var (stnweq (inr tt))).

    Lemma U_compose
      (t : L (S n))
      : U_term ∘ (abs t) = abs t.
    Proof.
      refine '(compose_abs _ Lβ _ _ @ _).
      refine '(maponpaths (λ x, (abs (app x _))) (inflate_abs _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (subst_subst _ _ _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (var_subst _ _ _) @ _).
      refine '(maponpaths (λ x, (abs (x • _))) (extend_tuple_inr _ _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (var_subst _ _ _) @ _).
      exact (maponpaths (λ x, (abs x)) (extend_tuple_inr _ _ _)).
    Qed.

    Lemma compose_U
      (t : L (S n))
      : (abs t) ∘ U_term = abs t.
    Proof.
      refine '(compose_abs _ Lβ _ _ @ _).
      refine '(maponpaths (λ x, (abs (app x _))) (inflate_abs _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _).
      refine '(maponpaths (λ x, (abs x)) (subst_subst _ _ _ _) @ _).
      refine '(_ @ maponpaths abs (subst_var L t)).
      refine '(maponpaths (λ x, abs (_ • x)) _).
      apply funextfun.
      intro i.
      rewrite <- (homotweqinvweq stnweq i).
      induction (invmap stnweq i) as [i' | i'].
      - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inl _ _ _) @ _).
        refine '(var_subst _ _ _ @ _).
        exact (extend_tuple_inl _ _ _).
      - refine '(maponpaths (λ x, (x • _)) (extend_tuple_inr _ _ _) @ _).
        refine '(var_subst _ _ _ @ _).
        exact (extend_tuple_inr _ _ _).
    Qed.

    Definition U
      : R_ob
      := U_term ,, U_compose _.

    Section Retraction.

      Context (A : R_ob).

      Lemma retraction_is_mor
        : A ∘ A ∘ U = A.
      Proof.
        exact (compose_U _ @ R_ob_idempotent _).
      Qed.

      Definition retraction
        : R_mor U A
        := (A : L n) ,, retraction_is_mor.

      Lemma section_is_mor
        : U ∘ A ∘ A = A.
      Proof.
        exact (!compose_assoc _ Lβ _ _ _ @ U_compose _ @ R_ob_idempotent _).
      Qed.

      Definition section
        : R_mor A U
        := (A : L n) ,, section_is_mor.

      Lemma retraction_is_retraction
        : (section : R⟦A, U⟧) · retraction = identity (A : R).
      Proof.
        apply R_mor_eq.
        apply R_ob_idempotent.
      Qed.

    End Retraction.

    Definition E
      : lambda_theory.
    Proof.
      refine '(endomorphism_lambda_theory _ _ _ _ _ _).
      - exact R.
      - exact R_terminal.
      - exact R_binproducts.
      - exact U.
      - apply R_exponentials.
      - exact (section _).
      - exact (retraction _).
    Defined.

    Definition Eβ
      : has_β E.
    Proof.
      apply endomorphism_theory_has_β.
      apply retraction_is_retraction.
    Qed.

  End Endomorphism.

End Category.

Section Category.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).

  Section Iso.

    Definition representation_theorem_iso_mor_0
      : E (n := 0) L Lβ 0 → L 0.
    Proof.
      intro f.
      exact (app (R_mor_to_L L f) (U_term L)).
    Defined.

    Definition representation_theorem_iso_inv_0
      : L 0 → E (n := 0) L Lβ 0.
    Proof.
      intro f.
      exists (abs (inflate f)).
      abstract (now (
        refine '(maponpaths (λ x, x ∘ _) ((U_compose _ Lβ _)) @ _);
        refine '(compose_abs _ Lβ _ _ @ _);
        refine '(maponpaths (λ x, (abs (app x _))) (inflate_abs _ _) @ _);
        refine '(maponpaths (λ x, (abs x)) (beta_equality _ Lβ _ _) @ _);
        refine '(maponpaths (λ x, (abs x)) (subst_subst _ _ _ _) @ _);
        refine '(maponpaths (λ x, (abs x)) (subst_inflate _ _ _) @ _);
        now do 2 (refine '(maponpaths (λ x, abs (_ • x)) (pr2 (iscontr_empty_tuple (L 1)) _) @ !_))
      )).
    Defined.

    Definition representation_theorem_iso_mor
      {n : nat}
      : E (n := 0) L Lβ n → L n.
    Proof.
      induction n as [ | n Fn ].
      - exact representation_theorem_iso_mor_0.
      - intro f.
        exact (app
          (inflate (Fn (abs f)))
          (var (stnweq (inr tt)))).
    Defined.

    Definition representation_theorem_iso_inv
      {n : nat}
      : L n → E (n := 0) L Lβ n.
    Proof.
      induction n as [ | n Fn ].
      - exact representation_theorem_iso_inv_0.
      - intro f.
        exact (app
          (inflate (Fn (abs f)))
          (var (T := E _ _) (stnweq (inr tt)))).
    Defined.

    Lemma representation_theorem_iso_inv_mor_0
      (f : E L Lβ 0)
      : representation_theorem_iso_inv (representation_theorem_iso_mor f) = f.
    Proof.
      apply R_mor_eq.
      refine '(maponpaths (λ x, (abs x)) (inflate_app _ _ _) @ _).
      refine '(maponpaths (λ x, (abs (app _ x))) (inflate_abs _ _) @ _).
      refine '(maponpaths (λ x, (abs (app _ (abs x)))) (var_subst _ _ _) @ _).
      refine '(maponpaths (λ x, (abs (app _ (abs x)))) (extend_tuple_inr _ _ _) @ _).
      refine '(_ @ R_mor_is_mor_right _ Lβ _).
      exact (!compose_abs _ Lβ _ _).
    Qed.

    Lemma representation_theorem_iso_mor_inv_0
      (f : L 0)
      : representation_theorem_iso_mor (representation_theorem_iso_inv f) = f.
    Proof.
      refine '(beta_equality _ Lβ _ _ @ _).
      refine '(subst_inflate _ _ _ @ _).
      refine '(_ @ subst_var L f).
      now do 2 (refine '(maponpaths (λ x, _ • x) (pr2 (iscontr_empty_tuple _) _) @ !_)).
    Qed.

    Lemma representation_theorem_is_iso_0
      : is_inverse_in_precat (C := HSET) representation_theorem_iso_mor_0 representation_theorem_iso_inv_0.
    Proof.
      split;
        apply funextfun;
        intro f.
      - apply R_mor_eq.
        refine '(maponpaths (λ x, (abs x)) (inflate_app _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ x))) (inflate_abs _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (abs x)))) (var_subst _ _ _) @ _).
        refine '(maponpaths (λ x, (abs (app _ (abs x)))) (extend_tuple_inr _ _ _) @ _).
        refine '(_ @ R_mor_is_mor_right L Lβ _).
        exact (!compose_abs _ Lβ _ _).
      - refine '(beta_equality _ Lβ _ _ @ _).
        refine '(subst_inflate _ _ _ @ _).
        refine '(_ @ subst_var L f).
        now do 2 (refine '(maponpaths (λ x, _ • x) (pr2 (iscontr_empty_tuple _) _) @ !_)).
    Qed.

    Definition representation_theorem_iso_0
      : z_iso (C := HSET) (E _ _ 0) (L 0)
      := make_z_iso (C := HSET)
        representation_theorem_iso_mor_0
        representation_theorem_iso_inv_0
        representation_theorem_is_iso_0.

  End Iso.

End Category.
