Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraCategory.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.IndexedSetCategory.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.

Local Open Scope algebraic_theories.
Local Open Scope cat.

Definition is_algebra_morphism
  {T : algebraic_theory}
  {A A' : algebra_data T}
  (F : A → A')
  : UU
  := ∏ n f a, mor_action_ax (identity T) F (@action T A) (@action T A') n f a.

Section TheoryAlgebra.

  Context (T : algebraic_theory).
  Context (n : nat).

  Definition theory_algebra_data
    : algebra_data T
    := make_algebra_data
      (T n)
      (λ _ f a, f • a).

  Lemma theory_is_algebra
    : is_algebra theory_algebra_data.
  Proof.
    use make_is_algebra.
    - intros.
      apply subst_subst.
    - intros.
      apply var_subst.
  Qed.

  Definition theory_algebra
    : algebra T
    := make_algebra _ theory_is_algebra.

  Definition theory_algebra_free
    (A : algebra T)
    (a : stn n → A)
    : algebra_morphism theory_algebra A.
  Proof.
    use make_algebra_morphism.
    - intro f.
      exact (action f a).
    - abstract (intros; apply subst_action).
  Defined.

End TheoryAlgebra.

Section Pullback.

  Context {T T' : algebraic_theory}.
  Context (F : algebraic_theory_morphism T T').

  Section Ob.

    Context (A : algebra T').

    Definition algebra_pullback_ob_data
      : algebra_data T
      := make_algebra_data
        A
        (λ n f a, action (F _ f) a).

    Lemma algebra_pullback_ob_is_algebra
      : is_algebra algebra_pullback_ob_data.
    Proof.
      use make_is_algebra.
      - intros m n f g a.
        refine (maponpaths (λ x, action (A := A) x a) (mor_subst _ _ _) @ _).
        apply subst_action.
      - intros n i a.
        refine (maponpaths (λ x, action (A := A) x a) (mor_var _ _) @ _).
        apply var_action.
    Qed.

    Definition algebra_pullback_ob
      : algebra T
      := make_algebra _ algebra_pullback_ob_is_algebra.

  End Ob.

  Section Mor.

    Context {A A' : algebra T'}.
    Context (G : algebra_morphism A A').

    Definition algebra_pullback_mor_data
      : algebra_pullback_ob A → algebra_pullback_ob A'
      := G.

    Lemma algebra_pullback_mor_is_morphism
      : is_algebra_morphism algebra_pullback_mor_data.
    Proof.
      do 3 intro.
      apply (mor_action G).
    Qed.

    Definition algebra_pullback_mor
      : algebra_morphism (algebra_pullback_ob A) (algebra_pullback_ob A')
      := make_algebra_morphism _ algebra_pullback_mor_is_morphism.

  End Mor.

End Pullback.

Section TheoryOfExtensions.

  Context (T : algebraic_theory).
  Context (H : BinCoproducts (algebra_cat T)).
  Context (A : algebra T).

  Definition extensions_theory_data
    : algebraic_theory_data.
  Proof.
    use make_algebraic_theory_data.
    - intro n.
      exact (BinCoproductObject (H A (theory_algebra T n)) : algebra _).
    - intros n i.
      refine ((BinCoproductIn2 _ : algebra_morphism _ _) _).
      exact (var i).
    - intros m n f g.
      revert f.
      refine (BinCoproductArrow _ _ _ : algebra_morphism _ _).
      + exact (BinCoproductIn1 _).
      + apply theory_algebra_free.
        exact g.
  Defined.

  Lemma extensions_theory_is_theory
    : is_algebraic_theory extensions_theory_data.
  Proof.
    use make_is_algebraic_theory.
    - intros l m n f_l f_m f_n.
      refine (!maponpaths (λ x, x _) (algebra_mor_comp _ _) @ _).
      revert f_l.
      apply eqtohomot.
      apply (maponpaths algebra_morphism_to_function).
      apply BinCoproductArrowUnique.
      + refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (BinCoproductIn1Commutes _ _ _ _ _ _ _) @ _).
        apply BinCoproductIn1Commutes.
      + refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
        apply algebra_morphism_eq.
        refine (algebra_mor_comp _ _ @ _).
        apply funextfun.
        intro f_l.
        apply mor_action.
    - intros m n i f.
      refine (!maponpaths (λ x, x _) (algebra_mor_comp _ _) @ _).
      refine (maponpaths (λ x, _ x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
      apply var_action.
    - intros n f.
      refine (maponpaths (λ x, algebra_morphism_to_function x f) (_ : _ = identity _)).
      symmetry.
      apply BinCoproductArrowUnique.
      + apply id_right.
      + refine (id_right _ @ _).
        apply algebra_morphism_eq.
        apply funextfun.
        intro f'.
        refine (_ @ mor_action _ _ _).
        apply maponpaths.
        apply (!subst_var _ _).
  Qed.

  Definition extensions_theory
    : algebraic_theory
    := make_algebraic_theory _ extensions_theory_is_theory.

  Definition extensions_theory_embedding_data
    : algebraic_theory_morphism_data T extensions_theory
    := λ n, (BinCoproductIn2 (H A (theory_algebra T n)) : algebra_morphism _ _).

  Lemma extensions_theory_embedding_is_morphism
    : is_algebraic_theory_morphism extensions_theory_embedding_data.
  Proof.
    use make_is_algebraic_theory_morphism.
    - reflexivity.
    - intros m n f g.
      refine (mor_action _ _ _ @ _).
      refine (_ @ maponpaths (λ x, x f) (algebra_mor_comp (BinCoproductIn2 (H A (theory_algebra T m))) _)).
      symmetry.
      exact (maponpaths (λ x, algebra_morphism_to_function x (f : theory_algebra T m)) (BinCoproductIn2Commutes _ _ _ _ _ _ _)).
  Qed.

  Definition extensions_theory_embedding
    : algebraic_theory_morphism T extensions_theory
    := make_algebraic_theory_morphism _ extensions_theory_embedding_is_morphism.

  Section Algebras.

    Section AlgebraToCoslice.

      Context (B : algebra extensions_theory).

      Definition algebra_to_coslice_morphism_data
        : A → algebra_pullback_ob extensions_theory_embedding B.
      Proof.
        intro a.
        refine (action (A := B) _ (iscontrpr1 (iscontr_empty_tuple _))).
        refine ((BinCoproductIn1 (H A (theory_algebra T 0)) : algebra_morphism _ _) _).
        exact a.
      Defined.

      Lemma algebra_to_coslice_is_morphism
        : is_algebra_morphism algebra_to_coslice_morphism_data.
      Proof.
        intros n f a.
        refine (_ @ subst_action B (extensions_theory_embedding n f) _ _).
        refine (maponpaths (λ x, action x _) _).
        refine (_ @ (maponpaths (λ (x : theory_algebra T n → _), x f) (algebra_mor_comp _ _))).
        refine (_ @ !maponpaths (λ (x : algebra_morphism (theory_algebra T n) _), algebra_morphism_to_function x f) (BinCoproductIn2Commutes _ _ _ _ _ _ _)).
        apply mor_action.
      Qed.

      Definition algebra_to_coslice_morphism
        : algebra_morphism A (algebra_pullback_ob extensions_theory_embedding B)
        := make_algebra_morphism _ algebra_to_coslice_is_morphism.

    End AlgebraToCoslice.

    Section CosliceToAlgebra.

      Context (B : algebra T).
      Context (F : algebra_morphism A B).

      Definition coslice_to_algebra_data
        : algebra_data extensions_theory.
      Proof.
        use make_algebra_data.
        - exact B.
        - intros n f b.
          revert f.
          refine (BinCoproductArrow _ _ _ : algebra_morphism _ _).
          + exact F.
          + apply theory_algebra_free.
            exact b.
      Defined.

      Lemma coslice_to_is_algebra
        : is_algebra coslice_to_algebra_data.
      Proof.
        use make_is_algebra.
        - intros m n f g a.
          refine (!maponpaths (λ x, x _) (algebra_mor_comp _ _) @ _).
          revert f.
          apply eqtohomot.
          apply (maponpaths algebra_morphism_to_function).
          apply BinCoproductArrowUnique.
          + refine (assoc _ _ _ @ _).
            refine (maponpaths (λ x, x · _) (BinCoproductIn1Commutes _ _ _ _ _ _ _) @ _).
            apply BinCoproductIn1Commutes.
          + refine (assoc _ _ _ @ _).
            refine (maponpaths (λ x, x · _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
            apply algebra_morphism_eq.
            refine (algebra_mor_comp _ _ @ _).
            apply funextfun.
            intro f.
            apply mor_action.
        - intros n i a.
          refine (!maponpaths (λ x, x _) (algebra_mor_comp _ _) @ _).
          refine (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
          apply var_action.
      Qed.

      Definition coslice_to_algebra
        : algebra extensions_theory
        := make_algebra _ coslice_to_is_algebra.

    End CosliceToAlgebra.

    Section Preservation.

      Definition preserves_coslice_object
        (B : algebra T)
        (F : algebra_morphism A B)
        : z_iso (C := algebra_cat T) (algebra_pullback_ob extensions_theory_embedding (coslice_to_algebra B F)) B.
      Proof.
        use make_algebra_z_iso.
        - apply identity_z_iso.
        - abstract (
            intros n f a;
            refine (!maponpaths (λ x, x _) (algebra_mor_comp _ _) @ _);
            exact (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _))
          ).
      Defined.

      Lemma preserves_coslice_morphism
        (B : algebra T)
        (F : algebra_morphism A B)
        : algebra_to_coslice_morphism (coslice_to_algebra B F) · (preserves_coslice_object B F) = F.
      Proof.
        apply algebra_morphism_eq.
        refine (algebra_mor_comp _ _ @ _).
        apply funextfun.
        intro i.
        refine (!maponpaths (λ x, x _) (algebra_mor_comp (BinCoproductIn1 _) (BinCoproductArrow _ _ _)) @ _).
        exact (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn1Commutes _ _ _ _ _ _ _)).
      Qed.

      Lemma preserves_algebra_structure
        (B : algebra extensions_theory)
        : is_algebra_morphism (A := (coslice_to_algebra _ (algebra_to_coslice_morphism B))) (A' := B) (z_iso_mor (identity_z_iso (C := HSET) (B : hSet))).
      Proof.
        intros n f b.
        revert f.
        apply eqtohomot.
        use (maponpaths algebra_morphism_to_function (_ : _ = make_algebra_morphism _ (_ : is_algebra_morphism (A' := algebra_pullback_ob _ B) _))).
        {
          intros n' f' a'.
          refine (_ @ subst_action (T := extensions_theory) B _ a' b).
          apply (maponpaths (λ x, action x _)).
          refine (_ @ maponpaths (λ x, x _) (algebra_mor_comp (BinCoproductIn2 _) (BinCoproductArrow _ _ _))).
          symmetry.
          exact (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _)).
        }
        symmetry.
        apply BinCoproductArrowUnique.
        - apply algebra_morphism_eq.
          refine (algebra_mor_comp _ _ @ _).
          apply funextfun.
          intro a.
          refine (_ @ subst_action B ((BinCoproductIn1 _ : algebra_morphism _ _) a) (iscontrpr1 (iscontr_empty_tuple _)) b @ _).
          + refine (!_ @ maponpaths (λ x, action (A := B) (x a) b) (algebra_mor_comp _ _)).
            apply (maponpaths (λ x, action (A := B) (algebra_morphism_to_function x a) b)).
            apply BinCoproductIn1Commutes.
          + apply (maponpaths (action _)).
            apply iscontr_uniqueness.
        - apply algebra_morphism_eq.
          exact (algebra_mor_comp _ _).
      Qed.

      Definition preserves_algebra
        (B : algebra extensions_theory)
        : z_iso (coslice_to_algebra _ (algebra_to_coslice_morphism B)) B
        := make_algebra_z_iso _ _ _ _ (preserves_algebra_structure B).

    End Preservation.

  End Algebras.

End TheoryOfExtensions.

Section Factorizing.

  Context {T T' : algebraic_theory}.
  Context (H : BinCoproducts (algebra_cat T)).
  Context (F : algebraic_theory_morphism T T').
  Let A := algebra_pullback_ob F (theory_algebra T' 0).

  Definition first_factor
    : algebraic_theory_morphism T (extensions_theory T H A)
    := extensions_theory_embedding _ _ _.

  Definition second_factor_data
    : algebraic_theory_morphism_data (extensions_theory T H A) T'.
  Proof.
    intros n.
    refine (algebra_morphism_to_function (BinCoproductArrow _ (c := (algebra_pullback_ob F (theory_algebra T' n))) _ _)).
    - apply algebra_pullback_mor.
      apply theory_algebra_free.
      apply (iscontrpr1 (iscontr_empty_tuple _)).
    - apply theory_algebra_free.
      exact var.
  Defined.

  Lemma second_factor_is_morphism
    : is_algebraic_theory_morphism second_factor_data.
  Proof.
    use make_is_algebraic_theory_morphism.
    - intros n i.
      refine (!maponpaths (λ x, x _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T n (algebra_pullback_ob F (theory_algebra T' n)) var))) @ _).
      refine (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
      refine (subst_var _ _ @ _).
      apply mor_var.
    - intros m n f g.
      refine (!maponpaths (λ x, x _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T n (algebra_pullback_ob F (theory_algebra T' n)) var))) @ _).
      revert f.
      apply eqtohomot.
      use (maponpaths algebra_morphism_to_function (_ : _ = make_algebra_morphism _ (_ : is_algebra_morphism _))).
      {
        intros n' f' a'.
        refine (maponpaths (λ x, x • _) (mor_action (BinCoproductArrow _ _ (theory_algebra_free T m (algebra_pullback_ob F (theory_algebra T' m)) var)) _ _) @ _).
        apply (subst_subst T' (F n' f')).
      }
      apply BinCoproductArrowsEq.
      + refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (BinCoproductIn1Commutes _ _ _ _ _ _ _) @ _).
        refine (BinCoproductIn1Commutes _ _ _ _ _ _ _ @ _).
        apply algebra_morphism_eq.
        refine (_ @ !algebra_mor_comp _ _).
        apply funextfun.
        intro f.
        refine (_ @ maponpaths (λ x, x _ • _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T m (algebra_pullback_ob F (theory_algebra T' m)) var)))).
        refine (_ @ !maponpaths (λ x, algebra_morphism_to_function (A' := algebra_pullback_ob F (theory_algebra T' m)) x _ • _) (BinCoproductIn1Commutes _ _ _ _ _ _ _)).
        refine (_ @ !subst_subst T' f _ _).
        apply (maponpaths (λ x, f • x)).
        symmetry.
        apply iscontr_uniqueness.
      + refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
        apply algebra_morphism_eq.
        do 2 refine (algebra_mor_comp _ _ @ !_).
        apply funextfun.
        intro f.
        refine (mor_action _ _ _ @ _).
        refine (_ @ maponpaths (λ x, x _ • _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T m (algebra_pullback_ob F (theory_algebra T' m)) var)))).
        refine (_ @ !maponpaths (λ x, algebra_morphism_to_function (A' := algebra_pullback_ob F (theory_algebra T' m)) x _ • _) (BinCoproductIn2Commutes _ _ _ _ _ _ _)).
        exact (!maponpaths (λ x, x • _) (subst_var _ _)).
  Qed.

  Definition second_factor
    : algebraic_theory_morphism (extensions_theory T H A) T'
    := make_algebraic_theory_morphism _ second_factor_is_morphism.

  Lemma factorization_eq
    : first_factor · second_factor = F.
  Proof.
    apply algebraic_theory_morphism_eq.
    intros n f.
    refine (!maponpaths (λ x, x _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T n (algebra_pullback_ob F (theory_algebra T' n)) var))) @ _).
    refine (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
    apply subst_var.
  Qed.

End Factorizing.
