(**************************************************************************************************

  The theory of extensions of an algebra

  Given an algebraic theory T and a T-algebra A, we can construct the "theory of extensions" of A
  as the theory T_A with (T_A)_n = A + T_n as a coproduct of T-algebras. This is functorial in A.
  The category of algebras of this theory is equivalent to the coslice category (A / T-alg). For
  example, if T encodes the theory of rings and A is a T-algebra (equivalent to a ring R), then T_A
  is the theory of R-algebras. Lastly, for any algebraic theory morphism F : T -> T', if we take
  A = F^*(T'_0), the pullback of the T'-algebra T'_0 along F, then F factors through T_A.

  Contents
  1. The theory of extensions functor [extensions_theory]
  2. The category of T_A-algebras is equivalent to A / T-alg [algebra_coslice_equivalence]
  3. Every morphism F: T -> T' factors through T_(F^*(T'_0)) [factorization]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.Examples.TheoryAlgebra.

Local Open Scope algebraic_theories.
Local Open Scope cat.

(** * 1. The theory of extensions *)

Section TheoryOfExtensions.

  Context (T : algebraic_theory).
  Context (H : BinCoproducts (algebra_cat T)).

  Section Ob.

    Context (A : algebra T).

    Definition extensions_theory_ob_data
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

    Lemma extensions_theory_ob_is_theory
      : is_algebraic_theory extensions_theory_ob_data.
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

    Definition extensions_theory_ob
      : algebraic_theory
      := make_algebraic_theory _ extensions_theory_ob_is_theory.

  End Ob.

  Section Mor.

    Context {A B : algebra T}.
    Context (f : algebra_morphism A B).

    Definition extensions_theory_mor_data
      (n : nat)
      : extensions_theory_ob A n → extensions_theory_ob B n.
    Proof.
      apply algebra_morphism_to_function.
      apply BinCoproductOfArrows.
      - exact f.
      - exact (identity _).
    Defined.

    Lemma extensions_theory_mor_is_morphism
      : is_algebraic_theory_morphism extensions_theory_mor_data.
    Proof.
      use make_is_algebraic_theory_morphism.
      - intros n i.
        refine (!maponpaths (λ x, x _) (algebra_mor_comp _ _) @ _).
        refine (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductOfArrowsIn2 _ _ _ _ _) @ _).
        exact (maponpaths (λ x, algebra_morphism_to_function x _) (id_left _)).
      - intros m n g h.
        do 2 refine (!_ @ maponpaths (λ x, x _) (algebra_mor_comp _ _)).
        revert g.
        apply eqtohomot.
        apply maponpaths.
        do 2 refine (postcompWithBinCoproductArrow _ _ _ _ _ @ !_).
        refine (maponpaths (λ x, _ x _) _ @ maponpaths (λ x, _ x) _).
        + refine (BinCoproductOfArrowsIn1 _ _ _ _ _ @ !_).
          refine (assoc' _ _ _ @ _).
          exact (maponpaths (λ x, _ · x) (BinCoproductIn1Commutes _ _ _ _ _ _ _)).
        + refine (!_ @ !maponpaths (λ x, x · _) (id_left _)).
          refine (BinCoproductIn2Commutes _ _ _ _ _ _ _ @ !_).
          apply algebra_morphism_eq.
          refine (algebra_mor_comp _ _ @ _).
          apply funextfun.
          intro g.
          apply mor_action.
    Qed.

    Definition extensions_theory_mor
      : algebraic_theory_morphism (extensions_theory_ob A) (extensions_theory_ob B)
      := make_algebraic_theory_morphism _ extensions_theory_mor_is_morphism.

  End Mor.

  Section Functor.

    Definition extensions_theory_data
      : functor_data (algebra_cat T) algebraic_theory_cat
      := make_functor_data
        extensions_theory_ob
        (λ _ _, extensions_theory_mor).

    Lemma extensions_theory_is_functor
      : is_functor extensions_theory_data.
    Proof.
      split.
      - intro A.
        apply algebraic_theory_morphism_eq.
        intro n.
        apply eqtohomot.
        change ((identity _ : algebraic_theory_morphism _ _) n)
          with (algebra_morphism_to_function (identity (H A (theory_algebra T n)))).
        apply (maponpaths algebra_morphism_to_function).
        apply BinCoproductArrowsEq.
        + refine (BinCoproductOfArrowsIn1 _ _ _ _ _ @ _).
          refine (id_left _ @ !_).
          exact (id_right _).
        + refine (BinCoproductOfArrowsIn2 _ _ _ _ _ @ _).
          refine (id_left _ @ !_).
          exact (id_right _).
      - intros A B C f g.
        apply algebraic_theory_morphism_eq.
        intros n.
        apply eqtohomot.
        refine (_ @ algebra_mor_comp _ _).
        apply (maponpaths algebra_morphism_to_function).
        refine (_ @ !postcompWithBinCoproductArrow _ _ _ _ _).
        refine (maponpaths (λ x, BinCoproductArrow _ x _) _ @ maponpaths (λ x, BinCoproductArrow _ _ x) _).
        + refine (_ @ assoc _ _ _).
          refine (_ @ !maponpaths (λ x, _ · x) (BinCoproductOfArrowsIn1 _ _ _ _ _)).
          apply assoc'.
        + refine (_ @ assoc _ _ _).
          refine (_ @ !maponpaths (λ x, _ · x) (BinCoproductOfArrowsIn2 _ _ _ _ _)).
          apply (!id_left _).
    Qed.

    Definition extensions_theory
      : functor (algebra_cat T) algebraic_theory_cat
      := make_functor _ extensions_theory_is_functor.

  End Functor.

  Context (A : algebra T).

  Definition extensions_theory_embedding_data
    : algebraic_theory_morphism_data T (extensions_theory A : algebraic_theory)
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
    : algebraic_theory_morphism T (extensions_theory A)
    := make_algebraic_theory_morphism _ extensions_theory_embedding_is_morphism.

(** * 2. The category of T_A-algebras is equivalent to A / T-alg *)

  Section Algebras.

    Section AlgebraToCoslice.

      Section Ob.

        Context (B : algebra (extensions_theory A)).

        Definition algebra_to_coslice_morphism_data
          : A → (algebra_pullback extensions_theory_embedding B : algebra _).
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
          : algebra_morphism A (algebra_pullback extensions_theory_embedding B)
          := make_algebra_morphism _ algebra_to_coslice_is_morphism.

      End Ob.

      Section Mor.

        Context {B B' : algebra (extensions_theory A)}.
        Context (F : algebra_morphism B B').

        Lemma algebra_to_coslice_commutes
          : algebra_to_coslice_morphism B · # (algebra_pullback extensions_theory_embedding) F = algebra_to_coslice_morphism B'.
        Proof.
          apply algebra_morphism_eq.
          refine (algebra_mor_comp _ _ @ _).
          apply funextfun.
          intro a.
          refine (mor_action F _ _ @ _).
          apply (maponpaths (action _)).
          apply iscontr_uniqueness.
        Qed.

      End Mor.

      Definition algebra_to_coslice
        : algebra_cat (extensions_theory A) ⟶ coslice_cat_total _ A.
      Proof.
        apply (lifted_functor (F := algebra_pullback extensions_theory_embedding)).
        use tpair.
        - use tpair.
          + intro B.
            apply algebra_to_coslice_morphism.
          + intros B B' F.
            apply algebra_to_coslice_commutes.
        - split;
            intros;
            apply homset_property.
      Defined.

    End AlgebraToCoslice.

    Section CosliceToAlgebra.

      Section Ob.

        Context {B : algebra T}.
        Context (F : algebra_morphism A B).

        Definition coslice_to_algebra_ob_data
          : algebra_data (extensions_theory A).
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

        Lemma coslice_to_ob_is_algebra
          : is_algebra coslice_to_algebra_ob_data.
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

        Definition coslice_to_algebra_ob
          : algebra (extensions_theory A)
          := make_algebra _ coslice_to_ob_is_algebra.

      End Ob.

      Section Mor.

        Context {B B' : algebra T}.
        Context {F : algebra_morphism A B}.
        Context {F' : algebra_morphism A B'}.
        Context {G : algebra_morphism B B'}.
        Context (HG : F · G = F').

        Lemma G_is_algebra_morphism
          : is_algebra_morphism (A := coslice_to_algebra_ob F) (A' := coslice_to_algebra_ob F') G.
        Proof.
          induction HG.
          intros n f b.
          revert f.
          apply eqtohomot.
          use (maponpaths algebra_morphism_to_function (_ : make_algebra_morphism _ (_ : is_algebra_morphism _) = _)).
          {
            intros m f a.
            refine (maponpaths (λ x, _ x) (mor_action _ _ _) @ _).
            exact (mor_action G _ _).
          }
          apply BinCoproductArrowUnique.
          - apply algebra_morphism_eq.
            refine (algebra_mor_comp _ _ @ _).
            apply funextfun.
            intro a.
            refine (!maponpaths (λ x, G (x _)) (algebra_mor_comp _ _) @ _).
            refine (maponpaths (λ x, G (_ x _)) (BinCoproductIn1Commutes _ _ _ _ _ _ _) @ _).
            exact (!eqtohomot (algebra_mor_comp _ _) _).
          - apply algebra_morphism_eq.
            refine (algebra_mor_comp _ _ @ _).
            apply funextfun.
            intro a.
            refine (!maponpaths (λ x, G (x _)) (algebra_mor_comp _ _) @ _).
            refine (maponpaths (λ x, G (_ x _)) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
            apply mor_action.
        Qed.

        Definition coslice_to_algebra_mor
          : algebra_morphism (coslice_to_algebra_ob F) (coslice_to_algebra_ob F')
          := make_algebra_morphism
            _
            G_is_algebra_morphism.

      End Mor.

      Definition coslice_to_algebra_data
        : functor_data (coslice_cat_total _ A) (algebra_cat (extensions_theory A))
        := make_functor_data (C := coslice_cat_total _ A)
          (λ F, coslice_to_algebra_ob (pr2 F))
          (λ _ _ G, coslice_to_algebra_mor (pr2 G)).

      Lemma coslice_to_algebra_is_functor
        : is_functor coslice_to_algebra_data.
      Proof.
        split.
        - intro F.
          now apply algebra_morphism_eq.
        - intros F F' F'' G G'.
          apply algebra_morphism_eq.
          refine (_ @ !algebra_mor_comp _ _).
          refine (pr1_transportf (B := λ _, _ → _) _ _ @ _).
          exact (maponpaths (λ z, z _) (transportf_const _ _)).
      Qed.

      Definition coslice_to_algebra
        : coslice_cat_total _ A ⟶ algebra_cat (extensions_theory A)
        := make_functor
          coslice_to_algebra_data
          coslice_to_algebra_is_functor.

    End CosliceToAlgebra.

    Definition coslice_to_algebra_to_coslice_iso
      {B : algebra T}
      (F : algebra_morphism A B)
      : z_iso (C := algebra_cat T) (algebra_pullback extensions_theory_embedding (coslice_to_algebra (B ,, F))) B.
    Proof.
      use make_algebra_z_iso.
      - apply identity_z_iso.
      - abstract (
          intros n f a;
          refine (!maponpaths (λ x, x _) (algebra_mor_comp _ _) @ _);
          exact (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _))
        ).
    Defined.

    Lemma coslice_to_algebra_to_coslice_commutes
      {B : algebra T}
      (F : algebra_morphism A B)
      : algebra_to_coslice_morphism (coslice_to_algebra (B ,, F)) · coslice_to_algebra_to_coslice_iso F = F.
    Proof.
      apply algebra_morphism_eq.
      refine (algebra_mor_comp _ _ @ _).
      apply funextfun.
      intro i.
      refine (!maponpaths (λ x, x _) (algebra_mor_comp (BinCoproductIn1 _) (BinCoproductArrow _ _ _)) @ _).
      exact (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn1Commutes _ _ _ _ _ _ _)).
    Qed.

    Lemma algebra_to_coslice_to_algebra_is_morphism
      (B : algebra (extensions_theory A))
      : is_algebra_morphism (A := (coslice_to_algebra (_ ,, algebra_to_coslice_morphism B) : algebra _)) (A' := B) (z_iso_mor (identity_z_iso (C := HSET) (B : hSet))).
    Proof.
      intros n f b.
      revert f.
      apply eqtohomot.
      use (maponpaths algebra_morphism_to_function (_ : _ = make_algebra_morphism _ (_ : is_algebra_morphism (A' := (algebra_pullback _ B : algebra _)) _))).
      {
        intros n' f' a'.
        refine (_ @ subst_action (T := (extensions_theory A)) B _ a' b).
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

    Definition algebra_to_coslice_to_algebra
      (B : algebra (extensions_theory A))
      : z_iso (coslice_to_algebra (_ ,, algebra_to_coslice_morphism B)) B
      := make_algebra_z_iso _ _ _ _ (algebra_to_coslice_to_algebra_is_morphism B).

    Definition algebra_to_coslice_surjective
      : split_essentially_surjective algebra_to_coslice.
    Proof.
      intro F.
      exists (coslice_to_algebra F).
      apply weq_z_iso.
      exact (_ ,, coslice_to_algebra_to_coslice_commutes _).
    Defined.

    Definition algebra_to_coslice_fully_faithful
      : fully_faithful algebra_to_coslice.
    Proof.
      intros B B'.
      use isweq_iso.
      - intro F.
        refine (
          inv_from_z_iso (algebra_to_coslice_to_algebra _) ·
          _ ·
          algebra_to_coslice_to_algebra _
        ).
        apply (# coslice_to_algebra F).
      - abstract (
          intro;
          apply algebra_morphism_eq;
          refine (algebra_mor_comp _ _ @ _);
          exact (maponpaths (λ x, _ x _) (algebra_mor_comp _ _))
        ).
      - abstract (
          intro;
          apply subtypePath;
          [ intro;
            apply homset_property
          | apply algebra_morphism_eq;
            refine (algebra_mor_comp (T := (extensions_theory A)) _ _ @ _);
            exact (maponpaths (λ x, _ x _) (algebra_mor_comp (T := (extensions_theory A)) _ _)) ]
        ).
    Defined.

    Definition algebra_to_coslice_is_equivalence
      : adj_equivalence_of_cats algebra_to_coslice
      := rad_equivalence_of_cats' _ _ _
        algebra_to_coslice_fully_faithful
        algebra_to_coslice_surjective.

    Definition algebra_coslice_equivalence
      : adj_equiv (algebra_cat (extensions_theory A)) (coslice_cat_total _ A)
      := algebra_to_coslice ,, algebra_to_coslice_is_equivalence.

  End Algebras.

End TheoryOfExtensions.

(** * 3. Every morphism F: T -> T' factors through T_(F^*(T'_0)) *)

Section Factorization.

  Context {T T' : algebraic_theory}.
  Context (H : BinCoproducts (algebra_cat T)).
  Context (F : algebraic_theory_morphism T T').
  Let A := algebra_pullback F (theory_algebra T' 0).

  Definition factorization_first_factor
    : algebraic_theory_morphism T (extensions_theory T H A)
    := extensions_theory_embedding _ _ _.

  Definition factorization_second_factor_data
    : algebraic_theory_morphism_data (extensions_theory T H A : algebraic_theory) T'.
  Proof.
    intros n.
    refine (algebra_morphism_to_function (BinCoproductArrow _ (c := (algebra_pullback F (theory_algebra T' n))) _ _)).
    - apply algebra_pullback_mor.
      apply theory_algebra_free.
      apply (iscontrpr1 (iscontr_empty_tuple _)).
    - apply theory_algebra_free.
      exact var.
  Defined.

  Lemma factorization_second_factor_is_morphism
    : is_algebraic_theory_morphism factorization_second_factor_data.
  Proof.
    use make_is_algebraic_theory_morphism.
    - intros n i.
      refine (!maponpaths (λ x, x _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T n (algebra_pullback F (theory_algebra T' n)) var))) @ _).
      refine (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
      refine (subst_var _ _ @ _).
      apply mor_var.
    - intros m n f g.
      refine (!maponpaths (λ x, x _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T n (algebra_pullback F (theory_algebra T' n)) var))) @ _).
      revert f.
      apply eqtohomot.
      use (maponpaths algebra_morphism_to_function (_ : _ = make_algebra_morphism _ (_ : is_algebra_morphism _))).
      {
        intros n' f' a'.
        refine (maponpaths (λ x, x • _) (mor_action (BinCoproductArrow _ _ (theory_algebra_free T m (algebra_pullback F (theory_algebra T' m)) var)) _ _) @ _).
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
        refine (_ @ maponpaths (λ x, x _ • _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T m (algebra_pullback F (theory_algebra T' m)) var)))).
        refine (_ @ !maponpaths (λ x, algebra_morphism_to_function (A' := algebra_pullback F (theory_algebra T' m)) x _ • _) (BinCoproductIn1Commutes _ _ _ _ _ _ _)).
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
        refine (_ @ maponpaths (λ x, x _ • _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T m (algebra_pullback F (theory_algebra T' m)) var)))).
        refine (_ @ !maponpaths (λ x, algebra_morphism_to_function (A' := algebra_pullback F (theory_algebra T' m)) x _ • _) (BinCoproductIn2Commutes _ _ _ _ _ _ _)).
        exact (!maponpaths (λ x, x • _) (subst_var _ _)).
  Qed.

  Definition factorization_second_factor
    : algebraic_theory_morphism (extensions_theory T H A) T'
    := make_algebraic_theory_morphism _ factorization_second_factor_is_morphism.

  Lemma factorization
    : factorization_first_factor · factorization_second_factor = F.
  Proof.
    apply algebraic_theory_morphism_eq.
    intros n f.
    refine (!maponpaths (λ x, x _) (algebra_mor_comp _ (BinCoproductArrow _ _ (theory_algebra_free T n (algebra_pullback F (theory_algebra T' n)) var))) @ _).
    refine (maponpaths (λ x, algebra_morphism_to_function x _) (BinCoproductIn2Commutes _ _ _ _ _ _ _) @ _).
    apply subst_var.
  Qed.

End Factorization.
