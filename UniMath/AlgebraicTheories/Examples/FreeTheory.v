(**************************************************************************************************

  The free theory

  This file defines the free functor from sets to algebraic theories, and shows that it is left
  adjoint to the forgetful functor. The free algebraic theory on set X is the theory with just
  constants (taken from X) and variables. The category of algebras for the free theory on X
  is equivalent to the coslice category X ↓ SET.

  Contents
  1. The free functor [free_functor]
  2. The forgetful functor [forgetful_functor]
  3. The adjunction [free_functor_is_free]
  4. The equivalence between algebras and coslices [algebra_coslice_equivalence]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.


Require Import UniMath.AlgebraicTheories.AlgebraCategory.
Require Import UniMath.AlgebraicTheories.AlgebraCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Algebras.

Local Open Scope cat.
Local Open Scope algebraic_theories.
Local Open Scope vec.

(** * 1. The free functor *)

Definition free_theory_data (X : hSet) : algebraic_theory_data.
Proof.
  use make_algebraic_theory_data.
  - intro n.
    exact (setcoprod (stnset n) X).
  - exact (λ _ i, inl i).
  - intros m n f g.
    induction f as [f' | f'].
    + exact (g f').
    + exact (inr f').
Defined.

Definition free_is_theory {X : hSet} : is_algebraic_theory (free_theory_data X).
Proof.
  use make_is_algebraic_theory.
  - intros l m n f_l f_m f_n.
    now induction f_l.
  - now do 4 intro.
  - do 2 intro.
    now induction f.
Qed.

Definition free_theory (X : hSet) : algebraic_theory
  := make_algebraic_theory _ (free_is_theory (X := X)).

Definition free_functor_morphism_data
  {X X' : hSet}
  (f : X → X')
  : algebraic_theory_morphism_data (free_theory X) (free_theory X').
Proof.
  intros n x.
  induction x as [left | right].
  - exact (inl left).
  - exact (inr (f right)).
Defined.

Lemma free_functor_is_morphism
  {X X' : hSet}
  (f : X → X')
  : is_algebraic_theory_morphism (free_functor_morphism_data f).
Proof.
  use make_is_algebraic_theory_morphism.
  - intros n t.
    now induction t.
  - intros m n s t.
    now induction s.
Qed.

Definition free_functor_data
  : functor_data SET algebraic_theory_cat
  := make_functor_data (C := SET) (C' := algebraic_theory_cat)
    (λ X, free_theory X)
    (λ X X' f, (make_algebraic_theory_morphism _ (free_functor_is_morphism f))).

Lemma free_functor_is_functor
  : is_functor free_functor_data.
Proof.
  split.
  - intro A.
    use (algebraic_theory_morphism_eq (T := free_theory A) (T' := free_theory A)).
    intros n f.
    now induction f.
  - intros a b c d e.
    use (algebraic_theory_morphism_eq (T := free_theory a) (T' := free_theory c)).
    intros n f.
    now induction f.
Qed.

Definition free_functor : HSET ⟶ algebraic_theory_cat
  := make_functor _ free_functor_is_functor.

(** * 2. The forgetful functor *)

Definition forgetful_functor_data : functor_data algebraic_theory_cat HSET.
Proof.
  use make_functor_data.
  - intro T.
    exact ((T : algebraic_theory) 0).
  - intros T T' F.
    exact ((F : algebraic_theory_morphism T T') 0).
Defined.

Lemma forgetful_is_functor : is_functor forgetful_functor_data.
Proof.
  use tpair;
    easy.
Qed.

Definition forgetful_functor : algebraic_theory_cat ⟶ HSET
  := make_functor _ forgetful_is_functor.

(** * 3. The adjunction *)

Lemma lift_constant_eq
  (T : algebraic_theory)
  {n : nat}
  (f f' : T 0)
  (g : stn 0 → T n)
  (H : f = f')
  : lift_constant n f = f' • g.
Proof.
  induction H.
  refine (maponpaths (subst f) _).
  apply funextfun.
  intro x.
  apply fromempty.
  exact (negnatlthn0 _ (stnlt x)).
Qed.

Section Adjunction.

  Context (A : hSet).
  Context (T : algebraic_theory).

  Definition theory_morphism_to_function
    (F : algebraic_theory_morphism (free_theory A) T)
    : A → (forgetful_functor T : hSet)
    := λ a, F 0 (inr a).

  Definition function_to_theory_morphism_data
    (F : A → (forgetful_functor T : hSet))
    : algebraic_theory_morphism_data (free_theory A) T.
  Proof.
    intros n f.
    induction f as [i | a].
    - exact (var i).
    - exact (lift_constant _ (F a)).
  Defined.

  Lemma function_to_is_theory_morphism
    (F : A → (forgetful_functor T : hSet))
    : is_algebraic_theory_morphism (function_to_theory_morphism_data F).
  Proof.
    use make_is_algebraic_theory_morphism.
    - easy.
    - intros ? ? f ?.
      induction f.
      + exact (!var_subst _ _ _).
      + refine (lift_constant_eq _ _ _ _ (idpath _) @ !_).
        apply subst_subst.
  Qed.

  Definition function_to_theory_morphism
    (F : A → (forgetful_functor T : hSet))
    : algebraic_theory_morphism (free_theory A) T
    := make_algebraic_theory_morphism _ (function_to_is_theory_morphism F).

  Lemma invweqweq
    (F : algebraic_theory_morphism (free_theory A) T)
    : function_to_theory_morphism (theory_morphism_to_function F) = F.
  Proof.
    apply algebraic_theory_morphism_eq.
    intros ? f.
    induction f.
    - exact (!mor_var _ _).
    - refine (lift_constant_eq _ _ _ _ (idpath _) @ _).
      exact (!mor_subst F _ _ : _ = F _ (lift_constant _ _)).
  Qed.

  Lemma weqinvweq
    (F : A → (forgetful_functor T : hSet))
    : theory_morphism_to_function (function_to_theory_morphism F) = F.
  Proof.
    apply funextfun.
    intro.
    refine (lift_constant_eq _ _ _ _ (idpath _) @ _).
    exact (subst_var _ _).
  Qed.

End Adjunction.

Definition free_functor_is_free
  : are_adjoints free_functor forgetful_functor.
Proof.
  use adj_from_nathomweq.
  use tpair.
  - refine (λ A (T : algebraic_theory), _).
    use weq_iso.
    + exact (theory_morphism_to_function A T).
    + exact (function_to_theory_morphism A T).
    + exact (invweqweq A T).
    + exact (weqinvweq A T).
  - abstract (
      use tpair;
      easy
    ).
Defined.

(** * 4. The equivalence between algebras and coslices *)

Section CosliceCatEquivalence.

  Context (S : hSet).

  Definition coslice_functor_base_functor : algebra_cat (free_theory S) ⟶ SET.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro A. exact ((A : algebra _) : hSet).
      + intros A B F.
        exact (F : algebra_morphism _ _).
    - split.
      + abstract (intro A;
                  easy).
      + abstract (intros A B C F G;
                  apply algebra_mor_comp).
  Defined.

  (**
    We define the coslice functor as a lift of the base functor. Note that by from_lifted_functor,
    postcomposing this lift with the forgetful functor (f: A → B) ↦ B gives
    coslice_functor_base_functor again.
   *)
  Definition coslice_functor
    : algebra_cat (free_theory S) ⟶ coslice_cat_total SET S.
  Proof.
    apply (lifted_functor (F:=coslice_functor_base_functor)).
    use tpair.
    - use tpair.
      + intros A s.
        exact (action (T := free_theory S) (n := 0) (inr s) (weqvecfun 0 [()])).
      + abstract (intros A B F;
        apply funextfun;
        intro s;
        refine (mor_action _ _ _ @ _);
        apply (maponpaths (action _));
        apply funextfun;
        intro i; apply (fromstn0 i)).
    - abstract (split; intros; apply funspace_isaset; apply setproperty).
  Defined.

  Definition coslice_to_algebra_morphism_data
    {A B : algebra (free_theory S)}
    (F : coslice_cat_total SET S ⟦ coslice_functor A, coslice_functor B ⟧)
    : A → B
    := coslicecat_mor_morphism _ _ F.

  Lemma coslice_to_is_algebra_morphism
    {A B : algebra (free_theory S)}
    (F : coslice_cat_total SET S ⟦ coslice_functor A, coslice_functor B ⟧)
    : ∏ n f a, mor_action_ax (identity _) (coslice_to_algebra_morphism_data F) (@action _ A) (@action _ B) n f a.
  Proof.
    intros n f a.
    induction f as [i | s].
    - refine (maponpaths _ (var_action _ _ _) @ !_).
      exact (var_action _ _ _).
    - refine (maponpaths _ (subst_action A (inr s) (weqvecfun _ [()]) a) @ !_).
      refine (subst_action B (inr s) (weqvecfun _ [()]) (λ i, coslicecat_mor_morphism _ _ F (a i)) @ !_).
      refine (_ @ eqtohomot (coslicecat_mor_comm _ _ F) s @ _).
      + apply (maponpaths (coslicecat_mor_morphism _ _ F)).
        apply (maponpaths (action (A := A) _)).
        apply funextfun.
        intro i.
        apply (fromstn0 i).
      + apply (maponpaths (action (A := B) _)).
        apply funextfun.
        intro i.
        apply (fromstn0 i).
  Qed.

  Definition coslice_to_algebra_morphism
    {A B : algebra (free_theory S)}
    (F : coslice_cat_total SET S ⟦ coslice_functor A, coslice_functor B ⟧)
    : algebra_morphism A B
    := make_algebra_morphism _ (coslice_to_is_algebra_morphism F).

  Definition fully_faithful_coslice_functor
    : fully_faithful coslice_functor.
  Proof.
    intros A B.
    use isweq_iso.
    - exact coslice_to_algebra_morphism.
    - abstract now (
        intro F;
        apply algebra_morphism_eq
      ).
    - abstract now (
        intro F;
        apply subtypePath;
        [ intro;
          apply homset_property
        | apply idpath ]
      ).
  Defined.

  Definition coslice_to_algebra_data
    (T : coslice_cat_total SET S)
    : algebra_data (free_theory S).
  Proof.
    use make_algebra_data.
    - exact (coslicecat_ob_object _ _ T).
    - intros n f a.
      induction f as [i | s].
      + exact (a i).
      + exact (coslicecat_ob_morphism _ _ T s).
  Defined.

  Lemma coslice_to_is_algebra
    (T : coslice_cat_total SET S)
    : is_algebra (coslice_to_algebra_data T).
  Proof.
    split.
    - intros m n f g a.
      now induction f.
    - easy.
  Qed.

  Definition coslice_to_algebra
    (T : coslice_cat_total SET S)
    : algebra (free_theory S)
    := make_algebra _ (coslice_to_is_algebra T).

  Definition algebra_coslice_equivalence
    : adj_equivalence_of_cats coslice_functor.
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_algebra_cat.
    - exact fully_faithful_coslice_functor.
    - intro T.
      apply hinhpr.
      exists (coslice_to_algebra T).
      apply identity_z_iso.
  Defined.

End CosliceCatEquivalence.
