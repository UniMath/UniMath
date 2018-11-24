(** ***************************************************************

Contents :

  - Definition of the category of algebras of a monad

  - The free-forgetful adjunction between a category C and the
    category of algebras of a monad on C.

******************************************************************)



Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.


Section Algebras.

Context {C : precategory} (T : Monad C).



(** Definition of an algebra of a monad T *)

Section Algebra_def.

Definition Algebra_data : UU := ∑ X : C, T X --> X.

Coercion Alg_carrier (X : Algebra_data) : C := pr1 X.

Definition Alg_map (X : Algebra_data) : T X --> X := pr2 X.

Definition Algebra_laws (X : Algebra_data) : UU
  := (η T X · Alg_map X = identity X)
   × (μ T X · Alg_map X = #T (Alg_map X) · Alg_map X).

Definition Algebra : UU := ∑ X : Algebra_data, Algebra_laws X.

Coercion Algebra_data_from_Algebra (X : Algebra) : Algebra_data := pr1 X.

Definition Algebra_idlaw (X : Algebra) : η T X · Alg_map X = identity X
  := pr1 (pr2 X).

Definition Algebra_multlaw (X : Algebra) : μ T X · Alg_map X = #T (Alg_map X) · Alg_map X
  := pr2 (pr2 X).

Definition free_Algebra (X : C) : Algebra.
Proof.
  use tpair.
  - exists (T X).
    exact (μ T X).
  - split.
    + apply Monad_law1.
    + apply pathsinv0.
      apply Monad_law3.
Defined.

End Algebra_def.


(** Data for the category of algebras of the monad T, following FunctorAlgebras.v *)

Section Algebra_precategory_data.

Definition is_Algebra_mor {X Y : Algebra} (f : X --> Y) : UU
  := Alg_map X · f = #T f · Alg_map Y.

Definition Algebra_mor (X Y : Algebra) : UU
  := ∑ f : X --> Y, is_Algebra_mor f.

Coercion mor_from_Algebra_mor (X Y : Algebra) (f : Algebra_mor X Y)
  : X --> Y := pr1 f.

Definition Algebra_mor_commutes (X Y : Algebra) (f : Algebra_mor X Y)
  : Alg_map X · f = #T f · Alg_map Y := pr2 f.

Definition Algebra_mor_id (X : Algebra) : Algebra_mor X X.
Proof.
  exists (identity X).
  unfold is_Algebra_mor.
  rewrite functor_id, id_right, id_left.
  apply idpath.
Defined.

Definition Algebra_mor_comp (X Y Z : Algebra) (f : Algebra_mor X Y) (g : Algebra_mor Y Z)
  : Algebra_mor X Z.
Proof.
  exists (f · g).
  unfold is_Algebra_mor.
  rewrite assoc.
  rewrite Algebra_mor_commutes.
  rewrite <- assoc.
  rewrite Algebra_mor_commutes.
  rewrite functor_comp, assoc.
  apply idpath.
Defined.

Definition precategory_Alg_ob_mor : precategory_ob_mor
  := (Algebra,, Algebra_mor).

Definition precategory_Alg_data : precategory_data
  := (precategory_Alg_ob_mor,, Algebra_mor_id,, Algebra_mor_comp).

End Algebra_precategory_data.


(** Definition of the category MonadAlg of algebras for T. Requires that C is a category. *)

Section Algebra_category.

Context {hs : has_homsets C}.

Definition Algebra_mor_eq {X Y : Algebra} {f g : Algebra_mor X Y}
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro h. apply hs.
Defined.

Lemma is_precategory_precategory_Alg_data : is_precategory precategory_Alg_data.
Proof.
  apply mk_is_precategory; intros;
  apply Algebra_mor_eq.
  - apply id_left.
  - apply id_right.
  - apply assoc.
  - apply assoc'.
Defined.

Definition MonadAlg : precategory := ( _,, is_precategory_precategory_Alg_data).

Lemma has_homsets_MonadAlg : has_homsets MonadAlg.
Proof.
  intros X Y.
  apply (isofhleveltotal2 2).
  - apply hs.
  - intro f.
    apply isasetaprop.
    apply hs.
Defined.


(** Adjunction between MonadAlg and C, with right adjoint the forgetful functor
   and left adjoint the free algebra functor. *)

Section Algebra_adjunction.

Definition forget_Alg_data : functor_data MonadAlg C.
Proof.
  exists (fun X => (X : Algebra)).
  intros X Y f.
  apply f.
Defined.

(* forgetful functor from MonadAlg to its underlying category *)

Definition forget_Alg : functor MonadAlg C.
Proof.
  exists forget_Alg_data.
  split; red; intros; apply idpath.
Defined.

Definition free_Alg_data : functor_data C MonadAlg.
Proof.
  exists free_Algebra.
  intros X Y f.
  exists (#T f).
  intermediate_path (#(T □ T) f · (μ T) Y).
  - apply pathsinv0.
    apply (nat_trans_ax (μ T)).
  - apply idpath.
Defined.

(* free T-algebra functor on C *)

Definition free_Alg : functor C MonadAlg.
Proof.
  exists free_Alg_data.
  split; red; intros.
  - apply subtypePairEquality'.
    + apply functor_id.
    + apply hs.
  - apply subtypePairEquality'.
    + apply functor_comp.
    + apply hs.
Defined.

Lemma free_forgetful_are_adjoints : are_adjoints free_Alg forget_Alg.
Proof.
  use mk_are_adjoints.
  - apply (mk_nat_trans _ _ (η T)).
    intros X Y f.
    apply η.
  - use mk_nat_trans.
    + intro X.
      exact (Alg_map (X : Algebra),, Algebra_multlaw X).
    + intros X Y f.
      apply Algebra_mor_eq; cbn.
      apply pathsinv0.
      apply f.
  - split; intro X.
    + apply Algebra_mor_eq; cbn.
      apply Monad_law2.
    + apply Algebra_idlaw.
Defined.

Lemma forget_free_is_T : forget_Alg □ free_Alg = T.
Proof.
  apply functor_eq.
  - exact hs.
  - apply idpath.
Defined.

Lemma Alg_adjunction_monad_eq : Monad_from_adjunction free_forgetful_are_adjoints = T.
Proof.
  apply Monad_eq_raw_data.
  - exact hs.
  - apply idpath.
Defined.

End Algebra_adjunction.

End Algebra_category.

End Algebras.
