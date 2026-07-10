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
  Context (psi : ∏ c, D⟦ L c, X ⟧ → D⟦ L (F c) , X ⟧).
  (* assumption: psi is natural in c *)

  Let Fchain : chain C := initChain O F.
  Variable (CC : ColimCocone Fchain).

  Let LFchain : chain D :=  mapchain L Fchain.

  Let x : LO --> X := InitialArrow LO X.

  (* The following definition gives psi^n (x) *)
  Local Definition iterate_psi_x (n : ℕ) : D ⟦ L (iter_functor F n O), X ⟧.
  Proof.
    induction n; simpl.
    - exact x.
    - use psi; exact IHn.
  Defined.

  Local Definition iterate_psi_x_cocone : cocone LFchain X.
  Proof.
    use make_cocone.
    - use iterate_psi_x.
    - intros n m e; induction e. induction n.
      * use (InitialArrowUnique LO).
      * simpl.
        rewrite <- IHn.
        cbn.
        Search (?a = ?b -> ?c = ?d -> ?x  ?a ?c -> ?x ?b ?d).
