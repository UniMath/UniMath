(*
  Shows that, given a presheaf P, there exists a presheaf P' with P'(n) = P(S n).
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Presheaves.
Require Import UniMath.AlgebraicTheories.Tuples.

Local Open Scope algebraic_theories.

Definition plus_1_presheaf_data'
  {T : algebraic_theory}
  (P : presheaf T)
  : presheaf_data' T.
Proof.
  - use make_presheaf_data'.
    + exact (λ n, P (1 + n)).
    + intros m n s t.
      refine (action (T := T) (P := P) s _).
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      * refine (t i' • (λ j, pr (stnweq (inl j)))).
      * exact (pr (stnweq (inr i'))).
Defined.

Lemma plus_1_is_presheaf'
  {T : algebraic_theory}
  (P : presheaf T)
  : is_presheaf' (plus_1_presheaf_data' P).
Proof.
  - use make_is_presheaf'.
    + intros l m n x f g.
      refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
      apply (maponpaths (action (x : (P _ : hSet)))).
      apply funextfun.
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      * do 2 refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_).
        apply maponpaths.
        apply funextfun.
        intro.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      * refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    + intros n x.
      refine (_ @ presheaf_identity_projections _ _ _).
      apply (maponpaths (action (x : (P _ : hSet)))).
      apply funextfun.
      intro i.
      refine (_ @ maponpaths _ (homotweqinvweq stnweq i)).
      induction (invmap stnweq i) as [i' | i'].
      * apply algebraic_theory_comp_projects_component.
      * apply idpath.
Qed.

Definition plus_1_presheaf
  {T : algebraic_theory}
  (P : presheaf T)
: presheaf T
:= make_presheaf' _ (plus_1_is_presheaf' P).
