(**

 Equivalence of fibers

 If we have a fibration `D` over `C`, then every morphism `f : x --> y` induces a
 functor `D[{y}] ⟶ D[{x}]`. If `f` is an isomorphism, then this functor is an
 adjoint equivalence, and we prove that in this file. Note that this statement is
 direct if we assume `C` is univalent, but here we construct the aforementioned
 equivalence without assuming that `C` is univalent.

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Proposition fiber_functor_on_eq_comm
            {C : category}
            {D : disp_cat C}
            (HD : cleaving D)
            {x y : C}
            {f g : x --> y}
            (p : f = g)
            (yy : D[{y}])
  : (fiber_functor_on_eq HD p yy ;; HD _ _ g yy
     =
     transportf
       (λ z, _ -->[ z ] _)
       (p @ !(id_left _))
       (HD _ _ f yy))%mor_disp.
Proof.
  induction p ; cbn.
  rewrite id_left_disp.
  apply idpath.
Qed.

Section FiberFunctorCleavingIso.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D)
          {x y : C}
          (f : z_iso x y).

  Definition fiber_functor_cleaving_of_z_iso_equiv_unit
    : nat_z_iso
        (functor_identity _)
        (fiber_functor_from_cleaving D HD f
         ∙ fiber_functor_from_cleaving D HD (inv_from_z_iso f)).
  Proof.
    refine (nat_z_iso_comp
              _
              (nat_z_iso_inv
                 (fiber_functor_from_cleaving_comp_nat_z_iso
                    HD
                    f
                    (inv_from_z_iso f)))).
    refine (nat_z_iso_comp
              (nat_z_iso_fiber_functor_from_cleaving_identity HD y)
              (fiber_functor_on_eq_nat_z_iso HD _)).
    exact (!(z_iso_after_z_iso_inv f)).
  Defined.

  Definition fiber_functor_cleaving_of_z_iso_equiv_counit
    : nat_z_iso
        (fiber_functor_from_cleaving D HD (inv_from_z_iso f)
         ∙ fiber_functor_from_cleaving D HD f)
        (functor_identity _).
  Proof.
    refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso
                 HD
                 (inv_from_z_iso f)
                 f)
              _).
    refine (nat_z_iso_comp
              (fiber_functor_on_eq_nat_z_iso HD _)
              (nat_z_iso_inv
                 (nat_z_iso_fiber_functor_from_cleaving_identity HD x))).
    exact (z_iso_inv_after_z_iso f).
  Defined.

  Definition fiber_functor_cleaving_of_z_iso_equiv
    : equivalence_of_cats (D[{y}]) (D[{x}]).
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact (fiber_functor_from_cleaving D HD f).
      + exact (fiber_functor_from_cleaving D HD (inv_from_z_iso f)).
      + exact fiber_functor_cleaving_of_z_iso_equiv_unit.
      + exact fiber_functor_cleaving_of_z_iso_equiv_counit.
    - split.
      + intros yy.
        apply (nat_z_iso_pointwise_z_iso fiber_functor_cleaving_of_z_iso_equiv_unit yy).
      + intros xx.
        apply (nat_z_iso_pointwise_z_iso fiber_functor_cleaving_of_z_iso_equiv_counit xx).
  Defined.

  Definition fiber_functor_cleaving_of_z_iso_adj_equiv
    : adj_equivalence_of_cats (fiber_functor_from_cleaving D HD f).
  Proof.
    apply (adjointification fiber_functor_cleaving_of_z_iso_equiv).
  Defined.
End FiberFunctorCleavingIso.
