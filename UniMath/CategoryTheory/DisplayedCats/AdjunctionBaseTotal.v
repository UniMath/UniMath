Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.limits.initial.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Section AdjunctionBaseTotal.

  Context {C : category} {D : disp_cat C}.

  Notation U := (pr1_category D).
  Context {pfIsRightAdj : is_right_adjoint U}.
  Notation F := (pr1 pfIsRightAdj). (* F is left adjoint of U *)

  Notation TD := (total_category D).

  Definition initial_in_fiber_existence
    : ∏ (x : C) (xx : D (pr1 (F x))), TD⟦ (F x), (pr1 (F x),, xx)⟧.
  Proof.
    intros x xx.
    apply (φ_adj_inv (pr2 pfIsRightAdj)).
    (* set (counit := (pr2 (pr1 (pr2 pfIsRightAdj)))). *)
    set (unit := (pr1 (pr1 (pr2 pfIsRightAdj)))).
    exact ((pr1 unit) x).
  Defined.

  Definition initial_in_fiber_existence' (pf : ∏ (x : C), x = U (F x))
    : ∏ (x : C) (xx : D (pr1 (F x))), D[{pr1 (F x)}] ⟦ pr2 (F x), xx ⟧.
  Proof.
    intros x xx.
    cbn.
    Check (pr2 (initial_in_fiber_existence x xx)).
    set (tmp := (pr1 (initial_in_fiber_existence x xx))).



    cbn in *.

    cbn.


    apply initial_in_fiber_existence.

  (* D[{x}] := fiber_category D x. *)
  Definition existence_leftadjoint  (pf : ∏ (x : C), x = U (F x))
    : ∏ (x : C), isInitial D[{pr1 (F x)}] ((pr2 (F x)) : D[{pr1 (F x)}]).
  Proof.
    intro x.
    intro xx. (* Show that for each xx, there merely exists a unique morphism (pr2 F x) -->[Id] xx *)

    use tpair.
    - apply (pr2 ((initial_in_fiber_existence pf) x xx)).
