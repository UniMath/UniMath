(** * Other structures in [type_precat] *)

(** ** Contents

  - Exponentials ([Exponentials_Type])
    - The exponential functor y ↦ yˣ ([exp_functor])
    - Exponentials ([ExponentialsType])

*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.PartA.

(* Basic category theory *)
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

(* Exponentials *)
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.categories.Type.Limits.

(** ** Exponentials *)

(** *** Exponential functor *)

Section ExponentialFunctor.
  Context (A : UU). (** This is the object we're ×-ing and ^-ing with *)

  (** To show that [type_precat] has exponentials, we need a right adjoint to the
      functor Y ↦ X × Y for fixed Y. *)
  Local Definition exp_functor_ob (X : UU) : UU := A -> X.
  Local Definition exp_functor_arr (X Y : UU) (f : X -> Y) :
    (A -> X) -> (A -> Y) := λ g, f ∘ g.
  Local Definition exp_functor_data : functor_data type_precat type_precat :=
    functor_data_constr _ _ (exp_functor_ob : type_precat → type_precat)
                            (@exp_functor_arr).

  Lemma exp_functor_is_functor : is_functor exp_functor_data.
  Proof.
    use dirprodpair.
    - intro; reflexivity.
    - intros ? ? ? ? ?; reflexivity.
  Defined.

  Definition exp_functor : functor type_precat type_precat :=
    mk_functor exp_functor_data exp_functor_is_functor.
End ExponentialFunctor.

Lemma ExponentialsType : Exponentials BinProductsType.
Proof.
  intro X.
  unfold is_exponentiable.
  unfold is_left_adjoint.
  refine (exp_functor X,, _).
  unfold are_adjoints.
  use tpair.
  - use dirprodpair.
    + use mk_nat_trans.
      * intro Y; cbn.
        unfold exp_functor_ob.
        exact (flip dirprodpair).
      * intros ? ? ?; reflexivity.
    + use mk_nat_trans.
      * intro Y; cbn.
        unfold exp_functor_ob.
        exact (λ pair, (pr2 pair) (pr1 pair)).
      * intros ? ? ?; reflexivity.
  - use mk_form_adjunction; reflexivity.
Defined.