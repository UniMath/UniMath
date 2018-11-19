(** * The precategory of types

This file defines the precategory of types in a fixed universe ([type_precat])
and shows that it has some limits and exponentials.

Author: Langston Barrett (@siddharthist), Feb 2018
*)

(** ** Contents:

- The precategory of types (of a fixed universe) ([type_precat])
- (Co)limits
  - Colimits
    - Initial object ([InitialType])
    - Binary coproducts ([BinCoproductsType])
  - Limits
    - Terminal object ([TerminalType])
    - Binary products ([BinProductsType])
- Exponentials
  - The exponential functor y ↦ yˣ ([exp_functor])
  - Exponentials ([ExponentialsType])
- Isomorphisms and weak equivalences
- Hom functors
  - As a bifunctor ([hom_functor])
  - Covariant ([cov_hom_functor])
  - Contravariant ([contra_hom_functor])
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

(* Basic category theory *)
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

(* (Co)limits *)
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.

(* Exponentials *)
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.

(* Hom functors *)
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.
Local Open Scope functions.

(** ** The precategory of types of a fixed universe *)

Definition type_precat : precategory.
Proof.
  use mk_precategory.
  - use tpair; use tpair.
    + exact UU.
    + exact (λ X Y, X -> Y).
    + exact (λ X, idfun X).
    + exact (λ X Y Z f g, funcomp f g).
  - repeat split; intros; apply idpath.
Defined.

(** ** (Co)limits *)

(** *** Colimits *)

(** **** Initial object ([InitialType]) *)
(** The [empty] type is an initial object for the precategory of types. *)
Lemma InitialType : Initial type_precat.
Proof.
  apply (mk_Initial (empty : ob type_precat)).
  exact iscontrfunfromempty.
Defined.

(** **** Binary coproducts ([BinCoproductsType]) *)
(** The precategory of types has binary coproducts. *)
Lemma BinCoproductsType : BinCoproducts type_precat.
Proof.
  intros X Y.
  use tpair.
  - exact (coprod X Y,, inl,, inr).
  - apply isBinCoproduct'_to_isBinCoproduct.
    intro Z; apply (weqfunfromcoprodtoprod X Y Z).
Defined.

(** *** Limits *)

(** **** Terminal object ([TerminalType]) *)
(** The [unit] type is a terminal object for the precategory of types. *)
Lemma TerminalType : Terminal type_precat.
Proof.
  apply (mk_Terminal (unit : ob type_precat)).
  exact iscontrfuntounit.
Defined.

(** **** Binary products ([BinProductsType]) *)
(** The precategory of types has binary products. *)
Lemma BinProductsType : BinProducts type_precat.
Proof.
  intros X Y.
  use tpair.
  - exact ((X × Y),, dirprod_pr1,, dirprod_pr2).
  - apply isBinProduct'_to_isBinProduct.
    intro; apply (weqfuntoprodtoprod _ X Y).
Defined.

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

(** ** Isomorphisms and weak equivalences *)

(** The following are mostly copied verbatim from
    [CategoryTheory.categories.HSET.MonoEpiIso]. *)

Lemma type_iso_is_equiv (A B : ob type_precat) (f : iso A B) : isweq (pr1 f).
Proof.
  apply (isweq_iso _ (inv_from_iso f)).
  - intro x.
    set (T:=iso_inv_after_iso f).
    set (T':=toforallpaths _ _ _ T). apply T'.
  - intro x.
    apply (toforallpaths _ _ _ (iso_after_iso_inv f)).
Defined.

Lemma hset_iso_equiv (A B : ob type_precat) : iso A B -> A ≃ B.
Proof.
  intro f; use weqpair; [exact (pr1 f)|apply type_iso_is_equiv].
Defined.

(** Given a weak equivalence, we construct an iso. Again mostly unwrapping and
    packing. *)

Lemma type_equiv_is_iso (A B : ob type_precat) (f : A ≃ B) :
           is_iso (C := type_precat) (pr1 f).
Proof.
  apply (is_iso_qinv (C := type_precat) _ (invmap f)).
  split; simpl.
  - apply funextfun; intro; simpl in *.
    unfold compose, identity; simpl.
    apply homotinvweqweq.
  - apply funextfun; intro; simpl in *.
    unfold compose, identity; simpl.
    apply homotweqinvweq.
Defined.

Lemma type_precat_equiv_iso (A B : ob type_precat) : A ≃ B -> iso A B.
Proof.
  intro f.
  use isopair.
  - exact (pr1 f).
  - apply type_equiv_is_iso.
Defined.

(** ** Hom functors *)

Section HomFunctors.

  Context {C : precategory}.

  (** ** As a bifunctor [hom_functor] *)

  Definition hom_functor_data :
    functor_data (precategory_binproduct C^op C) type_precat.
  Proof.
    use mk_functor_data.
    - intros pair; exact (C ⟦ pr1 pair, pr2 pair ⟧).
    - intros x y fg h.
      refine (_ · h · _).
      + exact (pr1 fg).
      + exact (pr2 fg).
  Defined.

  Lemma is_functor_hom_functor_type : is_functor hom_functor_data.
  Proof.
    use dirprodpair.
    - intro; cbn.
      apply funextsec; intro.
      unfold idfun.
      refine (id_right _ @ _).
      apply id_left.
    - intros ? ? ? ? ?; cbn in *.
      apply funextsec; intro; unfold funcomp.
      abstract (do 3 rewrite assoc; reflexivity).
  Defined.

  Definition hom_functor : functor (precategory_binproduct C^op C) type_precat :=
    mk_functor _ is_functor_hom_functor_type.

  Context (c : C).

  (** ** Covariant [cov_hom_functor] *)

  Definition cov_hom_functor : functor C type_precat :=
    functor_fix_fst_arg (C^op) _ _ hom_functor c.

  (** ** Contravariant [contra_hom_functor] *)

  Definition contra_hom_functor : functor (C^op) type_precat :=
    functor_fix_snd_arg (C^op) _ _ hom_functor c.

End HomFunctors.
