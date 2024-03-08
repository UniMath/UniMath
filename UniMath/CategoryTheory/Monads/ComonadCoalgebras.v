(** ***************************************************************

Contents :

  - Definition of the category of coCoalgebras of a comonad

******************************************************************)



Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Comonads.

Local Open Scope cat.

Ltac rewrite_cbn x := let H := fresh in (set (H := x); cbn in H; rewrite H; clear H).
Ltac rewrite_cbn_inv x := let H := fresh in (set (H := x); cbn in H; rewrite <- H; clear H).


Section Coalgebras.

Context {C : category} (T : Comonad C).


(** Definition of an Coalgebra of a monad T *)

Section Coalgebra_def.

Definition Coalgebra_data : UU := ∑ X : C, X --> T X.

#[reversible=no] Coercion Coalg_carrier (X : Coalgebra_data) : C := pr1 X.

Definition Coalg_map (X : Coalgebra_data) : X --> T X := pr2 X.

Definition Coalgebra_laws (X : Coalgebra_data) : UU
  := (Coalg_map X · ε T X  = identity X)
   × (Coalg_map X · δ T X = Coalg_map X · #T (Coalg_map X)).

Definition Coalgebra : UU := ∑ X : Coalgebra_data, Coalgebra_laws X.

#[reversible=no] Coercion Coalgebra_data_from_Coalgebra (X : Coalgebra) : Coalgebra_data := pr1 X.

Definition Coalgebra_idlaw (X : Coalgebra) : Coalg_map X · ε T X = identity X
  := pr1 (pr2 X).

Definition Coalgebra_multlaw (X : Coalgebra) : Coalg_map X · δ T X = Coalg_map X · #T (Coalg_map X)
  := pr2 (pr2 X).

Definition free_Coalgebra (X : C) : Coalgebra.
Proof.
  use tpair.
  - exists (T X).
    exact (δ T X).
  - abstract (split;
              [apply Comonad_law1 |
               apply pathsinv0;
               apply Comonad_law3]).
Defined.

End Coalgebra_def.


(** Data for the category of Coalgebras of the monad T, following FunctorCoalgebras.v *)

Section Coalgebra_precategory_data.

Definition is_Coalgebra_mor {X Y : Coalgebra} (f : X --> Y) : UU
  := f · Coalg_map Y = Coalg_map X · #T f.

Definition Coalgebra_mor (X Y : Coalgebra) : UU
  := ∑ f : X --> Y, is_Coalgebra_mor f.

#[reversible=no] Coercion mor_from_Coalgebra_mor {X Y : Coalgebra} (f : Coalgebra_mor X Y)
  : X --> Y := pr1 f.

Definition Coalgebra_mor_commutes {X Y : Coalgebra} (f : Coalgebra_mor X Y)
  : f · Coalg_map Y = Coalg_map X · #T f := pr2 f.

Definition Coalgebra_mor_id (X : Coalgebra) : Coalgebra_mor X X.
Proof.
  exists (identity X).
  abstract (unfold is_Coalgebra_mor;
            rewrite functor_id, id_right, id_left;
            apply idpath).
Defined.

Definition Coalgebra_mor_comp (X Y Z : Coalgebra) (f : Coalgebra_mor X Y) (g : Coalgebra_mor Y Z)
  : Coalgebra_mor X Z.
Proof.
  exists (f · g).
  abstract (unfold is_Coalgebra_mor;
            rewrite assoc';
            rewrite Coalgebra_mor_commutes;
            rewrite assoc;
            rewrite Coalgebra_mor_commutes;
            rewrite functor_comp, assoc;
            apply idpath).
Defined.

Definition precategory_Coalg_ob_mor : precategory_ob_mor
  := (Coalgebra,, Coalgebra_mor).

Definition precategory_Coalg_data : precategory_data
  := (precategory_Coalg_ob_mor,, Coalgebra_mor_id,, Coalgebra_mor_comp).

End Coalgebra_precategory_data.

End Coalgebras.


(** Definition of the category ComonadCoalg of Coalgebras for T. Requires that C is a category. *)

Section Coalgebra_category.

Context {C : category} (T : Comonad C).

Definition Coalgebra_mor_eq {X Y : Coalgebra T} {f g : Coalgebra_mor T X Y}
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro h.
  apply homset_property.
Defined.

Lemma is_precategory_precategory_Coalg_data : is_precategory (precategory_Coalg_data T).
Proof.
  apply make_is_precategory; intros;
  apply Coalgebra_mor_eq.
  - apply id_left.
  - apply id_right.
  - apply assoc.
  - apply assoc'.
Qed.

Definition ComonadCoalg_precat : precategory := ( _,, is_precategory_precategory_Coalg_data).

Lemma has_homsets_ComonadCoalg : has_homsets ComonadCoalg_precat.
Proof.
  intros X Y.
  apply (isofhleveltotal2 2).
  - apply homset_property.
  - intro f.
    apply isasetaprop.
    apply homset_property.
Qed.

Definition ComonadCoalg: category := ComonadCoalg_precat ,, has_homsets_ComonadCoalg.

End Coalgebra_category.
