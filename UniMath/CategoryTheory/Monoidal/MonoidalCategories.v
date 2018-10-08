(*
  Monoidal categories

  Based on an implementation by Anthony Bordg.
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 30).

Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).
Notation "( c , d )" := (precatbinprodpair c d).
Notation "( f #, g )" := (precatbinprodmor f g).

Section Monoidal_Precat.

Context {C : precategory} (tensor : C ⊠ C ⟶ C) (I : C).

Notation "X ⊗ Y" := (tensor (X, Y)) (at level 31).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Definition tensor_id {X Y : C} : id X #⊗ id Y = id (X ⊗ Y).
Proof.
  rewrite binprod_id.
  rewrite (functor_id tensor).
  reflexivity.
Defined.

Definition tensor_comp {X Y Z X' Y' Z' : C} (f : X --> Y) (g : Y --> Z) (f' : X' --> Y') (g' : Y' --> Z') : (f · g) #⊗ (f' · g') = f #⊗ f' · g #⊗ g'.
Proof.
  rewrite binprod_comp.
  rewrite (functor_comp tensor).
  reflexivity.
Defined.

Definition is_iso_tensor_iso {X Y X' Y' : C} {f : X --> Y} {g : X' --> Y'} (f_is_iso : is_iso f)
(g_is_iso : is_iso g) : is_iso (f #⊗ g).
Proof.
  exact (functor_on_is_iso_is_iso (is_iso_binprod_iso f_is_iso g_is_iso)).
Defined.

(* I ⊗ - *)
Definition I_pretensor : C ⟶ C.
Proof.
    use tpair.
    - use tpair.
      exact (λ c, I ⊗ c).
      intros ? ? f.
      exact (id I #⊗ f).
    - split.
      + intro.
        simpl.
        apply tensor_id.
      + unfold functor_compax.
        simpl.
        intros.
        replace (id I) with (id I · id I) by (
          rewrite id_left;
          reflexivity
        ).
        rewrite binprod_comp.
        rewrite id_left.
        rewrite (functor_comp tensor).
        reflexivity.
Defined.

(* λ *)
Definition left_unitor : UU :=
  nat_iso I_pretensor (functor_identity C).

(* - ⊗ I *)
Definition I_posttensor : C ⟶ C.
Proof.
    use tpair.
    - use tpair.
      exact (λ c, c ⊗ I).
      intros ? ? f.
      exact (f #⊗ id I).
    - split.
      + intro.
        simpl.
        apply tensor_id.
      + unfold functor_compax.
        simpl.
        intros.
        replace (id I) with (id I · id I) by (
          rewrite id_left;
          reflexivity
        ).
        rewrite binprod_comp.
        rewrite id_left.
        rewrite (functor_comp tensor).
        reflexivity.
Defined.

(* ρ *)
Definition right_unitor : UU :=
  nat_iso I_posttensor (functor_identity C).

(* (- ⊗ =) ⊗ ≡ *)
Definition assoc_left : (C ⊠ C) ⊠ C ⟶ C.
Proof.
  use tpair; [| split].
  - use tpair.
    exact (λ c, (ob1 (ob1 c) ⊗ ob2 (ob1 c)) ⊗ ob2 c).
    intros ? ? f.
    exact ((mor1 (mor1 f) #⊗ mor2 (mor1 f)) #⊗ mor2 f).
  - intro a.
    simpl.
    repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
    do 2 rewrite tensor_id.
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros a b c f g.
    repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
    do 2 rewrite tensor_comp.
    reflexivity.
Defined.

(* - ⊗ (= ⊗ ≡) *)
Definition assoc_right : (C ⊠ C) ⊠ C ⟶ C.
Proof.
  use tpair; [| split].
  - use tpair.
    exact (λ c, ob1 (ob1 c) ⊗ (ob2 (ob1 c) ⊗ ob2 c)).
    intros ? ? f.
    exact (mor1 (mor1 f) #⊗ (mor2 (mor1 f) #⊗ mor2 f)).
  - intro a.
    simpl.
    repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
    do 2 rewrite tensor_id.
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros a b c f g.
    repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
    do 2 rewrite tensor_comp.
    reflexivity.
Defined.

(* α *)
Definition associator : UU :=
  nat_iso assoc_left assoc_right.

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  ∏ (a b : C), pr1 ρ' a #⊗ id b = pr1 α' ((a, I), b) · id a #⊗ pr1 λ' b.

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗ b, c), d) · pr1 α' ((a, b), c ⊗ d) = pr1 α' ((a, b), c) #⊗ id d · pr1 α' ((a, b ⊗ c), d) · id a #⊗ pr1 α' ((b, c), d).

Definition is_strict (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  (is_nat_iso_id λ') × (is_nat_iso_id ρ') × (is_nat_iso_id α').

End Monoidal_Precat.

Definition monoidal_precat : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor,
  (triangle_eq tensor I λ' ρ' α') × (pentagon_eq tensor α').

Section Monoidal_Precat_Accessors.

Context (M : monoidal_precat).

Definition monoidal_precat_precat := pr1 M.

Definition monoidal_precat_tensor := pr1 (pr2 M).

Definition monoidal_precat_unit := pr1 (pr2 (pr2 M)).

Definition monoidal_precat_left_unitor := pr1 (pr2 (pr2 (pr2 M))).

Definition monoidal_precat_right_unitor := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition monoidal_precat_associator := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

Definition monoidal_precat_eq := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

End Monoidal_Precat_Accessors.

Definition strict_monoidal_precat : UU :=
  ∑ M : monoidal_precat, is_strict (monoidal_precat_tensor M) (monoidal_precat_unit M) (monoidal_precat_left_unitor M) (monoidal_precat_right_unitor M) (monoidal_precat_associator M).
