(*********************************************************************************

 Colimits of 1-types

 Contents:
 1. Initial object
 2. Coproducts

 *********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.

Local Open Scope cat.

(**
 1. Initial object
 *)

(** MOVE ??? *)
Definition empty_hlevel
           (n : nat)
  : isofhlevel (n + 1) ∅.
Proof.
  induction n.
  - exact isapropempty.
  - exact (λ x, fromempty x).
Defined.

Definition empty_one_type
  : one_types
  := (∅ ,, empty_hlevel 2).

Definition biinitial_one_types
  : is_biinitial empty_one_type.
Proof.
  use make_is_biinitial.
  - exact (λ _, fromempty).
  - exact (λ _ _ _ z, fromempty z).
  - exact (λ _ _ _ _ _, funextsec _ _ _ (λ z, fromempty z)).
Defined.

Definition strict_biinitial_one_types
  : is_strict_biinitial_obj empty_one_type.
Proof.
  refine (biinitial_one_types ,, _).
  intros X f.
  use weq_is_adjoint_equivalence.
  apply isweqtoempty.
Defined.

(**
 2. Coproducts
 *)
Definition coprod_one_types
           (X Y : one_type)
  : one_type.
Proof.
  use make_one_type.
  - exact (X ⨿ Y).
  - apply isofhlevelssncoprod.
    + apply X.
    + apply Y.
Defined.

Definition bincoprod_cocone_one_types
           (X Y : one_types)
  : bincoprod_cocone X Y.
Proof.
  use make_bincoprod_cocone.
  - exact (coprod_one_types X Y).
  - exact inl.
  - exact inr.
Defined.

Section CoprodUMP.
  Context (X Y : one_types).

  Definition binprod_cocone_has_binprod_ump_1_one_types
    : bincoprod_ump_1 (bincoprod_cocone_one_types X Y).
  Proof.
    intros Z.
    use make_bincoprod_1cell.
    - cbn ; intro z.
      induction z as [ x | y ].
      + exact (bincoprod_cocone_inl Z x).
      + exact (bincoprod_cocone_inr Z y).
    - use make_invertible_2cell.
      + intro ; apply idpath.
      + apply one_type_2cell_iso.
    - use make_invertible_2cell.
      + intro ; apply idpath.
      + apply one_type_2cell_iso.
  Defined.

  Definition binprod_cocone_has_binprod_ump_2_one_types
    : bincoprod_ump_2 (bincoprod_cocone_one_types X Y).
  Proof.
    intros Z φ ψ α β.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros γ₁ γ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use funextsec ; intro z ;
         induction z as [ x | y ] ;
         [ exact (eqtohomot (pr12 γ₁) x @ !(eqtohomot (pr12 γ₂) x))
         | exact (eqtohomot (pr22 γ₁) y @ !(eqtohomot (pr22 γ₂) y)) ]).
    - simple refine (_ ,, _ ,, _).
      + cbn ; intro z.
        induction z as [ x | y ].
        * exact (α x).
        * exact (β y).
      + abstract
          (use funextsec ;
           intro z ; cbn ;
           apply idpath).
      + abstract
          (use funextsec ;
           intro z ; cbn ;
           apply idpath).
  Defined.

  Definition binprod_cocone_has_binprod_ump_one_types
    : has_bincoprod_ump (bincoprod_cocone_one_types X Y).
  Proof.
    split.
    - exact binprod_cocone_has_binprod_ump_1_one_types.
    - exact binprod_cocone_has_binprod_ump_2_one_types.
  Defined.
End CoprodUMP.

Definition coprod_one_types
  : has_bincoprod one_types
  := λ X Y,
     bincoprod_cocone_one_types X Y
     ,,
     binprod_cocone_has_binprod_ump_one_types X Y.
