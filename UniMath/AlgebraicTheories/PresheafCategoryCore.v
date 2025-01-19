(**************************************************************************************************

  The category of algebraic theory presheaves

  Defines the category of presheaves for an algebraic theory. First, the category of dependent pairs
  of theories and presheaves is formalized as a stack of displayed categories, then the category of
  presheaves is a fiber of a (repeated) sigma category of this.

  Contents
  1. The dependent product category of theories and presheaves [presheaf_full_cat]
  1.1. The full category of presheaf data [presheaf_data_cat]
  1.1.1. Temporary accessors
  1.2. The full category of presheaves
  1.2.1. A lemma about presheaves [isaprop_full_is_presheaf]
  2. The category of presheaves [presheaf_cat]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.IndexedSetCategory.

Local Open Scope algebraic_theories.
Local Open Scope cat.

Section PresheafCategory.

(** * 1. The dependent product category of theories and presheaves *)
(** ** 1.1. The full category of presheaf data *)

  Definition op_ax
    (T : algebraic_theory)
    (P : indexed_set_cat nat)
    (m n : nat)
    (f : P m)
    (g : stn m → T n)
    : UU
    := P n.

  Definition mor_op_ax
    {T T' : algebraic_theory}
    {P P' : indexed_set_cat nat}
    (F : algebraic_theory_morphism T T')
    (G : indexed_set_cat nat⟦P, P'⟧)
    (op : ∏ m n f g, op_ax T P m n f g)
    (op' : ∏ m n f g, op_ax T' P' m n f g)
    (m n : nat)
    (f : P m)
    (g : stn m → T n)
    : UU
    := G n (op m n f g) = op' m n (G m f) (λ i, F n (g i)).

  Definition presheaf_data_disp_cat
    : disp_cat (cartesian' algebraic_theory_cat (indexed_set_cat nat)).
  Proof.
    use disp_struct.
    - intro X.
      exact (∏ m n f g, op_ax (pr1 X) (pr2 X) m n f g).
    - intros X X' op op' Y.
      exact (∏ m n f g, mor_op_ax (pr1 Y) (pr2 Y) op op' m n f g).
    - abstract (
        intros;
        do 4 (apply impred_isaprop; intro);
        apply setproperty
      ).
    - abstract easy.
    - abstract (
        intros X X' X'' op op' op'' Y Y' HY HY' m n a f;
        exact (maponpaths _ (HY _ _ _ _) @ HY' _ _ _ _)
      ).
  Defined.

  Definition presheaf_data_cat
    : category
    := total_category presheaf_data_disp_cat.

(** *** 1.1.1. Temporary accessors *)

  Let data_theory
    (P : presheaf_data_cat)
    : algebraic_theory
    := pr11 P.

  Let data_set
    (P : presheaf_data_cat)
    : indexed_set_cat nat
    := pr21 P.

  Let data_op
    {P : presheaf_data_cat}
    {m n : nat}
    (f : data_set P m)
    (g : stn m → data_theory P n)
    : op_ax (data_theory P) (data_set P) m n f g
    := pr2 P m n f g.

  Let data_mor_theory
    {P P' : presheaf_data_cat}
    (F : presheaf_data_cat⟦P, P'⟧)
    : algebraic_theory_morphism (data_theory P) (data_theory P')
    := pr11 F.

  Let data_mor_set
    {P P' : presheaf_data_cat}
    (F : presheaf_data_cat⟦P, P'⟧)
    : indexed_set_cat nat⟦data_set P, data_set P'⟧
    := pr21 F.

  Let data_mor_op
    {P P' : presheaf_data_cat}
    (F : presheaf_data_cat⟦P, P'⟧)
    {m n : nat}
    (f : data_set P m)
    (g : stn m → data_theory P n)
    : mor_op_ax (data_mor_theory F) (data_mor_set F) (@data_op P) (@data_op P') m n f g
    := pr2 F m n f g.

(** ** 1.2. The full category of presheaves *)

  Definition op_op_ax
    (T : algebraic_theory)
    (P : indexed_set_cat nat)
    (op : ∏ m n f g, op_ax T P m n f g)
    (l m n : nat)
    (a : P l)
    (f : stn l → T m)
    (g : stn m → T n)
    : UU
    := op m n (op l m a f) g = op l n a (λ i, (f i) • g).

  Definition op_var_ax
    (T : algebraic_theory)
    (P : indexed_set_cat nat)
    (op : ∏ m n f g, op_ax T P m n f g)
    (n : nat)
    (a : P n)
    : UU
    := op n n a var = a.

  Definition full_is_presheaf (P : presheaf_data_cat) : UU :=
    (∏ l m n a f g, op_op_ax (data_theory P) (data_set P) (@data_op P) l m n a f g) ×
    (∏ n a, op_var_ax (data_theory P) (data_set P) (@data_op P) n a).

  Definition presheaf_full_disp_cat
    : disp_cat presheaf_data_cat
    := disp_full_sub presheaf_data_cat full_is_presheaf.

  Definition presheaf_full_cat
    : category
    := total_category presheaf_full_disp_cat.

(** *** 1.2.1. A lemma about presheaves *)

  Lemma isaprop_full_is_presheaf
    (P : presheaf_data_cat)
    : isaprop (full_is_presheaf P).
  Proof.
    repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply setproperty.
  Qed.

End PresheafCategory.

Arguments op_ax /.
Arguments mor_op_ax /.
Arguments op_op_ax /.
Arguments op_op_ax /.

(** * 2. The category of presheaves *)

Definition presheaf_disp_cat
  : disp_cat algebraic_theory_cat
  := sigma_disp_cat (sigma_disp_cat presheaf_full_disp_cat).

Definition presheaf_cat
  (T : algebraic_theory)
  : category
  := fiber_category presheaf_disp_cat T.

Lemma displayed_presheaf_morphism_eq
  {T T' : algebraic_theory}
  {F : algebraic_theory_morphism T T'}
  {P : presheaf_disp_cat T}
  {P' : presheaf_disp_cat T'}
  (G G' : (P : presheaf_disp_cat _) -->[F] P')
  (H : pr1 G = pr1 G')
  : G = G'.
Proof.
  refine (subtypePath _ H).
  intro.
  use (isapropdirprod _ _ _ isapropunit).
  do 4 (apply impred_isaprop; intro).
  apply setproperty.
Qed.
