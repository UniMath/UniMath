Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Declare Scope algebraic_theories.

Local Open Scope cat.
Local Open Scope algebraic_theories.


(* Definition of the base category of functors *)

Definition base_functor_category
  : category
  := [finite_set_skeleton_category, HSET].

Definition base_functor
  : UU
  := finite_set_skeleton_category ⟶ HSET.

Coercion base_functor_to_functor (T : base_functor) : finite_set_skeleton_category ⟶ HSET := T.

Definition base_nat_trans
  (T T' : base_functor)
  : UU
  := T ⟹ T'.

Coercion base_nat_trans_to_nat_trans
  (T T' : base_functor)
  (F : base_nat_trans T T')
  : T ⟹ T'
  := F.


(* Definition of the category of 'pointed functors' *)

Definition pointed_functor_disp_cat
  : disp_cat base_functor_category.
Proof.
  use disp_struct.
  - intro T.
    exact ((T : base_functor) 1 : hSet).
  - intros T T' Tdata T'data F.
    exact ((F : base_nat_trans _ _) _ Tdata = T'data).
  - abstract (intros; apply setproperty).
  - now intros.
  - intros T T' T'' e e' e'' F F' HF HF'.
    now rewrite (!HF'), (!HF).
Defined.

Definition pointed_functor_cat
  : category
  := total_category pointed_functor_disp_cat.

Definition pointed_functor
  : UU
  := ∑ (T : base_functor), (T 1 : hSet).

Coercion pointed_functor_to_base_functor (T : pointed_functor) : base_functor := pr1 T.

Definition id_pr {T : pointed_functor} : (T 1 : hSet) := pr2 T.

Definition pointed_functor_morphism
  (T T' : pointed_functor)
  : UU
  := ∑ (F : T ⟹ T'), F _ id_pr = id_pr.

Coercion pointed_functor_morphism_to_nat_trans {T T' : pointed_functor} (F : pointed_functor_morphism T T') : nat_trans T T' := pr1 F.

(* Accessor for the projections *)
Definition pr {T : pointed_functor} {n : nat} (i : stn n) : (T n : hSet) := # T (λ _, i) id_pr.


(* Definition of the category of algebraic theory data *)

Definition algebraic_theory_data_disp_cat
  : disp_cat pointed_functor_cat.
Proof.
  use disp_struct.
  - exact (λ (T : pointed_functor), ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet)).
  - exact (λ T T' Tdata T'data (F : pointed_functor_morphism T T'),
      ∏ m n f g, (F _ (Tdata m n f g)) = T'data m n (F _ f) (λ i, F _ (g i))).
  - intros.
    repeat (apply impred_isaprop; intro).
    apply setproperty.
  - now intros.
  - intros T T' T'' Tdata T'data T''data F F' Fdata F'data.
    cbn.
    intros.
    now rewrite Fdata, F'data.
Defined.

Definition algebraic_theory_data_cat
  : category
  := total_category algebraic_theory_data_disp_cat.

Definition algebraic_theory_data
  : UU
  := ∑ (T : pointed_functor), ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet).

Coercion algebraic_theory_data_to_pointed_functor (T : algebraic_theory_data) : pointed_functor := pr1 T.

(* Accessor for the composition *)
Definition comp {T : algebraic_theory_data} {m n : nat} : ((T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet)) := pr2 T m n.

Notation "f • g" :=
  (comp f g)
  (at level 35) : algebraic_theories.

Definition algebraic_theory_data_morphism
  (T T' : algebraic_theory_data)
  : UU
  := ∑ (F : pointed_functor_morphism T T'), ∏ m n f g, (F n (f • g)) = (F m f) • (λ i, F n (g i)).

Coercion algebraic_theory_data_morphism_to_pointed_functor_morphism {T T' : algebraic_theory_data} (F : algebraic_theory_data_morphism T T') : pointed_functor_morphism T T' := pr1 F.


(* Definition of the category of algebraic theories with data and properties *)

Definition comp_is_assoc (T : algebraic_theory_data) : UU := ∏
  (l m n : nat)
  (f_l : (T l : hSet))
  (f_m : stn l → T m : hSet)
  (f_n : stn m → T n : hSet),
    (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n).

Definition comp_is_unital (T : algebraic_theory_data) : UU := ∏
  (n : nat)
  (f : (T n : hSet)),
    id_pr • (λ _, f) = f.

Definition comp_identity_projections (T : algebraic_theory_data) : UU := ∏
  (n : nat)
  (f : (T n : hSet)),
    f • (λ i, pr i) = f.

Definition comp_is_natural_l (T : algebraic_theory_data) : UU := ∏
  (m m' n : finite_set_skeleton_category)
  (a : finite_set_skeleton_category⟦m, m'⟧)
  (f : (T m : hSet))
  (g : stn m' → T n : hSet),
  (# T a f) • g = f • (λ i, g (a i)).

Definition is_algebraic_theory (T : algebraic_theory_data) : UU :=
  comp_is_assoc T ×
  comp_is_unital T ×
  comp_identity_projections T ×
  comp_is_natural_l T.

Definition algebraic_theory_disp_cat
  : disp_cat algebraic_theory_data_cat.
Proof.
  use disp_struct.
  - exact is_algebraic_theory.
  - intros.
    exact unit.
  - intros.
    exact isapropunit.
  - now intros.
  - intros.
    exact tt.
Defined.

Definition algebraic_theory : UU := ∑ (T : algebraic_theory_data), is_algebraic_theory T.

Coercion algebraic_theory_to_algebraic_theory_data (T : algebraic_theory) : algebraic_theory_data := pr1 T.

Definition algebraic_theory_morphism
  (T T' : algebraic_theory)
  : UU
  := algebraic_theory_data_morphism T T'.

(* Constructors for the algebraic theory type *)
Definition make_algebraic_theory_data
  (T : base_functor)
  (id_pr : (T 1 : hSet))
  (comp : ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet))
  : algebraic_theory_data
  := ((T ,, id_pr) ,, comp).

Definition make_is_algebraic_theory
  (T : algebraic_theory_data)
  (H1 : comp_is_assoc T)
  (H2 : comp_is_unital T)
  (H3 : comp_identity_projections T)
  (H4 : comp_is_natural_l T)
  : is_algebraic_theory T
  := (H1 ,, H2 ,, H3 ,, H4).

Definition make_algebraic_theory
  (T : algebraic_theory_data)
  (H : is_algebraic_theory T)
  : algebraic_theory
  := T ,, H.

