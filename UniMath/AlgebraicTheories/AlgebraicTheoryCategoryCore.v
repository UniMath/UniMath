(**************************************************************************************************

  The category of algebraic theories

  Defines the category of algebraic theories. The category is formalized via a stack of displayed
  categories.

  Contents
  1. The category of algebraic theories [algebraic_theory_cat]
  1.1. The category of algebraic theory data [algebraic_theory_data_cat]
  1.1.1. Temporary accessors
  1.2. The category of algebraic theories
  1.2.1. Temporary accessors
  1.2.2. A lemma about algebraic theories [isaprop_is_algebraic_theory]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.IndexedSetCategory.

Local Open Scope cat.

(** * 1. The category of algebraic theories *)

Section AlgebraicTheoryCategory.

(** ** 1.1. The category of algebraic theory data *)

  (* The suffix '_ax' for 'axiom' makes sense for descriptions of properties that are hProps. *)
  (* I am, however, still searching for a better naming scheme for non-propositional properties. *)
  Definition var_ax
    (T : indexed_set_cat nat)
    (n : nat)
    (i : stn n)
    : UU
    := T n.

  Definition subst_ax
    (T : indexed_set_cat nat)
    (m n : nat)
    (f : T m)
    (g : stn m → T n)
    : UU
    := T n.

  Let mor_var_ax'
    {T T' : indexed_set_cat nat}
    (F : indexed_set_cat nat⟦T, T'⟧)
    (var : ∏ n i, var_ax T n i)
    (var' : ∏ n i, var_ax T' n i)
    (n : nat)
    (i : stn n)
    : UU
    := F n (var n i) = var' n i.

  Let mor_subst_ax'
    {T T' : indexed_set_cat nat}
    (F : indexed_set_cat nat⟦T, T'⟧)
    (subst : ∏ m n f g, subst_ax T m n f g)
    (subst' : ∏ m n f g, subst_ax T' m n f g)
    (m n : nat)
    (f : T m)
    (g : stn m → T n)
    : UU
    := F n (subst m n f g) = subst' m n (F m f) (λ i, F n (g i)).

  Definition algebraic_theory_data_disp_cat
    : disp_cat (indexed_set_cat nat).
  Proof.
    use disp_struct.
    - refine (λ T, _ × _).
      + exact (∏ n i, var_ax T n i).
      + exact (∏ m n f g, subst_ax T m n f g).
    - refine (λ T T' Tdata T'data F, _ × _).
      + exact (∏ n i, mor_var_ax' F (pr1 Tdata) (pr1 T'data) n i).
      + exact (∏ m n f g, mor_subst_ax' F (pr2 Tdata) (pr2 T'data) m n f g).
    - abstract (
        intros;
        apply isapropdirprod;
        repeat (apply impred_isaprop; intro);
        apply setproperty
      ).
    - abstract easy.
    - abstract (
        intros T T' T'' Tdata T'data T''data F F' Fdata F'data;
        split;
        [ intros n i;
          exact (maponpaths _ (pr1 Fdata _ _) @ pr1 F'data _ _)
        | intros m n f g;
          refine (maponpaths _ (pr2 Fdata _ _ _ _) @ pr2 F'data _ _ _ _) ]
      ).
  Defined.

  Definition algebraic_theory_data_cat
    : category
    := total_category algebraic_theory_data_disp_cat.

(** *** 1.1.1. Temporary accessors *)

  Let data_set
    (T : algebraic_theory_data_cat)
    : nat → hSet
    := pr1 T.

  Let data_var
    {T : algebraic_theory_data_cat}
    {n : nat}
    (i : stn n)
    : var_ax (data_set T) n i
    := pr12 T n i.

  Let data_subst
    {T : algebraic_theory_data_cat}
    {m n : nat}
    (f : data_set T m)
    (g : stn m → data_set T n)
    : subst_ax (data_set T) m n f g
    := pr22 T m n f g.

  Let data_mor
    {T T' : algebraic_theory_data_cat}
    (F : T --> T')
    {n : nat}
    : data_set T n → data_set T' n
    := pr1 F n.

  Local Definition mor_var_ax
    {T T' : algebraic_theory_data_cat}
    (F : indexed_set_cat nat⟦data_set T, data_set T'⟧)
    (n : nat)
    (i : stn n)
    : UU
    := mor_var_ax' F (@data_var T) (@data_var T') n i.

  Local Definition mor_subst_ax
    {T T' : algebraic_theory_data_cat}
    (F : indexed_set_cat nat⟦data_set T, data_set T'⟧)
    (m n : nat)
    (f : data_set T m)
    (g : stn m → data_set T n)
    : UU
    := mor_subst_ax' F (@data_subst T) (@data_subst T') m n f g.

  Let data_mor_var
    {T T' : algebraic_theory_data_cat}
    (F : T --> T')
    {n : nat}
    (i : stn n)
    : mor_var_ax (@data_mor _ _ F) n i
    := pr12 F n i.

  Let data_mor_subst
    {T T' : algebraic_theory_data_cat}
    (F : T --> T')
    {m n : nat}
    (f : data_set T m)
    (g : stn m → data_set T n)
    : mor_subst_ax (@data_mor _ _ F) m n f g
    := pr22 F m n f g.

(** ** 1.2. The category of algebraic theories  *)

  Local Definition subst_subst_ax
    (T : algebraic_theory_data_cat)
    (l m n : nat)
    (f_l : data_set T l)
    (f_m : stn l → data_set T m)
    (f_n : stn m → data_set T n)
    : UU
    := data_subst (data_subst f_l f_m) f_n = data_subst f_l (λ t_l, data_subst (f_m t_l) f_n).

  Local Definition var_subst_ax
    (T : algebraic_theory_data_cat)
    (m n : nat)
    (i : stn m)
    (f : stn m → data_set T n)
    : UU
    := data_subst (data_var i) f = f i.

  Local Definition subst_var_ax
    (T : algebraic_theory_data_cat)
    (n : nat)
    (f : data_set T n)
    : UU
    := data_subst f data_var = f.

  Local Definition is_algebraic_theory (T : algebraic_theory_data_cat) : UU :=
    (∏ l m n f_l f_m f_n, subst_subst_ax T l m n f_l f_m f_n) ×
    (∏ m n i f, var_subst_ax T m n i f) ×
    (∏ n f, subst_var_ax T n f).

  Definition algebraic_theory_disp_cat
    : disp_cat algebraic_theory_data_cat
    := disp_full_sub algebraic_theory_data_cat is_algebraic_theory.

  Definition algebraic_theory_cat
    : category
    := total_category algebraic_theory_disp_cat.

(** *** 1.2.2. A lemma about algebraic theories *)

  Lemma isaprop_is_algebraic_theory (T : algebraic_theory_data_cat) : isaprop (is_algebraic_theory T).
  Proof.
    repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply setproperty.
  Qed.

End AlgebraicTheoryCategory.

(* The _ax definitions are mainly for ease of defining stuff. *)
(* The Arguments commands here make sure that they are unfolded as soon as possible. *)
Arguments var_ax /.
Arguments subst_ax /.
Arguments mor_var_ax /.
Arguments mor_subst_ax /.
Arguments subst_subst_ax /.
Arguments var_subst_ax /.
Arguments subst_var_ax /.
