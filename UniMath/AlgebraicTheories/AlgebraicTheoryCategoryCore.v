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
  Definition pr_ax
    (T : indexed_set_cat nat)
    (n : nat)
    (i : stn n)
    : UU
    := T n.

  Definition comp_ax
    (T : indexed_set_cat nat)
    (m n : nat)
    (f : T m)
    (g : stn m → T n)
    : UU
    := T n.

  Let mor_pr_ax'
    {T T' : indexed_set_cat nat}
    (F : indexed_set_cat nat⟦T, T'⟧)
    (pr : ∏ n i, pr_ax T n i)
    (pr' : ∏ n i, pr_ax T' n i)
    (n : nat)
    (i : stn n)
    : UU
    := F n (pr n i) = pr' n i.

  Let mor_comp_ax'
    {T T' : indexed_set_cat nat}
    (F : indexed_set_cat nat⟦T, T'⟧)
    (comp : ∏ m n f g, comp_ax T m n f g)
    (comp' : ∏ m n f g, comp_ax T' m n f g)
    (m n : nat)
    (f : T m)
    (g : stn m → T n)
    : UU
    := F n (comp m n f g) = comp' m n (F m f) (λ i, F n (g i)).

  Definition algebraic_theory_data_disp_cat
    : disp_cat (indexed_set_cat nat).
  Proof.
    use disp_struct.
    - refine (λ T, _ × _).
      + exact (∏ n i, pr_ax T n i).
      + exact (∏ m n f g, comp_ax T m n f g).
    - refine (λ T T' Tdata T'data F, _ × _).
      + exact (∏ n i, mor_pr_ax' F (pr1 Tdata) (pr1 T'data) n i).
      + exact (∏ m n f g, mor_comp_ax' F (pr2 Tdata) (pr2 T'data) m n f g).
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

  Let data_pr
    {T : algebraic_theory_data_cat}
    {n : nat}
    (i : stn n)
    : pr_ax (data_set T) n i
    := pr12 T n i.

  Let data_comp
    {T : algebraic_theory_data_cat}
    {m n : nat}
    (f : data_set T m)
    (g : stn m → data_set T n)
    : comp_ax (data_set T) m n f g
    := pr22 T m n f g.

  Let data_mor
    {T T' : algebraic_theory_data_cat}
    (F : T --> T')
    {n : nat}
    : data_set T n → data_set T' n
    := pr1 F n.

  Definition mor_pr_ax
    {T T' : algebraic_theory_data_cat}
    (F : indexed_set_cat nat⟦data_set T, data_set T'⟧)
    (n : nat)
    (i : stn n)
    : UU
    := mor_pr_ax' F (@data_pr T) (@data_pr T') n i.

  Definition mor_comp_ax
    {T T' : algebraic_theory_data_cat}
    (F : indexed_set_cat nat⟦data_set T, data_set T'⟧)
    (m n : nat)
    (f : data_set T m)
    (g : stn m → data_set T n)
    : UU
    := mor_comp_ax' F (@data_comp T) (@data_comp T') m n f g.

  Let data_mor_pr
    {T T' : algebraic_theory_data_cat}
    (F : T --> T')
    {n : nat}
    (i : stn n)
    : mor_pr_ax (@data_mor _ _ F) n i
    := pr12 F n i.

  Let data_mor_comp
    {T T' : algebraic_theory_data_cat}
    (F : T --> T')
    {m n : nat}
    (f : data_set T m)
    (g : stn m → data_set T n)
    : mor_comp_ax (@data_mor _ _ F) m n f g
    := pr22 F m n f g.

(** ** 1.2. The category of algebraic theories  *)

  Definition comp_comp_ax
    (T : algebraic_theory_data_cat)
    (l m n : nat)
    (f_l : data_set T l)
    (f_m : stn l → data_set T m)
    (f_n : stn m → data_set T n)
    : UU
    := data_comp (data_comp f_l f_m) f_n = data_comp f_l (λ t_l, data_comp (f_m t_l) f_n).

  Definition pr_comp_ax
    (T : algebraic_theory_data_cat)
    (m n : nat)
    (i : stn m)
    (f : stn m → data_set T n)
    : UU
    := data_comp (data_pr i) f = f i.

  Definition comp_pr_ax
    (T : algebraic_theory_data_cat)
    (n : nat)
    (f : data_set T n)
    : UU
    := data_comp f data_pr = f.

  Definition is_algebraic_theory (T : algebraic_theory_data_cat) : UU :=
    (∏ l m n f_l f_m f_n, comp_comp_ax T l m n f_l f_m f_n) ×
    (∏ m n i f, pr_comp_ax T m n i f) ×
    (∏ n f, comp_pr_ax T n f).

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
Arguments pr_ax /.
Arguments comp_ax /.
Arguments mor_pr_ax /.
Arguments mor_comp_ax /.
Arguments comp_comp_ax /.
Arguments pr_comp_ax /.
Arguments comp_pr_ax /.
