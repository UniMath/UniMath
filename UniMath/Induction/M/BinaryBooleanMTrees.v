(** ** Exemple of construction of M Types using ComputationalMWithSets

    Author : Antoine Fisse (@AextraT), 2025
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.Induction.FunctorCoalgebras_legacy.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.
Require Import UniMath.Induction.M.ComputationalM.
Require Import UniMath.Induction.M.ComputationalMWithSets.
Require Import UniMath.Induction.M.MWithSets.
Require Import UniMath.Induction.M.FinalCoalgebraHSET.

Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Chains.OmegaContPolynomialFunctors.
Require UniMath.CategoryTheory.FunctorCoalgebras.

Local Open Scope cat.

Local Definition A := setcoprod unitset boolset.
Local Definition B : pr1hSet A -> SET :=
  λ a, match a with
       | ii1 _ => emptyset
       | ii2 _ => setcoprod unitset unitset
       end.

Local Definition F := MWithSets.F B.
Local Definition F' := MWithSets.F' B.

(* The final coalgebra obtained corresponds to the type of possibly infinite binary trees labeled with booleands. *)
Local Definition C' := pr1 (GetMType_HSET B).
Local Definition C'_isfinal := pr2 (GetMType_HSET B).

Local Definition C'1 := ComputationalMWithSets.C' B C' C'_isfinal.
Local Definition C'1_isfinal : isTerminal (CoAlg_category F') C'1 := ComputationalMWithSets.finalC' B C' C'_isfinal.
Local Definition corec_C1 := ComputationalMWithSets.corecC B C' C'_isfinal.
Local Definition c1 := pr11 C'1.
Local Definition destr_c1 := pr2 C'1.

Lemma Get_list_at_depth (t : c1) (depth : nat) : list bool.
Proof.
  assert (l : list c1). (* List of subtrees at given depth *)
  {
    induction depth.
    - exact (cons t nil).
    - exact (list_ind
               (λ _, list c1)
               nil
               (λ t0 _ acc, match destr_c1 t0 with
                            | (ii1 _,, _) => acc
                            | (ii2 _,, f) => cons (f (ii1 tt)) (cons (f (ii2 tt)) acc)
                            end)
               IHdepth).
  }
  exact (list_ind
           (λ _, list bool)
           nil
           (λ t0 _ acc, match destr_c1 t0 with
                        | (ii1 _,, _) => acc
                        | (ii2 b,, _) => cons b acc
                        end)
           l).
Defined.

(* Full tree only labeled true *)
Definition t0 : c1.
Proof.
  set (c := unit).
  set (s_c := λ _ : c, (ii2 true,, λ _, tt) : F c).
  exact (corec_C1 (c,, s_c) tt).
Defined.

Lemma only_true : Get_list_at_depth t0 4 = functionToList 16 (λ _, true).
Proof.
  apply idpath.
Defined.

(*       true
        /    \
     false   true
    /       /    \
  true   true   false
*)
Definition t1 : c1.
Proof.
  set (c := nat).
  set (a0 := ii2 true : A).
  set (a1 := ii2 false : A).
  set (a2 := ii2 true : A).
  set (s_c := λ x : c, match x with
                       | 0 => (a0,, λ y : pr1hSet (B a0), match y with
                                                         | ii1 _ => 1
                                                         | ii2 _ => 2
                                                         end : c)
                       | 1 => (a1,, λ y : pr1hSet (B a1), match y with
                                                         | ii1 _ => 3
                                                         | ii2 _ => 5
                                                         end : c)
                       | 2 => (a2,, λ y : pr1hSet (B a2), match y with
                                                        | ii1 _ => 3
                                                        | ii2 _ => 4
                                                        end : c)
                       | 3 => (ii2 true,, λ _, 5)
                       | 4 => (ii2 false,, λ _, 5)
                       | _ => (ii1 tt,, λ _, 5)
                       end : F c).
  exact (corec_C1 (c,, s_c) 0).
Defined.

Lemma row2 : Get_list_at_depth t1 2 = cons true (cons true (cons false nil)).
Proof.
  apply idpath.
Defined.
