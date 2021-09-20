(**

    Monads in [sort,C]

Written by Anders Mörtberg, 2021 (adapted from MonadsMultiSorted.v)

*)
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Local Open Scope cat.

Section MonadInSortToC.

Variables (sort : hSet) (C : category) (BC : BinCoproducts C) (TC : Terminal C).

Let sortToC : category := [path_pregroupoid sort,C].
Let hs : has_homsets sortToC := homset_property sortToC.

Local Lemma BinCoproductsSortToC : BinCoproducts sortToC.
Proof.
apply BinCoproducts_functor_precat, BC.
Defined.

Local Lemma TerminalSortToC : Terminal sortToC.
Proof.
apply Terminal_functor_precat, TC.
Defined.

Local Notation "a ⊕ b" := (BinCoproductObject _ (BinCoproductsSortToC a b)).
Local Notation "1" := (TerminalObject TerminalSortToC).

Context {M : Monad sortToC}.

(* We can instantiate the monad laws at a specific sort t *)
Definition sortToC_fun {X Y : sortToC} (f : ∏ t, C⟦pr1 X t,pr1 Y t⟧) : sortToC⟦X,Y⟧ :=
  nat_trans_functor_path_pregroupoid (homset_property _) f.

Definition bind_fun {X Y : sortToC} (f : ∏ t, C⟦pr1 X t,pr1 (M Y) t⟧) :
  ∏ t, C⟦pr1 (M X) t,pr1 (M Y) t⟧ :=
    λ t, pr1 (bind (sortToC_fun f)) t.

Definition η_fun {X : sortToC} (t : sort) : C⟦pr1 X t,pr1 (M X) t⟧ :=
  pr1 (η M X) t.

Lemma η_bind_fun {X Y : sortToC} (f : ∏ t, C⟦pr1 X t,pr1 (M Y) t⟧) (t : sort) :
  η_fun t · bind_fun f t = f t.
Proof.
exact (nat_trans_eq_pointwise (η_bind (sortToC_fun f)) t).
Qed.

Lemma bind_η_fun {X : sortToC} (t : sort) :
  bind_fun η_fun t = pr1 (identity (M X)) t.
Proof.
etrans; [|apply (nat_trans_eq_pointwise (@bind_η _ M X) t)].
apply cancel_postcomposition.
assert (H : sortToC_fun η_fun = η M X).
{ now apply nat_trans_eq; [apply homset_property|]. }
exact (nat_trans_eq_pointwise (maponpaths (λ a, # M a) H) t).
Qed.

Lemma bind_bind_fun {X Y Z : sortToC}
                    (f : ∏ t, C⟦pr1 X t,pr1 (M Y) t⟧)
                    (g : ∏ t, C⟦pr1 Y t, pr1 (M Z) t ⟧)
                    (t : sort) :
  bind_fun f t · bind_fun g t = bind_fun (λ s, f s · bind_fun g s) t.
Proof.
etrans; [apply (nat_trans_eq_pointwise (bind_bind (sortToC_fun f) (sortToC_fun g)) t)|].
apply cancel_postcomposition.
assert (H : sortToC_fun f · bind (sortToC_fun g) = sortToC_fun (λ s, f s · bind_fun g s)).
{ now apply nat_trans_eq; [apply homset_property|]. }
exact (nat_trans_eq_pointwise (maponpaths (λ a, # M a) H) t).
Qed.

(* As the instantiation at a specific sort t does not add much we don't do it for the exchange law *)
Definition monadSubstGen_instantiated {X Y : sortToC} (f : sortToC⟦X,M Y⟧) :
  sortToC⟦M (X ⊕ Y),M Y⟧ := monadSubstGen M BinCoproductsSortToC Y f.

Definition monadSubstGen_fun {X Y : sortToC} (f : ∏ s, C⟦pr1 X s,pr1 (M Y) s⟧) :
  ∏ t, C⟦pr1 (M (X ⊕ Y)) t,pr1 (M Y) t⟧ :=
    λ t, pr1 (monadSubstGen_instantiated (sortToC_fun f)) t.

Definition mweak_instantiated {X Y : sortToC} :
  sortToC⟦M Y,M (X ⊕ Y)⟧ := mweak M BinCoproductsSortToC _ _.

Definition mexch_instantiated {X Y Z : sortToC} :
  sortToC⟦M (X ⊕ (Y ⊕ Z)), M (Y ⊕ (X ⊕ Z))⟧ :=
    mexch M BinCoproductsSortToC _ _ _.

Lemma subst_interchange_law_gen_instantiated {X Y Z : sortToC}
      (f : sortToC⟦X,M (Y ⊕ Z)⟧) (g : sortToC⟦Y, M Z⟧) :
  monadSubstGen_instantiated f · monadSubstGen_instantiated g =
  mexch_instantiated · monadSubstGen_instantiated (g · mweak_instantiated)
                     · monadSubstGen_instantiated (f · monadSubstGen_instantiated g).
Proof.
apply subst_interchange_law_gen.
Qed.

Lemma subst_interchange_law_instantiated {X Y Z : sortToC}
      (f : sortToC⟦1,M (1 ⊕ Z)⟧) (g : sortToC⟦1,M Z⟧) :
  monadSubstGen_instantiated f · monadSubstGen_instantiated g =
  mexch_instantiated · monadSubstGen_instantiated (g · mweak_instantiated)
                     · monadSubstGen_instantiated (f · monadSubstGen_instantiated g).
Proof.
use subst_interchange_law.
Qed.

End MonadInSortToC.
