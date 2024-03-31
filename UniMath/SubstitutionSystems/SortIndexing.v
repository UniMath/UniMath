(** collects the disparate definitions that had been spread over the package SubstitutionSystems

The notations that are used here speed up verification in the downstream files a lot.
TODO: Make all those downstream verifications quick so that the present definitions can be directly used in those downstream files.

author: Ralph Matthes, March 2024
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.

Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Local Open Scope cat.

Section SortIndexing.

  Context (sort : UU) (Hsort : isofhlevel 3 sort).

Section AbstractCat.

  Context (C : category).


(** Define the category of sorts *)
Definition sort_cat : category := path_pregroupoid sort Hsort.

(** This represents "sort → C" *)
(*
Definition sortToC : category := [sort_cat,C].
(* causes plenty of slow downstream verification *)
*)

Notation sortToC := ([path_pregroupoid sort Hsort,C]).

Definition make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

Definition make_sortToC_mor (ξ ξ' : sortToC) (fam : ∏ s: sort, pr1 ξ s --> pr1 ξ' s) : sortToC⟦ξ,ξ'⟧
  := nat_trans_functor_path_pregroupoid fam.

Definition BCsortToC (BC: BinCoproducts C) : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.
Definition BPsortToC (BP: BinProducts C) : BinProducts sortToC := BinProducts_functor_precat _ _ BP.

Definition TsortToC (TC : Terminal C) : Terminal sortToC := Terminal_functor_precat _ _  TC.
Definition IsortToC (IC : Initial C) : Initial sortToC := Initial_functor_precat _ _  IC.

(*
Definition CCsortToC (CC : forall (I : UU), isaset I → Coproducts I C)
  : forall (I : UU), isaset I → Coproducts I sortToC
  := fun I isa => Coproducts_functor_precat I sort_cat C (CC I isa).
(* has slow downstream verification *)
*)
Notation CCsortToC CC := (fun I isa => Coproducts_functor_precat I (path_pregroupoid sort Hsort) C (CC I isa)).

Definition CLsortToC (g : graph) (CL : Colims_of_shape g C) : Colims_of_shape g sortToC
  := ColimsFunctorCategory_of_shape g _ _ CL.
Definition LLsortToC (g : graph) (LL : Lims_of_shape g C) : Lims_of_shape g sortToC
  := LimsFunctorCategory_of_shape g _ _ LL.

(* Definition sortToCC : category := [sortToC, C]. *)
Notation sortToCC := ([sortToC,C]).

Definition BPsortToCC (BP: BinProducts C) : BinProducts sortToCC := BinProducts_functor_precat _ _ BP.

Definition TsortToCC (TC : Terminal C) : Terminal sortToCC := Terminal_functor_precat _ _ TC.

(* Definition sortToC2 : category := [sortToC, sortToC]. *)
Notation sortToC2 := ([sortToC, sortToC]).

Definition BCsortToC2 (BC: BinCoproducts C) : BinCoproducts sortToC2 := BinCoproducts_functor_precat _ _ (BCsortToC BC).

Definition BPsortToC2 (BP: BinProducts C) : BinProducts sortToC2 := BinProducts_functor_precat _ _ (BPsortToC BP).

Definition TsortToC2 (TC : Terminal C): Terminal sortToC2 := Terminal_functor_precat _ _ (TsortToC TC).
Definition IsortToC2 (IC : Initial C): Initial sortToC2 := Initial_functor_precat _ _ (IsortToC IC).

(*
Definition CCsortToC2 (CC : forall (I : UU), isaset I → Coproducts I C)
  : forall (I : UU), isaset I → Coproducts I sortToC2
  := fun I isa => Coproducts_functor_precat I _ _ (CCsortToC CC I isa).
(* has slow downstream verification *)
 *)
Notation CCsortToC2 CC := (fun I isa => Coproducts_functor_precat I _ _ (CCsortToC CC I isa)).

Definition CLsortToC2 (g : graph) (CL : Colims_of_shape g C) : Colims_of_shape g sortToC2
  := ColimsFunctorCategory_of_shape g _ _ (CLsortToC g CL).
Definition LLsortToC2 (g : graph) (LL : Lims_of_shape g C) : Lims_of_shape g sortToC2
  := LimsFunctorCategory_of_shape g _ _ (LLsortToC g LL).

(* Definition sortToC3 : category := [sortToC2, sortToC2]. *)
Notation sortToC3 := ([sortToC2, sortToC2]).

Lemma coproduct_of_functors_sortToC3_mor (CC : forall (I : UU), isaset I → Coproducts I C) (I : UU) (isa : isaset I)
  (F : I → sortToC3) (G G' : sortToC2) (α : sortToC2 ⟦ G, G' ⟧) (ξ : sortToC) (s : sort) :
  pr1 (pr1 (# (coproduct_of_functors I sortToC2 sortToC2 (CCsortToC2 CC _ isa) F) α) ξ) s
  = CoproductOfArrows _ _ _ _ (λ i, pr1 (pr1 (# (pr1 (F i)) α) ξ) s).
Proof.
  apply idpath.
Qed.
(* has slow downstream verification of its type when [CCsortToC2] is presented as definition *)

End AbstractCat.

Notation sortToC C := ([path_pregroupoid sort Hsort,C]).
Notation sortToCC C := ([sortToC C,C]).
Notation sortToC2 C := ([sortToC C, sortToC C]).
Notation sortToC3 C := ([sortToC2 C, sortToC2 C]).

Notation CCsortToC C CC := (fun I isa => Coproducts_functor_precat I (path_pregroupoid sort Hsort) C (CC I isa)).
Notation CCsortToC2 C CC := (fun I isa => Coproducts_functor_precat I _ _ (CCsortToC C CC I isa)).

Section HSET.

  Definition sortToSet : category := sortToC HSET.
  Definition BCsortToSet : BinCoproducts sortToSet := BCsortToC _ BinCoproductsHSET.
  Definition BPsortToSet : BinProducts sortToSet := BPsortToC _ BinProductsHSET.
  Definition TsortToSet : Terminal sortToSet := TsortToC _ TerminalHSET.
  Definition IsortToSet : Initial sortToSet := IsortToC _ InitialHSET.
  Definition CCsortToSet : forall (I : UU), isaset I → Coproducts I sortToSet := CCsortToC HSET CoproductsHSET.
  Definition CLsortToSet (g : graph) : Colims_of_shape g sortToSet := CLsortToC _ g (ColimsHSET_of_shape g).
  Definition LLsortToSet (g : graph) : Lims_of_shape g sortToSet := LLsortToC _ g (LimsHSET_of_shape g).

  Definition sortToSetSet : category := sortToCC HSET.
  Definition BPsortToSetSet : BinProducts sortToSetSet := BPsortToCC _ BinProductsHSET.

  Definition sortToSet2 : category := sortToC2 HSET.
  (* Definition CCsortToSet2 : forall (I : UU), isaset I → Coproducts I sortToSet2 := CCsortToC2 HSET CoproductsHSET. *)
  Definition BPsortToSet2 : BinProducts sortToSet2 := BPsortToC2 _ BinProductsHSET.
  Definition TsortToSet2 : Terminal sortToSet2 := TsortToC2 _ TerminalHSET.

  Definition sortToSet3 : category := sortToC3 HSET.

End HSET.

End SortIndexing.

Notation sortToC sort Hsort C := ([path_pregroupoid sort Hsort, C]).
Notation sortToCC sort Hsort C := ([sortToC sort Hsort C, C]).
Notation sortToC2 sort Hsort C := ([sortToC sort Hsort C, sortToC sort Hsort C]).
Notation sortToC3 sort Hsort C := ([sortToC2 sort Hsort C, sortToC2 sort Hsort C]).

Notation CCsortToC sort Hsort C CC := (fun I isa => Coproducts_functor_precat I (path_pregroupoid sort Hsort) C (CC I isa)).
Notation CCsortToC2 sort Hsort C CC := (fun I isa => Coproducts_functor_precat I _ _ (CCsortToC sort Hsort C CC I isa)).

(*
Lemma Hsort_from_hSet (sort : hSet) : isofhlevel 3 sort.
Proof.
  exact (isofhlevelssnset 1 sort (setproperty sort)).
Qed.
(* causes compilation errors downstream *)
*)
Notation Hsort_from_hSet sort := (isofhlevelssnset 1 sort (setproperty sort)).
