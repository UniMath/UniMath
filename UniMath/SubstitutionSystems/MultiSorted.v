(**

Definition of multisorted binding signatures.

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
(* Require Import UniMath.SubstitutionSystems.Notation. *)

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section move_upstream.

Lemma horcomp_id_prewhisker {C D E : precategory} (hsE : has_homsets E)
  (X : functor C D) (Z Z' : functor D E) (f : nat_trans Z Z') :
  hor_comp (nat_trans_id X) f = pre_whisker _ f.
Proof.
apply (nat_trans_eq hsE).
simpl.
intro x.
now rewrite functor_id, id_right.
Qed.

End move_upstream.

Section preamble.

Context {C D E : precategory} {hsE : has_homsets E}.

Lemma functor_swap : functor C [D,E,hsE] → functor D [C,E,hsE].
Proof.
intros F.
mkpair.
- mkpair.
  + intro d; simpl.
  { mkpair.
    - mkpair.
      + intro c.
        apply (pr1 (F c) d).
        + intros a b f; apply (# F f).
          - abstract (split;
            [ now intro x; simpl; rewrite (functor_id F)
            | now intros a b c f g; simpl; rewrite (functor_comp F)]).
  }
  + intros a b f; simpl.
  { mkpair.
    - intros x; apply (# (pr1 (F x)) f).
    - abstract (intros c d g; simpl; apply pathsinv0, nat_trans_ax).
  }
- abstract (split;
  [ intros d; simpl;
    apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]; simpl;
    apply funextsec; intro c; apply functor_id
  | intros a b c f g; simpl;
    apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]; simpl;
    apply funextsec; intro x; apply functor_comp ]).
Defined.

Lemma functor_cat_swap : functor [C, [D, E, hsE], functor_category_has_homsets _ _ hsE]
                                 [D, [C, E, hsE], functor_category_has_homsets _ _ hsE].
Proof.
mkpair.
- apply (tpair _ functor_swap); simpl.
  intros F G α.
  mkpair.
  + intros d; simpl.
    mkpair.
    * intro c; apply (α c).
    * abstract (intros a b f; apply (nat_trans_eq_pointwise (nat_trans_ax α _ _ f) d)).
  + abstract (intros a b f; simpl;
              apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]; simpl;
              apply funextsec; intro c; apply nat_trans_ax).
- abstract (split;
  [ intro F; simpl; apply subtypeEquality;
      [ intro x; apply isaprop_is_nat_trans, (functor_category_has_homsets _ _ hsE)|]; simpl;
    apply funextsec; intro d;
    now apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]
  | intros F G H α β; simpl in *; apply subtypeEquality;
      [ intro x; apply isaprop_is_nat_trans, (functor_category_has_homsets _ _ hsE)|]; simpl;
    apply funextsec; intro d;
    now apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ hsE) |]]).
Defined.

End preamble.

(** * Discrete categories *)
Section DiscreteCategory.

Variable (A : UU).

Definition DiscPrecat_data : precategory_data.
Proof.
mkpair.
- apply (A,,paths).
- mkpair; [ apply idpath | apply @pathscomp0 ].
Defined.

Definition is_precategory_DiscPrecat_data : is_precategory DiscPrecat_data.
Proof.
split; [split|]; trivial; intros.
+ apply pathscomp0rid.
+ apply path_assoc.
Qed.

Definition DiscPrecat : precategory :=
  (DiscPrecat_data,,is_precategory_DiscPrecat_data).

Lemma has_homsets_DiscPrecat (H : isofhlevel 3 A) : has_homsets DiscPrecat.
Proof.
intros ? ? ? ? ? ?; apply H.
Qed.

End DiscreteCategory.

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variable (sort : UU).
Variable (eq : isdeceq sort). (* Can we eliminate this assumption? *)

Let sort_cat : precategory := DiscPrecat sort.
Let sortToHSET : precategory := [sort_cat,HSET,has_homsets_HSET].

Lemma has_homsets_sortToHSET : has_homsets sortToHSET.
Proof.
apply functor_category_has_homsets.
Qed.

Local Definition BinProductsSortToHSETToHSET : BinProducts [sortToHSET,HSET,has_homsets_HSET].
Proof.
apply (BinProducts_functor_precat _ _ BinProductsHSET).
Defined.

Local Definition CoproductsSortToHSET I (hI : isaset I) : Coproducts I sortToHSET.
Proof.
now apply Coproducts_functor_precat, Coproducts_HSET.
Defined.

Local Definition CoproductsSortToHSET2 I (hI : isaset I) :
  Coproducts I [sortToHSET, sortToHSET, has_homsets_sortToHSET].
Proof.
now apply Coproducts_functor_precat, CoproductsSortToHSET.
Defined.

Lemma functor_sort_cat (D : precategory) (f : sort → D) : functor sort_cat D.
Proof.
mkpair.
+ mkpair.
  - apply f.
  - intros s t []; apply identity.
+ abstract (now split; [intro|intros a b c [] []; simpl; rewrite id_left]).
Defined.

Definition mk_sortToHSET (f : sort → HSET) : sortToHSET.
Proof.
apply (functor_sort_cat _ f).
(* mkpair. *)
(* + apply (tpair _ f). *)
(*   intros a b hab; simpl; apply (transportf f hab). *)
(* + abstract (now split; [ intros a; apply idpath | intros a b c [] [] ]). *)
Defined.

(* Coercion sortToHsetToFun (s : sortToHSET) : sort → HSET := pr1 s. *)

Definition MSig : UU :=
  Π (s : sort), Σ (I : UU), (I → list (list sort × sort)) × (isaset I).

Definition indices (M : MSig) : sort → UU := fun s => pr1 (M s).

Definition args (M : MSig) (s : sort) : indices M s → list (list sort × sort) :=
  pr1 (pr2 (M s)).

Lemma isaset_indices (M : MSig) (s : sort) : isaset (indices M s).
Proof.
apply (pr2 (pr2 (M s))).
Qed.

Local Notation "'1'" := (TerminalHSET).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BinCoproductsHSET a b)) (at level 50).

(* Definition option : sort -> sortToHSET -> sortToHSET. *)
(* Proof. *)
(* intros s f. *)
(* apply mk_sortToHSET; intro t. *)
(* induction (eq s t) as [H|H]. *)
(* - apply (pr1 f t ⊕ 1). (* TODO: Can one add a coercion to make this look like sort -> Set *) *)
(* - apply (pr1 f t). *)
(* Defined. *)

Definition option_functor_data  (s : sort) : functor_data sortToHSET sortToHSET.
Proof.
mkpair.
+ intro f.
  apply mk_sortToHSET; intro t.
  induction (eq s t) as [H|H].
  * apply (pr1 f t ⊕ 1). (* TODO: Can one add a coercion to make this look like sort -> Set *)
  * apply (pr1 f t).
+ intros F G α.
  mkpair.
  * simpl; intro t.
    induction (eq s t) as [p|p]; simpl; clear p.
    { apply (coprodf (α t) (idfun unit)). }
    { apply α. }
  * abstract (intros t1 t2 []; apply idpath).
Defined.

Lemma is_functor_option_functor s : is_functor (option_functor_data s).
Proof.
split.
+ intros F; simpl in *.
  apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]; simpl.
  apply funextsec; intro t.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  now apply funextfun; intros [].
+ intros F G H αFG αGH; simpl in *.
  apply subtypeEquality; [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]; simpl.
  apply funextsec; intro t.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  now apply funextfun; intros [].
Qed.

Definition option_functor (s : sort) : functor sortToHSET sortToHSET :=
  tpair _ _ (is_functor_option_functor s).

Definition option_list (xs : list sort) : functor sortToHSET sortToHSET.
Proof.
use (foldr _ _ xs).
+ intros s F.
  apply (functor_composite (option_functor s) F).
+ apply functor_identity.
Defined.

(** This applies the sortToHSET to s and returns HSET *)
Definition sortToHSETToHSET (s : sort) : functor sortToHSET HSET.
Proof.
mkpair.
+ mkpair.
  - intro f; apply (pr1 f s).
  - simpl; intros a b f H; apply (f s H).
+ abstract (split;
    [ now intros f; apply funextsec
    | now intros f g h fg gh; apply funextsec; intro x ]).
Defined.

Definition endo_fun (X : functor sortToHSET sortToHSET) (a : list sort × sort) :
  functor sortToHSET HSET.
Proof.
(* Version 1: *)
(* apply (functor_composite (functor_composite (option_list (pr1 a)) X) *)
(*                          (sortToHSETToHSET (pr2 a))). *)

(* same thing but different associativity: *)
apply (functor_composite (option_list (pr1 a))
                         (functor_composite X (sortToHSETToHSET (pr2 a)))).
Defined.

Local Arguments hor_comp : simpl never.

Lemma endo_fun_functor (a : list sort × sort) :
  functor [sortToHSET,sortToHSET,has_homsets_sortToHSET]
          [sortToHSET,HSET,has_homsets_HSET].
Proof.
mkpair.
- mkpair.
  + intro X.
    apply (endo_fun X a).
  + intros F G α.
    use (@hor_comp sortToHSET _ HSET).
    * apply (nat_trans_id _).
    * use hor_comp; [ assumption | apply nat_trans_id ].
- split.
+ intro F; simpl in *.
  repeat rewrite horcomp_id_postwhisker, post_whisker_identity; trivial;
    try apply has_homsets_HSET; try apply has_homsets_sortToHSET.
+ intros F G H α β. simpl in *.
rewrite !horcomp_id_postwhisker.
eapply pathscomp0.
eapply maponpaths.
apply (post_whisker_composition sortToHSET _ _ has_homsets_HSET (sortToHSETToHSET (pr2 a))).
eapply pathscomp0.
simpl.
Check ( (nat_trans_comp (post_whisker α (sortToHSETToHSET (pr2 a)))
         (post_whisker β (sortToHSETToHSET (pr2 a))))).
(* This is not the right thing to do... *)
apply (@horcomp_id_prewhisker sortToHSET sortToHSET HSET has_homsets_HSET  (option_list (pr1 a)) (functor_composite F (sortToHSETToHSET (pr2 a))) (functor_composite H (sortToHSETToHSET (pr2 a)))).
simpl.
cbn.
apply (nat_trans_eq has_homsets_HSET).
intro x.
simpl.
apply funextsec; intro xx.
cbn.
admit.
Admitted.

(* Definition endo_funs (xs : list (list sort × sort)) (X : functor sortToHSET sortToHSET) : *)
(*   functor sortToHSET HSET. *)
(* Proof. *)
(* set (XS := map (endo_fun X) xs). *)
(* (* The output for the empty list *) *)
(* set (T := constant_functor sortToHSET HSET emptyHSET). *)
(* apply (foldr1 (fun F G => BinProductObject _ (BinProductsSortToHSETToHSET F G)) T XS). *)
(* Defined. *)

Definition endo_funs_functor (xs : list (list sort × sort)) :
  functor [sortToHSET,sortToHSET,has_homsets_sortToHSET]
          [sortToHSET,HSET,has_homsets_HSET].
Proof.
set (XS := map endo_fun_functor xs).
set (T := constant_functor [sortToHSET, sortToHSET, has_homsets_sortToHSET]
                           [sortToHSET, HSET, has_homsets_HSET]
                           (constant_functor sortToHSET HSET emptyHSET)).
(* TODO: Maybe use indexed finite products instead of a fold? *)
(* TODO: Should we use BinProduct_of_functors? *)
apply (foldr1 (fun F G => BinProduct_of_functors _ _ BinProductsSortToHSETToHSET F G) T XS).
Defined.

(* This lemma is just here to check that the correct sort_cat gets pulled out *)
Definition MSigToFunctor_helper (C D E F G : precategory)
  (hsD : has_homsets D) (hsG : has_homsets G)
  (H : functor F [[C,D,hsD],[E,G,hsG],functor_category_has_homsets _ _ hsG]) :
  functor [C,D,hsD] [E,[F,G,hsG],functor_category_has_homsets _ _ hsG] :=
    functor_composite (functor_swap H) functor_cat_swap.

Definition MSigToFunctor (M : MSig) :
  functor [sortToHSET,sortToHSET,has_homsets_sortToHSET]
          [sortToHSET,sortToHSET,has_homsets_sortToHSET].
Proof.
apply MSigToFunctor_helper.
apply functor_sort_cat.
intro s.
use (coproduct_of_functors (indices M s)).
+ apply Coproducts_functor_precat, Coproducts_HSET, isaset_indices.
+ intros y.
  apply (endo_funs_functor (args M s y)).
Defined.

End MBindingSig.
