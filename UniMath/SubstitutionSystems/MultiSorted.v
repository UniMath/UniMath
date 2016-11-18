(**

This file formalizes multisorted binding signatures:

- Definition of multisorted binding signatures ([MultiSortedSig])
- Construction of a functor from a multisorted binding signature ([MultiSortedSigToFunctor])



Written by: Anders Mörtberg, 2016. The formalization follows a note written by Benedikt Ahrens and
Ralph Matthes, and is also inspired by discussions with them and Vladimir Voevodsky.

*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.DiscretePrecategory.
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
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
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

Local Notation "[ C , D ]" := (functor_Precategory C D).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section postcomp.

Variables (C D E : precategory) (hsD : has_homsets D) (hsE : has_homsets E).
Variables (F : functor D E).
Variables (H : is_left_adjoint F).

Let G : functor E D := right_adjoint H.
Let η : nat_trans (functor_identity D) (functor_composite F G):= unit_from_left_adjoint H.
Let ε : nat_trans (functor_composite G F) (functor_identity E) := counit_from_left_adjoint H.
Let H1 : Π a : D, # F (η a) ;; ε (F a) = identity (F a) := triangle_id_left_ad _ _ _ H.
Let H2 : Π b : E, η (G b) ;; # G (ε b) = identity (G b) := triangle_id_right_ad _ _ _ H.

Lemma is_left_adjoint_post_composition_functor :
  is_left_adjoint (post_composition_functor C D E hsD hsE F).
Proof.
exists (post_composition_functor _ _ _ _ _ G).
admit.
Admitted.

End postcomp.

Section post_composition_functor.

Context {C D E : precategory} (hsD : has_homsets D) (hsE : has_homsets E).
Context (F : functor D E) (HF : is_left_adjoint F).

Lemma is_cocont_post_composition_functor :
  is_cocont (post_composition_functor C D E hsD hsE F).
Proof.
apply left_adjoint_cocont; try apply functor_category_has_homsets.
apply (is_left_adjoint_post_composition_functor _ _ _ _ _ _ HF).
Defined.

Lemma is_omega_cocont_post_composition_functor :
  is_omega_cocont (post_composition_functor C D E hsD hsE F).
Proof.
now intros c L ccL; apply is_cocont_post_composition_functor.
Defined.

End post_composition_functor.

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variables  (sort : UU) (eq : isdeceq sort). (* Can we eliminate this assumption? *)
Variables (C : Precategory) (BP : BinProducts C) (BC : BinCoproducts C) (TC : Terminal C) (LC : Lims C).

(** Define the discrete category of sorts *)
Let sort_cat : precategory := discrete_precategory sort.

Let hsC : has_homsets C := homset_property C.

(** This represents "sort → C" *)
Let sortToC : Precategory := [sort_cat,C].

Local Lemma has_homsets_sortToC : has_homsets sortToC.
Proof.
apply homset_property.
Qed.

Local Definition BinProductsSortToCToC : BinProducts [sortToC,C].
Proof.
apply (BinProducts_functor_precat _ _ BP).
Defined.

Definition mk_sortToC (f : sort → C) : sortToC :=
  functor_discrete_precategory _ _ f.

Definition proj_gen_fun (D : precategory) (E : Precategory) (d : D) : functor [D,E] E.
Proof.
mkpair.
+ mkpair.
  - intro f; apply (pr1 f d).
  - simpl; intros a b f; apply (f d).
+ abstract (split; [intro f; apply idpath|intros f g h fg gh; apply idpath]).
Defined.

Definition proj_gen {D : precategory} {E : Precategory} : functor D [[D,E],E].
Proof.
mkpair.
+ mkpair.
  - apply proj_gen_fun.
  - intros d1 d2 f.
    mkpair.
    * simpl; intro F; apply (# F f).
    * abstract (intros F G α; simpl in *; apply pathsinv0, (nat_trans_ax α d1 d2 f)).
+ abstract (split;
  [ intros F; simpl; apply nat_trans_eq; [apply homset_property|]; intro G; simpl; apply functor_id
  | intros F G H α β; simpl; apply nat_trans_eq; [apply homset_property|];
    intro γ; simpl; apply functor_comp ]).
Defined.

(** Given a sort s this applies the sortToC to s and returns C *)
Definition projSortToC (s : sort) : functor sortToC C.
Proof.
apply proj_gen_fun.
apply s.
Defined.



(** Definition of multi sorted signatures *)
Definition MultiSortedSig : UU :=
  Π (s : sort), Σ (I : UU), (I → list (list sort × sort)). (* × (isaset I). *)

Definition indices (M : MultiSortedSig) : sort → UU := fun s => pr1 (M s).

Definition args (M : MultiSortedSig) (s : sort) : indices M s → list (list sort × sort) :=
  pr2 (M s).

(* Lemma isaset_indices (M : MultiSortedSig) (s : sort) : isaset (indices M s). *)
(* Proof. *)
(* apply (pr2 (pr2 (M s))). *)
(* Qed. *)



Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BC a b)) (at level 50).

(* Code for option as a function, below is the definition as a functor *)
Definition option_fun : sort -> sortToC -> sortToC.
Proof.
intros s f.
apply mk_sortToC; intro t.
induction (eq s t) as [H|H].
- apply (pr1 f t ⊕ 1).
- apply (pr1 f t).
Defined.

(* The function part of Definition 3 *)
Definition option_functor_data  (s : sort) : functor_data sortToC sortToC.
Proof.
mkpair.
+ apply (option_fun s).
+ intros F G α.
  mkpair.
  * simpl; intro t.
    induction (eq s t) as [p|p]; simpl; clear p.
    { apply (BinCoproductOfArrows _ _ _ (α t) (identity _)). }
    { apply α. }
  * abstract (now intros t1 t2 []; cbn; induction (eq s t1); simpl; rewrite id_left, id_right).
Defined.

Lemma is_functor_option_functor s : is_functor (option_functor_data s).
Proof.
split.
+ intros F; apply (nat_trans_eq hsC); intro t; simpl.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  now apply pathsinv0, BinCoproductArrowUnique; rewrite id_left, id_right.
+ intros F G H αFG αGH; apply (nat_trans_eq hsC); intro t; simpl.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  apply pathsinv0; eapply pathscomp0; [apply precompWithBinCoproductArrow|].
  rewrite !id_left; apply BinCoproductArrowUnique.
  * now rewrite BinCoproductIn1Commutes, assoc.
  * now rewrite BinCoproductIn2Commutes, id_left.
Qed.

(* This is Definition 3 (sorted context extension) from the note *)
Definition option_functor (s : sort) : functor sortToC sortToC :=
  tpair _ _ (is_functor_option_functor s).

(* option_functor for lists (also called option in the note) *)
Definition option_list (xs : list sort) : functor sortToC sortToC.
Proof.
use (foldr _ _ xs).
+ intros s F.
  apply (functor_composite (option_functor s) F).
+ apply functor_identity.
Defined.

(* This is X^a as a functor between functor categories *)
Lemma exp_functor (a : list sort × sort) : functor [sortToC,sortToC] [sortToC,C].
Proof.
eapply functor_composite.
- apply (pre_composition_functor _ _ _ has_homsets_sortToC _ (option_list (pr1 a))).
- apply post_composition_functor, (projSortToC (pr2 a)).
Defined.

Lemma is_omega_cocont_exp_functor (a : list sort × sort)
  (H : Colims_of_shape nat_graph sortToC) :
  is_omega_cocont (exp_functor a).
Proof.
apply is_omega_cocont_functor_composite.
+ apply functor_category_has_homsets.
+ apply is_omega_cocont_pre_composition_functor.
  apply H.
+ admit. (* is_omega_cocont post_composition_functor *)
Admitted.

(* This defines X^as where as is a list. Outputs a product of functors if the list is nonempty and
otherwise the constant functor. *)
Definition exp_functors (xs : list (list sort × sort)) :
  functor [sortToC,sortToC] [sortToC,C].
Proof.
(* Apply the exp functor to every element of the list *)
set (XS := map exp_functor xs).
(* If the list is empty we output the constant functor *)
set (T := constant_functor [sortToC,sortToC] [sortToC,C]
                           (constant_functor sortToC C TC)).
(* TODO: Maybe use indexed finite products instead of a fold? *)
apply (foldr1 (fun F G => BinProduct_of_functors _ _ BinProductsSortToCToC F G) T XS).
Defined.

(* H follows if C has exponentials? *)
Lemma is_omega_cocont_exp_functors (xs : list (list sort × sort))
  (H : Π x : [sortToC, C], is_omega_cocont (constprod_functor1 BinProductsSortToCToC x))
  (H2 : Colims_of_shape nat_graph sortToC) :
  is_omega_cocont (exp_functors xs).
Proof.
destruct xs as [[|n] xs].
- destruct xs.
  apply is_omega_cocont_constant_functor.
  apply (functor_category_has_homsets sortToC).
- induction n as [|n IHn].
  + destruct xs as [m []].
    apply is_omega_cocont_exp_functor, H2.
  + destruct xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_functors; try apply homset_property.
    * now repeat apply BinProducts_functor_precat.
    * apply H.
    * apply is_omega_cocont_exp_functor, H2.
    * apply (IHn (k,,xs)).
Defined.



(* From here on things are not so nice: *)

Local Definition MultiSortedSigToFunctor_helper1 (C1 D E1 : precategory) (E2 : Precategory)
  : functor [E1,[C1,[D,E2]]] [E1,[D,[C1,E2]]].
Proof.
eapply post_composition_functor.
apply functor_cat_swap.
Defined.

(* This lemma is just here to check that the correct sort_cat gets pulled out when reorganizing *)
(*    arguments *)
Local Definition MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (E2 : Precategory) :
  functor [E1,[C1,[D,E2]]] [C1,[D,[E1,E2]]].
Proof.
eapply (functor_composite (functor_cat_swap _ _ _)).
apply MultiSortedSigToFunctor_helper1.
Defined.



(* The above definition might be the same as: *)
(* functor_composite (functor_cat_swap F) functor_cat_swap. *)

(* Local Definition MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (E2 : Precategory) *)
(*   (F : functor E1 [C1,[D,E2]]) : functor C1 [D,[E1,E2]]. *)
(*     functor_composite (functor_cat_swap F) functor_cat_swap. *)


Lemma is_omega_cocont_MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (E2 : Precategory)
  (F : functor E1 [C1,[D,E2]]) (HF : Π s, is_omega_cocont (F s)) :
  is_omega_cocont (MultiSortedSigToFunctor_helper C1 D E1 E2 F).
Proof.
apply is_omega_cocont_functor_composite.
+ apply functor_category_has_homsets.
+ admit.
+ apply is_omega_cocont_functor_cat_swap.
Admitted.

Local Definition MultiSortedSigToFunctor_helper2 (C1 D E1 : precategory) (E2 : Precategory) :
  functor [E1,[D,[C1,E2]]] [C1,[D,[E1,E2]]].
Proof.
eapply functor_composite;[apply functor_cat_swap|].
eapply functor_composite;[|apply functor_cat_swap].
eapply functor_composite; [eapply post_composition_functor; apply functor_cat_swap|].
apply functor_identity.
Defined.

Definition MultiSortedSigToFunctor_fun (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C)
  : [sort_cat, [[sortToC, sortToC], [sortToC, C]]].
Proof.
(* As we're defining a functor out of a discrete category it suffices to give a function: *)
apply functor_discrete_precategory; intro s.
use (coproduct_of_functors (indices M s)).
+ apply Coproducts_functor_precat, CC.
+ intros y; apply (exp_functors (args M s y)).
Defined.

Lemma is_omega_cocont_MultiSortedSigToFunctor_fun
  (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C)
  (CP : Π s, Products (indices M s) C)
  (hs : Π s, isdeceq (indices M s))
  (H : Π x : [sortToC, C], is_omega_cocont (constprod_functor1 BinProductsSortToCToC x))
  (H2 : Colims_of_shape nat_graph sortToC) :
  Π s, is_omega_cocont (pr1 (MultiSortedSigToFunctor_fun M CC) s).
Proof.
intros s.
apply is_omega_cocont_coproduct_of_functors; try apply homset_property.
+ apply Products_functor_precat, Products_functor_precat, CP.
+ apply (hs s).
+ intros y; apply is_omega_cocont_exp_functors.
  - apply H.
  - apply H2.
Defined.

(** * The functor constructed from a multisorted binding signature *)
Definition MultiSortedSigToFunctor (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C) :
  functor [sortToC,sortToC] [sortToC,sortToC].
Proof.
(* First reorganize so that the last sort argument is first: *)
set (F := MultiSortedSigToFunctor_helper [sortToC,sortToC] sortToC sort_cat C).
set (x := MultiSortedSigToFunctor_fun M CC).
apply (F x).
Defined.

Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig)
  (CC : Π s, Coproducts (indices M s) C)
  (PC : Π s, Products (indices M s) C)
  (Hi : Π s, isdeceq (indices M s))
  (H : Π x : [sortToC, C], is_omega_cocont (constprod_functor1 BinProductsSortToCToC x)) :
   is_omega_cocont (MultiSortedSigToFunctor M CC).
Proof.
apply is_omega_cocont_functor_composite.
+ apply (homset_property [sortToC,sortToC]).
+ simpl. admit.
+ apply is_omega_cocont_functor_cat_swap.
Admitted.

End MBindingSig.


(************************** OLD POINTFULL VERSION BELOW **************************)

(* (** * Definition of multisorted binding signatures *) *)
(* Section MBindingSig. *)

(* Variable (sort : UU) (C : Precategory) (BP : BinProducts C) (BC : BinCoproducts C) (TC : Terminal C). *)
(* Variable (eq : isdeceq sort). (* Can we eliminate this assumption? *) *)

(* (** Define the discrete category of sorts *) *)
(* Let sort_cat : precategory := discrete_precategory sort. *)

(* Let hsC : has_homsets C := homset_property C. *)

(* (** This represents "sort → C" *) *)
(* Let sortToC : Precategory := [sort_cat,C]. *)

(* Local Lemma has_homsets_sortToC : has_homsets sortToC. *)
(* Proof. *)
(* apply homset_property. *)
(* Qed. *)

(* Local Definition BinProductsSortToCToC : BinProducts [sortToC,C]. *)
(* Proof. *)
(* apply (BinProducts_functor_precat _ _ BP). *)
(* Defined. *)

(* Definition mk_sortToC (f : sort → C) : sortToC := *)
(*   functor_discrete_precategory _ _ f. *)

(* (** Given a sort s this applies the sortToC to s and returns C *) *)
(* Definition sortToCToC (s : sort) : functor sortToC C. *)
(* Proof. *)
(* mkpair. *)
(* + mkpair. *)
(*   - intro f; apply (pr1 f s). *)
(*   - simpl; intros a b f; apply (f s). *)
(* + abstract (split; [intro f; apply idpath|intros f g h fg gh; apply idpath]). *)
(* Defined. *)



(* (** Definition of multi sorted signatures *) *)
(* Definition MultiSortedSig : UU := *)
(*   Π (s : sort), Σ (I : UU), (I → list (list sort × sort)). (* × (isaset I). *) *)

(* Definition indices (M : MultiSortedSig) : sort → UU := fun s => pr1 (M s). *)

(* Definition args (M : MultiSortedSig) (s : sort) : indices M s → list (list sort × sort) := *)
(*   pr2 (M s). *)

(* (* Lemma isaset_indices (M : MultiSortedSig) (s : sort) : isaset (indices M s). *) *)
(* (* Proof. *) *)
(* (* apply (pr2 (pr2 (M s))). *) *)
(* (* Qed. *) *)



(* Local Notation "'1'" := (TerminalObject TC). *)
(* Local Notation "a ⊕ b" := (BinCoproductObject _ (BC a b)) (at level 50). *)

(* (* Code for option as a function, below is the definition as a functor *) *)
(* Definition option_fun : sort -> sortToC -> sortToC. *)
(* Proof. *)
(* intros s f. *)
(* apply mk_sortToC; intro t. *)
(* induction (eq s t) as [H|H]. *)
(* - apply (pr1 f t ⊕ 1). *)
(* - apply (pr1 f t). *)
(* Defined. *)

(* (* The function part of Definition 3 *) *)
(* Definition option_functor_data  (s : sort) : functor_data sortToC sortToC. *)
(* Proof. *)
(* mkpair. *)
(* + apply (option_fun s). *)
(* + intros F G α. *)
(*   mkpair. *)
(*   * simpl; intro t. *)
(*     induction (eq s t) as [p|p]; simpl; clear p. *)
(*     { apply (BinCoproductOfArrows _ _ _ (α t) (identity _)). } *)
(*     { apply α. } *)
(*   * abstract (now intros t1 t2 []; cbn; induction (eq s t1); simpl; rewrite id_left, id_right). *)
(* Defined. *)

(* Lemma is_functor_option_functor s : is_functor (option_functor_data s). *)
(* Proof. *)
(* split. *)
(* + intros F; apply (nat_trans_eq hsC); intro t; simpl. *)
(*   induction (eq s t) as [p|p]; trivial; simpl; clear p. *)
(*   now apply pathsinv0, BinCoproductArrowUnique; rewrite id_left, id_right. *)
(* + intros F G H αFG αGH; apply (nat_trans_eq hsC); intro t; simpl. *)
(*   induction (eq s t) as [p|p]; trivial; simpl; clear p. *)
(*   apply pathsinv0; eapply pathscomp0; [apply precompWithBinCoproductArrow|]. *)
(*   rewrite !id_left; apply BinCoproductArrowUnique. *)
(*   * now rewrite BinCoproductIn1Commutes, assoc. *)
(*   * now rewrite BinCoproductIn2Commutes, id_left. *)
(* Qed. *)

(* (* This is Definition 3 (sorted context extension) from the note *) *)
(* Definition option_functor (s : sort) : functor sortToC sortToC := *)
(*   tpair _ _ (is_functor_option_functor s). *)

(* (* option_functor for lists (also called option in the note) *) *)
(* Definition option_list (xs : list sort) : functor sortToC sortToC. *)
(* Proof. *)
(* use (foldr _ _ xs). *)
(* + intros s F. *)
(*   apply (functor_composite (option_functor s) F). *)
(* + apply functor_identity. *)
(* Defined. *)

(* (* This is X^a, defined as a function *) *)
(* Definition exp_fun (X : functor sortToC sortToC) (a : list sort × sort) : *)
(*   functor sortToC C. *)
(* Proof. *)
(* (* Version 1: *) *)
(* (* apply (functor_composite (functor_composite (option_list (pr1 a)) X) *) *)
(* (*                          (sortToCToC (pr2 a))). *) *)

(* (* Version 2: (same thing but reorganized using associativity) *) *)
(* apply (functor_composite (option_list (pr1 a)) *)
(*                          (functor_composite X (sortToCToC (pr2 a)))). *)
(* Defined. *)

(* (* Lemma is_omega_cocont_exp_fun (X : functor sortToC sortToC) (a : list sort × sort) : *) *)
(* (*   is_omega_cocont (exp_fun X a). *) *)
(* (* Admitted. *) *)

(* (* This stops Coq from unfolding horcomp too much *) *)
(* Local Arguments horcomp : simpl never. *)

(* (* This is X^a as a functor between functor categories *) *)
(* Lemma exp_functor (a : list sort × sort) : functor [sortToC,sortToC] [sortToC,C]. *)
(* Proof. *)
(* mkpair. *)
(* - mkpair. *)
(*   + intro X; apply (exp_fun X a). *)
(*   + intros F G α. *)
(*     use (@horcomp sortToC _ C _ _ _ _ (nat_trans_id _)). *)
(*     use horcomp; [ assumption | apply nat_trans_id ]. *)
(* - abstract (split; *)
(*   [ intro F; cbn; *)
(*     rewrite (horcomp_id_postwhisker _ _ _ has_homsets_sortToC hsC); *)
(*     rewrite post_whisker_identity; try apply hsC; *)
(*     rewrite (horcomp_id_postwhisker _ _ _ has_homsets_sortToC hsC); *)
(*     now rewrite post_whisker_identity; try apply hsC *)
(*   | intros F G H α β; cbn; *)
(*     rewrite !(horcomp_id_postwhisker _ _ _ has_homsets_sortToC hsC); *)
(*     rewrite !(horcomp_id_prewhisker hsC (option_list (pr1 a))); *)
(*     rewrite (post_whisker_composition sortToC _ _ hsC (sortToCToC (pr2 a))); *)
(*     now rewrite (pre_whisker_composition _ _ _ hsC)]). *)
(* Defined. *)

(* (* Lemma  is_omega_cocont_exp_functor a : is_omega_cocont (exp_functor a). *) *)
(* (* Admitted. *) *)

(* (* First version: *) *)
(* (* Definition exp_funs (xs : list (list sort × sort)) (X : functor sortToC sortToC) : *) *)
(* (*   functor sortToC C. *) *)
(* (* Proof. *) *)
(* (* set (XS := map (exp_fun X) xs). *) *)
(* (* (* The output for the empty list *) *) *)
(* (* set (T := constant_functor sortToC C emptyC). *) *)
(* (* apply (foldr1 (fun F G => BinProductObject _ (BinProductsSortToCToC F G)) T XS). *) *)
(* (* Defined. *) *)

(* (* This defines X^as where as is a list. Outputs a product of functors if the list is nonempty and *)
(* otherwise the constant functor. *) *)
(* Definition exp_functors (xs : list (list sort × sort)) : *)
(*   functor [sortToC,sortToC] [sortToC,C]. *)
(* Proof. *)
(* (* Apply the exp functor to every element of the list *) *)
(* set (XS := map exp_functor xs). *)
(* (* If the list is empty we output the constant functor *) *)
(* set (T := constant_functor [sortToC,sortToC] [sortToC,C] *)
(*                            (constant_functor sortToC C TC)). *)
(* (* TODO: Maybe use indexed finite products instead of a fold? *) *)
(* apply (foldr1 (fun F G => BinProduct_of_functors _ _ BinProductsSortToCToC F G) T XS). *)
(* Defined. *)

(* (* Lemma is_omega_cocont_exp_functors (xs : list (list sort × sort)) : *) *)
(* (*   is_omega_cocont (exp_functors xs). *) *)
(* (* Proof. *) *)
(* (* use (list_ind (fun xs => is_omega_cocont (exp_functors xs)) _ _ xs); simpl; clear xs. *) *)
(* (* - apply is_omega_cocont_constant_functor. *) *)
(* (*   apply (functor_category_has_homsets sortToC). *) *)
(* (* - intros x xs. *) *)
(* (* use (list_ind (fun xs => is_omega_cocont (exp_functors xs) -> is_omega_cocont (exp_functors (cons x xs))) _ _ xs); simpl; clear xs. *) *)
(* (* + intros _. unfold exp_functors. *) *)
(* (* rewrite map_cons, map_nil. *) *)
(* (* rewrite foldr1_cons_nil. *) *)
(* (* apply is_omega_cocont_exp_functor. *) *)
(* (* + *) *)
(* (* intros y xs Hxs Hys. *) *)
(* (* unfold exp_functors. *) *)
(* (* rewrite !map_cons. *) *)
(* (* rewrite foldr1_cons. *) *)
(* (* apply is_omega_cocont_BinProduct_of_functors. *) *)
(* (* admit. *) *)
(* (* admit. *) *)
(* (* admit. *) *)
(* (* admit. *) *)
(* (* apply is_omega_cocont_exp_functor. *) *)
(* (* admit. *) *)
(* (* Admitted. *) *)

(* (* This lemma is just here to check that the correct sort_cat gets pulled out when reorganizing *)
(*    arguments *) *)
(* Local Definition MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (C2 E2 : Precategory) *)
(*   (F : functor E1 [[C1,C2],[D,E2]]) : functor [C1,C2] [D,[E1,E2]] := *)
(*     functor_composite (functor_cat_swap F) functor_cat_swap. *)

(* (* Lemma is_omega_cocont_MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (C2 E2 : Precategory) *) *)
(* (*   (F : functor E1 [[C1,C2],[D,E2]]) (HF : Π c, is_omega_cocont (F c)) : *) *)
(* (*   is_omega_cocont (MultiSortedSigToFunctor_helper C1 D E1 C2 E2 F). *) *)
(* (* Admitted. *) *)

(* Definition MultiSortedSigToFunctor_fun (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C) (s : sort) : *)
(*   [[sortToC, sortToC], [sortToC, C]]. *)
(* Proof. *)
(* use (coproduct_of_functors (indices M s)). *)
(* + apply Coproducts_functor_precat, CC. *)
(* + intros y; apply (exp_functors (args M s y)). *)
(* Defined. *)

(* (* Lemma is_omega_cocont_MultiSortedSigToFunctor_fun *) *)
(* (*  (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C) (s : sort) *) *)
(* (*  (CP : Products (indices M s) C) *) *)
(* (*  (hs : isdeceq (indices M s)) : *) *)
(* (*  is_omega_cocont (MultiSortedSigToFunctor_fun M CC s). *) *)
(* (* Proof. *) *)
(* (* apply is_omega_cocont_coproduct_of_functors; try apply homset_property. *) *)
(* (* + apply Products_functor_precat, Products_functor_precat, CP. *) *)
(* (* + assumption. *) *)
(* (* + intros y; apply is_omega_cocont_exp_functors. *) *)
(* (* Defined. *) *)

(* (** * The functor constructed from a multisorted binding signature *) *)
(* Definition MultiSortedSigToFunctor (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C) : *)
(*   functor [sortToC,sortToC] [sortToC,sortToC]. *)
(* Proof. *)
(* (* First reorganize so that the last sort argument is first: *) *)
(* apply MultiSortedSigToFunctor_helper. *)
(* (* As we're defining a functor out of a discrete category it suffices to give a function: *) *)
(* apply functor_discrete_precategory; intro s. *)
(* apply (MultiSortedSigToFunctor_fun M CC s). *)
(* Defined. *)

(* (* Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig) *) *)
(* (*   (CC : Π s, Coproducts (indices M s) C) *) *)
(* (*   (PC : Π s, Products (indices M s) C) *) *)
(* (*   (Hi : Π s, isdeceq (indices M s)) : *) *)
(* (*    is_omega_cocont (MultiSortedSigToFunctor M CC). *) *)
(* (* Proof. *) *)
(* (* apply is_omega_cocont_MultiSortedSigToFunctor_helper. *) *)
(* (* intros s; apply is_omega_cocont_MultiSortedSigToFunctor_fun. *) *)
(* (* - apply PC. *) *)
(* (* - apply Hi. *) *)
(* (* Defined. *) *)
(* (* use is_omega_cocont_functor_composite. *) *)
(* (* + apply (functor_category_has_homsets sortToC). *) *)
(* (* + apply is_omega_cocont_functor_swap. *) *)
(* (*   intros s; apply is_omega_cocont_MultiSortedSigToFunctor_fun. *) *)
(* (*   - apply PC. *) *)
(* (*   - apply Hi. *) *)
(* (* + *) *)

(* End MBindingSig. *)
