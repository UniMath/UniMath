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

(** Swapping of functor arguments *)
(* TODO: Move upstream? *)
Section functor_swap.

Context {C D : precategory} {E : Precategory}.

Lemma functor_swap : functor C [D,E] → functor D [C,E].
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
  [ intros d; apply (nat_trans_eq (homset_property E)); intro c; simpl; apply functor_id
  | intros a b c f g; apply (nat_trans_eq (homset_property E)); intro x; simpl; apply functor_comp]).
Defined.

(* Lemma is_omega_cocont_functor_swap *)
(*   (F : functor C [D,E]) (HF : forall c, is_omega_cocont (F c)) : *)
(*    is_omega_cocont (functor_swap F). *)
(* Proof. *)
(* intros d L ccL HccL G ccG. *)
(* simpl in G. *)
(* transparent assert (temp : (Π c, cocone (mapdiagram (F c) d) (G c))). *)
(* { intro c; use mk_cocone. *)
(*   + simpl; intro n. *)
(*     apply (pr1 (coconeIn ccG n) c). *)
(*   + abstract (intros m n e; apply (nat_trans_eq_pointwise (coconeInCommutes ccG _ _ e) c)). *)
(* } *)
(* transparent assert (apa : (nat_trans (pr1 (functor_swap F L)) G)). *)
(* + intro c. *)
(* apply (HF c d L ccL HccL (G c) (temp c)). *)
(* + apply H. intros x y f. *)
(* simpl. *)
(* } *)
(* mkpair. *)
(* + mkpair. *)
(* - mkpair. *)
(* * intro c. *)
(* simpl. *)
(* apply apa. *)
(* (* simpl. *) *)
(* (* apply (HF c d L ccL HccL (G c) (temp c)). *) *)
(* * intros x y f; simpl. *)
(* (* destruct (HF y d L ccL HccL (G y) (temp y)) as [[hy1 hy2] hy3]. *) *)
(* (* destruct (HF x d L ccL HccL (G x) (temp x)) as [[hx1 hx2] hx3]. *) *)
(* apply (nat_trans_ax apa x y f). *)
(* - admit. *)
(* + admit. *)
(* Admitted. *)

Lemma functor_cat_swap_nat_trans (F G : functor C [D, E]) (α : nat_trans F G) :
  nat_trans (functor_swap F) (functor_swap G).
Proof.
mkpair.
+ intros d; simpl.
  mkpair.
  * intro c; apply (α c).
  * abstract (intros a b f; apply (nat_trans_eq_pointwise (nat_trans_ax α _ _ f) d)).
+ abstract (intros a b f; apply (nat_trans_eq (homset_property E)); intro c; simpl; apply nat_trans_ax).
Defined.

Lemma functor_cat_swap : functor [C, [D, E]] [D, [C, E]].
Proof.
mkpair.
- apply (tpair _ functor_swap functor_cat_swap_nat_trans).
- abstract (split;
  [ intro F; apply (nat_trans_eq (functor_category_has_homsets _ _ (homset_property E))); simpl; intro d;
    now apply (nat_trans_eq (homset_property E))
  | intros F G H α β; cbn; apply (nat_trans_eq (functor_category_has_homsets _ _ (homset_property E))); intro d;
    now apply (nat_trans_eq (homset_property E))]).
Defined.

(* How should one even express this: *)
(* Lemma is_omega_cocont_functor_cat_swap : is_omega_cocont functor_cat_swap. *)

End functor_swap.

(** * Discrete precategories *)
Section DiscreteCategory.

Variable (A : UU).

Definition discrete_precategory_data : precategory_data.
Proof.
mkpair.
- apply (A,,paths).
- mkpair; [ apply idpath | apply @pathscomp0 ].
Defined.

Definition is_precategory_discrete_precategory_data : is_precategory discrete_precategory_data.
Proof.
split; [split|]; trivial; intros.
+ apply pathscomp0rid.
+ apply path_assoc.
Qed.

Definition discrete_precategory : precategory :=
  (discrete_precategory_data,,is_precategory_discrete_precategory_data).

Lemma has_homsets_discrete_precategory (H : isofhlevel 3 A) : has_homsets discrete_precategory.
Proof.
intros ? ? ? ? ? ?; apply H.
Qed.

(** To define a functor out of a discrete category it suffices to give a function *)
Lemma functor_discrete_precategory (D : precategory) (f : A → D) :
  functor discrete_precategory D.
Proof.
mkpair.
+ mkpair.
  - apply f.
  - intros s t []; apply identity.
+ abstract (now split; [intro|intros a b c [] []; simpl; rewrite id_left]).
Defined.

End DiscreteCategory.

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variable (sort : UU) (C : Precategory) (BP : BinProducts C) (BC : BinCoproducts C) (TC : Terminal C).
Variable (eq : isdeceq sort). (* Can we eliminate this assumption? *)

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

(** Given a sort s this applies the sortToC to s and returns C *)
Definition sortToCToC (s : sort) : functor sortToC C.
Proof.
mkpair.
+ mkpair.
  - intro f; apply (pr1 f s).
  - simpl; intros a b f; apply (f s).
+ abstract (split; [intro f; apply idpath|intros f g h fg gh; apply idpath]).
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
(* Definition option : sort -> sortToC -> sortToC. *)
(* Proof. *)
(* intros s f. *)
(* apply mk_sortToC; intro t. *)
(* induction (eq s t) as [H|H]. *)
(* - apply (pr1 f t ⊕ 1). *)
(* - apply (pr1 f t). *)
(* Defined. *)

(* The function part of Definition 3 *)
Definition option_functor_data  (s : sort) : functor_data sortToC sortToC.
Proof.
mkpair.
+ intro f.
  apply mk_sortToC; intro t.
  induction (eq s t) as [H|H].
  * apply (pr1 f t ⊕ 1).
  * apply (pr1 f t).
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

(* This is X^a, defined as a function *)
Definition exp_fun (X : functor sortToC sortToC) (a : list sort × sort) :
  functor sortToC C.
Proof.
(* Version 1: *)
(* apply (functor_composite (functor_composite (option_list (pr1 a)) X) *)
(*                          (sortToCToC (pr2 a))). *)

(* Version 2: (same thing but reorganized using associativity) *)
apply (functor_composite (option_list (pr1 a))
                         (functor_composite X (sortToCToC (pr2 a)))).
Defined.

Lemma is_omega_cocont_exp_fun (X : functor sortToC sortToC) (a : list sort × sort) :
  is_omega_cocont (exp_fun X a).
Admitted.

(* This stops Coq from unfolding horcomp too much *)
Local Arguments horcomp : simpl never.

(* This is X^a as a functor between functor categories *)
Lemma exp_functor (a : list sort × sort) : functor [sortToC,sortToC] [sortToC,C].
Proof.
mkpair.
- mkpair.
  + intro X; apply (exp_fun X a).
  + intros F G α.
    use (@horcomp sortToC _ C _ _ _ _ (nat_trans_id _)).
    use horcomp; [ assumption | apply nat_trans_id ].
- abstract (split;
  [ intro F; cbn;
    rewrite (horcomp_id_postwhisker _ _ _ has_homsets_sortToC hsC);
    rewrite post_whisker_identity; try apply hsC;
    rewrite (horcomp_id_postwhisker _ _ _ has_homsets_sortToC hsC);
    now rewrite post_whisker_identity; try apply hsC
  | intros F G H α β; cbn;
    rewrite !(horcomp_id_postwhisker _ _ _ has_homsets_sortToC hsC);
    rewrite !(horcomp_id_prewhisker hsC (option_list (pr1 a)));
    rewrite (post_whisker_composition sortToC _ _ hsC (sortToCToC (pr2 a)));
    now rewrite (pre_whisker_composition _ _ _ hsC)]).
Defined.

Lemma  is_omega_cocont_exp_functor a : is_omega_cocont (exp_functor a).
Proof.
assert (lol : is_omega_cocont (pr1 (exp_functor a)).
unfold exp_functor.
simpl.

Admitted.

(* First version: *)
(* Definition exp_funs (xs : list (list sort × sort)) (X : functor sortToC sortToC) : *)
(*   functor sortToC C. *)
(* Proof. *)
(* set (XS := map (exp_fun X) xs). *)
(* (* The output for the empty list *) *)
(* set (T := constant_functor sortToC C emptyC). *)
(* apply (foldr1 (fun F G => BinProductObject _ (BinProductsSortToCToC F G)) T XS). *)
(* Defined. *)

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

(* TODO: move these *)
Lemma foldr_cons {A B : UU} (f : A -> B -> B) (b : B) (x : A) (xs : list A) :
  foldr f b (cons x xs) = f x (foldr f b xs).
Proof.
now destruct xs.
Qed.

Lemma map_nil {A B : UU} (f : A -> B) : map f nil = nil.
Proof.
apply idpath.
Qed.

Lemma map_cons {A B : UU} (f : A -> B) (x : A) (xs : list A) :
  map f (cons x xs) = cons (f x) (map f xs).
Proof.
now destruct xs.
Qed.

Lemma foldr1_cons_nil {A : UU} (f : A -> A -> A) (a : A) (x : A) :
  foldr1 f a (cons x nil) = x.
Proof.
apply idpath.
Qed.

Lemma foldr1_cons {A : UU} (f : A -> A -> A) (a : A) (x y : A) (xs : list A) :
  foldr1 f a (cons x (cons y xs)) = f x (foldr1 f a (cons y xs)).
Proof.
apply idpath.
Qed.

(* Lemma exp_functor_cons x xs : *)
(*   exp_functors (cons x xs) = BinProduct_of_functors _ _ BinProductsSortToCToC F (exp_functors G). *)

Lemma is_omega_cocont_exp_functors (xs : list (list sort × sort)) :
  is_omega_cocont (exp_functors xs).
Proof.
use (list_ind (fun xs => is_omega_cocont (exp_functors xs)) _ _ xs); simpl; clear xs.
- apply is_omega_cocont_constant_functor.
  apply (functor_category_has_homsets sortToC).
- intros x xs.
use (list_ind (fun xs => is_omega_cocont (exp_functors xs) -> is_omega_cocont (exp_functors (cons x xs))) _ _ xs); simpl; clear xs.

+ intros _. unfold exp_functors.
rewrite map_cons, map_nil.
rewrite foldr1_cons_nil.
apply is_omega_cocont_exp_functor.
+
intros y xs Hxs Hys.
unfold exp_functors.
rewrite !map_cons.
rewrite foldr1_cons.
apply is_omega_cocont_BinProduct_of_functors.
admit.
admit.
admit.
admit.
apply is_omega_cocont_exp_functor.
admit.
Admitted.

(* This lemma is just here to check that the correct sort_cat gets pulled out when reorganizing
   arguments *)
Local Definition MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (C2 E2 : Precategory)
  (F : functor E1 [[C1,C2],[D,E2]]) : functor [C1,C2] [D,[E1,E2]] :=
    functor_composite (functor_cat_swap F) functor_cat_swap.

Lemma is_omega_cocont_MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (C2 E2 : Precategory)
  (F : functor E1 [[C1,C2],[D,E2]]) (HF : Π c, is_omega_cocont (F c)) :
  is_omega_cocont (MultiSortedSigToFunctor_helper C1 D E1 C2 E2 F).
Proof.
(* unfold MultiSortedSigToFunctor_helper. *)
(* intros diag L ccL HccL G ccG. *)
(* mkpair. *)
(* + mkpair. *)
(* mkpair. *)
(* - *)
(* intro d. *)
(* mkpair. *)
(* * *)
(* intro e1. *)
(* simpl. *)
(* generalize (HF e1 diag L ccL HccL (functor_swap G e1)). *)
(* simpl. *)
Admitted.

Definition MultiSortedSigToFunctor_fun (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C) (s : sort) :
  [[sortToC, sortToC], [sortToC, C]].
Proof.
use (coproduct_of_functors (indices M s)).
+ apply Coproducts_functor_precat, CC.
+ intros y; apply (exp_functors (args M s y)).
Defined.

Lemma is_omega_cocont_MultiSortedSigToFunctor_fun
 (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C) (s : sort)
 (CP : Products (indices M s) C)
 (hs : isdeceq (indices M s)) :
 is_omega_cocont (MultiSortedSigToFunctor_fun M CC s).
Proof.
apply is_omega_cocont_coproduct_of_functors; try apply homset_property.
+ apply Products_functor_precat, Products_functor_precat, CP.
+ assumption.
+ intros y; apply is_omega_cocont_exp_functors.
Defined.

(** * The functor constructed from a multisorted binding signature *)
Definition MultiSortedSigToFunctor (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C) :
  functor [sortToC,sortToC] [sortToC,sortToC].
Proof.
(* First reorganize so that the last sort argument is first: *)
apply MultiSortedSigToFunctor_helper.
(* As we're defining a functor out of a discrete category it suffices to give a function: *)
apply functor_discrete_precategory; intro s.
apply (MultiSortedSigToFunctor_fun M CC s).
Defined.

Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig)
  (CC : Π s, Coproducts (indices M s) C)
  (PC : Π s, Products (indices M s) C)
  (Hi : Π s, isdeceq (indices M s)) :
   is_omega_cocont (MultiSortedSigToFunctor M CC).
Proof.
apply is_omega_cocont_MultiSortedSigToFunctor_helper.
intros s; apply is_omega_cocont_MultiSortedSigToFunctor_fun.
- apply PC.
- apply Hi.
Defined.
(* use is_omega_cocont_functor_composite. *)
(* + apply (functor_category_has_homsets sortToC). *)
(* + apply is_omega_cocont_functor_swap. *)
(*   intros s; apply is_omega_cocont_MultiSortedSigToFunctor_fun. *)
(*   - apply PC. *)
(*   - apply Hi. *)
(* + *)

End MBindingSig.
