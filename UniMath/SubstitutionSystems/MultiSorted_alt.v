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
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.

Local Notation "[ C , D ]" := (functor_Precategory C D).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "C / X" := (slicecat_ob C X).
Local Notation "C / X" := (slice_precat_data C X).
Local Notation "C / X" := (slice_precat C X (homset_property C)).
Local Notation "C / X ⟦ a , b ⟧" := (slicecat_mor C X a b) (at level 50, format "C / X ⟦ a , b ⟧").

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variables (sort : hSet).
(* Variables (C : Precategory) (BP : BinProducts C) (BC : BinCoproducts C) (TC : Terminal C) (LC : Lims C). *)

Let SET : Precategory := (HSET,,has_homsets_HSET).

(* Let Csort : precategory := HSET / sort. *)

Lemma has_homsets_Csort : has_homsets (SET / sort).
Proof.
apply has_homsets_slice_precat.
Qed.

(** Definition of multi sorted signatures *)
Definition MultiSortedSig : UU := Σ (I : hSet), I → list (list sort × sort) × sort.

Definition ops (M : MultiSortedSig) : hSet := pr1 M.

Definition arity (M : MultiSortedSig) : ops M → list (list sort × sort) × sort :=
  λ x, pr2 M x.

Definition proj_fun (s : sort) : SET / sort -> SET.
Proof.
intros p.
mkpair.
- apply (Σ x, pr2 p x = s).
- abstract (apply isaset_total2; [|intros x; apply isasetaprop]; apply setproperty).
Defined.

Definition proj (s : sort) : functor (SET / sort) SET.
Proof.
mkpair.
- mkpair.
  + apply (proj_fun s).
  + intros X Y f p.
    mkpair.
    * apply (pr1 f (pr1 p)).
    * abstract (now destruct f as [h hh]; destruct p as [x hx]; simpl in *; rewrite <- hx, <- hh).
- abstract (split; [intros X|intros X Y Z f g];
            apply funextsec; intro p; apply subtypeEquality; trivial; intros x; apply setproperty).
Defined.

Local Notation "'1'" := (TerminalHSET).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BinCoproductsHSET a b)) (at level 50).

(* opt (s:sort)(xi:sort -> Set) := fun s => total2 fun (z : hfiber (sumofmap<s (idfun sort) (termfun s)) *)
(* s => sumofmaps xi (termfun unit)) *)

(* where termfun is from PartA. *)

(* The idea is to take (sort \coprod unit) -> Set given by xi \coprod (a=>unit) . Then (sort \coprod *)
(* unit) -> sort that maps unit to s. Then to take sort -> Set given by the sums of the sets given by *)
(* the first function over the fibers of the second. *)

(* The fiber of the second function over s’ != s is unit that maps to xi(s’) and the fiber over s is *)
(* unit\coprod \unit where the first unit maps to xi(s) and the second one to unit. *)

(* Code for option as a function, below is the definition as a functor *)
Definition option_fun : sort -> SET / sort -> SET / sort.
Proof.
simpl; intros s Xf.
mkpair.
+ mkpair.
  - apply (hfiber (sumofmaps (pr2 Xf) (termfun s)) s). (* TODO: add hfiber for hSet *)
  - abstract (apply isaset_total2;
                [apply isasetcoprod; [apply setproperty| apply isasetunit]
                |intros []; simpl; intro x; apply isasetaprop, setproperty]).
+ simpl; intros F.
  induction F as [t h].
  induction t as [t|t]; simpl in *.
  - apply (pr2 Xf t).
  - apply s.
Defined.
(* apply mk_sortToC; intro t. *)
(* induction (eq s t) as [H|H]. *)
(* - apply (pr1 f t ⊕ 1). *)
(* - apply (pr1 f t). *)
(* Defined. *)

Definition option_functor_data  (s : sort) : functor_data (SET / sort) (SET / sort).
Proof.
mkpair.
+ apply (option_fun s).
+ intros X Y f.
  mkpair.
  - simpl; intros F.
{
 mkpair.
+ induction F as [t h].
    induction t as [t|t]; simpl in *.
-
(* induction f as [h1 h2]. *)
simpl in *.
apply ii1.
apply (pr1 f).
apply t.
- apply ii2.
apply t.
+
 induction F as [t h].
simpl.
    induction t as [t|t]; simpl in *; trivial.
rewrite <- h.
apply (toforallpaths _ _ _ (pr2 f) t).
}
-
simpl.
apply funextsec; intro F; simpl.
 induction F as [t h].
simpl.
    induction t as [t|t]; simpl in *; trivial.
apply (toforallpaths _ _ _ (pr2 f) t).
Defined.
    (* induction (eq s t) as [p|p]; simpl; clear p. *)
    (* { apply (BinCoproductOfArrows _ _ _ (α t) (identity _)). } *)
    (* { apply α. } *)
 (* * abstract (now intros t1 t2 []; cbn; induction (eq s t1); simpl; rewrite id_left, id_right). *)

Lemma is_functor_option_functor s : is_functor (option_functor_data s).
Proof.
split; simpl.
+ intros X; apply (eq_mor_slicecat _ has_homsets_HSET), funextsec; intros [t Ht].
  apply subtypeEquality; [intros x; apply setproperty|]; simpl.
  now induction t.
+ intros X Y Z f g; apply (eq_mor_slicecat _ has_homsets_HSET), funextsec; intros [t Ht].
  apply subtypeEquality; [intros x; apply setproperty|]; simpl.
  now induction t.
Qed.

Definition option_functor (s : sort) : functor (SET / sort) (SET / sort) :=
  tpair _ _ (is_functor_option_functor s).

(* option_functor for lists (also called option in the note) *)
Definition option_list (xs : list sort) : functor (SET / sort) (SET / sort).
Proof.
use (foldr _ _ xs).
+ intros s F.
  apply (functor_composite (option_functor s) F).
+ apply functor_identity.
Defined.

Definition SET_over_sort : Precategory.
Proof.
mkpair.
- apply (SET / sort).
- simpl; apply has_homsets_Csort.
Defined.

(* This is X^a as a functor between functor categories *)
Lemma exp_functor (a : list sort × sort) : functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET].
Proof.
eapply functor_composite.
- apply (pre_composition_functor _ _ _ has_homsets_Csort _ (option_list (pr1 a))).
- apply post_composition_functor, (proj (pr2 a)).
Defined.

Lemma is_omega_cocont_exp_functor (a : list sort × sort) :
  is_omega_cocont (exp_functor a).
Proof.
apply is_omega_cocont_functor_composite.
+ apply functor_category_has_homsets.
+ apply is_omega_cocont_pre_composition_functor.
  (* apply LimsFunctorCategory, LC. *)
  admit.
+ admit. (* is_omega_cocont post_composition_functor *)
Admitted.

(* This defines X^as where as is a list. Outputs a product of functors if the list is nonempty and
otherwise the constant functor. *)
Definition exp_functors (xs : list (list sort × sort)) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET].
Proof.
(* Apply the exp functor to every element of the list *)
set (XS := map exp_functor xs).
(* If the list is empty we output the constant functor *)
set (T := constant_functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET]
                           (constant_functor SET_over_sort HSET 1)).
(* TODO: Maybe use indexed finite products instead of a fold? *)
use (foldr1 (fun F G => BinProduct_of_functors _ _ _ F G) T XS).
apply BinProducts_functor_precat.
apply BinProductsHSET.
Defined.

(* H follows if C has exponentials? *)
Lemma is_omega_cocont_exp_functors (xs : list (list sort × sort))
  (* (H : Π x : [SET_over_sort, SET], is_omega_cocont (constprod_functor1 BinProductsSortToCToC x)) *) :
  is_omega_cocont (exp_functors xs).
Proof.
destruct xs as [[|n] xs].
- destruct xs.
  apply is_omega_cocont_constant_functor.
  apply functor_category_has_homsets.
- induction n as [|n IHn].
  + destruct xs as [m []].
    apply is_omega_cocont_exp_functor.
  + destruct xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_functors; try apply homset_property.
    * apply BinProducts_functor_precat. admit.
    * admit.
    * apply is_omega_cocont_exp_functor.
    * apply (IHn (k,,xs)).
Admitted.

(* Definition MultiSortedSigToFunctor_fun (M : MultiSortedSig) (CC : Π s, Coproducts (indices M s) C) *)
(*   : [sort_cat, [[sortToC, sortToC], [sortToC, C]]]. *)
(* Proof. *)
(* (* As we're defining a functor out of a discrete category it suffices to give a function: *) *)
(* apply functor_discrete_precategory; intro s. *)
(* use (coproduct_of_functors (indices M s)). *)
(* + apply Coproducts_functor_precat, CC. *)
(* + intros y; apply (exp_functors (args M s y)). *)
(* Defined. *)

Definition MultiSortedSigToFunctor (M : MultiSortedSig) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET_over_sort].
Proof.
use (coproduct_of_functors (ops M)).
+ admit.
+ intros op.
  admit.
Admitted.

Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig) :
   is_omega_cocont (MultiSortedSigToFunctor M).
Admitted.

End MBindingSig.