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

Let SET : Precategory := (HSET,,has_homsets_HSET).

Lemma has_homsets_Csort : has_homsets (SET / sort).
Proof.
apply has_homsets_slice_precat.
Qed.

Variable (LimsCsort : Lims (SET / sort)).

(** Definition of multi sorted signatures *)
Definition MultiSortedSig : UU := Σ (I : hSet), I → list (list sort × sort) × sort.

Definition ops (M : MultiSortedSig) : hSet := pr1 M.
Definition arity (M : MultiSortedSig) : ops M → list (list sort × sort) × sort :=
  λ x, pr2 M x.

Definition proj_fun (s : sort) : SET / sort -> SET.
Proof.
intros p.
mkpair.
- apply (hfiber (pr2 p) s).
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

Definition HatFunctor (t : sort) : functor SET (SET / sort).
Proof.
mkpair.
- mkpair.
  + intro A; apply (A,,λ _, t).
  + intros A B f; apply (tpair _ f), idpath.
- abstract (now split; [intros A|intros A B C f g];
            apply subtypeEquality; try (intro x; apply has_homsets_HSET)).
Defined.

Lemma is_left_adjoint_hat (s : sort) : is_left_adjoint (HatFunctor s).
Proof.
apply (tpair _ (proj s)).
mkpair.
+ split.
  - mkpair.
    * intros X; simpl; intros x; apply (x,,idpath s).
    * abstract (intros X Y f; simpl; apply funextsec; intro x; cbn; apply subtypeEquality; trivial;
                intros y; apply setproperty).
  - mkpair.
    * intros X; simpl in *.
      mkpair; simpl.
      { intros H; apply (pr1 H). }
      { abstract (apply funextsec; intro x; apply (pr2 x)). }
    * abstract (now intros X Y f; apply (eq_mor_slicecat _ has_homsets_HSET)).
+ split.
  - abstract (now intros X; apply (eq_mor_slicecat _ has_homsets_HSET)).
  - abstract (intros X; apply funextsec; intro x;
              apply subtypeEquality; trivial; intros x'; apply setproperty).
Defined.

(* Could maybe be proved by showing that (proj s) is a product in Set/sort (it's a pullback) and
   then use that Set/sort is cartesian closed *)
Lemma is_left_adjoint_proj (s : sort) : is_left_adjoint (proj s).
Admitted.

Lemma is_omega_cocont_postcomp_proj (s : sort) :
  is_omega_cocont (post_composition_functor (SET / sort) _ _ has_homsets_Csort has_homsets_HSET (proj s)).
Proof.
(* intros d L ccL Hccl F ccF; simpl in *. *)
(* use unique_exists. *)
Admitted.

(* TODO: this could be defined more abstractly as:
     option(s)(X,f) := [f, \lambda _ .s] : X+1 -> sort *)
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

Definition option_functor_data  (s : sort) : functor_data (SET / sort) (SET / sort).
Proof.
mkpair.
+ apply (option_fun s).
+ intros X Y f.
  mkpair.
  - intros F; induction F as [t h]; simpl.
    mkpair.
    * induction t as [t|t]; [apply (ii1 (pr1 f t)) | apply (ii2 t)].
    * abstract (induction t as [t|t]; trivial; rewrite <- h; apply (toforallpaths _ _ _ (pr2 f) t)).
  - abstract (apply funextsec; intros [[t|t] h]; trivial; apply (toforallpaths _ _ _ (pr2 f) t)).
Defined.

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
  apply LimsCsort. (* Limits in Set/sort *)
+ apply is_omega_cocont_postcomp_proj.
Defined.

(* This defines X^as where as is a list. Outputs a product of functors if the list is nonempty and
otherwise the constant functor. *)
Definition exp_functors (xs : list (list sort × sort)) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET].
Proof.
(* Apply the exp functor to every element of the list *)
set (XS := map exp_functor xs).
(* If the list is empty we output the constant functor *)
set (T := constant_functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET]
                           (constant_functor SET_over_sort HSET TerminalHSET)).
(* TODO: Maybe use indexed finite products instead of a fold? *)
use (foldr1 (fun F G => BinProduct_of_functors _ _ _ F G) T XS).
apply BinProducts_functor_precat.
apply BinProductsHSET.
Defined.

Lemma is_omega_cocont_exp_functors (xs : list (list sort × sort)) :
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
    * apply BinProducts_functor_precat.
      apply BinProducts_from_Lims.
      apply has_homsets_Csort.
      apply LimsCsort.
    * apply is_omega_cocont_constprod_functor1; try apply functor_category_has_homsets.
      apply has_exponentials_functor_HSET, has_homsets_Csort.
    * apply is_omega_cocont_exp_functor.
    * apply (IHn (k,,xs)).
Defined.

Lemma is_omega_cocont_postcomp_HatFunctor (t : sort) :
  is_omega_cocont (post_composition_functor SET_over_sort  _ _
       (homset_property SET) (homset_property SET_over_sort)
       (HatFunctor t)).
Proof.
(* intros d L ccL Hccl F ccF; simpl in *. *)
(* use unique_exists. *)
Admitted.

Definition hat_exp_functors (xst : list (list sort × sort) × sort) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET_over_sort].
Proof.
eapply functor_composite.
+ apply (exp_functors (pr1 xst)).
+ eapply post_composition_functor.
  apply (HatFunctor (pr2 xst)).
Defined.

Lemma is_omega_cocont_hat_exp_functors (xst : list (list sort × sort) × sort) :
  is_omega_cocont (hat_exp_functors xst).
Proof.
apply is_omega_cocont_functor_composite.
+ apply functor_category_has_homsets.
+ apply is_omega_cocont_exp_functors.
+ apply is_omega_cocont_postcomp_HatFunctor.
Defined.

Definition MultiSortedSigToFunctor (M : MultiSortedSig) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET_over_sort].
Proof.
use (coproduct_of_functors (ops M)).
+ apply Coproducts_functor_precat.
  apply Coproducts_from_Colims.
  apply has_homsets_Csort.
  apply slice_precat_colims.
  apply ColimsHSET.
+ intros op.
  apply (hat_exp_functors (arity M op)).
Defined.

Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig)
  (H : isdeceq (ops M)) : is_omega_cocont (MultiSortedSigToFunctor M).
Proof.
apply is_omega_cocont_coproduct_of_functors; try apply homset_property.
+ apply Products_functor_precat.
  apply Products_from_Lims.
  apply has_homsets_Csort.
  apply LimsCsort.
+ apply H.
+ intros op; apply is_omega_cocont_hat_exp_functors.
Defined.

End MBindingSig.
