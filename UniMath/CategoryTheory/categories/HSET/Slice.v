(** * Slices of [HSET] *)

(** ** Contents

- Locally cartesian closed structure
  - Terminal object ([Terminal_HSET_slice])
  - Binary products ([BinProducts_HSET_slice])
  - General indexed products ([Products_HSET_slice])
  - Exponentials ([Exponentials_HSET_slice])
- Colimits
  - Binary coproducts ([BinCoproducts_HSET_slice])
- The forgetful functor [HSET/X --> HSET] is a left adjoint
  ([is_left_adjoint_slicecat_to_cat])

Written by: Benedikt Ahrens, Anders Mörtberg

October 2015 - January 2016

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA. (* flip *)
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.AxiomOfChoice.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.covyoneda.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.

Local Open Scope cat.

(** ** Locally cartesian closed structure *)

Section set_slicecat.

Local Notation "HSET / X" := (slice_precat HSET X has_homsets_HSET) (only parsing).

(** *** Terminal object ([Terminal_HSET_slice]) *)

Lemma Terminal_HSET_slice X : Terminal (HSET / X).
Proof.
  now apply Terminal_slice_precat.
Defined.

(** *** Binary products ([BinProducts_HSET_slice]) *)

Lemma BinProducts_HSET_slice X : BinProducts (HSET / X).
Proof.
  now apply BinProducts_slice_precat, PullbacksHSET.
Defined.

(** *** General indexed products ([Products_HSET_slice]) *)

Section products_set_slice.

(* The following is an experiment which computes what the product in Set/X
   should be from the one in [X,Set] using the equivalence between Set/X
   and [X,Set] *)
(* Require Import UniMath.CategoryTheory.set_slice_fam_equiv. *)

(* Lemma Products_HSET_slice I X : Products I (HSET / X). *)
(* Proof. *)
(* intros F. *)
(* set (foo1 := Products_functor_precat I (discrete_precategory (pr1 X)) HSET (ProductsHSET I) has_homsets_HSET). *)
(* set (XHSET := [discrete_precategory (pr1 X), HSET, has_homsets_HSET]). *)
(* set (G := λ i, slice_to_fam X (F i) : XHSET). *)
(* set (foo2 := ProductObject I XHSET (foo1 G)). *)
(* set (goal := pr1 (pr1 (fam_to_slice _ foo2))). *)
(* cbn in goal. *)

(** Products in Set/X *)
Lemma Products_HSET_slice I X : Products I (HSET / X).
Proof.
intros F.
use mk_Product.
+ use tpair.
  - exists (∑ x : pr1 X, ∏ i : I, hfiber_hSet (pr2 (F i)) x).
    abstract (apply isaset_total2; [apply setproperty|];
              now intros x; apply impred_isaset; intro i; apply setproperty).
  - cbn. apply pr1.
+ intros i.
  use tpair.
  - intros H; apply (pr1 (pr2 H i)).
  - abstract (now apply funextsec; intros H; apply (!pr2 (pr2 H i))).
+ intros f H.
  use unique_exists.
  - use tpair; simpl.
    * intros x.
      exists (pr2 f x).
      intros i.
      exists (pr1 (H i) x).
      abstract (exact (!toforallpaths _ _ _ (pr2 (H i)) x)).
    * abstract (now apply funextsec).
  - abstract (now intros i; apply eq_mor_slicecat, funextsec).
  - abstract (now intros g; apply impred_isaprop; intro i; apply has_homsets_slice_precat).
  - abstract(simpl; intros [y1 y2] Hy; apply eq_mor_slicecat, funextsec; intro x;
    use total2_paths_f; [apply (toforallpaths _ _ _ (!y2) x)|];
    apply funextsec; intro i; apply subtypeEquality; [intros w; apply setproperty|];
    destruct f as [f Hf]; cbn in *;
    rewrite y2;
    simpl;
    rewrite idpath_transportf;
    rewrite <- Hy;
    reflexivity).
Defined.

End products_set_slice.

(** *** Exponentials ([Exponentials_HSET_slice]) *)

(** Direct proof that HSET/X has exponentials using explicit formula in example 2.2 of:

    https://ncatlab.org/nlab/show/locally+cartesian+closed+category#in_category_theory
*)

Definition hfiber_fun (X : HSET) (f : HSET / X) : HSET / X → HSET / X.
Proof.
intros g.
  use tpair.
  - exists (∑ x, HSET⟦hfiber_hSet (pr2 f) x,hfiber_hSet (pr2 g) x⟧).
    abstract (apply isaset_total2; [ apply setproperty | intros x; apply has_homsets_HSET ]).
  - cbn. now apply pr1.
Defined.

Definition hfiber_functor (X : HSET) (f : HSET / X) :
  functor (HSET / X) (HSET / X).
Proof.
  use mk_functor.
  + use tpair.
    * apply (hfiber_fun _ f).
    * cbn. intros a b g.
      { use tpair; simpl.
      - intros h.
        exists (pr1 h).
        intros fx.
        use tpair.
        * exact (pr1 g (pr1 (pr2 h fx))).
        * abstract (etrans; [ apply (!toforallpaths _ _ _ (pr2 g) (pr1 (pr2 h fx)))|];
                    apply (pr2 (pr2 h fx))).
      - abstract (now apply funextsec).
      }
  + split.
    - intros x; apply (eq_mor_slicecat has_homsets_HSET); simpl.
      apply funextsec; intros [y hy].
      use total2_paths_f; [ apply idpath |].
      apply funextsec; intros w; apply subtypeEquality; [|apply idpath].
      now intros XX; apply setproperty.
    - intros x y z g h; apply (eq_mor_slicecat has_homsets_HSET); simpl.
      apply funextsec; intros [w hw].
      use total2_paths_f; [ apply idpath |].
      apply funextsec; intros w'.
      apply subtypeEquality; [|apply idpath].
      now intros XX; apply setproperty.
Defined.

Local Definition eta X (f : HSET / X) :
  nat_trans (functor_identity (HSET / X))
            (functor_composite (constprod_functor1 (BinProducts_HSET_slice X) f) (hfiber_functor X f)).
Proof.
  use mk_nat_trans.
  + intros g; simpl.
    use tpair.
    * intros y; simpl.
      exists (pr2 g y); intros fgy.
      exists ((pr1 fgy,,y),,(pr2 fgy)).
      abstract (now apply (pr2 fgy)).
    * abstract (now apply funextsec).
  + intros [g Hg] [h Hh] [w Hw].
    apply (eq_mor_slicecat has_homsets_HSET), funextsec; intro x1.
    apply (two_arg_paths_f (!toforallpaths _ _ _ Hw x1)), funextsec; intro y.
    repeat (apply subtypeEquality; [intros x; apply setproperty|]); cbn in *.
    now induction (! toforallpaths _ _ (λ x : g, Hh (w x)) _ _).
Defined.

Local Definition eps X (f : HSET / X) :
  nat_trans (functor_composite (hfiber_functor X f) (constprod_functor1 (BinProducts_HSET_slice X) f))
            (functor_identity (HSET / X)).
Proof.
  use mk_nat_trans.
  + intros g; simpl.
    use tpair.
    * intros H; apply (pr1 ((pr2 (pr2 (pr1 H))) (pr1 (pr1 H),,pr2 H))).
    * abstract (cbn; apply funextsec; intros [[x1 [x2 x3]] x4]; simpl in *;
                now rewrite (pr2 (x3 (x1,,x4))), x4).
  + intros g h w; simpl.
    apply (eq_mor_slicecat has_homsets_HSET), funextsec; intro x1; cbn.
    now repeat apply maponpaths; apply setproperty.
Defined.

Lemma Exponentials_HSET_slice (X : HSET) : Exponentials (BinProducts_HSET_slice X).
Proof.
  intros f.
  exists (hfiber_functor _ f).
  use mk_are_adjoints.
  - apply eta.
  - apply eps.
  - split.
    + intros x; apply eq_mor_slicecat, funextsec; intro x1.
      now apply subtypeEquality; [intro y; apply setproperty|]; reflexivity.
    + intros x; apply eq_mor_slicecat, funextsec; intro x1; simpl.
      use total2_paths_f; [apply idpath|]; cbn.
      apply funextsec; intro y.
      use subtypeEquality.
      * intro z; apply setproperty.
      * simpl.
        apply maponpaths.
        apply maponpaths.
        reflexivity.
Defined.

(** ** Colimits *)

(** *** Binary coproducts ([BinCoproducts_HSET_slice]) *)

Lemma BinCoproducts_HSET_slice X : BinCoproducts (HSET / X).
Proof.
  now apply BinCoproducts_slice_precat, BinCoproductsHSET.
Defined.

(** ** The forgetful functor [HSET/X --> HSET] is a left adjoint *)

Lemma is_left_adjoint_slicecat_to_cat_HSET (X : HSET) :
  is_left_adjoint (slicecat_to_cat has_homsets_HSET X).
Proof.
apply is_left_adjoint_slicecat_to_cat, BinProductsHSET.
Defined.

End set_slicecat.
