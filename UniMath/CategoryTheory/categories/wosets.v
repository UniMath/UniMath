Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.Combinatorics.WellOrderedSets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.covyoneda.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Local Open Scope cat.
Local Open Scope woset.
Local Open Scope functions.

(* TODO: upstream *)
Notation "x < y" := (WOlt x y) : woset.

Lemma WO_isrefl (X : WellOrderedSet) : isrefl (WOrel X).
Proof.
exact (pr211 (WO_isTotalOrder X)).
Defined.

Lemma WO_istrans (X : WellOrderedSet) : istrans (WOrel X).
Proof.
exact (pr111 (WO_isTotalOrder X)).
Defined.

Lemma WO_istotal (X : WellOrderedSet) : istotal (WOrel X).
Proof.
exact (pr2 (WO_isTotalOrder X)).
Defined.

Lemma WO_isantisymm (X : WellOrderedSet) : isantisymm (WOrel X).
Proof.
exact (pr21 (WO_isTotalOrder X)).
Defined.

Lemma WOlt_istrans (X : WellOrderedSet) : istrans (@WOlt X).
Proof.
intros x y z H1 H2 H3; simpl in *.
generalize (WO_istotal X y z).
apply (@hinhuniv _ (_,,isapropempty)); intros [H|H]; simpl.
- now apply H1, (WO_istrans X y z x H H3).
- now apply H2.
Qed.

Lemma WOlt_isirrefl (X : WellOrderedSet) : isirrefl (@WOlt X).
Proof.
now intros x; simpl; intros H; apply H, WO_isrefl.
Qed.

(** Equivalent definition of the < relation *)
Definition WOlt' (X : WellOrderedSet) (x y : X) : hProp.
Proof.
exists ((x ≤ y) × (x != y)).
abstract (now apply isapropdirprod; [ apply propproperty | apply isapropneg ]).
Defined.

Lemma WOlt_to_WOlt' (X : WellOrderedSet) (hX : isdeceq X) (x y : X) : x < y → WOlt' X x y.
Proof.
intros H.
generalize (WO_istotal X x y).
apply hinhuniv; intros [Hle|Hle]; simpl.
- induction (hX x y) as [Heq|Hneq].
  + rewrite Heq in H.
    induction (WOlt_isirrefl _ _ H).
  + now split.
- induction (H Hle).
Qed.

Lemma WOlt'_to_WOlt (X : WellOrderedSet) (x y : X) : WOlt' X x y → x < y.
Proof.
intros [H1 H2] H3.
now apply H2, (WO_isantisymm X x y H1 H3).
Qed.

Lemma WOlt_trich (X : WellOrderedSet) (hX : isdeceq X) (x y : X) :
  y < x ∨ x = y ∨ x < y.
Proof.
induction (hX x y) as [Heq|Hneq].
- now apply hinhpr, inr, hinhpr, inl.
- generalize (WO_istotal X x y).
  apply hinhuniv; intros [Hle|Hle].
  + now apply hinhpr, inr, hinhpr, inr, WOlt'_to_WOlt.
  + apply hinhpr, inl, WOlt'_to_WOlt; split; trivial.
    now intros H; apply Hneq.
Qed.

(** Functions of well-ordered sets that preserve the ordering and initial segments *)
Definition iswofun {X Y : WellOrderedSet} (f : X → Y) : UU :=
  (iscomprelrelfun (WOrel X) (WOrel Y) f) ×
  (∏ (x : X) (y : Y), y < f x → ∃ (z : X), z < x × f z = y).

Lemma isaprop_iswofun {X Y : WellOrderedSet} (f : X → Y) : isaprop (iswofun f).
Proof.
intros h; apply isapropdirprod; do 3 (apply impred_isaprop; intros).
- now apply propproperty.
- now apply isapropishinh.
Qed.

Definition wofun (X Y : WellOrderedSet) : UU := ∑ (f : X → Y), iswofun f.

Definition pr1wofun (X Y : WellOrderedSet) : wofun X Y → (X → Y) := @pr1 _ _.

Lemma wofun_eq {X Y : WellOrderedSet} {f g : wofun X Y} : pr1 f = pr1 g → f = g.
Proof.
intros Heq.
apply subtypeEquality; trivial.
now intros h; apply isaprop_iswofun.
Qed.

Lemma iswofun_idfun {X : WellOrderedSet} : iswofun (idfun X).
Proof.
split.
- now intros x.
- intros x y hxy.
  now apply hinhpr; exists y.
Qed.

Lemma iswofun_funcomp {X Y Z : WellOrderedSet} (f : wofun X Y) (g : wofun Y Z) :
  iswofun (pr1 g ∘ pr1 f).
Proof.
induction f as [f [h1f h2f]].
induction g as [g [h1g h2g]].
split.
- intros x y hxy.
  exact (h1g _ _ (h1f _ _ hxy)).
- intros x z hf.
  generalize (h2g (f x) z hf).
  apply hinhuniv; intros [y [h1y h2y]].
  generalize (h2f x y h1y).
  apply hinhuniv; intros [x' [h1x' h2x']].
  apply hinhpr; exists x'; cbn.
  now rewrite h2x'.
Qed.

(** The empty set is well-ordered *)
Definition empty_woset : WellOrderedSet.
Proof.
exists emptyHSET.
use tpair.
- intros [].
- abstract (repeat split; try (now intros []);
            now intros T t'; apply (squash_to_hProp t'); intros [[]]).
Defined.

(** The unit set is well-ordered *)
Definition unit_woset : WellOrderedSet.
Proof.
exists unitHSET.
use tpair.
- intros x y.
  exists (x = y).
  abstract (apply isapropifcontr, isapropunit).
- repeat split.
  + now intros x y z [].
  + now intros x.
  + intros [] [] H H2.
    now apply H2, inl.
  + intros T t'; apply (squash_to_hProp t'); clear t'; intros [[] H].
    apply hinhpr; exists tt.
    now split; [|intros []].
Defined.

(** * The category of well-ordered sets with order preserving morphisms *)
Section wosetfuncat.

Definition wosetfun_precategory : precategory.
Proof.
use mk_precategory.
- exists (WellOrderedSet,,wofun).
  split; simpl.
  + intros X.
    apply (_,,iswofun_idfun).
  + intros X Y Z f g.
    apply (_,,iswofun_funcomp f g).
- abstract (now repeat split; simpl; intros; apply wofun_eq).
Defined.

Lemma has_homsets_wosetfun_precategory : has_homsets wosetfun_precategory.
Proof.
intros X Y.
apply (isasetsubset (pr1wofun X Y)).
- apply isaset_set_fun_space.
- apply isinclpr1; intro f.
  apply isaprop_iswofun.
Qed.

Definition wosetfuncat : category :=
  (wosetfun_precategory,,has_homsets_wosetfun_precategory).

(* TODO: We need the following missing lemma: *)
(* Lemma isaset_WellOrderedSet : isaset WellOrderedSet. *)
(* Admitted. *)

(* Definition wo_setcategory : setcategory. *)
(* Proof. *)
(* exists wosetfun_precategory. *)
(* split. *)
(* - apply isaset_WellOrderedSet. *)
(* - apply has_homsets_wosetfun_precategory. *)
(* Defined. *)

Lemma Initial_wosetfuncat : Initial wosetfuncat.
Proof.
use mk_Initial.
- exact empty_woset.
- apply mk_isInitial; intro a; simpl.
  use tpair.
  + exists fromempty.
    abstract (now split; intros []).
  + abstract (now intros f; apply wofun_eq, funextfun; intros []).
Defined.

Lemma Terminal_wosetfuncat : Terminal wosetfuncat.
Proof.
use mk_Terminal.
+ exact unit_woset.
+ apply mk_isTerminal; intro a.
  use tpair.
  - exists (λ _, tt).
    abstract (split; [intros x y H|intros x [] []]; apply (WO_isrefl unit_woset)).
  - abstract (now intros f; apply wofun_eq, funextfun; intros x; induction (pr1 f x)).
Defined.

(** Can we prove further properties of wosetcat? It doesn't seem like it has binary products, at
least the lexicographic ordering does not work. Consider {0,1} × {2,3}, in it we have (0,3) < (1,2)
but pr2 doesn't preserve the ordering, *)

End wosetfuncat.

(** * The category of well-ordered sets with arbitrary functions as morphisms *)
Section wosetcat.

Definition woset_precategory : precategory.
Proof.
use mk_precategory.
- use tpair.
  + exists WellOrderedSet.
    apply (λ X Y, pr11 X → pr11 Y).
  + split; simpl.
    * intros X; apply idfun.
    * intros X Y Z f g; apply (funcomp f g).
- abstract (now intros).
Defined.

Lemma has_homsets_wosetcat : has_homsets woset_precategory.
Proof.
now intros X Y; apply hset_fun_space.
Qed.

Definition wosetcat : category :=
  (woset_precategory,,has_homsets_wosetcat).

(* TODO: We need the following missing lemma: *)
(* Lemma isaset_WellOrderedSet : isaset WellOrderedSet. *)
(* Admitted. *)

(* Definition wo_setcategory : setcategory. *)
(* Proof. *)
(* exists woset_precategory. *)
(* split. *)
(* - apply isaset_WellOrderedSet. *)
(* - apply has_homsets_woset_precategory. *)
(* Defined. *)

Lemma Initial_wosetcat : Initial wosetcat.
Proof.
use mk_Initial.
- exact empty_woset.
- apply mk_isInitial; intro a.
  use tpair.
  + simpl; intro e; induction e.
  + abstract (intro f; apply funextfun; intro e; induction e).
Defined.

Lemma Terminal_wosetcat : Terminal wosetcat.
Proof.
use mk_Terminal.
- exact unit_woset.
- apply mk_isTerminal; intro a.
  exists (λ _, tt).
  abstract (simpl; intro f; apply funextfun; intro x; case (f x); apply idpath).
Defined.

(** Direct proof that woset has binary products using Zermelo's well-ordering theorem. We could
prove this using the lexicograpic ordering, but it seems like we need decidable equality for this to
work which would not work for exponentials. *)
Lemma hasBinProducts_wosetcat (AC : AxiomOfChoice) : hasBinProducts wosetcat.
Proof.
intros A B.
apply (squash_to_hProp (@ZermeloWellOrdering (pr1 A × pr1 B)%set AC)); intros R.
apply hinhpr.
use mk_BinProduct.
- exists (BinProductObject _ (BinProductsHSET (pr1 A) (pr1 B))).
  exact R.
- apply (BinProductPr1 _ (BinProductsHSET _ _)).
- apply (BinProductPr2 _ (BinProductsHSET _ _)).
- intros H.
  apply (isBinProduct_BinProduct _ (BinProductsHSET (pr1 A) (pr1 B)) (pr1 H)).
Defined.

End wosetcat.