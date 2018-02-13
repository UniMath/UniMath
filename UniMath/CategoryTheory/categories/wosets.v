Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.Combinatorics.WellOrderedSets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
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

Lemma WOlt_trich (X : WellOrderedSet) (x y : X) : y < x ∨ x = y ∨ x < y.
Admitted.

(* Definition WOlt' (X : WellOrderedSet) (x y : X) : UU := (x ≤ y) × (x != y). *)

(* Lemma WOlt_trich' (X : WellOrderedSet) (x y : X) : WOlt' X y x ∨ x = y ∨ WOlt' X x y. *)
(* Proof. *)
(* generalize (WO_istotal X x y). *)
(* apply hinhuniv; intros [H|H]. *)
(* unfold WOlt'. *)


Section wosetcat.

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

Definition woset_precategory : precategory.
Proof.
use mk_precategory.
- exists (WellOrderedSet,,wofun).
  split; simpl.
  + intros X.
    exists (idfun X).
    apply iswofun_idfun.
  + intros X Y Z f g.
    exists (pr1 g ∘ pr1 f).
    apply iswofun_funcomp.
- abstract (now repeat split; simpl; intros; apply wofun_eq).
Defined.

Lemma has_homsets_woset_precategory : has_homsets woset_precategory.
Proof.
intros X Y.
apply (isasetsubset (pr1wofun X Y)).
- apply isaset_set_fun_space.
- apply isinclpr1; intro f.
  apply isaprop_iswofun.
Qed.

Definition wosetcat : category :=
  (woset_precategory,,has_homsets_woset_precategory).

(* We need the following missing lemma: *)
Lemma isaset_WellOrderedSet : isaset WellOrderedSet.
Admitted.

Definition wo_setcategory : setcategory.
Proof.
exists woset_precategory.
split.
- apply isaset_WellOrderedSet.
- apply has_homsets_woset_precategory.
Defined.

End wosetcat.

Section wosetcat_structures.

Definition empty_woset : WellOrderedSet.
Proof.
exists emptyHSET.
use tpair.
- intros [].
- abstract (repeat split; try (now intros []);
            now intros T t'; apply (squash_to_hProp t'); intros [[]]).
Defined.

Lemma Initial_wosetcat : Initial wosetcat.
Proof.
use mk_Initial.
- exact empty_woset.
- apply mk_isInitial; intro a; simpl.
  use tpair.
  + exists fromempty.
    abstract (now split; intros []).
  + abstract (now intros f; apply wofun_eq, funextfun; intros []).
Defined.

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

Lemma Terminal_wosetcat : Terminal wosetcat.
Proof.
use mk_Terminal.
+ exact unit_woset.
+ apply mk_isTerminal; intro a.
  use tpair.
  - exists (λ _, tt).
    abstract (split; [intros x y H|intros x [] []]; apply (WO_isrefl unit_woset)).
  - abstract (now intros f; apply wofun_eq, funextfun; intros x; induction (pr1 f x)).
Defined.

(* In order not to unfold the relation below when running simpl *)
Opaque WOlt.
Opaque hdisj.

Lemma foo (X : WellOrderedSet) (x y : X) : x ≤ y → (x < y) ⨿ (x = y).
Admitted.

(* TODO: upstream the product of relations and its properties *)
Definition BinProduct_WellOrderedSet (X Y : WellOrderedSet) : WellOrderedSet.
Proof.
exists (X × Y)%set.
use tpair; simpl.
- intros xy xy'.
  exact ((pr1 xy < pr1 xy') ∨ (((pr1 xy = pr1 xy'),,pr21 X _ _) ∧ pr2 xy ≤ pr2 xy')).
- split;[split;[split;[split|]|]|].
  + intros [x1 x2] [y1 y2] [z1 z2].
    apply hinhuniv2; intros H1 H2; apply hinhpr.
    simpl in *.
    induction H1 as [H1|H1]; induction H2 as [H2|H2].
    * now apply inl, (WOlt_istrans _ _ _ _ H1 H2).
    * now rewrite <- (pr1 H2); apply inl.
    * now rewrite (pr1 H1); apply inl.
    * apply inr; split.
      { exact (pathscomp0 (pr1 H1) (pr1 H2)). }
      { exact (WO_istrans _ _ _ _ (pr2 H1) (pr2 H2)). }
  + intros [x y]. simpl.
    apply hinhpr, inr; split; trivial.
    now apply WO_isrefl.
  + intros [x1 y1] [x2 y2]; simpl; intros H.
    apply factor_through_squash.
    generalize (pr21 Y y1 y2).
    generalize (pr21 X x1 x2).
    admit.
    intros H1.
    generalize H; clear H.
    apply factor_through_squash.
    admit.
    intros H2.
    induction H1 as [H1|H1]; induction H2 as [H2|H2].
    * now induction (WOlt_isirrefl _ _ (WOlt_istrans _ _ _ _ H1 H2)).
    * rewrite (pr1 H2) in H1.
      now induction (WOlt_isirrefl _ _ H1).
    * rewrite (pr1 H1) in H2.
      now induction (WOlt_isirrefl _ _ H2).
    * now rewrite (pr1 H1), (WO_isantisymm Y _ _ (pr2 H1) (pr2 H2)).
  + intros [x1 y1] [x2 y2]; simpl.
    generalize (WO_istotal X x1 x2), (WO_istotal Y y1 y2).
    apply hinhuniv2.
    intros [Hx|Hx]; intros [Hy|Hy]; apply hinhpr.
    * induction (foo X _ _ Hx) as [H|H].
      now apply inl, hinhpr, inl.
      now apply inl, hinhpr, inr.
    * induction (foo X _ _ Hx) as [H|H].
      now apply inl, hinhpr, inl.
      now apply inr, hinhpr, inr.
    * induction (foo X _ _ Hx) as [H|H].
      now apply inr, hinhpr, inl.
      now apply inl, hinhpr, inr.
    * induction (foo X _ _ Hx) as [H|H].
      now apply inr, hinhpr, inl.
      now apply inr, hinhpr, inr.
    Print isirrefl.
    generalize
    unfold isaprop.
    simpl.
    intros H1 H2.
    intros xy1 xy2.

    intros xx yy.
    induction yy.
    simpl.
    Search dirprod isaprop.
    Search (_,,_ = _,,_).
    generalize (@total2_paths2).
    apply squash_to_hProp.
      generalize (WO_isantisymm X x1 x2).



    Unset Printing Notations. right.
  + admit.
  + admit.
  + admit.
(*   + intros [x y]. *)
(*     exact (WO_isrefl X x,,WO_isrefl Y y). *)
(*   + intros [x1 y1] [x2 y2] [H1 H2] [H3 H4]; simpl in *. *)
(*     now rewrite (WO_isantisymm X _ _ H1 H3), (WO_isantisymm Y _ _ H2 H4). *)
(*   + intros [x1 y1] [x2 y2]. *)
(*     generalize (WO_istotal X x1 x2). *)
(*     apply hinhuniv; intros H1. *)
(*     generalize (WO_istotal Y y1 y2). *)
(*     apply hinhuniv; intros H2. *)
(*     apply hinhpr. *)
(*     simpl in *. *)
(*     induction H1 as [H1|H1]. *)
(*     induction H2 as [H2|H2]. *)
(*     left. *)
(*     now split. *)
(*     trivial. *)
(*     Print istotal. *)
(*     intros HH. *)
(*     apply HH. *)
Admitted.

(* Lemma BinProducts_wosetcat : BinProducts wosetcat. *)
(* Proof. *)
(* intros A B. *)
(* use mk_BinProduct. *)
(* - simpl in *. ; apply (tpair _ (A × B)). *)
(*   abstract (apply isasetdirprod; apply setproperty). *)
(* - simpl in *; apply pr1. *)
(* - simpl in *; intros x; apply (pr2 x). *)
(* - apply (mk_isBinProduct _ has_homsets_HSET). *)
(*   intros C f g; simpl in *. *)
(*   use tpair. *)
(*   * apply (tpair _ (prodtofuntoprod (f ,, g))); abstract (split; apply idpath). *)
(*   * abstract (intros h; apply subtypeEquality; *)
(*     [ intros x; apply isapropdirprod; apply has_homsets_HSET *)
(*     | destruct h as [t [ht1 ht2]]; simpl; apply funextfun; intro x; *)
(*                rewrite <- ht2, <- ht1; unfold compose; simpl; *)
(*                unfold prodtofuntoprod; *)
(*                now case (t x)]). *)
(* Defined. *)

End wosetcat_structures.