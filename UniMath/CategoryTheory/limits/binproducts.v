(** * Direct implementation of binary products

Written by: Benedikt Ahrens, Ralph Matthes
Extended by: Anders Mörtberg and Tomi Pannila
Extended by: Langston Barrett (@siddharthist), 2018

*)

(** ** Contents

- Definition of binary products
- Definition of binary product functor ([binproduct_functor])
- Definition of a binary product structure on a functor category by taking
  pointwise binary products in the target category ([BinProducts_functor_precat])
- Binary products from limits ([BinProducts_from_Lims])
- Equivalent universal property: [(C --> A) × (C --> B) ≃ (C --> A × B)]
- Terminal object as the unit (up to isomorphism) of binary products
- Definition of the "associative" z-isomorphism [BinProduct_assoc]
- Definition of the diagonal map [diagonalMap]

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Local Open Scope cat.

(** ** Definition of binary products *)
Section binproduct_def.

Context (C : category).

Definition isBinProduct (c d p : C) (p1 : p --> c) (p2 : p --> d) : UU :=
  ∏ (a : C) (f : a --> c) (g : a --> d),
  ∃! fg, (fg · p1 = f) × (fg · p2 = g).

Lemma isaprop_isBinProduct (c d p : C) (p1 : p --> c) (p2 : p --> d) :
  isaprop (isBinProduct c d p p1 p2).
Proof.
  do 3 (apply impred_isaprop; intro).
  apply isapropiscontr.
Qed.

Definition BinProduct (c d : C) : UU :=
  ∑ pp1p2 : (∑ p : C, (p --> c) × (p --> d)),
    isBinProduct c d (pr1 pp1p2) (pr1 (pr2 pp1p2)) (pr2 (pr2 pp1p2)).

Definition BinProducts : UU := ∏ (c d : C), BinProduct c d.
Definition hasBinProducts : UU := ∏ (c d : C), ∥ BinProduct c d ∥.

Definition BinProductObject {c d : C} (P : BinProduct c d) : C := pr1 (pr1 P).
Coercion BinProductObject : BinProduct >-> ob.

Definition BinProductPr1 {c d : C} (P : BinProduct c d): BinProductObject P --> c :=
  pr1 (pr2 (pr1 P)).
Definition BinProductPr2 {c d : C} (P : BinProduct c d) : BinProductObject P --> d :=
   pr2 (pr2 (pr1 P)).

Definition isBinProduct_BinProduct {c d : C} (P : BinProduct c d) :
   isBinProduct c d (BinProductObject P) (BinProductPr1 P) (BinProductPr2 P).
Proof.
  exact (pr2 P).
Defined.

Definition BinProductArrow {c d : C} (P : BinProduct c d) {a : C} (f : a --> c) (g : a --> d) :
       a --> BinProductObject P.
Proof.
  exact (pr1 (pr1 (isBinProduct_BinProduct P _ f g))).
Defined.

Lemma BinProductPr1Commutes (c d : C) (P : BinProduct c d):
     ∏ (a : C) (f : a --> c) g, BinProductArrow P f g · BinProductPr1 P = f.
Proof.
  intros a f g.
  exact (pr1 (pr2 (pr1 (isBinProduct_BinProduct P _ f g)))).
Qed.

Lemma BinProductPr2Commutes (c d : C) (P : BinProduct c d):
     ∏ (a : C) (f : a --> c) g, BinProductArrow P f g · BinProductPr2 P = g.
Proof.
  intros a f g.
  exact (pr2 (pr2 (pr1 (isBinProduct_BinProduct P _ f g)))).
Qed.

Lemma BinProductArrowUnique (c d : C) (P : BinProduct c d) (x : C)
    (f : x --> c) (g : x --> d) (k : x --> BinProductObject P) :
    k · BinProductPr1 P = f -> k · BinProductPr2 P = g ->
      k = BinProductArrow P f g.
Proof.
  intros; apply path_to_ctr; split; assumption.
Qed.

Lemma BinProductArrowsEq (c d : C) (P : BinProduct c d) (x : C)
      (k1 k2 : x --> BinProductObject P) :
  k1 · BinProductPr1 P = k2 · BinProductPr1 P ->
  k1 · BinProductPr2 P = k2 · BinProductPr2 P ->
  k1 = k2.
Proof.
  intros H1 H2.
  set (p1 := k1 · BinProductPr1 P).
  set (p2 := k1 · BinProductPr2 P).
  rewrite (BinProductArrowUnique _ _ P _ p1 p2 k1).
  apply pathsinv0.
  apply BinProductArrowUnique.
  unfold p1. apply pathsinv0. apply H1.
  unfold p2. apply pathsinv0. apply H2.
  apply idpath. apply idpath.
Qed.

Definition make_BinProduct (a b : C) :
  ∏ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
   isBinProduct _ _ _ f g -> BinProduct a b.
Proof.
  intros.
  use tpair.
  - exists c.
    exists f.
    exact g.
  - exact X.
Defined.

Definition make_isBinProduct (a b p : C)
  (pa : C⟦p,a⟧) (pb : C⟦p,b⟧) :
  (∏ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
    ∃! k : C⟦c,p⟧, k · pa = f × k · pb = g) ->
  isBinProduct a b p pa pb.
Proof.
  intros H c cc g.
  apply H.
Defined.

Lemma BinProductArrowEta (c d : C) (P : BinProduct c d) (x : C)
    (f : x --> BinProductObject P) :
    f = BinProductArrow P (f · BinProductPr1 P) (f · BinProductPr2 P).
Proof.
  apply BinProductArrowUnique;
  apply idpath.
Qed.


Definition BinProductOfArrows {c d : C} (Pcd : BinProduct c d) {a b : C}
    (Pab : BinProduct a b) (f : a --> c) (g : b --> d) :
          BinProductObject Pab --> BinProductObject Pcd :=
    BinProductArrow Pcd (BinProductPr1 Pab · f) (BinProductPr2 Pab · g).

Lemma BinProductOfArrowsPr1 {c d : C} (Pcd : BinProduct c d) {a b : C}
    (Pab : BinProduct a b) (f : a --> c) (g : b --> d) :
    BinProductOfArrows Pcd Pab f g · BinProductPr1 Pcd = BinProductPr1 Pab · f.
Proof.
  unfold BinProductOfArrows.
  rewrite BinProductPr1Commutes.
  apply idpath.
Qed.

Lemma BinProductOfArrowsPr2 {c d : C} (Pcd : BinProduct c d) {a b : C}
    (Pab : BinProduct a b) (f : a --> c) (g : b --> d) :
    BinProductOfArrows Pcd Pab f g · BinProductPr2 Pcd = BinProductPr2 Pab · g.
Proof.
  unfold BinProductOfArrows.
  rewrite BinProductPr2Commutes.
  apply idpath.
Qed.


Lemma postcompWithBinProductArrow {c d : C} (Pcd : BinProduct c d) {a b : C}
    (Pab : BinProduct a b) (f : a --> c) (g : b --> d)
    {x : C} (k : x --> a) (h : x --> b) :
        BinProductArrow Pab k h · BinProductOfArrows Pcd Pab f g =
         BinProductArrow Pcd (k · f) (h · g).
Proof.
  apply BinProductArrowUnique.
  - rewrite <- assoc, BinProductOfArrowsPr1.
    rewrite assoc, BinProductPr1Commutes.
    apply idpath.
  - rewrite <- assoc, BinProductOfArrowsPr2.
    rewrite assoc, BinProductPr2Commutes.
    apply idpath.
Qed.


Lemma precompWithBinProductArrow {c d : C} (Pcd : BinProduct c d) {a : C}
    (f : a --> c) (g : a --> d) {x : C} (k : x --> a)  :
       k · BinProductArrow Pcd f g  = BinProductArrow Pcd (k · f) (k · g).
Proof.
  apply BinProductArrowUnique.
  -  rewrite <- assoc, BinProductPr1Commutes;
     apply idpath.
  -  rewrite <- assoc, BinProductPr2Commutes;
     apply idpath.
Qed.

End binproduct_def.


Section BinProducts.

Context (C : category) (CC : BinProducts C).

Definition BinProductOfArrows_comp (a b c d x y : C) (f : a --> c) (f' : b --> d) (g : c --> x) (g' : d --> y)
  : BinProductOfArrows _ (CC c d) (CC a b) f f' ·
    BinProductOfArrows _ (CC _ _) (CC _ _) g g'
    =
    BinProductOfArrows _ (CC _ _) (CC _ _)(f · g) (f' · g').
Proof.
  apply BinProductArrowUnique.
  - rewrite <- assoc.
    rewrite BinProductOfArrowsPr1.
    rewrite assoc.
    rewrite BinProductOfArrowsPr1.
    apply pathsinv0.
    apply assoc.
  - rewrite <- assoc.
    rewrite BinProductOfArrowsPr2.
    rewrite assoc.
    rewrite BinProductOfArrowsPr2.
    apply pathsinv0.
    apply assoc.
Qed.

Lemma BinProductOfArrows_idxcomp {a b c d : C} (f:C⟦ b, c ⟧) (g:C⟦ c, d ⟧)
  :   BinProductOfArrows _ (CC a c) (CC a b) (identity a) f ·
      BinProductOfArrows _ (CC _ _) (CC _ _) (identity a) g
  =
  BinProductOfArrows _ (CC _ _) (CC _ _)(identity a) (f·g).
Proof.
  now rewrite BinProductOfArrows_comp, id_right.
Qed.

Lemma BinProductOfArrows_compxid {a b c d : C} (f:C⟦ b, c ⟧) (g:C⟦ c, d ⟧)
  :   BinProductOfArrows _ (CC c a) (CC b a) f (identity a) ·
      BinProductOfArrows _ (CC _ _) (CC _ _) g (identity a)
      =
      BinProductOfArrows _ (CC _ _) (CC _ _) (f·g) (identity a).
Proof.
  now rewrite BinProductOfArrows_comp, id_right.
Qed.

Lemma BinProductOfArrows_id (a b:C)
  : BinProductOfArrows _ (CC a b) (CC a b) (identity a) (identity b)
    = identity _ .
Proof.
  unfold BinProductOfArrows.
  use pathsinv0.
  use BinProductArrowUnique.
  + now rewrite id_left, id_right.
  + now rewrite id_left, id_right.
Qed.

End BinProducts.

Section BinProduct_unique.

Context (C : category) (CC : BinProducts C) (a b : C).

Lemma BinProduct_endo_is_identity (P : BinProduct _ a b)
  (k : BinProductObject _ P --> BinProductObject _ P)
  (H1 : k · BinProductPr1 _ P = BinProductPr1 _ P)
  (H2 : k · BinProductPr2 _ P = BinProductPr2 _ P)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply BinProductArrowEta.
  apply pathsinv0.
  apply BinProductArrowUnique; apply pathsinv0.
  + rewrite id_left. exact H1.
  + rewrite id_left. exact H2.
Qed.

End BinProduct_unique.

(** ** Binary products from limits ([BinProducts_from_Lims]) *)

Section BinProducts_from_Lims.

Context (C : category).

Definition two_graph : graph := (bool,,λ _ _,empty).

Definition binproduct_diagram (a b : C) : diagram two_graph C.
Proof.
exists (λ x : bool, if x then a else b).
abstract (intros u v F; induction F).
Defined.

Definition Binproduct {a b c : C} (f : c --> a) (g : c --> b) :
  cone (binproduct_diagram a b) c.
Proof.
use make_cone.
+ intros x; induction x; assumption.
+ abstract (intros x y e; destruct e).
Defined.

Lemma BinProducts_from_Lims : Lims_of_shape two_graph C -> BinProducts C.
Proof.
intros H a b.
set (LC := H (binproduct_diagram a b)).
use make_BinProduct.
+ apply (lim LC).
+ apply (limOut LC true).
+ apply (limOut LC false).
+ apply (make_isBinProduct C); intros c f g.
  use unique_exists.
  - apply limArrow, (Binproduct f g).
  - abstract (split;
      [ apply (limArrowCommutes LC c (Binproduct f g) true)
      | apply (limArrowCommutes LC c (Binproduct f g) false) ]).
  - abstract (intros h; apply isapropdirprod; apply C).
  - abstract (now intros h [H1 H2]; apply limArrowUnique; intro x; induction x).
Defined.

End BinProducts_from_Lims.

Section test.

  Context (C : category) (H : BinProducts C).

Arguments BinProductObject [C] c d {_}.

Local Notation "c 'x' d" := (BinProductObject  c d )(at level 5).
(*
Check (λ c d : C, c x d).
*)
End test.

(** ** Definition of binary product functor ([binproduct_functor]) *)

Section binproduct_functor.

Context {C : category} (PC : BinProducts C).

Definition binproduct_functor_data :
  functor_data (category_binproduct C C) C.
Proof.
use tpair.
- intros p.
  apply (BinProductObject _ (PC (pr1 p) (pr2 p))).
- intros p q f.
  apply (BinProductOfArrows _ (PC (pr1 q) (pr2 q))
                           (PC (pr1 p) (pr2 p)) (pr1 f) (pr2 f)).
Defined.

Definition binproduct_functor : functor (category_binproduct C C) C.
Proof.
apply (tpair _ binproduct_functor_data).
abstract (split;
  [ intro x; simpl; apply pathsinv0, BinProduct_endo_is_identity;
    [ now rewrite BinProductOfArrowsPr1, id_right
    | now rewrite BinProductOfArrowsPr2, id_right ]
  | now intros x y z f g; simpl; rewrite BinProductOfArrows_comp]).
Defined.

End binproduct_functor.

(* Defines the product of two functors by:
    x -> (x,x) -> (F x,G x) -> F x * G x

  For a direct definition see FunctorsPointwiseBinProduct.v

*)
Definition BinProduct_of_functors_alt {C D : category} (HD : BinProducts D)
  (F G : functor C D) : functor C D :=
  functor_composite (bindelta_functor C)
     (functor_composite (pair_functor F G) (binproduct_functor HD)).


(** In the following section we show that if the morphism to components are
    zero, then the unique morphism factoring through the binproduct is the
    zero morphism. *)
Section BinProduct_zeroarrow.

  Context (C : category) (Z : Zero C).

  Lemma BinProductArrowZero {x y z: C} {BP : BinProduct C x y} (f : z --> x) (g : z --> y) :
    f = ZeroArrow Z _ _ -> g = ZeroArrow Z _ _ -> BinProductArrow C BP f g = ZeroArrow Z _ _ .
  Proof.
    intros X X0. apply pathsinv0.
    use BinProductArrowUnique.
    rewrite X. apply ZeroArrow_comp_left.
    rewrite X0. apply ZeroArrow_comp_left.
  Qed.

End BinProduct_zeroarrow.

(** ** Definition of a binary product structure on a functor category *)

(** Goal: lift binary products from the target (pre)category to the functor (pre)category *)
Section def_functor_pointwise_binprod.

Context (C D : category) (HD : BinProducts D).

Section BinProduct_of_functors.

Context (F G : functor C D).

Local Notation "c ⊗ d" := (BinProductObject _ (HD c d)).

Definition BinProduct_of_functors_ob (c : C) : D := F c ⊗ G c.

Definition BinProduct_of_functors_mor (c c' : C) (f : c --> c')
  : BinProduct_of_functors_ob c --> BinProduct_of_functors_ob c'
  := BinProductOfArrows _ _ _ (#F f) (#G f).

Definition BinProduct_of_functors_data : functor_data C D.
Proof.
  exists BinProduct_of_functors_ob.
  exact BinProduct_of_functors_mor.
Defined.

Lemma is_functor_BinProduct_of_functors_data : is_functor BinProduct_of_functors_data.
Proof.
  split; simpl; intros.
  - red; intros; simpl in *.
    apply pathsinv0.
    unfold BinProduct_of_functors_mor.
    apply BinProduct_endo_is_identity.
    + rewrite BinProductOfArrowsPr1.
      rewrite functor_id.
      apply id_right.
    + rewrite BinProductOfArrowsPr2.
      rewrite functor_id.
      apply id_right.
  - red; intros; simpl in *.
    unfold BinProduct_of_functors_mor.
    do 2 rewrite functor_comp.
    apply pathsinv0.
    apply BinProductOfArrows_comp.
Qed.

Definition BinProduct_of_functors : functor C D :=
  tpair _ _ is_functor_BinProduct_of_functors_data.

Lemma BinProduct_of_functors_alt_eq_BinProduct_of_functors :
  BinProduct_of_functors_alt HD F G = BinProduct_of_functors.
Proof.
now apply (functor_eq _ _ D).
Qed.

Definition binproduct_nat_trans_pr1_data : ∏ c, BinProduct_of_functors c --> F c
  := λ c : C, BinProductPr1 _ (HD (F c) (G c)).

Lemma is_nat_trans_binproduct_nat_trans_pr1_data
  : is_nat_trans _ _ binproduct_nat_trans_pr1_data.
Proof.
  red.
  intros c c' f.
  unfold binproduct_nat_trans_pr1_data.
  unfold BinProduct_of_functors. simpl.
  unfold BinProduct_of_functors_mor.
  apply BinProductOfArrowsPr1.
Qed.

Definition binproduct_nat_trans_pr1 : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_pr1_data.


Definition binproduct_nat_trans_pr2_data : ∏ c, BinProduct_of_functors c --> G c
  := λ c : C, BinProductPr2 _ (HD (F c) (G c)).

Lemma is_nat_trans_binproduct_nat_trans_pr2_data
  : is_nat_trans _ _ binproduct_nat_trans_pr2_data.
Proof.
  red.
  intros c c' f.
  unfold binproduct_nat_trans_pr2_data.
  unfold BinProduct_of_functors. simpl.
  unfold BinProduct_of_functors_mor.
  apply BinProductOfArrowsPr2.
Qed.

Definition binproduct_nat_trans_pr2 : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_pr2_data.


Section vertex.

(** The product morphism of a diagram with vertex [A] *)

Context (A : functor C D) (f : A ⟹ F) (g : A ⟹ G).

Definition binproduct_nat_trans_data : ∏ c,  A c --> BinProduct_of_functors c.
Proof.
  intro c.
  apply BinProductArrow.
  - exact (f c).
  - exact (g c).
Defined.

Lemma is_nat_trans_binproduct_nat_trans_data : is_nat_trans _ _ binproduct_nat_trans_data.
Proof.
  intros a b k.
  simpl.
  unfold BinProduct_of_functors_mor.
  unfold binproduct_nat_trans_data.
  set (XX:=postcompWithBinProductArrow).
  set (X1 := XX D _ _ (HD (F b) (G b))).
  set (X2 := X1 _ _ (HD (F a) (G a))).
  rewrite X2.
  clear X2 X1 XX.
  set (XX:=precompWithBinProductArrow).
  set (X1 := XX D _ _ (HD (F b) (G b))).
  rewrite X1.
  rewrite (nat_trans_ax f).
  rewrite (nat_trans_ax g).
  apply idpath.
Qed.

Definition binproduct_nat_trans : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_data.

Lemma binproduct_nat_trans_Pr1Commutes :
  nat_trans_comp _ _ _ binproduct_nat_trans binproduct_nat_trans_pr1  = f.
Proof.
  apply nat_trans_eq.
  - apply D.
  - intro c; simpl.
    apply BinProductPr1Commutes.
Qed.

Lemma binproduct_nat_trans_Pr2Commutes :
  nat_trans_comp _ _ _ binproduct_nat_trans binproduct_nat_trans_pr2  = g.
Proof.
  apply nat_trans_eq.
  - apply D.
  - intro c; simpl.
    apply BinProductPr2Commutes.
Qed.

End vertex.


Lemma binproduct_nat_trans_univ_prop (A : [C, D])
  (f : A --> (F:[C,D])) (g : A --> (G:[C,D])) :
   ∏
   t : ∑ fg : A --> (BinProduct_of_functors:[C,D]),
       fg · (binproduct_nat_trans_pr1 : (BinProduct_of_functors:[C,D]) --> F) = f
      ×
       fg · (binproduct_nat_trans_pr2 : (BinProduct_of_functors:[C,D]) --> G) = g,
   t =
   tpair
     (λ fg : A --> (BinProduct_of_functors:[C,D]),
      fg · (binproduct_nat_trans_pr1 : (BinProduct_of_functors:[C,D]) --> F) = f
   ×
      fg · (binproduct_nat_trans_pr2 : (BinProduct_of_functors:[C,D]) --> G) = g)
     (binproduct_nat_trans A f g)
     (make_dirprod (binproduct_nat_trans_Pr1Commutes A f g)
        (binproduct_nat_trans_Pr2Commutes A f g)).
Proof.
  intro t.
  simpl in *.
  destruct t as [t1 [ta tb]].
  simpl in *.
  apply subtypePath.
  - intro.
    simpl.
    apply isapropdirprod;
    apply isaset_nat_trans;
    apply D.
  - simpl.
    apply nat_trans_eq.
    + apply D.
    + intro c.
      unfold binproduct_nat_trans.
      simpl.
      unfold binproduct_nat_trans_data.
      apply BinProductArrowUnique.
      * apply (nat_trans_eq_pointwise ta).
      * apply (nat_trans_eq_pointwise tb).
Qed.

Definition functor_precat_binproduct_cone
  : BinProduct [C, D] F G.
Proof.
use make_BinProduct.
- apply BinProduct_of_functors.
- apply binproduct_nat_trans_pr1.
- apply binproduct_nat_trans_pr2.
- use make_isBinProduct.
  + intros A f g.
    exists (tpair _ (binproduct_nat_trans A f g)
             (make_dirprod (binproduct_nat_trans_Pr1Commutes _ _ _ )
                          (binproduct_nat_trans_Pr2Commutes _ _ _ ))).
    apply binproduct_nat_trans_univ_prop.
Defined.

End BinProduct_of_functors.

Definition BinProducts_functor_precat : BinProducts [C, D].
Proof.
  intros F G.
  apply functor_precat_binproduct_cone.
Defined.

End def_functor_pointwise_binprod.

Section BinProduct_of_functors_commutative.

  Context (C D : category) (BD : BinProducts D) (F G : functor C D).

Definition BinProduct_of_functors_commutes_data :
  nat_trans_data (BinProduct_of_functors C D BD F G) (BinProduct_of_functors C D BD G F).
Proof.
  intro c.
  use BinProductArrow.
  - apply BinProductPr2.
  - apply BinProductPr1.
Defined.

Definition BinProduct_of_functors_commutes_invdata :
  nat_trans_data (BinProduct_of_functors C D BD G F) (BinProduct_of_functors C D BD F G).
Proof.
  intro c.
  use BinProductArrow.
  - apply BinProductPr2.
  - apply BinProductPr1.
Defined.

Lemma BinProduct_of_functors_commutes_is_inverse (c: C) :
  is_inverse_in_precat (BinProduct_of_functors_commutes_data c) (BinProduct_of_functors_commutes_invdata c).
Proof.
  split.
  - apply BinProductArrowsEq.
    + rewrite assoc'.
      etrans.
      { apply maponpaths.
        apply BinProductPr1Commutes. }
      etrans.
      { apply BinProductPr2Commutes. }
      apply pathsinv0, id_left.
    + rewrite assoc'.
      etrans.
      { apply maponpaths.
        apply BinProductPr2Commutes. }
      etrans.
      { apply BinProductPr1Commutes. }
      apply pathsinv0, id_left.
  - apply BinProductArrowsEq.
    + rewrite assoc'.
      etrans.
      { apply maponpaths.
        apply BinProductPr1Commutes. }
      etrans.
      { apply BinProductPr2Commutes. }
      apply pathsinv0, id_left.
    + rewrite assoc'.
      etrans.
      { apply maponpaths.
        apply BinProductPr2Commutes. }
      etrans.
      { apply BinProductPr1Commutes. }
      apply pathsinv0, id_left.
Qed.

Lemma BinProduct_of_functors_commutes_law : is_nat_trans _ _ BinProduct_of_functors_commutes_data.
Proof.
  intros c c' f.
  cbn.
  unfold BinProduct_of_functors_mor.
  etrans.
  2: { apply pathsinv0, postcompWithBinProductArrow. }
  apply BinProductArrowUnique.
  - rewrite assoc'.
    etrans.
    { apply maponpaths.
      apply BinProductPr1Commutes. }
    etrans.
    { apply BinProductOfArrowsPr2. }
    apply idpath.
  - rewrite assoc'.
    etrans.
    { apply maponpaths.
      apply BinProductPr2Commutes. }
    etrans.
    { apply BinProductOfArrowsPr1. }
    apply idpath.
Qed.

Definition BinProduct_of_functors_commutes :
  nat_z_iso (BinProduct_of_functors C D BD F G) (BinProduct_of_functors C D BD G F).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact BinProduct_of_functors_commutes_data.
    + exact BinProduct_of_functors_commutes_law.
  - intro c.
    use make_is_z_isomorphism.
    { apply BinProduct_of_functors_commutes_invdata. }
    apply BinProduct_of_functors_commutes_is_inverse.
Defined.

End BinProduct_of_functors_commutative.


Section PairNatTrans.
  Context {C₁ C₂ C₃ : category}
          {F : C₁ ⟶ C₂}
          {G₁ G₂ G₃ : C₂ ⟶ C₃}
          (H : BinProducts C₃)
          (η₁ : F ∙ G₁ ⟹ F ∙ G₂)
          (η₂ : F ∙ G₁ ⟹ F ∙ G₃).

  Local Definition pair_nat_trans_data
    : nat_trans_data (F ∙ G₁) (F ∙ BinProduct_of_functors C₂ C₃ H G₂ G₃).
  Proof.
    intros x.
    apply (BinProductArrow).
    - exact (η₁ x).
    - exact (η₂ x).
  Defined.

  Definition pair_nat_trans_is_nat_trans
    : is_nat_trans
        (F ∙ G₁)
        (F ∙ BinProduct_of_functors C₂ C₃ H G₂ G₃)
        pair_nat_trans_data.
  Proof.
    intros x y f ; cbn.
    refine (precompWithBinProductArrow _ _ _ _ _ @ _).
    pose (pr2 η₁ x y f) as p.
    pose (pr2 η₂ x y f) as q.
    cbn in p, q.
    refine (_ @ _).
    {
      apply maponpaths.
      exact q.
    }
    refine (_ @ _).
    {
      apply maponpaths_2.
      exact p.
    }
    unfold BinProduct_of_functors_mor, BinProductOfArrows, BinProductPr1, BinProductPr2.
    exact (!(postcompWithBinProductArrow _ _ _ _ _ _ _)).
  Qed.

  Definition pair_nat_trans
    : F ∙ G₁ ⟹ F ∙ (BinProduct_of_functors _ _ H G₂ G₃).
  Proof.
    use make_nat_trans.
    - exact pair_nat_trans_data.
    - exact pair_nat_trans_is_nat_trans.
  Defined.
End PairNatTrans.

(** ** Construction of BinProduct from an isomorphism to BinProduct. *)
Section BinProduct_from_iso.

  Context (C : category).

  Local Lemma iso_to_isBinProduct_comm {x y z : C} (BP : BinProduct C x y)
        (i : iso z (BinProductObject C BP)) (w : C) (f : w --> x) (g : w --> y) :
    (BinProductArrow C BP f g · inv_from_iso i · (i · BinProductPr1 C BP) = f)
      × (BinProductArrow C BP f g · inv_from_iso i · (i · BinProductPr2 C BP) = g).
  Proof.
    split.
    - rewrite <- assoc. rewrite (assoc _ i).
      rewrite (iso_after_iso_inv i). rewrite id_left.
      apply BinProductPr1Commutes.
    - rewrite <- assoc. rewrite (assoc _ i).
      rewrite (iso_after_iso_inv i). rewrite id_left.
      apply BinProductPr2Commutes.
  Qed.

  Local Lemma iso_to_isBinProduct_unique {x y z : C} (BP : BinProduct C x y)
        (i : iso z (BinProductObject C BP)) (w : C) (f : C ⟦w, x⟧) (g : C ⟦w, y⟧) (y0 : C ⟦w, z⟧)
        (T : y0 · (i · BinProductPr1 C BP) = f × y0 · (i · BinProductPr2 C BP) = g) :
    y0 = BinProductArrow C BP f g · iso_inv_from_iso i.
  Proof.
    apply (post_comp_with_iso_is_inj _ _ i (pr2 i)).
    rewrite <- assoc. cbn. rewrite (iso_after_iso_inv i). rewrite id_right.
    apply BinProductArrowUnique.
    - rewrite <- assoc. apply (dirprod_pr1 T).
    - rewrite <- assoc. apply (dirprod_pr2 T).
  Qed.

  Lemma iso_to_isBinProduct {x y z : C} (BP : BinProduct C x y)
        (i : iso z (BinProductObject C BP)) :
    isBinProduct C _ _ z (i · (BinProductPr1 C BP))  (i · (BinProductPr2 C BP)).
  Proof.
    intros w f g.
    use unique_exists.
    (* Arrow *)
    - exact ((BinProductArrow C BP f g) · (iso_inv_from_iso i)).
    (* Commutativity *)
    - abstract (exact (iso_to_isBinProduct_comm BP i w f g)).
    (* Equality of equalities of morphisms. *)
    - abstract (intro; apply isapropdirprod; apply C).
    (* Uniqueness *)
    - abstract (intros y0 T; exact (iso_to_isBinProduct_unique BP i w f g y0 T)).
  Defined.

  Definition iso_to_BinProduct {x y z : C} (BP : BinProduct C x y)
             (i : iso z (BinProductObject C BP)) :
    BinProduct C x y := make_BinProduct C _ _ z
                                              (i · (BinProductPr1 C BP))
                                              (i · (BinProductPr2 C BP))
                                              (iso_to_isBinProduct BP i).

End BinProduct_from_iso.

(** ** Equivalent universal property: [(C --> A) × (C --> B) ≃ (C --> A × B)]

 Compare to [weqfuntoprodtoprod].
 *)

Section EquivalentDefinition.
  Context {C : category} {c d p : ob C} (p1 : p --> c) (p2 : p --> d).

  Definition postcomp_with_projections (a : ob C) (f : a --> p) :
    (a --> c) × (a --> d) := make_dirprod (f · p1)  (f · p2).

  Definition isBinProduct' : UU := ∏ a : ob C, isweq (postcomp_with_projections a).

  Definition isBinProduct'_weq (is : isBinProduct') :
    ∏ a, (a --> p) ≃ (a --> c) × (a --> d) :=
    λ a, make_weq (postcomp_with_projections a) (is a).

  Lemma isBinProduct'_to_isBinProduct :
    isBinProduct' -> isBinProduct _ _ _ p p1 p2.
  Proof.
    intros isBP' ? f g.
    apply (@iscontrweqf (hfiber (isBinProduct'_weq isBP' _)
                                (make_dirprod f g))).
    - use weqfibtototal; intro; cbn.
      unfold postcomp_with_projections.
      apply pathsdirprodweq.
    - apply weqproperty.
  Defined.

  Lemma isBinProduct_to_isBinProduct' :
    isBinProduct _ _ _ p p1 p2 -> isBinProduct'.
  Proof.
    intros isBP ? fg.
    unfold hfiber, postcomp_with_projections.
    apply (@iscontrweqf (∑ u : C ⟦ a, p ⟧, u · p1 = pr1 fg × u · p2 = pr2 fg)).
    - use weqfibtototal; intro; cbn.
      apply invweq, pathsdirprodweq.
    - exact (isBP a (pr1 fg) (pr2 fg)). (* apply universal property *)
  Defined.

  (* TODO: prove that [isBinProduct'_to_isBinProduct] is an equivalence *)

End EquivalentDefinition.

(** Match non-implicit arguments of [isBinProduct] *)
Arguments isBinProduct' _ _ _ _ _ : clear implicits.

(** ** Terminal object as the unit (up to isomorphism) of binary products *)

(** [T × x ≅ x]*)
Lemma terminal_binprod_unit_l_z_aux {C : category} (T : Terminal C) (BC : BinProducts C) (x : C) :
  is_inverse_in_precat (BinProductPr2 C (BC T x))
    (BinProductArrow C (BC T x) (TerminalArrow T x) (identity x)).
Proof.
  unfold is_inverse_in_precat.
  split; [|apply BinProductPr2Commutes].
  refine (precompWithBinProductArrow _ _ _ _ _ @ _).
  refine (_ @ !BinProductArrowEta _ _ _ _ _ (identity _)).
  apply maponpaths_12.
  - apply TerminalArrowEq.
  - exact (id_right _ @ !id_left _).
Qed.

Lemma terminal_binprod_unit_l_z {C : category}
      (T : Terminal C) (BC : BinProducts C) (x : C) :
  is_z_isomorphism (BinProductPr2 C (BC T x)).
Proof.
  use make_is_z_isomorphism.
  - apply BinProductArrow.
    + (** The unique [x -> T] *)
      apply TerminalArrow.
    + apply identity.
  - apply terminal_binprod_unit_l_z_aux.
Defined.

(** [x × T ≅ x]*)
Lemma terminal_binprod_unit_r_z_aux {C : category} (T : Terminal C) (BC : BinProducts C) (x : C) :
  is_inverse_in_precat (BinProductPr1 C (BC x T)) (BinProductArrow C (BC x T) (identity x)
                                                     (TerminalArrow T x)).
Proof.
  unfold is_inverse_in_precat.
  split; [|apply BinProductPr1Commutes].
  refine (precompWithBinProductArrow _ _ _ _ _ @ _).
  refine (_ @ !BinProductArrowEta _ _ _ _ _ (identity _)).
  apply maponpaths_12.
  - exact (id_right _ @ !id_left _).
  - apply TerminalArrowEq.
Qed.

Lemma terminal_binprod_unit_r_z {C : category}
      (T : Terminal C) (BC : BinProducts C) (x : C) :
  is_z_isomorphism (BinProductPr1 C (BC x T)).
Proof.
  use make_is_z_isomorphism.
  - apply BinProductArrow.
    + apply identity.
    + (** The unique [x -> T] *)
      apply TerminalArrow.
  - apply terminal_binprod_unit_r_z_aux.
Defined.

Section BinProduct_of_functors_with_terminal.

Context (C D : category) (HD : BinProducts D) (TD : Terminal D) (F : functor C D).

Definition terminal_BinProduct_of_functors_unit_l_data :
  nat_trans_data (BinProduct_of_functors C D HD (constant_functor C D TD) F) F.
Proof.
  intro c. exact (BinProductPr2 D (HD TD (F c))).
Defined.

Lemma terminal_BinProduct_of_functors_unit_l_law :
  is_nat_trans _ _ terminal_BinProduct_of_functors_unit_l_data.
Proof.
  intros c c' f.
  apply BinProductOfArrowsPr2.
Qed.

Definition terminal_BinProduct_of_functors_unit_l  :
  nat_z_iso (BinProduct_of_functors _ _ HD (constant_functor _ _ TD) F) F.
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact terminal_BinProduct_of_functors_unit_l_data.
    + exact terminal_BinProduct_of_functors_unit_l_law.
  - intro c. apply terminal_binprod_unit_l_z.
Defined.

Definition terminal_BinProduct_of_functors_unit_r_data :
  nat_trans_data (BinProduct_of_functors C D HD F (constant_functor C D TD)) F.
Proof.
  intro c. exact (BinProductPr1 D (HD (F c) TD)).
Defined.

Lemma terminal_BinProduct_of_functors_unit_r_law :
  is_nat_trans _ _ terminal_BinProduct_of_functors_unit_r_data.
Proof.
  intros c c' f.
  apply BinProductOfArrowsPr1.
Qed.

Definition terminal_BinProduct_of_functors_unit_r  :
  nat_z_iso (BinProduct_of_functors _ _ HD F (constant_functor _ _ TD)) F.
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact terminal_BinProduct_of_functors_unit_r_data.
    + exact terminal_BinProduct_of_functors_unit_r_law.
  - intro c. apply terminal_binprod_unit_r_z.
Defined.

End BinProduct_of_functors_with_terminal.

(**
 In a univalent category, the type of binary products on a given diagram
 is a proposition
 *)
Definition eq_BinProduct
           {C : category}
           {x y : C}
           (prod₁ prod₂ : BinProduct C x y)
           (q : BinProductObject _ prod₁ = BinProductObject _ prod₂)
           (e₁ : BinProductPr1 _ prod₁ = idtoiso q · BinProductPr1 _ prod₂)
           (e₂ : BinProductPr2 _ prod₁ = idtoiso q · BinProductPr2 _ prod₂)
  : prod₁ = prod₂.
Proof.
  use subtypePath.
  {
    intro.
    repeat (use impred ; intro).
    use isapropiscontr.
  }
  use total2_paths_f.
  - exact q.
  - rewrite transportf_dirprod.
    rewrite <- !idtoiso_precompose.
    rewrite !idtoiso_inv.
    use pathsdirprod ; cbn ; use z_iso_inv_on_right.
    + exact e₁.
    + exact e₂.
Qed.

Section IsoBinProduct.
  Context {C : category}
          {x y : C}
          (p₁ p₂ : BinProduct C x y).

  Let f : BinProductObject C p₁ --> BinProductObject C p₂
      := BinProductArrow _ _ (BinProductPr1 _ p₁) (BinProductPr2 _ p₁).

  Let g : BinProductObject C p₂ --> BinProductObject C p₁
      := BinProductArrow _ _ (BinProductPr1 _ p₂) (BinProductPr2 _ p₂).

  Local Lemma iso_between_BinProduct_eq
    : is_inverse_in_precat f g.
  Proof.
    unfold f, g.
    split.
    - use BinProductArrowsEq.
      + rewrite assoc'.
        rewrite !BinProductPr1Commutes.
        rewrite id_left.
        apply idpath.
      + rewrite assoc'.
        rewrite !BinProductPr2Commutes.
        rewrite id_left.
        apply idpath.
    - use BinProductArrowsEq.
      + rewrite assoc'.
        rewrite !BinProductPr1Commutes.
        rewrite id_left.
        apply idpath.
      + rewrite assoc'.
        rewrite !BinProductPr2Commutes.
        rewrite id_left.
        apply idpath.
  Qed.

  Definition iso_between_BinProduct
    : z_iso (BinProductObject C p₁) (BinProductObject C p₂).
  Proof.
    use make_z_iso.
    - exact f.
    - exact g.
    - exact iso_between_BinProduct_eq.
  Defined.

End IsoBinProduct.

Definition isaprop_BinProduct
           {C : category}
           (HC : is_univalent C)
           (x y : C)
  : isaprop (BinProduct C x y).
Proof.
  use invproofirrelevance.
  intros p₁ p₂.
  use eq_BinProduct.
  - refine (isotoid _ HC _).
    apply iso_between_BinProduct.
  - rewrite idtoiso_isotoid ; cbn.
    rewrite BinProductPr1Commutes.
    apply idpath.
  - rewrite idtoiso_isotoid ; cbn.
    rewrite BinProductPr2Commutes.
    apply idpath.
Qed.

(**
 Products when the projections are equal
 *)
Definition isBinProduct_eq_arrow
           {C : category}
           {x y z : C}
           {π₁ π₁' : z --> x}
           (p₁ : π₁ = π₁')
           {π₂ π₂' : z --> y}
           (p₂ : π₂ = π₂')
           (H : isBinProduct C x y z π₁ π₂)
  : isBinProduct C x y z π₁' π₂'.
Proof.
  pose (P := make_BinProduct _ _ _ _ _ _ H).
  use make_isBinProduct.
  intros w f g.
  use iscontraprop1.
  - abstract
      (induction p₁, p₂ ;
       apply isapropifcontr ;
       apply H).
  - simple refine (_ ,, _ ,, _).
    + exact (BinProductArrow _ P f g).
    + abstract
        (induction p₁ ;
         exact (BinProductPr1Commutes _ _ _ P _ f g)).
    + abstract
        (induction p₂ ;
         exact (BinProductPr2Commutes _ _ _ P _ f g)).
Defined.

(**
 Products of isos
 *)
Section BinProductOfIsos.
  Context {C : category}
          {a b c d : C}
          (Pab : BinProduct C a b)
          (Pcd : BinProduct C c d)
          (f : z_iso a c)
          (g : z_iso b d).

  Let fg : BinProductObject _ Pab --> BinProductObject _ Pcd
    := BinProductOfArrows _ _ _ f g.

  Let fg_inv : BinProductObject _ Pcd --> BinProductObject _ Pab
    := BinProductOfArrows _ _ _ (inv_from_z_iso f) (inv_from_z_iso g).

  Definition binproduct_of_z_iso_inv
    : is_inverse_in_precat fg fg_inv.
  Proof.
    split ; use BinProductArrowsEq ; unfold fg, fg_inv.
    - rewrite !assoc'.
      rewrite BinProductOfArrowsPr1.
      rewrite !assoc.
      rewrite BinProductOfArrowsPr1.
      rewrite !assoc'.
      rewrite z_iso_inv_after_z_iso.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite !assoc'.
      rewrite BinProductOfArrowsPr2.
      rewrite !assoc.
      rewrite BinProductOfArrowsPr2.
      rewrite !assoc'.
      rewrite z_iso_inv_after_z_iso.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite !assoc'.
      rewrite BinProductOfArrowsPr1.
      rewrite !assoc.
      rewrite BinProductOfArrowsPr1.
      rewrite !assoc'.
      rewrite z_iso_after_z_iso_inv.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite !assoc'.
      rewrite BinProductOfArrowsPr2.
      rewrite !assoc.
      rewrite BinProductOfArrowsPr2.
      rewrite !assoc'.
      rewrite z_iso_after_z_iso_inv.
      rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition binproduct_of_z_iso
    : z_iso (BinProductObject _ Pab) (BinProductObject _ Pcd).
  Proof.
    use make_z_iso.
    - exact fg.
    - exact fg_inv.
    - exact binproduct_of_z_iso_inv.
  Defined.

End BinProductOfIsos.

(*
Definition of the "associative" z-isomorphism
*)
Section BinProduct_assoc_z_iso.

  Context {C : category}
          (P : BinProducts C)
          (a b c : C).

  Let Pbc := P b c.
  Let Pa_bc := P a (BinProductObject _ Pbc).
  Let Pab := P a b.
  Let Pab_c := P (BinProductObject _ Pab) c.

  Definition BinProduct_assoc_mor : C ⟦ BinProductObject C Pa_bc , BinProductObject C Pab_c ⟧.
  Proof.
    use BinProductArrow.
    + use BinProductOfArrows.
      - exact (identity a).
      - use BinProductPr1.
    + use (compose (b := BinProductObject C Pbc)).
      - use BinProductPr2.
      - use BinProductPr2.
  Defined.

  Definition BinProduct_assoc_invmor : C ⟦ BinProductObject C Pab_c , BinProductObject C Pa_bc ⟧.
  Proof.
    use BinProductArrow.
    + use (compose (b := BinProductObject C Pab)).
      - use BinProductPr1.
      - use BinProductPr1.
    + use BinProductOfArrows.
      - use BinProductPr2.
      - exact (identity c).
  Defined.

  Lemma BinProduct_assoc_is_inverse : is_inverse_in_precat BinProduct_assoc_mor BinProduct_assoc_invmor.
  Proof.
    use make_is_inverse_in_precat.
    - unfold BinProduct_assoc_mor, BinProduct_assoc_invmor.
      use BinProductArrowsEq.
      * now rewrite
          id_left,
          assoc',
          BinProductPr1Commutes,
          assoc,
          BinProductPr1Commutes,
          BinProductOfArrowsPr1,
          id_right.
      * now rewrite
          id_left,
          assoc',
          BinProductPr2Commutes,
          postcompWithBinProductArrow,
          id_right,
          BinProductOfArrowsPr2,
          <-precompWithBinProductArrow,
          <-(id_left (BinProductPr1 C Pbc)),
          <-(id_left (BinProductPr2 C Pbc)),
          <-BinProductArrowEta,
          id_right.
    - unfold BinProduct_assoc_mor, BinProduct_assoc_invmor.
      use BinProductArrowsEq.
      * now rewrite
          id_left,
          assoc',
          BinProductPr1Commutes,
          postcompWithBinProductArrow,
          id_right,
          BinProductOfArrowsPr1,
          <-precompWithBinProductArrow,
          <-(id_left (BinProductPr1 C Pab)),
          <-(id_left (BinProductPr2 C Pab)),
          <-BinProductArrowEta, id_right.
      * now rewrite
          id_left,
          assoc',
          BinProductPr2Commutes,
          assoc,
          BinProductPr2Commutes,
          BinProductOfArrowsPr2,
          id_right.
  Qed.

  Definition BinProduct_assoc_is_z_iso : is_z_isomorphism (BinProduct_assoc_mor).
  Proof.
    use make_is_z_isomorphism.
    + exact BinProduct_assoc_invmor.
    + exact BinProduct_assoc_is_inverse.
  Defined.

  Definition BinProduct_assoc : z_iso (BinProductObject C Pa_bc) (BinProductObject C Pab_c).
  Proof.
    use make_z_iso'.
    + exact BinProduct_assoc_mor.
    + exact BinProduct_assoc_is_z_iso.
  Defined.

End BinProduct_assoc_z_iso.

Section BinProduct_OfArrows_assoc.

  Context {C : category}
  (P : BinProducts C)
  {a a' b b' c c' : C}
  (f : C ⟦ a', a ⟧) (g : C ⟦ b', b ⟧) (h : C ⟦ c', c ⟧).

  Let Pbc := P b c.
  Let Pa_bc := P a (BinProductObject _ Pbc).
  Let Pab := P a b.
  Let Pab_c := P (BinProductObject _ Pab) c.
  Let Pbc' := P b' c'.
  Let Pa_bc' := P a' (BinProductObject _ Pbc').
  Let Pab' := P a' b'.
  Let Pab_c' := P (BinProductObject _ Pab') c'.

  Lemma BinProduct_OfArrows_assoc
  : BinProductOfArrows _ Pa_bc Pa_bc' f (BinProductOfArrows _ Pbc Pbc' g h) · (BinProduct_assoc P a b c) =
    (BinProduct_assoc P a' b' c') · BinProductOfArrows _ Pab_c Pab_c' (BinProductOfArrows _ Pab Pab' f g) h.
  Proof.
    unfold BinProduct_assoc, BinProduct_assoc_mor.
    simpl.
    use BinProductArrowsEq.
    + rewrite !assoc', (BinProductPr1Commutes), BinProductOfArrowsPr1, assoc, BinProductPr1Commutes.
      use BinProductArrowsEq.
      - now rewrite !assoc',
          !BinProductOfArrowsPr1,
          !assoc,
          !BinProductOfArrowsPr1,
          id_right, !assoc', id_left.
      - now rewrite !assoc',
          !BinProductOfArrowsPr2,
          !assoc,
          !BinProductOfArrowsPr2,
          !assoc',
          !BinProductOfArrowsPr1.
    + now rewrite !assoc',
        !BinProductOfArrowsPr2, !BinProductPr2Commutes,
        !assoc,
        !BinProductOfArrowsPr2, !BinProductPr2Commutes,
        !assoc',
        !BinProductOfArrowsPr2.
  Qed.

End BinProduct_OfArrows_assoc.

Section diagonalMap.

  Context {C:category} (P : BinProducts C) (B:C).

  Definition diagonalMap' : C ⟦ B, BinProductObject C (P B B) ⟧.
  Proof.
    use BinProductArrow.
    - exact (identity B).
    - exact (identity B).
  Defined.

  Lemma diagonalMap_isMonic : isMonic (diagonalMap').
  Proof.
    use make_isMonic.
    intros x g h p.
    assert (p' :=
      (maponpaths (λ f, compose f (BinProductPr1 C (P B B))) p)).
    unfold diagonalMap' in p'.
    rewrite !assoc', BinProductPr1Commutes , !id_right in p'.
    exact p'.
  Qed.

  Definition diagonalMap : Monic _ B (BinProductObject C (P B B)).
  Proof.
    use make_Monic.
    + exact diagonalMap'.
    + exact diagonalMap_isMonic.
  Defined.

End diagonalMap.

Section ProductFunctions.
  Context {C : category}
          (prodC : BinProducts C).

  Definition prod_swap
             (x y : C)
    : prodC x y --> prodC y x.
  Proof.
    use BinProductArrow.
    - apply BinProductPr2.
    - apply BinProductPr1.
  Defined.

  Definition prod_lwhisker
             {x₁ x₂ : C}
             (f : x₁ --> x₂)
             (y : C)
    : prodC x₁ y --> prodC x₂ y.
  Proof.
    use BinProductOfArrows.
    - exact f.
    - exact (identity _).
  Defined.

  Definition prod_rwhisker
             (x : C)
             {y₁ y₂ : C}
             (g : y₁ --> y₂)
    : prodC x y₁ --> prodC x y₂.
  Proof.
    use BinProductOfArrows.
    - exact (identity _).
    - exact g.
  Defined.

  Proposition prod_lwhisker_rwhisker
              {x₁ x₂ : C}
              {y₁ y₂ : C}
              (f : x₁ --> x₂)
              (g : y₁ --> y₂)
    : prod_lwhisker f _ · prod_rwhisker _ g
      =
      BinProductOfArrows _ _ _ f g.
  Proof.
    unfold prod_lwhisker, prod_rwhisker.
    rewrite BinProductOfArrows_comp.
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Proposition prod_swap_swap
              (x y : C)
    : prod_swap x y · prod_swap y x = identity _.
  Proof.
    use BinProductArrowsEq.
    - unfold prod_swap.
      rewrite !assoc'.
      rewrite !id_left.
      rewrite BinProductPr1Commutes.
      rewrite BinProductPr2Commutes.
      apply idpath.
    - unfold prod_swap.
      rewrite !assoc'.
      rewrite !id_left.
      rewrite BinProductPr2Commutes.
      rewrite BinProductPr1Commutes.
      apply idpath.
  Qed.

  Proposition BinProductOfArrows_swap
              {x₁ x₂ : C}
              {y₁ y₂ : C}
              (f : x₁ --> x₂)
              (g : y₁ --> y₂)
    : BinProductOfArrows C (prodC _ _) (prodC _ _) f g · prod_swap x₂ y₂
      =
      prod_swap x₁ y₁ · BinProductOfArrows C _ _ g f.
  Proof.
    use BinProductArrowsEq.
    - unfold prod_swap.
      rewrite !assoc'.
      rewrite BinProductPr1Commutes.
      rewrite BinProductOfArrowsPr2.
      rewrite BinProductOfArrowsPr1.
      rewrite !assoc.
      rewrite BinProductPr1Commutes.
      apply idpath.
    - unfold prod_swap.
      rewrite !assoc'.
      rewrite BinProductPr2Commutes.
      rewrite BinProductOfArrowsPr2.
      rewrite BinProductOfArrowsPr1.
      rewrite !assoc.
      rewrite BinProductPr2Commutes.
      apply idpath.
  Qed.
End ProductFunctions.

(**
 Binary products are closed under iso
 *)
Definition isBinProduct_z_iso
           {C : category}
           {x y a₁ a₂ : C}
           {p₁ : a₁ --> x}
           {q₁ : a₁ --> y}
           {p₂ : a₂ --> x}
           {q₂ : a₂ --> y}
           (H : isBinProduct C x y a₁ p₁ q₁)
           (f : z_iso a₂ a₁)
           (r₁ : p₂ = f · p₁)
           (r₂ : q₂ = f · q₁)
  : isBinProduct C x y a₂ p₂ q₂.
Proof.
  intros w h₁ h₂.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
       use (cancel_z_iso _ _ f) ;
       use (BinProductArrowsEq _ _ _ (make_BinProduct _ _ _ _ _ _ H)) ;
       [ cbn ;
         rewrite !assoc' ;
         rewrite <- !r₁ ;
         exact (pr12 φ₁ @ !(pr12 φ₂))
       | cbn ;
         rewrite !assoc' ;
         rewrite <- !r₂ ;
         exact (pr22 φ₁ @ !(pr22 φ₂)) ]).
  - simple refine (_ ,, _ ,, _).
    + exact (BinProductArrow _ (make_BinProduct _ _ _ _ _ _ H) h₁ h₂ · inv_from_z_iso f).
    + abstract
        (rewrite r₁ ;
         rewrite !assoc' ;
         rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)) ;
         rewrite z_iso_after_z_iso_inv ;
         rewrite id_left ;
         apply BinProductPr1Commutes).
    + abstract
        (cbn ;
         rewrite r₂ ;
         rewrite !assoc' ;
         rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)) ;
         rewrite z_iso_after_z_iso_inv ;
         rewrite id_left ;
         apply (BinProductPr2Commutes _ _ _ (make_BinProduct _ _ _ _ _ _ H))).
Defined.

Section BinProductsFromProducts.

Context {C : category}.
Context (c d : C).

Let binproduct_indexed_objects
  (i : bool)
  : C
  := if i then c else d.

Context (P : Product bool C binproduct_indexed_objects).

Definition BinProduct_from_Product
  : BinProduct _ c d.
Proof.
  use ((_ ,, _ ,, _) ,, (λ p' π₁ π₂, ((_ ,, _ ,, _) ,, _))).
  - exact (ProductObject _ _ P).
  - exact (ProductPr _ _ P true).
  - exact (ProductPr _ _ P false).
  - apply ProductArrow.
    intro i.
    induction i.
    + exact π₁.
    + exact π₂.
  - exact (ProductPrCommutes _ _ _ P _ _ true).
  - exact (ProductPrCommutes _ _ _ P _ _ false).
  - abstract (
      intro t;
      apply subtypePath;
      [ intro;
        apply isapropdirprod;
        apply homset_property | ];
      apply (ProductArrowUnique _ _ _ P);
      intro i;
      induction i;
      [ exact (pr12 t)
      | exact (pr22 t) ]
    ).
Defined.

End BinProductsFromProducts.

Definition BinProducts_from_Products
  {C : category}
  (P : Products bool C)
  : BinProducts C
  := λ c d, BinProduct_from_Product c d (P _).

Section ProductsFromBinProducts.

  Context {C : category}.
  Context (BP : BinProducts C).
  Context {n : nat}.
  Context {c : C}.
  Context (P : Product (stn n) C (λ _, c)).
  Let stnweq := (weqdnicoprod n lastelement).

  Definition sn_power_object
    : C
    := BP c P.

  Definition sn_power_projection
    (i : stn (S n))
    : C ⟦ sn_power_object, c ⟧.
  Proof.
    induction (invmap stnweq i) as [i' | i'].
    - exact (
        BinProductPr2 _ _ ·
        ProductPr _ _ _ i'
      ).
    - apply BinProductPr1.
  Defined.

  Section Arrow.

    Context (c' : C).
    Context (cone' : stn (S n) → C⟦c', c⟧).

    Definition sn_power_arrow
      : C ⟦c', sn_power_object⟧.
    Proof.
      use BinProductArrow.
      - apply (cone' (stnweq (inr tt))).
      - apply ProductArrow.
        intro i.
        apply (cone' (stnweq (inl i))).
    Defined.

    Lemma sn_power_arrow_commutes
      (i : stn (S n))
      : sn_power_arrow · sn_power_projection i = cone' i.
    Proof.
      rewrite <- (homotweqinvweq stnweq i).
      induction (invmap stnweq i) as [i' | i'].
      - refine (maponpaths (λ x, _ · (_ x)) (homotinvweqweq stnweq (inl i')) @ _).
        refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (BinProductPr2Commutes _ _ _ _ _ _ _) @ _).
        apply (ProductPrCommutes _ _ _ P).
      - refine (maponpaths (λ x, _ · (_ x)) (homotinvweqweq stnweq (inr i')) @ _).
        refine (BinProductPr1Commutes _ _ _ (BP c P) _ _ _ @ _).
        apply maponpaths.
        now apply stn_eq.
    Qed.

    Lemma sn_power_arrow_unique
      (t : ∑ (f: C ⟦c', sn_power_object⟧),
        ∏ i, f · sn_power_projection i = cone' i)
      : t = (sn_power_arrow ,, sn_power_arrow_commutes).
    Proof.
      apply subtypePairEquality.
      {
        intro.
        apply impred_isaprop.
        intro.
        apply homset_property.
      }
      apply BinProductArrowUnique.
      - refine (!_ @ pr2 t _).
        apply maponpaths.
        exact (maponpaths _ (homotinvweqweq _ _)).
      - apply ProductArrowUnique.
        intro i.
        refine (_ @ pr2 t _).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (!_)).
        exact (maponpaths _ (homotinvweqweq _ _)).
    Qed.

  End Arrow.

  Definition sn_power_is_product
    : isProduct _ _ _ sn_power_object sn_power_projection.
  Proof.
    use (make_isProduct _ _ (homset_property C)).
    intros c' cone'.
    use make_iscontr.
    + exists (sn_power_arrow c' cone').
      exact (sn_power_arrow_commutes c' cone').
    + exact (sn_power_arrow_unique c' cone').
  Defined.

  Definition n_power_to_sn_power
    : Product (stn (S n)) C (λ _, c).
  Proof.
    use make_Product.
    - exact sn_power_object.
    - exact sn_power_projection.
    - exact sn_power_is_product.
  Defined.

End ProductsFromBinProducts.

Definition bin_product_power
  (C : category)
  (c : C)
  (T : Terminal C)
  (BP : BinProducts C)
  (n : nat)
  : Product (stn n) C (λ _, c).
Proof.
  induction n as [ | n IHn].
  - refine (transportf (λ x, Product x C (λ y: x, c)) _ (Terminal_is_empty_product T _)).
    abstract exact (invmap (univalence _ _) (invweq weqstn0toempty)).
  - apply (n_power_to_sn_power BP IHn).
Defined.
