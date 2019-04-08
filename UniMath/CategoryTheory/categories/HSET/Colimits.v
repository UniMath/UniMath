(** * Colimits in [HSET] *)

(** ** Contents

  - Minimal equivalence relations
  - General colimits [ColimsHSET]
  - Binary coproducs [BinCoproductsHSET]
  - General indexed coproducs [CoproductsHSET]
    - Binary coproducts from colimits [BinCoproductsHSET_from_Colims]
  - Pushouts from colimits [PushoutsHSET_from_Colims]
  - Initial object [InitialHSET]
    - Initial object from colimits [InitialHSET_from_Colims]

Written by: Benedikt Ahrens, Anders Mörtberg

October 2015 - January 2016

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA. (* flip *)
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pushouts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import UniMath.CategoryTheory.categories.HSET.Core.

Local Open Scope cat.

(** ** General colimits [ColimsHSET] *)

Section colimits.

Variable g : graph.
Variable D : diagram g HSET.

Local Definition cobase : UU := ∑ j : vertex g, pr1hSet (dob D j).

(* Theory about hprop is in UniMath.Foundations.Propositions *)
Local Definition rel0 : hrel cobase := λ (ia jb : cobase),
  hProppair (ishinh (∑ f : edge (pr1 ia) (pr1 jb), dmor D f (pr2 ia) = pr2 jb))
            (isapropishinh _).

Local Definition rel : hrel cobase := eqrel_from_hrel rel0.

Lemma iseqrel_rel : iseqrel rel.
Proof.
  now apply iseqrel_eqrel_from_hrel.
Qed.

Local Definition eqr : eqrel cobase := eqrelpair _ iseqrel_rel.

(* Defined in UniMath.Foundations.Sets *)
Definition colimHSET : HSET :=
  hSetpair (setquot eqr) (isasetsetquot _).

(*
           (X,~)
            | \
            |   \
            |     \
  setquotpr |       \
            |         \
            |           \
            |             \
            V              V
           X/~ ----------> (Y,=)
*)

Local Definition injections j : HSET ⟦dob D j, colimHSET⟧.
Proof.
  intros Fj; apply (setquotpr _).
  exact (j,,Fj).
Defined.

(* Define the morphism out of the colimit *)
Section from_colim.

Variables (c : HSET) (cc : cocone D c).

Local Definition from_cobase : cobase -> pr1hSet c.
Proof.
  now intro iA; apply (coconeIn cc (pr1 iA) (pr2 iA)).
Defined.

Local Definition from_cobase_rel : hrel cobase.
Proof.
  intros x x'; exists (from_cobase x = from_cobase x').
  now apply setproperty.
Defined.

Local Definition from_cobase_eqrel : eqrel cobase.
Proof.
  exists from_cobase_rel.
  abstract (
  repeat split;
  [ intros x y z H1 H2 ;
    exact (pathscomp0 H1 H2)
  |
    intros x y H;
    exact (pathsinv0 H)
  ]).
Defined.

Lemma rel0_impl a b (Hab : rel0 a b) : from_cobase_eqrel a b.
Proof.
  use Hab. clear Hab.
  intro H; simpl.
  destruct H as [f Hf].
  generalize (toforallpaths _ _ _ (coconeInCommutes cc (pr1 a) (pr1 b) f) (pr2 a)).
  unfold compose, from_cobase; simpl; intro H.
  now rewrite <- H, Hf.
Qed.

Lemma rel_impl a b (Hab : rel a b) : from_cobase_eqrel a b.
Proof.
  now apply (@minimal_eqrel_from_hrel _ rel0); [apply rel0_impl|].
Qed.

Lemma iscomprel_from_base : iscomprelfun rel from_cobase.
Proof.
  now intros a b; apply rel_impl.
Qed.

Definition from_colimHSET : HSET ⟦colimHSET, c⟧.
Proof.
  now simpl; apply (setquotuniv _ _ from_cobase iscomprel_from_base).
Defined.

End from_colim.

Definition colimCoconeHSET : cocone D colimHSET.
Proof.
  use mk_cocone.
  - now apply injections.
  - abstract (intros u v e;
              apply funextfun; intros Fi; simpl;
              unfold compose, injections; simpl;
              apply (weqpathsinsetquot eqr), (eqrelsymm eqr), eqrel_impl, hinhpr; simpl;
              now exists e).
Defined.

Definition ColimHSETArrow (c : HSET) (cc : cocone D c) :
  ∑ x : HSET ⟦ colimHSET, c ⟧, ∏ v : vertex g, injections v · x = coconeIn cc v.
Proof.
  exists (from_colimHSET _ cc).
  abstract (intro i; simpl; unfold injections, compose, from_colimHSET; simpl;
            apply funextfun; intro Fi; now rewrite (setquotunivcomm eqr)).
Defined.

Definition ColimCoconeHSET : ColimCocone D.
Proof.
  apply (mk_ColimCocone _ colimHSET colimCoconeHSET); intros c cc.
  exists (ColimHSETArrow _ cc).
  abstract (intro f; apply subtypeEquality;
            [ intro; now apply impred; intro i; apply has_homsets_HSET
            | apply funextfun; intro x; simpl;
              apply (surjectionisepitosets (setquotpr eqr));
                [now apply issurjsetquotpr | now apply pr2 | ];
              intro y; destruct y as [u fu]; destruct f as [f Hf];
              now apply (toforallpaths _ _ _ (Hf u) fu)]).
Defined.

End colimits.

Opaque from_colimHSET.

Lemma ColimsHSET : Colims HSET.
Proof.
  now intros g d; apply ColimCoconeHSET.
Defined.

Lemma ColimsHSET_of_shape (g : graph) :
  Colims_of_shape g HSET.
Proof.
now intros d; apply ColimCoconeHSET.
Defined.

(** ** Binary coproducs [BinCoproductsHSET] *)

(* rules for coproducts in HSET *)
Lemma BinCoproductIn1CommutesHSET (A B : HSET) (CC : BinCoproduct HSET A B)(C : HSET)
      (f : A --> C)(g: B --> C) (a:pr1 A):
  BinCoproductArrow HSET CC f g (BinCoproductIn1 HSET CC a)  = f a.
Proof.
  set (H1 := BinCoproductIn1Commutes _ _ _ CC _ f g).
  apply toforallpaths in H1.
  now apply H1.
Qed.

Lemma BinCoproductIn2CommutesHSET (A B : HSET) (CC : BinCoproduct HSET A B)(C : HSET)
      (f : A --> C)(g: B --> C) (b:pr1 B):
  BinCoproductArrow HSET CC f g (BinCoproductIn2 HSET CC b)  = g b.
Proof.
  set (H1 := BinCoproductIn2Commutes _ _ _ CC _ f g).
  apply toforallpaths in H1.
  now apply H1.
Qed.

Lemma postcompWithBinCoproductArrowHSET {A B : HSET} (CCAB : BinCoproduct HSET A B) {C : HSET}
    (f : A --> C) (g : B --> C) {X : HSET} (k : C --> X) z:
       k (BinCoproductArrow _ CCAB f g z) = BinCoproductArrow _ CCAB (f · k) (g · k) z.
Proof.
  set (H1 := postcompWithBinCoproductArrow _ CCAB f g k).
  apply toforallpaths in H1.
  now apply H1.
Qed.

(* Direct construction of binary coproducts in HSET *)
Lemma BinCoproductsHSET : BinCoproducts HSET.
Proof.
  intros A B.
  use mk_BinCoproduct.
  - apply (setcoprod A B).
  - simpl in *; apply ii1.
  - simpl in *; intros x; apply (ii2 x).
  - apply (mk_isBinCoproduct _ has_homsets_HSET).
    intros C f g; simpl in *.
    use tpair.
    * exists (sumofmaps f g); abstract (split; apply idpath).
    * abstract (intros h; apply subtypeEquality;
      [ intros x; apply isapropdirprod; apply has_homsets_HSET
      | destruct h as [t [ht1 ht2]]; simpl;
                apply funextfun; intro x;
                rewrite <- ht2, <- ht1; unfold compose; simpl;
                case x; intros; apply idpath]).
Defined.

(** ** General indexed coproducs [CoproductsHSET] *)

Lemma CoproductsHSET (I : UU) (HI : isaset I) : Coproducts I HSET.
Proof.
  intros A.
  use mk_Coproduct.
  - exists (∑ i, pr1 (A i)).
    apply (isaset_total2 _ HI); intro i; apply setproperty.
  - simpl; apply tpair.
  - apply (mk_isCoproduct _ _ has_homsets_HSET).
    intros C f; simpl in *.
    use tpair.
    * exists (λ X, f (pr1 X) (pr2 X)); abstract (intro i; apply idpath).
    * abstract (intros h; apply subtypeEquality; simpl;
        [ intro; apply impred; intro; apply has_homsets_HSET
        | destruct h as [t ht]; simpl; apply funextfun;
          intro x; rewrite <- ht; destruct x; apply idpath]).
Defined.

(** *** Binary coproducts from colimits [BinCoproductsHSET_from_Colims] *)

Require UniMath.CategoryTheory.limits.graphs.bincoproducts.

Lemma BinCoproductsHSET_from_Colims : graphs.bincoproducts.BinCoproducts HSET.
Proof.
  now apply bincoproducts.BinCoproducts_from_Colims, ColimsHSET_of_shape.
Defined.

(** *** Pushouts from colimits [PushoutsHSET_from_Colims] *)

Lemma PushoutsHSET_from_Colims : graphs.pushouts.Pushouts HSET.
Proof.
  red; intros; apply ColimsHSET_of_shape.
Qed.

(** ** Initial object [InitialHSET] *)

Lemma InitialHSET : Initial HSET.
Proof.
  apply (mk_Initial emptyHSET).
  apply mk_isInitial; intro a.
  use tpair.
  - simpl; intro e; induction e.
  - abstract (intro f; apply funextfun; intro e; induction e).
Defined.

(** *** Initial object from colimits [InitialHSET_from_Colims] *)

Require UniMath.CategoryTheory.limits.graphs.initial.

Lemma InitialHSET_from_Colims : graphs.initial.Initial HSET.
Proof.
  apply initial.Initial_from_Colims, ColimsHSET_of_shape.
Defined.
