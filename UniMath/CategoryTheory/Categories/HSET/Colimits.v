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
  - Every set is the colimit of its finite subsets [is_colimit_finite_subsets_cocone]

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

Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Pushouts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Initial.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.

(* For colimits of finite subsets. *)
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.MoreFoundations.Subtypes.
Local Open Scope cat.

(** ** General colimits [ColimsHSET] *)

Section colimits.

Variable g : graph.
Variable D : diagram g HSET.

Local Definition cobase : UU := ∑ j : vertex g, pr1hSet (dob D j).

(* Theory about hprop is in UniMath.Foundations.Propositions *)
Local Definition rel0 : hrel cobase := λ (ia jb : cobase),
    ∥(∑ f : edge (pr1 ia) (pr1 jb), dmor D f (pr2 ia) = pr2 jb)∥.

Local Definition rel : hrel cobase := eqrel_from_hrel rel0.

Lemma iseqrel_rel : iseqrel rel.
Proof.
  now apply iseqrel_eqrel_from_hrel.
Qed.

Local Definition eqr : eqrel cobase := make_eqrel _ iseqrel_rel.

(* Defined in UniMath.Foundations.Sets *)
Definition colimHSET : HSET :=
  make_hSet (setquot eqr) (isasetsetquot _).

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
  rewrite <- H.
  rewrite <- Hf.
  apply idpath.
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
  use make_cocone.
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
  apply (make_ColimCocone _ colimHSET colimCoconeHSET); intros c cc.
  exists (ColimHSETArrow _ cc).
  abstract (intro f; apply subtypePath;
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
Lemma BinCoproductIn1CommutesHSET (A B : HSET) (CC : BinCoproduct A B)(C : HSET)
      (f : A --> C)(g: B --> C) (a:pr1 A):
  BinCoproductArrow CC f g (BinCoproductIn1 CC a)  = f a.
Proof.
  set (H1 := BinCoproductIn1Commutes _ _ _ CC _ f g).
  apply toforallpaths in H1.
  now apply H1.
Qed.

Lemma BinCoproductIn2CommutesHSET (A B : HSET) (CC : BinCoproduct A B)(C : HSET)
      (f : A --> C)(g: B --> C) (b:pr1 B):
  BinCoproductArrow CC f g (BinCoproductIn2 CC b)  = g b.
Proof.
  set (H1 := BinCoproductIn2Commutes _ _ _ CC _ f g).
  apply toforallpaths in H1.
  now apply H1.
Qed.

Lemma postcompWithBinCoproductArrowHSET {A B : HSET} (CCAB : BinCoproduct A B) {C : HSET}
    (f : A --> C) (g : B --> C) {X : HSET} (k : C --> X) z:
       k (BinCoproductArrow CCAB f g z) = BinCoproductArrow CCAB (f · k) (g · k) z.
Proof.
  set (H1 := postcompWithBinCoproductArrow _ CCAB f g k).
  apply toforallpaths in H1.
  now apply H1.
Qed.

(* Direct construction of binary coproducts in HSET *)
Lemma BinCoproductsHSET : BinCoproducts HSET.
Proof.
  intros A B.
  use make_BinCoproduct.
  - apply (setcoprod A B).
  - simpl in *; apply ii1.
  - simpl in *; intros x; apply (ii2 x).
  - apply (make_isBinCoproduct _ HSET).
    intros C f g; simpl in *.
    use tpair.
    * exists (sumofmaps f g); abstract (split; apply idpath).
    * abstract (intros h; apply subtypePath;
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
  use make_Coproduct.
  - exists (∑ i, pr1 (A i)).
    apply (isaset_total2 _ HI); intro i; apply setproperty.
  - simpl; apply tpair.
  - apply (make_isCoproduct _ _ HSET).
    intros C f; simpl in *.
    use tpair.
    * exists (λ X, f (pr1 X) (pr2 X)); abstract (intro i; apply idpath).
    * abstract (intros h; apply subtypePath; simpl;
        [ intro; apply impred; intro; apply has_homsets_HSET
        | destruct h as [t ht]; simpl; apply funextfun;
          intro x; rewrite <- ht; destruct x; apply idpath]).
Defined.

Definition CoproductsHSET_type (I : UU) : Coproducts I HSET.
Proof.
  use Coproducts_from_Colims.
  use ColimsHSET.
Defined.

(** *** Binary coproducts from colimits [BinCoproductsHSET_from_Colims] *)

Require UniMath.CategoryTheory.Limits.Graphs.BinCoproducts.

Lemma BinCoproductsHSET_from_Colims : Graphs.BinCoproducts.BinCoproducts HSET.
Proof.
  now apply BinCoproducts.BinCoproducts_from_Colims, ColimsHSET_of_shape.
Defined.

(** *** Pushouts from colimits [PushoutsHSET_from_Colims] *)

Lemma PushoutsHSET_from_Colims : Graphs.Pushouts.Pushouts HSET.
Proof.
  red; intros; apply ColimsHSET_of_shape.
Qed.

(** ** Initial object [InitialHSET] *)

Lemma InitialHSET : Initial HSET.
Proof.
  apply (make_Initial emptyHSET).
  apply make_isInitial; intro a.
  use tpair.
  - simpl; intro e; induction e.
  - abstract (intro f; apply funextfun; intro e; induction e).
Defined.

(** *** Initial object from colimits [InitialHSET_from_Colims] *)

Require UniMath.CategoryTheory.Limits.Graphs.Initial.

Lemma InitialHSET_from_Colims : Graphs.Initial.Initial HSET.
Proof.
  apply Initial.Initial_from_Colims, ColimsHSET_of_shape.
Defined.

Section finite_subsets.
  (* This section proves that every set is the colimit of its finite subsets
     by showing that it satisfies the universal property. *)

  Local Open Scope subtype.
  Local Open Scope logic.

  Definition finite_subsets_graph (X : hSet) : graph.
  Proof.
    use make_graph.
    - exact(finite_subset X).
    - exact(λ (A B : finite_subset X), A ⊆ B).
  Defined.

  Definition finite_subsets_diagram (X : hSet)
    : diagram (finite_subsets_graph X) HSET.
  Proof.
    use make_diagram.
    - exact(λ (A : finite_subset X), carrier_subset A).
    - exact(λ (A B : finite_subset X)
              (E : A ⊆ B),
             subtype_inc E).
  Defined.

  (* Construct the cocone with apex X over the finite subsets diagram
     with injections taken to be the projections from the carriers of the subsets. *)
  Definition finite_subsets_cocone (X : hSet)
    : cocone (finite_subsets_diagram X) X.
  Proof.
    use make_cocone.
    - exact(λ (A : finite_subset X), pr1carrier A).
    - red ; intros ; apply idpath.
  Defined.

  (* Every set is the colimit of its finite subsets. *)
  Definition is_colimit_finite_subsets_cocone (X : hSet)
    : isColimCocone (finite_subsets_diagram X) X (finite_subsets_cocone X).
  Proof.
    set (D := finite_subsets_diagram X).
    intros Y CC.
    (* Construct the unique cocone morphism X --> Y by mapping x : X to
       whatever coconeIn CC maps the unique inhabitant of {x} to. *)
    use unique_exists.
    - exact(λ (x : X), coconeIn CC (finite_singleton x) singleton_point).
    - intros A.
      apply funextfun ; intro a.

      (* {a} ⊆ A *)
      set (a_in_A := finite_singleton_is_in (A : finite_subset X) a).

      (* {a} -⊆-> A ---> Y commutes with {a} -(inj)-> Y by the cocone property of CC. *)
      assert(p : dmor D a_in_A · coconeIn CC A = coconeIn CC (finite_singleton (pr1 a)))
        by apply coconeInCommutes.

      apply(eqtohomot (!p)).
    - intro ; apply isaprop_is_cocone_mor.
    - intros f fmor.
      apply funextfun ; intro x.
      exact(eqtohomot (fmor (finite_singleton x)) singleton_point).
  Defined.

End finite_subsets.

(**
 Concrete construction of coequalizers of sets
 *)
Section HSETCoequalizer.
  Context {X Y : hSet}
          (f g : X → Y).

  Definition coequalizer_eqrel
    : eqrel Y.
  Proof.
    use make_eqrel.
    - exact (eqrel_from_hrel (λ y₁ y₂, ∃ (x : X) , f x = y₁ × g x = y₂)).
    - apply iseqrel_eqrel_from_hrel.
  Defined.

  Definition coequalizer_hSet
    : hSet
    := setquotinset coequalizer_eqrel.

  Definition coequalizer_map_hSet
    : Y → coequalizer_hSet
    := setquotpr coequalizer_eqrel.

  Proposition coequalizer_eq_hSet
              (x : X)
    : coequalizer_map_hSet (f x)
      =
      coequalizer_map_hSet (g x).
  Proof.
    apply iscompsetquotpr.
    use eqrel_impl.
    apply hinhpr.
    exists x.
    split.
    - apply idpath.
    - apply idpath.
  Qed.

  Lemma coequalizer_out_hSet_equality
        (Z : hSet)
        (h : Y → Z)
        (p : ∏ (x : X), h(f x) = h(g x))
    : iscomprelfun coequalizer_eqrel h.
  Proof.
    intros y₁ y₂ q.
    cbn in *.
    use (q (make_eqrel (λ y₁ y₂, make_hProp (h y₁ = h y₂) _) _)).
    - apply setproperty.
    - repeat split.
      + exact (λ _ _ _ r₁ r₂, r₁ @ r₂).
      + exact (λ _ _ r, !r).
    - intros x y ; cbn.
      use factor_through_squash.
      {
        apply setproperty.
      }
      intros r.
      rewrite <- (pr12 r).
      rewrite <- (pr22 r).
      apply p.
  Qed.

  Definition coequalizer_out_hSet
             {Z : hSet}
             (h : Y → Z)
             (p : ∏ (x : X), h(f x) = h(g x))
    : coequalizer_hSet → Z.
  Proof.
    use setquotuniv.
    - exact h.
    - exact (coequalizer_out_hSet_equality Z h p).
  Defined.
End HSETCoequalizer.

Definition Coequalizers_HSET
  : Coequalizers HSET.
Proof.
  intros X Y f g.
  use make_Coequalizer.
  - exact (coequalizer_hSet f g).
  - exact (coequalizer_map_hSet f g).
  - abstract
      (use funextsec ;
       intro x ;
       cbn ;
       exact (coequalizer_eq_hSet f g x)).
  - intros Z h p.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use funextsec ;
         use setquotunivprop' ; [ intro ; apply setproperty | ] ;
         intro x ; cbn ;
         exact (eqtohomot (pr2 φ₁ @ !(pr2 φ₂)) x)).
    + simple refine (_ ,, _).
      * exact (coequalizer_out_hSet f g h (eqtohomot p)).
      * abstract
          (apply idpath).
Defined.
