(** testing whether our way of doing coproducts fits with SubstitutionSystems  *)

(** ******************************************
Benedikt Ahrens, March 2015
*********************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.

Require Import UniMath.Ktheory.Representation.
Require UniMath.Ktheory.Precategories.
Coercion Precategories.Precategory_to_precategory : Precategories.Precategory >-> precategory.

Section MyWay.

Variable C : Precategories.Precategory.

Set Automatic Introduction.

Definition isCoproductCocone (a b co : C) (ia : a ⇒ co) (ib : b ⇒ co) :=
  binarySumProperty ia ib.

Definition mk_isCoproductCocone (a b co : C) (ia : a ⇒ co) (ib : b ⇒ co) :
   (∀ (c : C) (f : a ⇒ c) (g : b ⇒ c),
    ∃! k : C ⟦co, c⟧,
      ia ;; k = f ×
      ib ;; k = g)
   →
   isCoproductCocone a b co ia ib.
Proof.
  intros u c fg. refine (iscontrweqf _ (u c (pr1 fg) (pr2 fg))).
  apply weqfibtototal. intro d. apply weqiff.
  { split.
    { intros ee. apply dirprod_eq.
      { simpl. exact (pr1 ee). }
      { simpl. exact (pr2 ee). } }
    { intros ee. split.
      { simpl. exact (maponpaths (HomPair_1 _ _ _) ee). }
      { simpl. exact (maponpaths (HomPair_2 _ _ _) ee). } } }
  { apply isapropdirprod; apply (Precategories.homset_property C). }
  { apply setproperty. }
Defined.

Definition CoproductCocone (a b : C) := BinarySum a b.

Definition mk_CoproductCocone (a b : C) :
  ∀ (c : C) (f : a ⇒ c) (g : b ⇒ c),
    isCoproductCocone _ _ _ f g →  CoproductCocone a b
  := λ c f g i, c,,(f,,g),,i.

Definition Coproducts := hasBinarySums C.
Definition hasCoproducts := ishinh Coproducts.

Definition CoproductObject {a b : C} (CC : CoproductCocone a b) : C :=
  universalObject CC.

Definition CoproductIn1 {a b : C} (CC : CoproductCocone a b): a ⇒ CoproductObject CC
  := in_1 CC.

Definition CoproductIn2 {a b : C} (CC : CoproductCocone a b) : b ⇒ CoproductObject CC
  := in_2 CC.

Definition CoproductArrow {a b : C} (CC : CoproductCocone a b) {c : C} (f : a ⇒ c) (g : b ⇒ c) :
  CoproductObject CC ⇒ c
  := binarySumMap CC f g.

Lemma CoproductIn1Commutes (a b : C) (CC : CoproductCocone a b):
     ∀ (c : C) (f : a ⇒ c) g, CoproductIn1 CC ;; CoproductArrow CC f g  = f.
Proof.
  intros c f g.
  exact (binarySum_in_1_eqn CC f g).
Qed.

Lemma CoproductIn2Commutes (a b : C) (CC : CoproductCocone a b):
     ∀ (c : C) (f : a ⇒ c) g, CoproductIn2 CC ;; CoproductArrow CC f g = g.
Proof.
  intros c f g.
  exact (binarySum_in_2_eqn CC f g).
Qed.

Lemma CoproductArrowUnique (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : a ⇒ x) (g : b ⇒ x) (k : CoproductObject CC ⇒ x) :
    CoproductIn1 CC ;; k = f → CoproductIn2 CC ;; k = g →
      k = CoproductArrow CC f g.
Proof.
  intros u v.
  apply binarySumMapUniqueness.
  { refine (u @ _). apply pathsinv0, CoproductIn1Commutes. }
  { refine (v @ _). apply pathsinv0, CoproductIn2Commutes. }
Qed.

Lemma CoproductArrowEta (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : CoproductObject CC ⇒ x) :
    f = CoproductArrow CC (CoproductIn1 CC ;; f) (CoproductIn2 CC ;; f).
Proof.
  apply CoproductArrowUnique;
  apply idpath.
Qed.

Definition CoproductOfArrows {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) :
          CoproductObject CCab ⇒ CoproductObject CCcd :=
    CoproductArrow CCab (f ;; CoproductIn1 CCcd) (g ;; CoproductIn2 CCcd).

Lemma CoproductOfArrowsIn1 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) :
    CoproductIn1 CCab ;; CoproductOfArrows CCab CCcd f g = f ;; CoproductIn1 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductOfArrowsIn2 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) :
    CoproductIn2 CCab ;; CoproductOfArrows CCab CCcd f g = g ;; CoproductIn2 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn2Commutes.
Qed.


Lemma precompWithCoproductArrow {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d)
    {x : C} (k : c ⇒ x) (h : d ⇒ x) :
        CoproductOfArrows CCab CCcd f g ;; CoproductArrow CCcd k h =
         CoproductArrow CCab (f ;; k) (g ;; h).
Proof.
  apply CoproductArrowUnique.
  - rewrite assoc. rewrite CoproductOfArrowsIn1.
    rewrite <- assoc, CoproductIn1Commutes.
    apply idpath.
  - rewrite assoc, CoproductOfArrowsIn2.
    rewrite <- assoc, CoproductIn2Commutes.
    apply idpath.
Qed.


Lemma postcompWithCoproductArrow {a b : C} (CCab : CoproductCocone a b) {c : C}
    (f : a ⇒ c) (g : b ⇒ c) {x : C} (k : c ⇒ x)  :
       CoproductArrow CCab f g ;; k = CoproductArrow CCab (f ;; k) (g ;; k).
Proof.
  apply CoproductArrowUnique.
  -  rewrite assoc, CoproductIn1Commutes;
     apply idpath.
  -  rewrite assoc, CoproductIn2Commutes;
     apply idpath.
Qed.


Section coproduct_unique.

Hypothesis H : is_category C.

Variables a b : C.

Definition from_Coproduct_to_Coproduct (CC CC' : CoproductCocone a b)
  : CoproductObject CC ⇒ CoproductObject CC'.
Proof.
  apply (CoproductArrow CC  (CoproductIn1 _ ) (CoproductIn2 _ )).
Defined.


Lemma Coproduct_endo_is_identity (CC : CoproductCocone a b)
  (k : CoproductObject CC ⇒ CoproductObject CC)
  (H1 : CoproductIn1 CC ;; k = CoproductIn1 CC)
  (H2 : CoproductIn2 CC ;; k = CoproductIn2 CC)
  : identity _ = k.
Proof.
(*  apply pathsinv0. *)
(*   apply colim_endo_is_identity. *)
(*   intro u; induction u; simpl; assumption. *)
(* Defined. *)
Abort.

End coproduct_unique.


End MyWay.

(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Definition of a coproduct structure on a functor category
  by taking pointwise coproducts in the target category



************************************************************)



Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.SubstitutionSystems.Auxiliary.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** Goal: lift coproducts from the target (pre)category to the functor (pre)category *)

Section def_functor_pointwise_coprod.

Variable C D : Precategories.Precategory.
Variable HD : Coproducts D.

Definition hsD := Precategories.homset_property D.

Section coproduct_functor.

Variables F G : functor C D.

Local Notation "c ⊗ d" := (CoproductObject _ (HD c d))(at level 45).

Definition coproduct_functor_ob (c : C) : D := F c ⊗ G c.

Definition coproduct_functor_mor (c c' : C) (f : c ⇒ c')
  : coproduct_functor_ob c ⇒ coproduct_functor_ob c'
  := CoproductOfArrows _ _ _ (#F f) (#G f).

Definition coproduct_functor_data : functor_data C D.
Proof.
  exists coproduct_functor_ob.
  exact coproduct_functor_mor.
Defined.


Lemma is_functor_coproduct_functor_data : is_functor coproduct_functor_data.
Proof.
  split; simpl; intros.
  - unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply Coproduct_endo_is_identity.
    + unfold coproduct_functor_mor.
      rewrite CoproductOfArrowsIn1.
      rewrite functor_id.
      apply id_left.
    + unfold coproduct_functor_mor.
      rewrite CoproductOfArrowsIn2.
      rewrite functor_id.
      apply id_left.
  - unfold functor_compax, coproduct_functor_mor;
    intros; simpl in *.
    unfold coproduct_functor_mor.
    do 2 rewrite functor_comp.
    rewrite <- CoproductOfArrows_comp.
    apply idpath.
(* former proof:
    unfold CoproductOfArrows.
    apply pathsinv0.
    apply CoproductArrowUnique.
    + rewrite assoc. simpl in *.
      set (H:= CoproductIn1Commutes ).
      set (H2 := H D _ _ (HD (F a) (G a))).
      rewrite H2.
      rewrite <- assoc.
      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply CoproductIn1Commutes.
    + rewrite assoc.
      set (H:= CoproductIn2Commutes D _ _ (HD (F a) (G a))).
      rewrite H.
      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply CoproductIn2Commutes.
*)
Qed.

Definition coproduct_functor : functor C D := tpair _ _ is_functor_coproduct_functor_data.

Definition coproduct_nat_trans_in1_data : ∀ c, F c ⇒ coproduct_functor c
  := λ c : C, CoproductIn1 _ (HD (F c) (G c)).

Lemma is_nat_trans_coproduct_nat_trans_in1_data
  : is_nat_trans _ _ coproduct_nat_trans_in1_data.
Proof.
  unfold is_nat_trans.
  intros c c' f.
  unfold coproduct_nat_trans_in1_data.
  unfold coproduct_functor. simpl.
  unfold coproduct_functor_mor.
  assert (XX:= CoproductOfArrowsIn1).
  assert (X1 := XX _ (F c) (G c) (HD (F c) (G c))).
  assert (X2 := X1 _ _ (HD (F c') (G c'))).
  rewrite X2.
  apply idpath.
Qed.

Definition coproduct_nat_trans_in1 : nat_trans _ _
  := tpair _ _ is_nat_trans_coproduct_nat_trans_in1_data.

Definition coproduct_nat_trans_in2_data : ∀ c, G c ⇒ coproduct_functor c
  := λ c : C, CoproductIn2 _ (HD (F c) (G c)).

Lemma is_nat_trans_coproduct_nat_trans_in2_data
  : is_nat_trans _ _ coproduct_nat_trans_in2_data.
Proof.
  unfold is_nat_trans.
  intros c c' f.
  unfold coproduct_nat_trans_in2_data.
  unfold coproduct_functor. simpl.
  unfold coproduct_functor_mor.
  assert (XX:= CoproductOfArrowsIn2).
  assert (X1 := XX _ (F c) (G c) (HD (F c) (G c))).
  assert (X2 := X1 _ _ (HD (F c') (G c'))).
  rewrite X2.
  apply idpath.
Qed.

Definition coproduct_nat_trans_in2 : nat_trans _ _
  := tpair _ _ is_nat_trans_coproduct_nat_trans_in2_data.


Section vertex.

(** The coproduct morphism of a diagram with vertex [A] *)

Variable A : functor C D.
Variable f : F ⟶ A.
Variable g : G ⟶ A.

Definition coproduct_nat_trans_data : ∀ c, coproduct_functor c ⇒ A c.
Proof.
  intro c.
  apply CoproductArrow.
  - exact (f c).
  - exact (g c).
Defined.

Lemma is_nat_trans_coproduct_nat_trans_data : is_nat_trans _ _ coproduct_nat_trans_data.
Proof.
  intros a b k.
  simpl.
  unfold coproduct_functor_mor.
  unfold coproduct_nat_trans_data.
  simpl.
  set (XX:=precompWithCoproductArrow).
  set (X1 := XX D _ _ (HD (F a) (G a))).
  set (X2 := X1 _ _ (HD (F b) (G b))).
  rewrite X2.
  clear X2 X1 XX.
  set (XX:=postcompWithCoproductArrow).
  set (X1 := XX D _ _ (HD (F a) (G a))).
  rewrite X1.
  rewrite (nat_trans_ax f).
  rewrite (nat_trans_ax g).
  apply idpath.
Qed.

Definition coproduct_nat_trans : nat_trans _ _
  := tpair _ _ is_nat_trans_coproduct_nat_trans_data.

Lemma coproduct_nat_trans_In1Commutes :
  nat_trans_comp _ _ _ coproduct_nat_trans_in1 coproduct_nat_trans = f.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply CoproductIn1Commutes.
Qed.

Lemma coproduct_nat_trans_In2Commutes :
  nat_trans_comp _ _ _ coproduct_nat_trans_in2 coproduct_nat_trans = g.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply CoproductIn2Commutes.
Qed.

End vertex.


Lemma coproduct_nat_trans_univ_prop (A : [C, D, hsD])
  (f : (F : [C,D,hsD]) ⇒ A) (g : (G : [C,D,hsD]) ⇒ A) :
   ∀
   t : Σ fg : (coproduct_functor:[C,D,hsD]) ⇒ A,
       (coproduct_nat_trans_in1 : (F:[C,D,hsD]) ⇒ coproduct_functor);; fg = f
      ×
       (coproduct_nat_trans_in2: (G : [C,D,hsD]) ⇒ coproduct_functor);; fg = g,
   t =
   tpair
     (λ fg : (coproduct_functor:[C,D,hsD]) ⇒ A,
      (coproduct_nat_trans_in1 : (F:[C,D,hsD]) ⇒ coproduct_functor);; fg = f
   ×
      (coproduct_nat_trans_in2 : (G:[C,D,hsD]) ⇒ coproduct_functor) ;; fg = g)
     (coproduct_nat_trans A f g)
     (dirprodpair (coproduct_nat_trans_In1Commutes A f g)
        (coproduct_nat_trans_In2Commutes A f g)).
Proof.
  intro t.
  simpl in *.
  destruct t as [t1 [ta tb]].
  simpl in *.
  apply subtypeEquality.
  - intro.
    apply isapropdirprod;
    apply isaset_nat_trans;
    apply hsD.
  - simpl.
    apply nat_trans_eq.
    + apply hsD.
    + intro c.
      unfold coproduct_nat_trans.
      simpl.
      unfold coproduct_nat_trans_data.
      simpl.
      apply CoproductArrowUnique.
      * apply (nat_trans_eq_pointwise ta).
      * apply (nat_trans_eq_pointwise tb).
Qed.


Definition functor_precat_coproduct_cocone
  : CoproductCocone [C, D, hsD] F G.
Proof.
  refine (mk_CoproductCocone _ _ _ _ _ _ _ ).
  - apply coproduct_functor.
  - apply coproduct_nat_trans_in1.
  - apply coproduct_nat_trans_in2.
  - refine (mk_isCoproductCocone _ _ _ _ _ _ _ _ ).
    + apply functor_category_has_homsets.
    + intros A f g.
     exists (tpair _ (coproduct_nat_trans A f g)
             (dirprodpair (coproduct_nat_trans_In1Commutes _ _ _ )
                          (coproduct_nat_trans_In2Commutes _ _ _ ))).
     simpl.
     apply coproduct_nat_trans_univ_prop.
Defined.

End coproduct_functor.


Definition Coproducts_functor_precat : Coproducts [C, D, hsD].
Proof.
  intros F G.
  apply functor_precat_coproduct_cocone.
Defined.

End def_functor_pointwise_coprod.
