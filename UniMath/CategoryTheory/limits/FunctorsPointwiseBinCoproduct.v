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
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** Goal: lift coproducts from the target (pre)category to the functor (pre)category *)

Section def_functor_pointwise_coprod.

Variable C D : precategory.
Variable HD : BinCoproducts D.
Variable hsD : has_homsets D.

Section BinCoproduct_of_functors.

Variables F G : functor C D.

Local Notation "c ⊗ d" := (BinCoproductObject _ (HD c d))(at level 45).

Definition BinCoproduct_of_functors_ob (c : C) : D := F c ⊗ G c.

Definition BinCoproduct_of_functors_mor (c c' : C) (f : c --> c')
  : BinCoproduct_of_functors_ob c --> BinCoproduct_of_functors_ob c'
  := BinCoproductOfArrows _ _ _ (#F f) (#G f).

Definition BinCoproduct_of_functors_data : functor_data C D.
Proof.
  exists BinCoproduct_of_functors_ob.
  exact BinCoproduct_of_functors_mor.
Defined.

Lemma is_functor_BinCoproduct_of_functors_data : is_functor BinCoproduct_of_functors_data.
Proof.
  split; simpl; intros.
  - unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply BinCoproduct_endo_is_identity.
    + unfold BinCoproduct_of_functors_mor.
      rewrite BinCoproductOfArrowsIn1.
      rewrite functor_id.
      apply id_left.
    + unfold BinCoproduct_of_functors_mor.
      rewrite BinCoproductOfArrowsIn2.
      rewrite functor_id.
      apply id_left.
  - unfold functor_compax, BinCoproduct_of_functors_mor;
    intros; simpl in *.
    unfold BinCoproduct_of_functors_mor.
    do 2 rewrite functor_comp.
    rewrite <- BinCoproductOfArrows_comp.
    apply idpath.
(* former proof:
    unfold BinCoproductOfArrows.
    apply pathsinv0.
    apply BinCoproductArrowUnique.
    + rewrite assoc. simpl in *.
      set (H:= BinCoproductIn1Commutes ).
      set (H2 := H D _ _ (HD (F a) (G a))).
      rewrite H2.
      rewrite <- assoc.
      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply BinCoproductIn1Commutes.
    + rewrite assoc.
      set (H:= BinCoproductIn2Commutes D _ _ (HD (F a) (G a))).
      rewrite H.
      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply BinCoproductIn2Commutes.
*)
Qed.

Definition BinCoproduct_of_functors : functor C D :=
  tpair _ _ is_functor_BinCoproduct_of_functors_data.

Lemma BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors :
  BinCoproduct_of_functors_alt HD F G = BinCoproduct_of_functors.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

Definition coproduct_nat_trans_in1_data : ∀ c, F c --> BinCoproduct_of_functors c
  := λ c : C, BinCoproductIn1 _ (HD (F c) (G c)).

Lemma is_nat_trans_coproduct_nat_trans_in1_data
  : is_nat_trans _ _ coproduct_nat_trans_in1_data.
Proof.
  unfold is_nat_trans.
  intros c c' f.
  unfold coproduct_nat_trans_in1_data.
  unfold BinCoproduct_of_functors. simpl.
  unfold BinCoproduct_of_functors_mor.
  assert (XX:= BinCoproductOfArrowsIn1).
  assert (X1 := XX _ (F c) (G c) (HD (F c) (G c))).
  assert (X2 := X1 _ _ (HD (F c') (G c'))).
  rewrite X2.
  apply idpath.
Qed.

Definition coproduct_nat_trans_in1 : nat_trans _ _
  := tpair _ _ is_nat_trans_coproduct_nat_trans_in1_data.

Definition coproduct_nat_trans_in2_data : ∀ c, G c --> BinCoproduct_of_functors c
  := λ c : C, BinCoproductIn2 _ (HD (F c) (G c)).

Lemma is_nat_trans_coproduct_nat_trans_in2_data
  : is_nat_trans _ _ coproduct_nat_trans_in2_data.
Proof.
  unfold is_nat_trans.
  intros c c' f.
  unfold coproduct_nat_trans_in2_data.
  unfold BinCoproduct_of_functors. simpl.
  unfold BinCoproduct_of_functors_mor.
  assert (XX:= BinCoproductOfArrowsIn2).
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

Definition coproduct_nat_trans_data : ∀ c, BinCoproduct_of_functors c --> A c.
Proof.
  intro c.
  apply BinCoproductArrow.
  - exact (f c).
  - exact (g c).
Defined.

Lemma is_nat_trans_coproduct_nat_trans_data : is_nat_trans _ _ coproduct_nat_trans_data.
Proof.
  intros a b k.
  simpl.
  unfold BinCoproduct_of_functors_mor.
  unfold coproduct_nat_trans_data.
  simpl.
  set (XX:=precompWithBinCoproductArrow).
  set (X1 := XX D _ _ (HD (F a) (G a))).
  set (X2 := X1 _ _ (HD (F b) (G b))).
  rewrite X2.
  clear X2 X1 XX.
  set (XX:=postcompWithBinCoproductArrow).
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
    apply BinCoproductIn1Commutes.
Qed.

Lemma coproduct_nat_trans_In2Commutes :
  nat_trans_comp _ _ _ coproduct_nat_trans_in2 coproduct_nat_trans = g.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply BinCoproductIn2Commutes.
Qed.

End vertex.


Lemma coproduct_nat_trans_univ_prop (A : [C, D, hsD])
  (f : (F : [C,D,hsD]) --> A) (g : (G : [C,D,hsD]) --> A) :
   ∀
   t : Σ fg : (BinCoproduct_of_functors:[C,D,hsD]) --> A,
       (coproduct_nat_trans_in1 : (F:[C,D,hsD]) --> BinCoproduct_of_functors);; fg = f
      ×
       (coproduct_nat_trans_in2: (G : [C,D,hsD]) --> BinCoproduct_of_functors);; fg = g,
   t =
   tpair
     (λ fg : (BinCoproduct_of_functors:[C,D,hsD]) --> A,
      (coproduct_nat_trans_in1 : (F:[C,D,hsD]) --> BinCoproduct_of_functors);; fg = f
   ×
      (coproduct_nat_trans_in2 : (G:[C,D,hsD]) --> BinCoproduct_of_functors) ;; fg = g)
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
      apply BinCoproductArrowUnique.
      * apply (nat_trans_eq_pointwise ta).
      * apply (nat_trans_eq_pointwise tb).
Qed.


Definition functor_precat_coproduct_cocone
  : BinCoproductCocone [C, D, hsD] F G.
Proof.
  simple refine (mk_BinCoproductCocone _ _ _ _ _ _ _ ).
  - apply BinCoproduct_of_functors.
  - apply coproduct_nat_trans_in1.
  - apply coproduct_nat_trans_in2.
  - simple refine (mk_isBinCoproductCocone _ _ _ _ _ _ _ _ ).
    + apply functor_category_has_homsets.
    + intros A f g.
     exists (tpair _ (coproduct_nat_trans A f g)
             (dirprodpair (coproduct_nat_trans_In1Commutes _ _ _ )
                          (coproduct_nat_trans_In2Commutes _ _ _ ))).
     simpl.
     apply coproduct_nat_trans_univ_prop.
Defined.

End BinCoproduct_of_functors.

Definition BinCoproducts_functor_precat : BinCoproducts [C, D, hsD].
Proof.
  intros F G.
  apply functor_precat_coproduct_cocone.
Defined.

End def_functor_pointwise_coprod.

Section option_functor.

Require Import UniMath.CategoryTheory.limits.terminal.

Variables (C : precategory) (hsC : has_homsets C) (CC : BinCoproducts C).

Variable terminal : Terminal C.
Let one : C :=  @TerminalObject C terminal.

Definition option_functor : functor C C :=
  BinCoproduct_of_functors C C CC (constant_functor _ _ one) (functor_identity C).

End option_functor.