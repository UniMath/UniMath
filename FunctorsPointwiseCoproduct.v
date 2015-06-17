Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import UnicodeNotations.
Require Import UniMath.RezkCompletion.limits.coproducts.
Require Import Auxiliary.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Section def_functor_pointwise_coprod.

Variable C D : precategory.
Variable HD : Coproducts D.
Variable hsD : has_homsets D.

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
  apply (total2_paths_second_isaprop).
  - apply isapropdirprod;
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
      * apply (nat_trans_eq_pointwise _ _ _ _ _ _ ta).
      * apply (nat_trans_eq_pointwise _ _ _ _ _ _ tb).
Qed.


Definition functor_precat_coproduct_cocone 
  : CoproductCocone [C, D, hsD] F G.
Proof.
  exists (tpair _ coproduct_functor (dirprodpair coproduct_nat_trans_in1 
                                                 coproduct_nat_trans_in2)).
  intros A f g.
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











