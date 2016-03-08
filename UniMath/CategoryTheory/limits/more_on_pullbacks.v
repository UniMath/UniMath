
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.functor_categories.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section lemmas_on_pullbacks.


(** setup for this section

                k
          d --------> c
          |           |
       h  |     H     | g
          v           v
          b --------> a
               f
*)

Context {C : precategory} (hsC : has_homsets C).
Context {a b c d : C}.
Context {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}.
Variable H : h ;; f = k ;; g.

(** Pullback is symmetric, i.e., we can rotate a pb square *)

Lemma is_symmetric_isPullback
  : isPullback _ _ _ _ H -> isPullback _ _ _ _ (!H).
Proof.
  intro isPb.
  simple refine (mk_isPullback _ _ _ _ _ _ ).
  intros e x y Hxy.
  set (Pb := mk_Pullback _ _ _ _ _ _ isPb).
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    + simple refine (PullbackArrow Pb _ _ _ _ ).
      * assumption.
      * assumption.
      * apply (!Hxy).
    + cbn.
      split.
      * apply (PullbackArrow_PullbackPr2 Pb).
      * apply (PullbackArrow_PullbackPr1 Pb).
  - cbn.
    intro t. apply subtypeEquality.
    intros ? . apply isapropdirprod; apply hsC.
    destruct t as [t Ht].
    cbn; apply PullbackArrowUnique.
    + apply (pr2 Ht).
    + apply (pr1 Ht).
Defined.

(** Pulling back a section *)

Definition pb_of_section (isPb : isPullback _ _ _ _ H)
  (s : C⟦a,c⟧) (K : s ;; g = identity _ )
  : Σ s' : C⟦b, d⟧, s' ;; h = identity _ .
Proof.
  simple refine (tpair _ _ _ ).
  - simple refine (PullbackArrow (mk_Pullback _ _ _ _ _ _ isPb) b (identity _ )
                  (f ;; s) _ ).
    abstract (rewrite id_left, <- assoc, K, id_right; apply idpath).
  - abstract (cbn; apply (PullbackArrow_PullbackPr1 (mk_Pullback f g d h k H isPb))).
Defined.


Ltac mk_pair := simple refine (tpair _ _ _ ).

(** Diagonal morphisms are equivalent to sections *)

Definition section_from_diagonal (isPb : isPullback _ _ _ _ H)
  : (Σ x : C⟦b, c⟧, x ;; g = f)
    ->
    Σ s' : C⟦b, d⟧, s' ;; h = identity _ .
Proof.
  intro X.
  mk_pair.
  - simple refine (PullbackArrow (mk_Pullback _ _ _ _ _ _ isPb) _ (identity _ ) (pr1 X) _ ).
    abstract (rewrite id_left ;  apply (! (pr2 X))).
  - cbn. apply (PullbackArrow_PullbackPr1 (mk_Pullback f g d h k H isPb) ).
Defined.

Definition diagonal_from_section (isPb : isPullback _ _ _ _ H)
  : (Σ x : C⟦b, c⟧, x ;; g = f)
    <-
    Σ s' : C⟦b, d⟧, s' ;; h = identity _ .
Proof.
  intro X.
  exists (pr1 X ;; k).
  abstract (rewrite <- assoc, <- H, assoc, (pr2 X) ; apply id_left).
Defined.

Definition weq_section_from_diagonal (isPb : isPullback _ _ _ _ H)
  : (Σ x : C⟦b, c⟧, x ;; g = f)
    ≃
    Σ s' : C⟦b, d⟧, s' ;; h = identity _ .
Proof.
  exists (section_from_diagonal isPb).
  apply (gradth _ (diagonal_from_section isPb )).
  - abstract (intro x; apply subtypeEquality; [intro; apply hsC  |];
              apply (PullbackArrow_PullbackPr2 (mk_Pullback f g d h k H isPb) )).
  - abstract (intro y; apply subtypeEquality; [intro; apply hsC |];
              destruct y as [y t2];
              apply pathsinv0, PullbackArrowUnique; [
                apply t2 |
                apply idpath] ).
Defined.

(**  Diagram for next lemma

              i'           k
         d' -------> d --------> c
         |           |           |
       h'|           |h          | g
         v           v           v
         b'--------> b --------> a
              i            f
*)

Lemma isPullback_two_pullback
     (b' d' : C) (h' : C⟦d', b'⟧)
     (i : C⟦b', b⟧) (i' : C⟦d', d⟧)
     (Hinner : h ;; f = k ;; g)
     (Hinnerpb : isPullback _ _ _ _ Hinner)
     (Hleft : h' ;; i = i' ;; h)
     (Houterpb : isPullback _ _ _ _ (glueSquares Hinner Hleft ))
     :isPullback _ _ _ _ Hleft.
Proof.
  apply (mk_isPullback).
  intros e x y Hxy.
  mkpair.
  - mkpair.
    use (PullbackArrow (mk_Pullback _ _ _ _ _ _ Houterpb)).
    + apply x.
    + apply (y ;; k).
    + abstract (rewrite assoc; rewrite Hxy;
                repeat rewrite <- assoc; rewrite Hinner; apply idpath).
    + abstract (
      split ;
      [
      apply (PullbackArrow_PullbackPr1 (mk_Pullback (i ;; f) g d' h' (i' ;; k) _ Houterpb))
      |
      idtac
      ];
      apply (MorphismsIntoPullbackEqual Hinnerpb);
      [rewrite <- assoc;
        match goal with |[ |- ?KK ;; ( _ ;; _ ) = _ ] => pathvia (KK ;; (h' ;; i)) end;
        [ apply maponpaths; apply (!Hleft) |
          rewrite assoc;
          assert (T:= PullbackArrow_PullbackPr1 (mk_Pullback (i ;; f) g d' h' (i' ;; k) _ Houterpb));
          cbn in T; rewrite T;
          apply Hxy ]
        | idtac ] ;
      assert (T:= PullbackArrow_PullbackPr2 (mk_Pullback (i ;; f) g d' h' (i' ;; k) _ Houterpb));
      cbn in T; rewrite <- assoc, T; apply idpath
      ).
  - abstract (
    intro t; apply subtypeEquality;
              [ intro; apply isapropdirprod; apply hsC
              |
              simpl; apply PullbackArrowUnique; [
                apply (pr1 (pr2 t))
              |
                cbn; rewrite assoc; rewrite (pr2 (pr2 t)); apply idpath ]]
    ).
Defined.

(**  Diagram for next lemma

              i'           k
         d' -------> d --------> c
         |           |           |
       h'|           |h          | g
         v           v           v
         b'--------> b --------> a
              i            f
*)

Lemma isPullback_iso_of_morphisms (b' d' : C) (h' : C⟦d', b'⟧)
     (i : C⟦b', b⟧) (i' : C⟦d', d⟧)
     (xi : is_iso i) (xi' : is_iso i')
     (Hi : h' ;; i = i' ;; h)
     (H' : h' ;; (i ;; f) = (i' ;; k) ;; g) (* this one is redundant *)
   : isPullback _ _ _ _ H ->
     isPullback _ _ _ _ H'.
Proof.
  intro isPb.
  simple refine (mk_isPullback _ _ _ _ _ _ ).
  intros e x y Hxy.
  set (Pb:= mk_Pullback _ _ _ _ _ _ isPb).
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    + simple refine ( PullbackArrow Pb _ _  _ _ ;; _ ).
      * apply (x ;; i).
      * apply y.
      * abstract (rewrite <- assoc; apply Hxy).
      * cbn. apply (inv_from_iso (isopair i' xi')).
    + cbn. split.
      * assert (X:= PullbackArrow_PullbackPr1 Pb e (x ;; i) y ).
        cbn in X.
        {
        match goal with
          |[ |- ?AA ;; _ ;; _ = _ ] =>
           pathvia (AA ;; h ;; inv_from_iso (isopair i xi)) end.
        - repeat rewrite <- assoc. apply maponpaths.
          apply iso_inv_on_right.
          rewrite assoc.
          apply iso_inv_on_left.
          apply pathsinv0, Hi.
        - rewrite X.
          apply pathsinv0.
          apply iso_inv_on_left. apply idpath.
        }
      * assert (X:= PullbackArrow_PullbackPr2 Pb e (x ;; i) y ).
        cbn in X.
        repeat rewrite assoc.
        {
        match goal with |[|- ?AA ;; _ ;; _ ;; ?K = _ ]
                         => pathvia (AA ;;  K) end.
        - apply cancel_postcomposition.
          repeat rewrite <- assoc.
          rewrite iso_after_iso_inv.
          apply id_right.
        - apply X.
        }
  - cbn. intro t.
    apply subtypeEquality.
    + intros ? . apply isapropdirprod; apply hsC.
    + cbn.
      destruct t as [t Ht]; cbn in *.
      apply iso_inv_on_left.
      apply pathsinv0 , PullbackArrowUnique; cbn in *.
      * rewrite <- assoc. rewrite <- Hi.
        rewrite assoc. rewrite (pr1 Ht). apply idpath.
      * rewrite <- assoc. apply (pr2 Ht).
Defined.

End lemmas_on_pullbacks.



Section functor_on_square.

(** * A fully faithful functor reflects limits *)

Variables C D : precategory.
Variable hsC : has_homsets C.
Variable F : functor C D.


Section isPullback_if_functor_on_square_is.

Variable Fff : fully_faithful F.

Context {a b c d : C}.
Context {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}.
Variable H : h ;; f = k ;; g.

Definition functor_on_square : #F h ;; #F f = #F k ;; #F g.
Proof.
  eapply pathscomp0; [ | apply functor_comp].
  eapply pathscomp0; [ | apply maponpaths ; apply H].
  apply (! functor_comp _ _ _ _ _ _ ).
Defined.

Variable X : isPullback _ _ _ _ functor_on_square.

Lemma isPullback_preimage_square : isPullback _ _ _ _ H.
Proof.
  refine (mk_isPullback _ _ _ _ _ _ ).
  intros e x y Hxy.
  set (T := maponpaths (#F) Hxy).
  set (T' := !functor_comp _ _ _ _ _ _
                 @
                 T
                 @
                 functor_comp _ _ _ _ _ _ ).
  set (TH := X _ _ _ T').
  set (FxFy := pr1 (pr1 TH)).
  set (HFxFy := pr2 (pr1 TH)). simpl in HFxFy.
  set (xy := fully_faithful_inv_hom Fff _ _ FxFy).
  simple refine (tpair _ _ _ ).
  - exists xy.
    set (t := pr1 HFxFy).
    set (p := pr2 HFxFy).
    split.
    + refine ( invmaponpathsweq (weqpair _ (Fff _ _ )) _ _ _ ).
      simpl.
      rewrite functor_comp.
      assert (XX:=homotweqinvweq (weqpair _ (Fff e d ))). simpl in XX.
      unfold xy.
      simpl.
      eapply pathscomp0.
      eapply cancel_postcomposition.
      assert (XXX := XX FxFy).
      apply XX. exact t.
    + refine ( invmaponpathsweq (weqpair _ (Fff _ _ )) _ _ _ ).
      simpl.
      rewrite functor_comp.
      assert (XX:=homotweqinvweq (weqpair _ (Fff e d ))). simpl in XX.
      unfold xy.
      simpl.
      eapply pathscomp0.
      eapply cancel_postcomposition.
      assert (XXX := XX FxFy).
      apply XX. exact p.
  - simpl.
    intro t.
    apply subtypeEquality.
    + intro kkkk. apply isapropdirprod; apply hsC.
    + simpl.
      refine ( invmaponpathsweq (weqpair _ (Fff _ _ )) _ _ _ ).
      simpl.
      unfold xy.
      assert (XX:=homotweqinvweq (weqpair _ (Fff e d ))). simpl in XX.
      apply pathsinv0.
      eapply pathscomp0.
      apply XX.
      apply pathsinv0.
      apply path_to_ctr.
      destruct (pr2 t) as [H1 H2].
      split.
      * assert (X1:= maponpaths (#F) H1).
        eapply pathscomp0. apply (!functor_comp _ _ _ _ _ _ ).
        apply X1.
      * assert (X2:= maponpaths (#F) H2).
        eapply pathscomp0. apply (!functor_comp _ _ _ _ _ _ ).
        apply X2.
Defined.

End isPullback_if_functor_on_square_is.

(** A ff and es functor preserves pullbacks *)

Section functor_preserves_pb.

Variable hsD : has_homsets D.
Variable Fff : fully_faithful F.
Variable Fes : essentially_surjective F.

Let FF a b := (weq_from_fully_faithful Fff a b).

Context {a b c d : C}.
Context {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}.
Variable H : h ;; f = k ;; g.

Variable X : isPullback _ _ _ _ H.

Lemma isPullback_image_square
  : isPullback _ _ _ _ (functor_on_square H).
Proof.
  intros e x y Hxy.
  apply (squash_to_prop (Fes e)).
  apply isapropiscontr.
  intros [e' i].
  set (e'c := invmap (FF _ _ ) (i ;;y)).
  set (e'b := invmap (FF _ _ ) (i ;;x)).
  set (Pb := mk_Pullback _ _ _ _ _ _ X).
  assert (XX : e'b ;; f = e'c ;; g).
  { apply (invmaponpathsweq (FF _ _ )).
    cbn. unfold e'b. unfold e'c.
    repeat rewrite functor_comp.
    set (T:=homotweqinvweq (FF e' b)). cbn in T.
    rewrite T; clear T.
    set (T:=homotweqinvweq (FF e' c)). cbn in T.
    rewrite T; clear T.
    repeat rewrite <- assoc. rewrite Hxy. apply idpath.
  }

  set (umor := PullbackArrow Pb _ e'b e'c XX).
  set (umorPr1 := PullbackArrow_PullbackPr1 Pb _ _ _ XX).
  set (umorPr2 := PullbackArrow_PullbackPr2 Pb _ _ _ XX).
  cbn in *.
  simple refine (tpair _ _ _ ).
  - exists (inv_from_iso i ;; #F umor ).
    split.
    + rewrite <- assoc. apply iso_inv_on_right.
      rewrite <- functor_comp.
      apply (invmaponpathsweq (invweq (FF _ _ ))).
      cbn.
      set (TX:= homotinvweqweq (FF e' b)). cbn in TX.
      rewrite TX; clear TX.
      unfold umor; rewrite umorPr1. apply idpath.
    + rewrite <- assoc. apply iso_inv_on_right.
      rewrite <- functor_comp.
      apply (invmaponpathsweq (invweq (FF _ _ ))).
      cbn.
      set (TX:= homotinvweqweq (FF e' c)). cbn in TX.
      rewrite TX; clear TX.
      unfold umor; rewrite umorPr2. apply idpath.
  - cbn. intro t. apply subtypeEquality ; [
        intros ?; apply isapropdirprod; apply hsD | cbn ].
    destruct t as [t [Htx Hty]]; cbn.
    apply (pre_comp_with_iso_is_inj _ _ _ _ i (pr2 i)).
    rewrite assoc. rewrite iso_inv_after_iso.
    rewrite id_left.
    apply (invmaponpathsweq (invweq (FF _ _ ))).
    cbn.
    set (TX:= homotinvweqweq (FF e' d)). cbn in TX.
    rewrite TX; clear TX.
    apply PullbackArrowUnique.
    + apply (invmaponpathsweq (FF _ _ )).
      set (TX:= homotweqinvweq (FF e' d)). cbn in *.
      rewrite functor_comp, TX; clear TX.
      rewrite <- assoc. rewrite Htx.
      unfold e'b.
      set (TX:= homotweqinvweq (FF e' b)). cbn in *.
      rewrite TX. apply idpath.
    + apply (invmaponpathsweq (FF _ _ )).
      set (TX:= homotweqinvweq (FF e' d)). cbn in *.
      rewrite functor_comp, TX; clear TX.
      rewrite <- assoc. rewrite Hty.
      unfold e'c.
      set (TX:= homotweqinvweq (FF e' c)). cbn in *.
      rewrite TX. apply idpath.
Qed.

End functor_preserves_pb.


Definition maps_pb_square_to_pb_square
  {a b c d : C}
  {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
  (H : h ;; f = k ;; g)
  : UU :=
  isPullback _ _ _ _ H -> isPullback _ _ _ _ (functor_on_square H).

Definition maps_pb_squares_to_pb_squares :=
   ∀ {a b c d : C}
     {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
     (H : h ;; f = k ;; g),
     maps_pb_square_to_pb_square H.

End functor_on_square.


Section pullbacks_pointwise.

(**

          d
    J -------> H
    |          |
  c |          | b
    v          v
    G -------> F
         a

*)

Context {C D : precategory}.
Variable hsD : has_homsets D.
Let CD := [C, D, hsD].
Context {F G H J : CD}.
Context {a : CD ⟦G, F⟧}{b : CD ⟦H, F⟧}{c : CD⟦J,G⟧}{d : CD⟦J, H⟧}.

Variable Hcomm : c ;; a = d ;; b.

Arguments mk_Pullback {_ _ _ _ _ _ _ _ _ _ } _ .

Lemma pb_if_pointwise_pb
  : (∀ x : C, isPullback _ _ _ _ (nat_trans_eq_pointwise Hcomm x)) -> isPullback _ _ _ _ Hcomm.
Proof.
  intro T.
  simple refine (mk_isPullback _ _ _ _ _ _ ).
  intros E h k Hhk.
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    + simple refine (tpair _ _ _ ).
      * intro x.
        {
          simple refine (PullbackArrow (mk_Pullback (T x)) _ _ _ _ ).
          - apply h.
          - apply k.
          - apply (nat_trans_eq_pointwise Hhk).
        }
      * intros x y f.
        {
          abstract (
          apply (MorphismsIntoPullbackEqual (T y)); [
          repeat rewrite <- assoc;
            assert (XX:= PullbackArrow_PullbackPr1
                     (mk_Pullback (T y))); cbn in XX;
            rewrite XX; clear XX;
            rewrite (nat_trans_ax c); rewrite assoc;
            assert (XX:= PullbackArrow_PullbackPr1
                     (mk_Pullback (T x))); cbn in XX;
            rewrite XX; clear XX;
            apply (nat_trans_ax h) |];
          repeat rewrite <- assoc;
            assert (XX:= PullbackArrow_PullbackPr2
                     (mk_Pullback (T y))); cbn in XX;
            rewrite XX; clear XX;
            rewrite (nat_trans_ax d); rewrite assoc;
            assert (XX:= PullbackArrow_PullbackPr2
                     (mk_Pullback (T x))); cbn in XX;
            rewrite XX; clear XX;
            apply (nat_trans_ax k)
            ).
        }
    + abstract (
      split;
       apply nat_trans_eq; try apply hsD ; cbn;
       [ intro ;
        assert (XX:= PullbackArrow_PullbackPr1
                     (mk_Pullback (T x))); cbn in XX;
        apply XX |];
      intro;
      assert (XX:= PullbackArrow_PullbackPr2
                     (mk_Pullback (T x))); cbn in XX;
        apply XX
      ).
  - abstract (
    intro t; apply subtypeEquality; [intro; apply isapropdirprod ;apply functor_category_has_homsets |];
    destruct t as [t Ht];
      apply nat_trans_eq; try assumption; cbn;
    intro x;
    apply PullbackArrowUnique;
     [ apply (nat_trans_eq_pointwise (pr1 Ht)) |];
     apply (nat_trans_eq_pointwise (pr2 Ht))
      ).
Defined.

End pullbacks_pointwise.