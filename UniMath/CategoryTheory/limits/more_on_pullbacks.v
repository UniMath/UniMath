
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.functor_categories.


Section functor_on_square.

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

Variable X : isPullback _ _ _ _ _ functor_on_square.

Lemma isPullback_preimage_square : isPullback _ _ _ _ _ H.
Proof.
  refine (mk_isPullback _ _ _ _ _ _ _ ).
  intros e x y Hxy.
  assert (T := maponpaths (#F) Hxy).
  assert (T' := !functor_comp _ _ _ _ _ _
                 @
                 T
                 @
                 functor_comp _ _ _ _ _ _ ).
  set (TH := X _ _ _ T').
  set (FxFy := pr1 (pr1 TH)).
  assert (HFxFy := pr2 (pr1 TH)). simpl in HFxFy.
  set (xy := fully_faithful_inv_hom Fff _ _ FxFy).
  simple refine (tpair _ _ _ ).
  - exists xy.
    destruct HFxFy as [t p]; split.
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

Definition maps_pb_square_to_pb_square
  {a b c d : C}
  {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
  (H : h ;; f = k ;; g)
  : UU :=
  isPullback _ _ _ _ _ H -> isPullback _ _ _ _ _ (functor_on_square H).

Definition maps_pb_squares_to_pb_squares :=
   ∀ {a b c d : C}
     {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
     (H : h ;; f = k ;; g),
     maps_pb_square_to_pb_square H.

End functor_on_square.