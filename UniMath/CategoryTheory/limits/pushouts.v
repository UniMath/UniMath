(** Direct implementation of pushouts

Definition of Epi in terms of a pushout diagram

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.Epis.

Local Open Scope cat.

Section def_po.

  Context {C : precategory} (hsC : has_homsets C).

  Definition isPushout {a b c d : C} (f : a --> b) (g : a --> c)
             (in1 : b --> d) (in2 : c --> d) (H : f · in1 = g · in2) : UU :=
    ∏ e (h : b --> e) (k : c --> e)(H : f · h = g · k),
    iscontr (total2 (fun hk : d --> e => (in1 · hk = h) × (in2 · hk = k))).

  Lemma isaprop_isPushout {a b c d : C} (f : a --> b) (g : a --> c)
        (in1 : b --> d) (in2 : c --> d) (H : f · in1 = g · in2) :
    isaprop (isPushout f g in1 in2 H).
  Proof.
    repeat (apply impred; intro).
    apply isapropiscontr.
  Qed.

  Lemma PushoutArrowUnique {a b c d : C} (f : a --> b) (g : a --> c)
        (in1 : b --> d) (in2 : c --> d) (H : f · in1 = g · in2)
        (P : isPushout f g in1 in2 H) e (h : b --> e) (k : c --> e)
        (Hcomm : f · h = g · k)
        (w : d --> e)
        (H1 : in1 · w = h) (H2 : in2 · w = k) :
    w = (pr1 (pr1 (P e h k Hcomm))).
  Proof.
    set (T := tpair (fun hk : d --> e => dirprod (in1 · hk = h)(in2 · hk = k))
                    w (dirprodpair H1 H2)).
    set (T' := pr2 (P e h k Hcomm) T).
    exact (base_paths _ _ T').
  Qed.

  Definition Pushout {a b c : C} (f : a --> b) (g : a --> c) :=
    total2 (fun pfg : total2 (λ p : C, (b --> p) × (c --> p)) =>
              total2 (fun H : f · pr1 (pr2 pfg) = g · pr2 (pr2 pfg) =>
                        isPushout f g (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H)).

  Definition Pushouts := ∏ (a b c : C) (f : a --> b) (g : a --> c),
      Pushout f g.

  Definition hasPushouts := ∏ (a b c : C) (f : a --> b) (g : a --> c),
      ishinh (Pushout f g).


  Definition PushoutObject {a b c : C} {f : a --> b} {g : a --> c}:
    Pushout f g -> C := λ H, pr1 (pr1 H).
  Coercion PushoutObject : Pushout >-> ob.

  Definition PushoutIn1 {a b c : C} {f : a --> b} {g : a --> c}
             (Pb : Pushout f g) : b --> Pb := pr1 (pr2 (pr1 Pb)).

  Definition PushoutIn2 {a b c : C} {f : a --> b} {g : a --> c}
             (Pb : Pushout f g) : c --> Pb := pr2 (pr2 (pr1 Pb)).

  Definition PushoutSqrCommutes {a b c : C} {f : a --> b} {g : a --> c}
             (Pb : Pushout f g) :
    f · PushoutIn1 Pb = g · PushoutIn2 Pb.
  Proof.
    exact (pr1 (pr2 Pb)).
  Qed.

  Definition isPushout_Pushout {a b c : C} {f : a --> b} {g : a --> c}
             (P : Pushout f g) :
    isPushout f g (PushoutIn1 P) (PushoutIn2 P) (PushoutSqrCommutes P).
  Proof.
    exact (pr2 (pr2 P)).
  Qed.

  Definition PushoutArrow {a b c : C} {f : a --> b} {g : a --> c}
             (Pb : Pushout f g) e (h : b --> e) (k : c --> e)
             (H : f · h = g · k) :
    Pb --> e := pr1 (pr1 (isPushout_Pushout Pb e h k H)).

  Lemma PushoutArrow_PushoutIn1 {a b c : C} {f : a --> b} {g : a --> c}
        (Pb : Pushout f g) e (h : b --> e) (k : c --> e)
        (H : f · h = g · k) :
    PushoutIn1 Pb · PushoutArrow Pb e h k H = h.
  Proof.
    exact (pr1 (pr2 (pr1 (isPushout_Pushout Pb e h k H)))).
  Qed.

  Lemma PushoutArrow_PushoutIn2 {a b c : C} {f : a --> b} {g : a --> c}
        (Pb : Pushout f g) e (h : b --> e) (k : c --> e)
        (H : f · h = g · k) :
    PushoutIn2 Pb · PushoutArrow Pb e h k H = k.
  Proof.
    exact (pr2 (pr2 (pr1 (isPushout_Pushout Pb e h k H)))).
  Qed.

  Definition mk_Pushout {a b c : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧)
             (d : C) (in1 : C⟦b,d⟧) (in2 : C ⟦c,d⟧)
             (H : f · in1 = g · in2)
             (ispb : isPushout f g in1 in2 H)
    : Pushout f g.
  Proof.
    simple refine (tpair _ _ _ ).
    - simple refine (tpair _ _ _ ).
      + apply d.
      + exists in1.
        exact in2.
    - exists H.
      apply ispb.
  Defined.

  Definition mk_isPushout {a b c d : C} (f : C ⟦a, b⟧) (g : C ⟦a, c⟧)
             (in1 : C⟦b,d⟧) (in2 : C⟦c,d⟧) (H : f · in1 = g · in2) :
    (∏ e (h : C ⟦b, e⟧) (k : C⟦c,e⟧)(Hk : f · h = g · k),
        iscontr (total2 (fun hk : C⟦d,e⟧ =>
                           dirprod (in1 · hk = h)(in2 · hk = k))))
    →
    isPushout f g in1 in2 H.
  Proof.
    intros H' x cx k sqr.
    apply H'. assumption.
  Defined.

  Lemma MorphismsOutofPushoutEqual {a b c d : C} {f : a --> b} {g : a --> c}
        {in1 : b --> d} {in2 : c --> d} {H : f · in1 = g · in2}
        (P : isPushout f g in1 in2 H) {e}
        (w w': d --> e)
        (H1 : in1 · w = in1 · w') (H2 : in2 · w = in2 · w')
    : w = w'.
  Proof.
    assert (Hw : f · in1 · w = g · in2 · w).
    { rewrite H. apply idpath. }
    assert (Hw' : f · in1 · w' = g · in2 · w').
    { rewrite H. apply idpath. }
    set (Pb := mk_Pushout _ _ _ _ _ _ P).
    rewrite <- assoc in Hw. rewrite <- assoc in Hw.
    set (Xw := PushoutArrow Pb e (in1 · w) (in2 · w) Hw).
    pathvia Xw; [ apply PushoutArrowUnique; apply idpath |].
    apply pathsinv0.
    apply PushoutArrowUnique. apply pathsinv0. apply H1.
    apply pathsinv0. apply H2.
  Qed.


  Definition identity_is_Pushout_input {a b c : C} {f : a --> b} {g : a --> c}
             (Pb : Pushout f g) :
    total2 (fun hk : Pb --> Pb =>
              dirprod (PushoutIn1 Pb · hk = PushoutIn1 Pb)
                      (PushoutIn2 Pb · hk = PushoutIn2 Pb)).
  Proof.
    exists (identity Pb).
    apply dirprodpair; apply id_right.
  Defined.

  Lemma PushoutEndo_is_identity {a b c : C} {f : a --> b} {g : a --> c}
        (Pb : Pushout f g) (k : Pb --> Pb)
        (kH1 : PushoutIn1 Pb · k = PushoutIn1 Pb)
        (kH2 : PushoutIn2 Pb · k = PushoutIn2 Pb) :
    identity Pb = k.
  Proof.
    set (H1 := tpair ((fun hk : Pb --> Pb => dirprod (_ · hk = _)(_ · hk = _)))
                     k (dirprodpair kH1 kH2)).
    assert (H2 : identity_is_Pushout_input Pb = H1).
    - apply proofirrelevance.
      apply isapropifcontr.
      apply (isPushout_Pushout Pb).
      apply PushoutSqrCommutes.
    - apply (base_paths _ _ H2).
  Qed.


  Definition from_Pushout_to_Pushout {a b c : C} {f : a --> b} {g : a --> c}
             (Pb Pb': Pushout f g) : Pb --> Pb'.
  Proof.
    apply (PushoutArrow Pb Pb' (PushoutIn1 _ ) (PushoutIn2 _)).
    exact (PushoutSqrCommutes _ ).
  Defined.


  Lemma are_inverses_from_Pushout_to_Pushout {a b c : C} {f : a --> b}
        {g : a --> c} (Pb Pb': Pushout f g) :
    is_inverse_in_precat (from_Pushout_to_Pushout Pb' Pb)
                         (from_Pushout_to_Pushout Pb Pb').
  Proof.
    split.

    (** First identity *)
    apply pathsinv0.
    apply PushoutEndo_is_identity.
    unfold from_Pushout_to_Pushout.
    unfold from_Pushout_to_Pushout.
    rewrite assoc.
    rewrite PushoutArrow_PushoutIn1.
    rewrite PushoutArrow_PushoutIn1.
    apply idpath.

    unfold from_Pushout_to_Pushout.
    unfold from_Pushout_to_Pushout.
    rewrite assoc.
    rewrite PushoutArrow_PushoutIn2.
    rewrite PushoutArrow_PushoutIn2.
    apply idpath.

    (** Second identity *)
    apply pathsinv0.
    apply PushoutEndo_is_identity.
    unfold from_Pushout_to_Pushout.
    unfold from_Pushout_to_Pushout.
    rewrite assoc.
    rewrite PushoutArrow_PushoutIn1.
    rewrite PushoutArrow_PushoutIn1.
    apply idpath.

    unfold from_Pushout_to_Pushout.
    unfold from_Pushout_to_Pushout.
    rewrite assoc.
    rewrite PushoutArrow_PushoutIn2.
    rewrite PushoutArrow_PushoutIn2.
    apply idpath.
  Qed.


  Lemma isiso_from_Pushout_to_Pushout {a b c : C} {f : a --> b} {g : a --> c}
        (Pb Pb': Pushout f g) :
    is_iso (from_Pushout_to_Pushout Pb Pb').
  Proof.
    apply (is_iso_qinv _ (from_Pushout_to_Pushout Pb' Pb)).
    apply are_inverses_from_Pushout_to_Pushout.
  Defined.


  Definition iso_from_Pushout_to_Pushout {a b c : C} {f : a --> b} {g : a --> c}
             (Pb Pb': Pushout f g) : iso Pb Pb' :=
    tpair _ _ (isiso_from_Pushout_to_Pushout Pb Pb').

  Section Universal_Unique.

    Hypothesis H : is_univalent C.


    Lemma inv_from_iso_iso_from_Pushout (a b c : C) (f : a --> b) (g : a --> c)
          (Pb : Pushout f g) (Pb' : Pushout f g):
      inv_from_iso (iso_from_Pushout_to_Pushout Pb Pb')
      = from_Pushout_to_Pushout Pb' Pb.
    Proof.
      apply pathsinv0.
      apply inv_iso_unique'.
      set (T:= are_inverses_from_Pushout_to_Pushout Pb' Pb).
      apply (pr1 T).
    Qed.


    Lemma isaprop_Pushouts: isaprop Pushouts.
    Proof.
      apply impred; intro a; apply impred; intro b; apply impred; intro c;
        apply impred; intro p1; apply impred; intro p2;
          apply invproofirrelevance.
      intros Pb Pb'.
      apply subtypeEquality.
      - intro; apply isofhleveltotal2.
        + apply hsC.
        + intros; apply isaprop_isPushout.
      - apply (total2_paths_f
                 (isotoid _ H (iso_from_Pushout_to_Pushout Pb Pb' ))).
        rewrite transportf_dirprod, transportf_isotoid', transportf_isotoid'.
        fold (PushoutIn1 Pb). fold (PushoutIn2 Pb).
        use (dirprodeq); simpl.

        destruct Pb as [Cone bla];
          destruct Pb' as [Cone' bla'];
          simpl in *.

        destruct Cone as [p [h k]];
          destruct Cone' as [p' [h' k']];
          simpl in *.

        unfold from_Pushout_to_Pushout.
        rewrite PushoutArrow_PushoutIn1.
        apply idpath.

        unfold from_Pushout_to_Pushout.
        rewrite PushoutArrow_PushoutIn2.
        apply idpath.
    Qed.

  End Universal_Unique.

End def_po.

(** Make the C not implicit for Pushouts *)
Arguments Pushouts : clear implicits.

(** In this section we prove that the pushout of an epimorphism is an
  epimorphism. *)
Section epi_po.

  Variable C : precategory.

  (** The pushout of an epimorphism is an epimorphism. *)
  Lemma EpiPushoutisEpi {a b c : C} (E : Epi _ a b) (g : a --> c) (PB : Pushout E g) :
    isEpi (PushoutIn2 PB).
  Proof.
    apply mk_isEpi. intros z g0 h X.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout PB) _ _ _ X).

    set (X0 := maponpaths (λ f, g · f) X); simpl in X0.
    rewrite assoc in X0. rewrite assoc in X0.
    rewrite <- (PushoutSqrCommutes PB) in X0.
    rewrite <- assoc in X0. rewrite <- assoc in X0.
    apply (pr2 E _ _ _) in X0. apply X0.
  Defined.

  (** Same result for the other morphism *)
  Lemma EpiPushoutisEpi' {a b c : C} (f : a --> b) (E : Epi _ a c) (PB : Pushout f E) :
    isEpi (PushoutIn1 PB).
  Proof.
    apply mk_isEpi. intros z g0 h X.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout PB) _ _ X).

    set (X0 := maponpaths (λ f', f · f') X); simpl in X0.
    rewrite assoc in X0. rewrite assoc in X0.
    rewrite (PushoutSqrCommutes PB) in X0.
    rewrite <- assoc in X0. rewrite <- assoc in X0.
    apply (pr2 E _ _ _) in X0. apply X0.
  Defined.

End epi_po.


(** Criteria for existence of pushouts. *)
Section po_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition Pushout_from_Coequalizer_BinCoproduct_eq (X Y Z : C)
             (f : Z --> X) (g : Z --> Y) (BinCoprod : BinCoproductCocone C X Y)
             (CEq : Coequalizer (f · (BinCoproductIn1 C BinCoprod))
                                (g · (BinCoproductIn2 C BinCoprod))) :
    f · ((BinCoproductIn1 C BinCoprod) · CoequalizerArrow CEq)
    = g · ((BinCoproductIn2 C BinCoprod) · CoequalizerArrow CEq).
  Proof.
    repeat rewrite assoc. apply CoequalizerEqAr.
  Qed.


  Definition Pushout_from_Coequalizer_BinCoproduct_isPushout (X Y Z : C)
             (f : Z --> X) (g : Z --> Y) (BinCoprod : BinCoproductCocone C X Y)
             (CEq : Coequalizer (f · (BinCoproductIn1 C BinCoprod))
                                (g · (BinCoproductIn2 C BinCoprod))) :
    isPushout f g (BinCoproductIn1 C BinCoprod · CoequalizerArrow CEq)
               (BinCoproductIn2 C BinCoprod · CoequalizerArrow CEq)
               (Pushout_from_Coequalizer_BinCoproduct_eq
                  X Y Z f g BinCoprod CEq).
  Proof.
    use mk_isPushout.
    intros e h k Hk.
    set (com1 := BinCoproductIn1Commutes C _ _ BinCoprod _ h k).
    set (com2 := BinCoproductIn2Commutes C _ _ BinCoprod _ h k).
    apply (maponpaths (λ l : _, f · l)) in com1.
    apply (maponpaths (λ l : _, g · l)) in com2.
    rewrite <- com1 in Hk. rewrite <- com2 in Hk.
    repeat rewrite assoc in Hk.
    apply (unique_exists (CoequalizerOut CEq _ _ Hk)).

    (* Commutativity *)
    split.
    rewrite <- assoc. rewrite (CoequalizerCommutes CEq e _).
    exact (BinCoproductIn1Commutes C _ _ BinCoprod _ h k).
    rewrite <- assoc. rewrite (CoequalizerCommutes CEq e _).
    exact (BinCoproductIn2Commutes C _ _ BinCoprod _ h k).

    (* Equality on equalities of morphisms. *)
    intros y. apply isapropdirprod. apply hs. apply hs.

    (* Uniqueness *)
    intros y H. induction H as [t p]. apply CoequalizerOutsEq.
    apply BinCoproductArrowsEq.
    rewrite <- assoc in t. rewrite t.
    rewrite (CoequalizerCommutes CEq e _). apply pathsinv0.
    exact (BinCoproductIn1Commutes C _ _ BinCoprod _ h k).
    rewrite <- assoc in p. rewrite p.
    rewrite (CoequalizerCommutes CEq e _). apply pathsinv0.
    exact (BinCoproductIn2Commutes C _ _ BinCoprod _ h k).
  Qed.

  Definition Pushout_from_Coequalizer_BinCoproduct (X Y Z : C)
             (f : Z --> X) (g : Z --> Y) (BinCoprod : BinCoproductCocone C X Y)
             (CEq : Coequalizer (f · (BinCoproductIn1 C BinCoprod))
                                (g · (BinCoproductIn2 C BinCoprod))) :
    Pushout f g.
  Proof.
    use (mk_Pushout f g CEq ((BinCoproductIn1 C BinCoprod)
                               · CoequalizerArrow CEq)
                    ((BinCoproductIn2 C BinCoprod) · CoequalizerArrow CEq)).
    apply Pushout_from_Coequalizer_BinCoproduct_eq.
    apply Pushout_from_Coequalizer_BinCoproduct_isPushout.
  Defined.

  Definition Pushouts_from_Coequalizers_BinCoproducts
             (BinCoprods : BinCoproducts C)
             (CEqs : Coequalizers C) : Pushouts C.
  Proof.
    intros Z X Y f g.
    use (Pushout_from_Coequalizer_BinCoproduct X Y Z f g).
    apply BinCoprods.
    apply CEqs.
  Defined.
End po_criteria.


Section lemmas_on_pushouts.

  Context {C : precategory} (hsC : has_homsets C).
  Context {a b c d : C}.
  Context {f : C ⟦a, b⟧} {g : C ⟦a, c⟧} {h : C⟦b, d⟧} {k : C⟦c, d⟧}.
  Variable H : f · h = g · k.

  (** Pushout is symmetric, i.e., we can rotate a po square *)

  Lemma is_symmetric_isPushout : isPushout _ _ _ _ H -> isPushout _ _ _ _ (!H).
  Proof.
    intro isPo.
    set (Po := mk_Pushout _ _ _ _ _ _ isPo).
    use mk_isPushout.
    intros e x y Hxy.
    use unique_exists.
    - use (PushoutArrow Po).
      + exact y.
      + exact x.
      + exact (! Hxy).
    - cbn. split.
      + apply (PushoutArrow_PushoutIn2 Po).
      + apply (PushoutArrow_PushoutIn1 Po).
    - intros y0. apply isapropdirprod.
      + apply hsC.
      + apply hsC.
    - intros y0. intros X. cbn in X.
      use PushoutArrowUnique.
      + exact (dirprod_pr2 X).
      + exact (dirprod_pr1 X).
  Defined.

End lemmas_on_pushouts.


Section pushout_up_to_iso.

  Context {C : precategory}.
  Context {hs : has_homsets C}.

  Local Lemma isPushout_up_to_iso_eq {a a' b c d : C} (f : a --> b) (g : a --> c)
        (in1 : b --> d) (in2 : c --> d) (H : f · in1 = g · in2) (i : iso a' a) :
    i · f · in1 = i · g · in2.
  Proof.
    rewrite <- assoc. rewrite <- assoc. rewrite H. apply idpath.
  Qed.

  Lemma isPushout_up_to_iso {a a' b c d : C} (f : a --> b) (g : a --> c)
        (in1 : b --> d) (in2 : c --> d) (H : f · in1 = g · in2) (i : iso a' a)
        (iPo : isPushout (i · f) (i · g) in1 in2 (isPushout_up_to_iso_eq f g in1 in2 H i)) :
    isPushout f g in1 in2 H.
  Proof.
    set (Po := mk_Pushout _ _ _ _ _ _ iPo).
    use mk_isPushout.
    intros e h k Hk.
    use unique_exists.
    - use (PushoutArrow Po).
      + exact h.
      + exact k.
      + use isPushout_up_to_iso_eq. exact Hk.
    - cbn. split.
      + exact (PushoutArrow_PushoutIn1 Po e h k (isPushout_up_to_iso_eq f g h k Hk i)).
      + exact (PushoutArrow_PushoutIn2 Po e h k (isPushout_up_to_iso_eq f g h k Hk i)).
    - intros y. apply isapropdirprod.
      + apply hs.
      + apply hs.
    - intros y X. cbn in X.
      use PushoutArrowUnique.
      + exact (dirprod_pr1 X).
      + exact (dirprod_pr2 X).
  Qed.

End pushout_up_to_iso.


Section pushout_paths.

  Context {C : precategory}.
  Context {hs : has_homsets C}.

  Lemma isPushout_mor_paths {a b c d : C} {f1 f2 : a --> b} {g1 g2 : a --> c} {in11 in21 : b --> d}
        {in12 in22 : c --> d} (e1 : f1 = f2) (e2 : g1 = g2) (e3 : in11 = in21) (e4 : in12 = in22)
        (H1 : f1 · in11 = g1 · in12) (H2 : f2 · in21 = g2 · in22)
        (iPo : isPushout f1 g1 in11 in12 H1) : isPushout f2 g2 in21 in22 H2.
  Proof.
    induction e1, e2, e3, e4.
    assert (e5 : H1 = H2) by apply hs.
    induction e5.
    exact iPo.
  Qed.

End pushout_paths.

(**
Proof that f: A -> B is an epi is the same as saying that the diagram
<<
A ---> B
|      |
|      |  id
‌v     ‌‌ v
B----> B
  id
>>
is a pushout
*)
Section EpiPushoutId.

  Context {C : category} {A B : C} (f : C⟦A,B ⟧).

  Lemma epi_to_pushout : isEpi f -> isPushout f f (identity _) (identity _) (idpath _).
  Proof.
    intro h.
    red.
    intros x p1 p2 eqx.
    assert (hp : p1 = p2).
    { now apply h. }
    induction hp.
    apply (unique_exists p1).
    - split; apply id_left.
    - intros y. apply isapropdirprod; apply homset_property.
    - intros y [h1 _].
      now rewrite id_left in h1.
  Qed.

  Lemma pushout_to_epi :  isPushout f f (identity _) (identity _) (idpath _)
                          -> isEpi f.
  Proof.
    intros hf.
    intros D p1 p2 hp.
    apply hf in hp.
    destruct hp as [[p [hp1 hp2]] _].
    now rewrite <- hp1,hp2.
  Qed.

End EpiPushoutId.
