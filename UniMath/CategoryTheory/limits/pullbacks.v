(**

Direct implementation of pullbacks together with:

- Proof that pullbacks form a property in a (saturated/univalent) category ([isaprop_Pullbacks])
- The pullback of a monic is monic ([MonicPullbackisMonic])
- A square isomorphic to a pullback is a pullback (case 1) ([isPullback_iso_of_morphisms])
- Symmetry ([is_symmetric_isPullback])
- Construction of pullbacks from equalizers and binary products
  ([Pullbacks_from_Equalizers_BinProducts])
- A fully faithful functor reflects limits ([isPullback_preimage_square])
- A fully faithfull and essentially surjects functor preserves pullbacks ([isPullback_image_square])
- Pullbacks in functor categories ([FunctorcategoryPullbacks])
- Construction of binary products from pullbacks ([BinProductsFromPullbacks])

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.

(** Definition of pullbacks *)
Section def_pb.

Context {C : precategory} (hsC : has_homsets C).

Definition isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 · f = p2· g) : UU :=
   ∏ e (h : e --> b) (k : e --> c)(H : h · f = k · g ),
      iscontr (total2 (fun hk : e --> d => dirprod (hk · p1 = h)(hk · p2 = k))).

Lemma isaprop_isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 · f = p2 · g) :
       isaprop (isPullback f g p1 p2 H).
Proof.
  repeat (apply impred; intro).
  apply isapropiscontr.
Qed.

Lemma PullbackArrowUnique {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 · f = p2· g)
     (P : isPullback f g p1 p2 H) e (h : e --> b) (k : e --> c)
     (Hcomm : h · f = k · g)
     (w : e --> d)
     (H1 : w · p1 = h) (H2 : w · p2 = k) :
     w = (pr1 (pr1 (P e h k Hcomm))).
Proof.
  set (T := tpair (fun hk : e --> d => dirprod (hk · p1 = h)(hk · p2 = k))
                    w (dirprodpair H1 H2)).
  set (T' := pr2 (P e h k Hcomm) T).
  exact (base_paths _ _ T').
Qed.

Definition Pullback {a b c : C} (f : b --> a)(g : c --> a) :=
     total2 (fun pfg : total2 (λ p : C, (p --> b) × (p --> c)) =>
         total2 (fun H : pr1 (pr2 pfg) · f = pr2 (pr2 pfg) · g =>
        isPullback f g (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H)).

Definition Pullbacks := ∏ (a b c : C)(f : b --> a)(g : c --> a),
       Pullback f g.

Definition hasPullbacks := ∏ (a b c : C) (f : b --> a) (g : c --> a),
         ishinh (Pullback f g).


Definition PullbackObject {a b c : C} {f : b --> a} {g : c --> a}:
   Pullback f g -> C := λ H, pr1 (pr1 H).
Coercion PullbackObject : Pullback >-> ob.

Definition PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) : Pb --> b := pr1 (pr2 (pr1 Pb)).

Definition PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) : Pb --> c := pr2 (pr2 (pr1 Pb)).

Definition PullbackSqrCommutes {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) :
    PullbackPr1 Pb · f = PullbackPr2 Pb · g .
Proof.
  exact (pr1 (pr2 Pb)).
Qed.

Definition isPullback_Pullback {a b c : C} {f : b --> a}{g : c --> a}
   (P : Pullback f g) :
  isPullback f g (PullbackPr1 P) (PullbackPr2 P) (PullbackSqrCommutes P).
Proof.
  exact (pr2 (pr2 P)).
Defined.

Definition PullbackArrow {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h · f = k · g) : e --> Pb :=
   pr1 (pr1 (isPullback_Pullback Pb e h k H)).

Lemma PullbackArrowUnique' {a b c : C} (f : C⟦b,a⟧) (g : C⟦c,a⟧)
      (P : Pullback f g) e (h : C⟦e,b⟧) (k : C⟦e,c⟧)
      (Hcomm : h · f = k · g) (w : C⟦e,P⟧) (H1 : w · PullbackPr1 P = h) (H2 : w · PullbackPr2 P = k) :
  w = PullbackArrow P e h k Hcomm.
Proof.
now apply PullbackArrowUnique.
Qed.


Lemma PullbackArrow_PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h · f = k · g) :
   PullbackArrow Pb e h k H · PullbackPr1 Pb = h.
Proof.
  exact (pr1 (pr2 (pr1 (isPullback_Pullback Pb e h k H)))).
Qed.

Lemma PullbackArrow_PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h · f = k · g) :
   PullbackArrow Pb e h k H · PullbackPr2 Pb = k.
Proof.
  exact (pr2 (pr2 (pr1 (isPullback_Pullback Pb e h k H)))).
Qed.

Definition mk_Pullback {a b c : C} (f : C⟦b, a⟧)(g : C⟦c, a⟧)
    (d : C) (p1 : C⟦d,b⟧) (p2 : C ⟦d,c⟧)
    (H : p1 · f = p2 · g)
    (ispb : isPullback f g p1 p2 H)
  : Pullback f g.
Proof.
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    + apply d.
    + exists p1.
      exact p2.
  - exists H.
    apply ispb.
Defined.

Definition mk_isPullback {a b c d : C} (f : C ⟦b, a⟧) (g : C ⟦c, a⟧)
           (p1 : C⟦d,b⟧) (p2 : C⟦d,c⟧) (H : p1 · f = p2· g) :
  (∏ e (h : C ⟦e, b⟧) (k : C⟦e,c⟧)(Hk : h · f = k · g ),
      iscontr (total2 (fun hk : C⟦e,d⟧ => dirprod (hk · p1 = h)(hk · p2 = k))))
  →
  isPullback f g p1 p2 H.
Proof.
  intros H' x cx k sqr.
  apply H'. assumption.
Defined.

Local Lemma postCompWithPullbackArrow_subproof
 {c d a b x : C} (k0 : C⟦c,d⟧) {f : C⟦a,x⟧} {g : C⟦b,x⟧}
 {h : C ⟦ d, a ⟧} {k : C ⟦ d, b ⟧} (H : h · f = k · g)  :
  k0 · h · f = k0 · k · g.
Proof.
now rewrite <- assoc, H, assoc.
Qed.

Lemma postCompWithPullbackArrow
 (c d : C) (k0 : C⟦c,d⟧) {a b x : C} {f : C⟦a,x⟧} {g : C⟦b,x⟧}
 (Pb : Pullback f g)
 (h : C ⟦ d, a ⟧) (k : C ⟦ d, b ⟧) (H : h · f = k · g) :
   k0 · PullbackArrow Pb d h k H =
   PullbackArrow Pb _ (k0 · h) (k0 · k) (postCompWithPullbackArrow_subproof k0 H).
Proof.
apply PullbackArrowUnique.
- now rewrite <- assoc, PullbackArrow_PullbackPr1.
- now rewrite <- assoc, PullbackArrow_PullbackPr2.
Qed.

Lemma MorphismsIntoPullbackEqual {a b c d : C} {f : b --> a} {g : c --> a}
        {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2· g}
        (P : isPullback f g p1 p2 H) {e}
        (w w': e --> d)
        (H1 : w · p1 = w' · p1) (H2 : w · p2 = w' · p2)
     : w = w'.
Proof.
  assert (Hw : w · p1 · f = w · p2 · g).
  { rewrite <- assoc , H, assoc; apply idpath. }
  assert (Hw' : w' · p1 · f = w' · p2 · g).
  { rewrite <- assoc , H, assoc; apply idpath. }
  set (Pb := mk_Pullback _ _ _ _ _ _ P).
  set (Xw := PullbackArrow Pb e (w·p1) (w·p2) Hw).
  pathvia Xw; [ apply PullbackArrowUnique; apply idpath |].
  apply pathsinv0.
  apply PullbackArrowUnique. apply pathsinv0. apply H1.
  apply pathsinv0. apply H2.
Qed.


Definition identity_is_Pullback_input {a b c : C}{f : b --> a} {g : c --> a} (Pb : Pullback f g) :
 total2 (fun hk : Pb --> Pb =>
   dirprod (hk · PullbackPr1 Pb = PullbackPr1 Pb)(hk · PullbackPr2 Pb = PullbackPr2 Pb)).
Proof.
  exists (identity Pb).
  apply dirprodpair; apply id_left.
Defined.

Lemma PullbackEndo_is_identity {a b c : C}{f : b --> a} {g : c --> a}
   (Pb : Pullback f g) (k : Pb --> Pb) (kH1 : k · PullbackPr1 Pb = PullbackPr1 Pb)
                                       (kH2 : k · PullbackPr2 Pb = PullbackPr2 Pb) :
       identity Pb = k.
Proof.
  set (H1 := tpair ((fun hk : Pb --> Pb => dirprod (hk · _ = _)(hk · _ = _))) k (dirprodpair kH1 kH2)).
  assert (H2 : identity_is_Pullback_input Pb = H1).
  - apply proofirrelevance.
    apply isapropifcontr.
    apply (isPullback_Pullback Pb).
    apply PullbackSqrCommutes.
  - apply (base_paths _ _ H2).
Qed.


Definition from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) : Pb --> Pb'.
Proof.
  apply (PullbackArrow Pb' Pb (PullbackPr1 _ ) (PullbackPr2 _)).
  exact (PullbackSqrCommutes _ ).
Defined.


Lemma are_inverses_from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) :
is_inverse_in_precat (from_Pullback_to_Pullback Pb Pb')
  (from_Pullback_to_Pullback Pb' Pb).
Proof.
  split; apply pathsinv0;
  apply PullbackEndo_is_identity;
  rewrite <- assoc;
  unfold from_Pullback_to_Pullback;
  repeat rewrite PullbackArrow_PullbackPr1;
  repeat rewrite PullbackArrow_PullbackPr2;
  auto.
Qed.


Lemma isiso_from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) :
      is_iso (from_Pullback_to_Pullback Pb Pb').
Proof.
  apply (is_iso_qinv _ (from_Pullback_to_Pullback Pb' Pb)).
  apply are_inverses_from_Pullback_to_Pullback.
Defined.


Definition iso_from_Pullback_to_Pullback {a b c : C}{f : b --> a} {g : c --> a}
   (Pb Pb': Pullback f g) : iso Pb Pb' :=
  tpair _ _ (isiso_from_Pullback_to_Pullback Pb Pb').


(** pullback lemma *)

Section pullback_lemma.

Variables a b c d e x : C.
Variables (f : b --> a) (g : c --> a) (h : e --> b) (k : e --> c)
          (i : d --> b) (j : x --> e) (m : x --> d).
Hypothesis H1 : h · f = k · g.
Hypothesis H2 : m · i = j · h.
Hypothesis P1 : isPullback _ _ _ _ H1.
Hypothesis P2 : isPullback _ _ _ _ H2.

Lemma glueSquares : m · (i · f) = (j · k) · g.
Proof.
  rewrite assoc.
  rewrite H2.
  repeat rewrite <- assoc.
  rewrite H1.
  apply idpath.
Qed.

Lemma isPullbackGluedSquare : isPullback (i · f) g m (j · k) glueSquares.
Proof.
  unfold isPullback.
  intros y p q.
  intro Hrt.
  assert (ex : (p· i)· f = q· g).
   { rewrite <- Hrt.
     rewrite assoc; apply idpath.
   }
  set (rt := P1 _ (p · i) q ex).
  set (Ppiq := pr1 (pr1 (rt))).
  assert (owiej : p · i = Ppiq · h).
   { apply pathsinv0. apply (pr1 (pr2 (pr1 rt))). }
  set (rt' := P2 _ p Ppiq owiej).
  set (awe := pr1 (pr1 rt')).
  assert (Hawe1 : awe · m = p).
   { exact (pr1 (pr2 (pr1 rt'))). }
  assert (Hawe2 : awe · (j · k) = q).
   { rewrite assoc.
     set (X := pr2 (pr2 (pr1 rt'))). simpl in X.
           unfold awe. rewrite X.
           exact (pr2 (pr2 (pr1 rt))).
   }
  exists (tpair _ awe (dirprodpair Hawe1 Hawe2)).
  intro t.
  apply subtypeEquality.
  - intro a0. apply isapropdirprod;
    apply hsC.
  - simpl. destruct t as [t [Ht1 Ht2]].
    simpl in *.
    apply PullbackArrowUnique.
    + assumption.
    + apply PullbackArrowUnique.
      * rewrite <- Ht1.
        repeat rewrite <- assoc.
        rewrite H2.
        apply idpath.
      * rewrite <- assoc.
        assumption.
Qed.

End pullback_lemma.

Section Universal_Unique.

Hypothesis H : is_univalent C.

Lemma inv_from_iso_iso_from_Pullback (a b c : C) (f : b --> a) (g : c --> a)
  (Pb : Pullback f g) (Pb' : Pullback f g):
    inv_from_iso (iso_from_Pullback_to_Pullback Pb Pb') = from_Pullback_to_Pullback Pb' Pb.
Proof.
  apply pathsinv0.
  apply inv_iso_unique'.
  set (T:= are_inverses_from_Pullback_to_Pullback Pb Pb').
  apply (pr1 T).
Qed.

Lemma isaprop_Pullbacks: isaprop Pullbacks.
Proof.
  apply impred; intro a;
  apply impred; intro b;
  apply impred; intro c;
  apply impred; intro f;
  apply impred; intro g;
  apply invproofirrelevance.
  intros Pb Pb'.
  apply subtypeEquality.
  - intro; apply isofhleveltotal2.
    + apply hsC.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths_f  (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))).
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in *.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in *.
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
Qed.

End Universal_Unique.

End def_pb.

(** Make the C not implicit for Pullbacks *)
Arguments Pullbacks : clear implicits.

(** In this section we prove that the pullback of a monomorphism is a
  monomorphism. *)
Section monic_pb.

  Variable C : precategory.

  (** The pullback of a Monic is isMonic. *)
  Lemma MonicPullbackisMonic {a b c : C} (M : Monic _ b a) (g : c --> a)
        (PB : Pullback M g) : isMonic (PullbackPr2 PB).
  Proof.
    apply mk_isMonic. intros x g0 h X.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback PB) _ _ _ X).

    set (X0 := maponpaths (λ f, f · g) X); simpl in X0.
    rewrite <- assoc in X0. rewrite <- assoc in X0.
    rewrite <- (PullbackSqrCommutes PB) in X0.
    rewrite assoc in X0. rewrite assoc in X0.
    apply (pr2 M _ _ _) in X0. apply X0.
  Defined.

  (** Same result for the other morphism. *)
  Lemma MonicPullbackisMonic' {a b c : C} (f : b --> a) (M : Monic _ c a)
        (PB : Pullback f M) : isMonic (PullbackPr1 PB).
  Proof.
    apply mk_isMonic. intros x g h X.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback PB) _ _ X).

    set (X0 := maponpaths (λ f', f' · f) X); simpl in X0.
    rewrite <- assoc in X0. rewrite <- assoc in X0.
    rewrite (PullbackSqrCommutes PB) in X0.
    rewrite assoc in X0. rewrite assoc in X0.
    apply (pr2 M _ _ _) in X0. apply X0.
  Defined.

End monic_pb.

Arguments glueSquares {_ _ _ _ _ _ _ _ _ _ _ _ _ _ } _ _ .


(** * Criteria for existence of pullbacks. *)
Section pb_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition Pullback_from_Equalizer_BinProduct_eq (X Y Z : C)
             (f : X --> Z) (g : Y --> Z) (BinProd : BinProductCone C X Y)
             (Eq : Equalizer ((BinProductPr1 C BinProd) · f)
                             ((BinProductPr2 C BinProd) · g)) :
    EqualizerArrow Eq · (BinProductPr1 C BinProd) · f
    = EqualizerArrow Eq · (BinProductPr2 C BinProd) · g.
  Proof.
    repeat rewrite <- assoc. apply EqualizerEqAr.
  Qed.

  Definition Pullback_from_Equalizer_BinProduct_isPullback (X Y Z : C)
             (f : X --> Z) (g : Y --> Z) (BinProd : BinProductCone C X Y)
             (Eq : Equalizer ((BinProductPr1 C BinProd) · f)
                             ((BinProductPr2 C BinProd) · g)) :
    isPullback f g (EqualizerArrow Eq · BinProductPr1 C BinProd)
               (EqualizerArrow Eq · BinProductPr2 C BinProd)
               (Pullback_from_Equalizer_BinProduct_eq
                  X Y Z f g BinProd Eq).
  Proof.
    use mk_isPullback.
    intros e h k Hk.
    set (com1 := BinProductPr1Commutes C _ _ BinProd _ h k).
    set (com2 := BinProductPr2Commutes C _ _ BinProd _ h k).
    apply (maponpaths (λ l : _, l · f)) in com1.
    apply (maponpaths (λ l : _, l · g)) in com2.
    rewrite <- com1 in Hk. rewrite <- com2 in Hk.
    repeat rewrite <- assoc in Hk.
    apply (unique_exists (EqualizerIn Eq _ _ Hk)).

    (* Commutativity *)
    split.
    rewrite assoc. rewrite (EqualizerCommutes Eq e _).
    exact (BinProductPr1Commutes C _ _ BinProd _ h k).
    rewrite assoc. rewrite (EqualizerCommutes Eq e _).
    exact (BinProductPr2Commutes C _ _ BinProd _ h k).

    (* Equality on equalities of morphisms. *)
    intros y. apply isapropdirprod. apply hs. apply hs.

    (* Uniqueness *)
    intros y H. induction H as [t p]. apply EqualizerInsEq. apply BinProductArrowsEq.
    rewrite assoc in t. rewrite t.
    rewrite (EqualizerCommutes Eq e _). apply pathsinv0.
    exact (BinProductPr1Commutes C _ _ BinProd _ h k).
    rewrite assoc in p. rewrite p.
    rewrite (EqualizerCommutes Eq e _). apply pathsinv0.
    exact (BinProductPr2Commutes C _ _ BinProd _ h k).
  Qed.

  Definition Pullback_from_Equalizer_BinProduct (X Y Z : C)
             (f : X --> Z) (g : Y --> Z) (BinProd : BinProductCone C X Y)
             (Eq : Equalizer ((BinProductPr1 C BinProd) · f)
                             ((BinProductPr2 C BinProd) · g)) :
    Pullback f g.
  Proof.
    use (mk_Pullback f g Eq (EqualizerArrow Eq · (BinProductPr1 C BinProd))
                     (EqualizerArrow Eq · (BinProductPr2 C BinProd))).
    apply Pullback_from_Equalizer_BinProduct_eq.
    apply Pullback_from_Equalizer_BinProduct_isPullback.
  Defined.

  Definition Pullbacks_from_Equalizers_BinProducts (BinProds : BinProducts C)
             (Eqs : Equalizers C) : Pullbacks C.
  Proof.
    intros Z X Y f g.
    use (Pullback_from_Equalizer_BinProduct X Y Z f g).
    apply BinProds.
    apply Eqs.
  Defined.

End pb_criteria.

Section lemmas_on_pullbacks.


(** setup for this section
<<
                k
          d --------> c
          |           |
       h  |     H     | g
          v           v
          b --------> a
               f
>>
*)

Context {C : precategory} (hsC : has_homsets C).
Context {a b c d : C}.
Context {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}.
Variable H : h · f = k · g.

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
  (s : C⟦a,c⟧) (K : s · g = identity _ )
  : ∑ s' : C⟦b, d⟧, s' · h = identity _ .
Proof.
  simple refine (tpair _ _ _ ).
  - simple refine (PullbackArrow (mk_Pullback _ _ _ _ _ _ isPb) b (identity _ )
                  (f · s) _ ).
    abstract (rewrite id_left, <- assoc, K, id_right; apply idpath).
  - abstract (cbn; apply (PullbackArrow_PullbackPr1 (mk_Pullback f g d h k H isPb))).
Defined.


Ltac mk_pair := simple refine (tpair _ _ _ ).

(** Diagonal morphisms are equivalent to sections *)

Definition section_from_diagonal (isPb : isPullback _ _ _ _ H)
  : (∑ x : C⟦b, c⟧, x · g = f)
    ->
    ∑ s' : C⟦b, d⟧, s' · h = identity _ .
Proof.
  intro X.
  mk_pair.
  - simple refine (PullbackArrow (mk_Pullback _ _ _ _ _ _ isPb) _ (identity _ ) (pr1 X) _ ).
    abstract (rewrite id_left ;  apply (! (pr2 X))).
  - cbn. apply (PullbackArrow_PullbackPr1 (mk_Pullback f g d h k H isPb) ).
Defined.

Definition diagonal_from_section (isPb : isPullback _ _ _ _ H)
  : (∑ x : C⟦b, c⟧, x · g = f)
    <-
    ∑ s' : C⟦b, d⟧, s' · h = identity _ .
Proof.
  intro X.
  exists (pr1 X · k).
  abstract (rewrite <- assoc, <- H, assoc, (pr2 X) ; apply id_left).
Defined.

Definition weq_section_from_diagonal (isPb : isPullback _ _ _ _ H)
  : (∑ x : C⟦b, c⟧, x · g = f)
    ≃
    ∑ s' : C⟦b, d⟧, s' · h = identity _ .
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
<<
              i'           k
         d' -------> d --------> c
         |           |           |
       h'|           |h          | g
         v           v           v
         b'--------> b --------> a
              i            f
>>
*)

Lemma isPullback_two_pullback
     (b' d' : C) (h' : C⟦d', b'⟧)
     (i : C⟦b', b⟧) (i' : C⟦d', d⟧)
     (Hinner : h · f = k · g)
     (Hinnerpb : isPullback _ _ _ _ Hinner)
     (Hleft : h' · i = i' · h)
     (Houterpb : isPullback _ _ _ _ (glueSquares Hinner Hleft ))
     :isPullback _ _ _ _ Hleft.
Proof.
  apply (mk_isPullback).
  intros e x y Hxy.
  mkpair.
  - mkpair.
    use (PullbackArrow (mk_Pullback _ _ _ _ _ _ Houterpb)).
    + apply x.
    + apply (y · k).
    + abstract (rewrite assoc; rewrite Hxy;
                repeat rewrite <- assoc; rewrite Hinner; apply idpath).
    + abstract (
      split ;
      [
      apply (PullbackArrow_PullbackPr1 (mk_Pullback (i · f) g d' h' (i' · k) _ Houterpb))
      |
      idtac
      ];
      apply (MorphismsIntoPullbackEqual Hinnerpb);
      [rewrite <- assoc;
        match goal with |[ |- ?KK · ( _ · _ ) = _ ] => pathvia (KK · (h' · i)) end;
        [ apply maponpaths; apply (!Hleft) |
          rewrite assoc;
          assert (T:= PullbackArrow_PullbackPr1 (mk_Pullback (i · f) g d' h' (i' · k) _ Houterpb));
          cbn in T; rewrite T;
          apply Hxy ]
        | idtac ] ;
      assert (T:= PullbackArrow_PullbackPr2 (mk_Pullback (i · f) g d' h' (i' · k) _ Houterpb));
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

(** * A square isomorphic to a pullback is a pullback (case 1) *)
Section pullback_iso.

(**  Diagram for next lemma
<<
              i'           k
         d' -------> d --------> c
         |           |           |
       h'|           |h          | g
         v           v           v
         b'--------> b --------> a
              i            f
>>
*)

Lemma isPullback_iso_of_morphisms (b' d' : C) (h' : C⟦d', b'⟧)
     (i : C⟦b', b⟧) (i' : C⟦d', d⟧)
     (xi : is_iso i) (xi' : is_iso i')
     (Hi : h' · i = i' · h)
     (H' : h' · (i · f) = (i' · k) · g) (* this one is redundant *)
   : isPullback _ _ _ _ H ->
     isPullback _ _ _ _ H'.
Proof.
  intro isPb.
  simple refine (mk_isPullback _ _ _ _ _ _ ).
  intros e x y Hxy.
  set (Pb:= mk_Pullback _ _ _ _ _ _ isPb).
  simple refine (tpair _ _ _ ).
  - simple refine (tpair _ _ _ ).
    + simple refine ( PullbackArrow Pb _ _  _ _ · _ ).
      * apply (x · i).
      * apply y.
      * abstract (rewrite <- assoc; apply Hxy).
      * cbn. apply (inv_from_iso (isopair i' xi')).
    + cbn. split.
      * assert (X:= PullbackArrow_PullbackPr1 Pb e (x · i) y ).
        cbn in X.
        {
        match goal with
          |[ |- ?AA · _ · _ = _ ] =>
           pathvia (AA · h · inv_from_iso (isopair i xi)) end.
        - repeat rewrite <- assoc. apply maponpaths.
          apply iso_inv_on_right.
          rewrite assoc.
          apply iso_inv_on_left.
          apply pathsinv0, Hi.
        - rewrite X.
          apply pathsinv0.
          apply iso_inv_on_left. apply idpath.
        }
      * assert (X:= PullbackArrow_PullbackPr2 Pb e (x · i) y ).
        cbn in X.
        repeat rewrite assoc.
        {
        match goal with |[|- ?AA · _ · _ · ?K = _ ]
                         => pathvia (AA ·  K) end.
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

End pullback_iso.

End lemmas_on_pullbacks.

(** * A fully faithful functor reflects limits *)
Section functor_on_square.

Variables C D : precategory.
Variable hsC : has_homsets C.
Variable F : functor C D.

Section isPullback_if_functor_on_square_is.

Variable Fff : fully_faithful F.

Context {a b c d : C}.
Context {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}.
Variable H : h · f = k · g.

Definition functor_on_square : #F h · #F f = #F k · #F g.
Proof.
  eapply pathscomp0; [ | apply functor_comp].
  eapply pathscomp0; [ | apply maponpaths ; apply H].
  apply (! functor_comp _ _ _ ).
Defined.

Variable X : isPullback _ _ _ _ functor_on_square.

Lemma isPullback_preimage_square : isPullback _ _ _ _ H.
Proof.
  refine (mk_isPullback _ _ _ _ _ _ ).
  intros e x y Hxy.
  set (T := maponpaths (#F) Hxy).
  set (T' := !functor_comp _ _ _
                 @
                 T
                 @
                 functor_comp _ _ _ ).
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
        eapply pathscomp0. apply (!functor_comp _ _ _ ).
        apply X1.
      * assert (X2:= maponpaths (#F) H2).
        eapply pathscomp0. apply (!functor_comp _ _ _).
        apply X2.
Defined.

End isPullback_if_functor_on_square_is.

(** * A fully faithful and essentially surjective functor preserves pullbacks *)
Section ff_es_functor_preserves_pb.

Variable hsD : has_homsets D.
Variable Fff : fully_faithful F.
Variable Fes : essentially_surjective F.

Let FF a b := (weq_from_fully_faithful Fff a b).

Context {a b c d : C}.
Context {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}.
Variable H : h · f = k · g.

Variable X : isPullback _ _ _ _ H.

Lemma isPullback_image_square
  : isPullback _ _ _ _ (functor_on_square H).
Proof.
  intros e x y Hxy.
  apply (squash_to_prop (Fes e)).
  apply isapropiscontr.
  intros [e' i].
  set (e'c := invmap (FF _ _ ) (i ·y)).
  set (e'b := invmap (FF _ _ ) (i ·x)).
  set (Pb := mk_Pullback _ _ _ _ _ _ X).
  assert (XX : e'b · f = e'c · g).
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
  - exists (inv_from_iso i · #F umor ).
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

End ff_es_functor_preserves_pb.


Definition maps_pb_square_to_pb_square
  {a b c d : C}
  {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
  (H : h · f = k · g)
  : UU :=
  isPullback _ _ _ _ H -> isPullback _ _ _ _ (functor_on_square H).

Definition maps_pb_squares_to_pb_squares :=
   ∏ (a b c d : C)
     {f : C ⟦b, a⟧} {g : C ⟦c, a⟧} {h : C⟦d, b⟧} {k : C⟦d,c⟧}
     (H : h · f = k · g),
     maps_pb_square_to_pb_square H.

End functor_on_square.

(** * Pullbacks in functor categories *)
Section pullbacks_pointwise.

(** Diagram for this section:
<<
          d
    J -------> H
    |          |
  c |          | b
    v          v
    G -------> F
         a
>>
*)

Context {C D : precategory} (hsD : has_homsets D).
Let CD := [C, D, hsD].
Context {F G H J : CD}.
Context {a : CD ⟦G, F⟧}{b : CD ⟦H, F⟧}{c : CD⟦J,G⟧}{d : CD⟦J, H⟧}.

Variable Hcomm : c · a = d · b.

Arguments mk_Pullback {_ _ _ _ _ _ _ _ _ _ } _ .

Let Hcommx x := nat_trans_eq_pointwise Hcomm x.

Local Definition g (T : ∏ x, isPullback _ _ _ _ (Hcommx x))
  E (h : CD ⟦ E, G ⟧) (k : CD ⟦ E, H ⟧)
  (Hhk : h · a = k · b) : ∏ x, D ⟦ pr1 E x, pr1 J x ⟧.
Proof.
intro x; apply (PullbackArrow (mk_Pullback (T x)) _ (pr1 h x) (pr1 k x)).
abstract (apply (nat_trans_eq_pointwise Hhk)).
Defined.

Local Lemma is_nat_trans_g (T : ∏ x, isPullback _ _ _ _ (Hcommx x))
  E (h : CD ⟦ E, G ⟧) (k : CD ⟦ E, H ⟧)
  (Hhk : h · a = k · b) : is_nat_trans _ _ (λ x : C, g T E h k Hhk x).
Proof.
intros x y f; unfold g.
apply (MorphismsIntoPullbackEqual (T y)).
+ rewrite <- !assoc, (PullbackArrow_PullbackPr1 (mk_Pullback (T y))).
  rewrite (nat_trans_ax c), assoc.
  now rewrite (PullbackArrow_PullbackPr1 (mk_Pullback (T x))), (nat_trans_ax h).
+ rewrite <- !assoc,(PullbackArrow_PullbackPr2 (mk_Pullback (T y))).
  rewrite (nat_trans_ax d), assoc.
  now rewrite (PullbackArrow_PullbackPr2 (mk_Pullback (T x))), (nat_trans_ax k).
Qed.

Lemma pb_if_pointwise_pb : (∏ x, isPullback _ _ _ _ (Hcommx x)) ->
  isPullback _ _ _ _ Hcomm.
Proof.
intro T.
use mk_isPullback; intros E h k Hhk.
use unique_exists.
- mkpair.
  + intro x; apply (g T E h k Hhk).
  + apply is_nat_trans_g.
- abstract (split; apply (nat_trans_eq hsD); intro x;
           [ apply (PullbackArrow_PullbackPr1 (mk_Pullback (T x)))
           | apply (PullbackArrow_PullbackPr2 (mk_Pullback (T x))) ]).
- abstract (intro; apply isapropdirprod; apply functor_category_has_homsets).
- abstract (intros t [h1 h2]; destruct h as [h Hh];
            apply (nat_trans_eq hsD); intro x; apply PullbackArrowUnique;
            [ apply (nat_trans_eq_pointwise h1) | apply (nat_trans_eq_pointwise h2) ]).
Defined.

End pullbacks_pointwise.

(** * Construction of binary products from pullbacks *)
Section binproduct_from_pullback.

Context {C : precategory} (Pb : Pullbacks C) (T : Terminal C).

Definition UnivProductFromPullback (c d a : C) (f : a --> c) (g : a --> d):
total2
     (fun fg : a --> Pb T c d (TerminalArrow c) (TerminalArrow d) =>
      dirprod (fg· PullbackPr1 (Pb T c d (TerminalArrow c) (TerminalArrow d)) = f)
        (fg· PullbackPr2 (Pb T c d (TerminalArrow c) (TerminalArrow d)) = g)).
Proof.
  unfold Pullbacks in Pb.
  exists (PullbackArrow (Pb _ _ _ (TerminalArrow c)(TerminalArrow d)) _ f g
       (ArrowsToTerminal _ _ _ _ _)).
  split.
  apply PullbackArrow_PullbackPr1 .
  apply PullbackArrow_PullbackPr2 .
Defined.

Lemma isBinProductCone_PullbackCone (c d : C):
   isBinProductCone C c d
            (PullbackObject (Pb _ _ _ (TerminalArrow c) (TerminalArrow (T:=T) d)))
   (PullbackPr1 _  ) (PullbackPr2 _ ).
Proof.
  intros a f g.
  exists (UnivProductFromPullback c d a f g).
  intro t.
  apply proofirrelevance,
        isapropifcontr,
        isPullback_Pullback,
        ArrowsToTerminal.
Qed.

Definition BinProductCone_PullbackCone (c d : C) : BinProductCone _ c d.
Proof.
  exists
  (tpair _ (PullbackObject (Pb _ _ _ (TerminalArrow c)(TerminalArrow (T:=T) d)))
               (dirprodpair  (PullbackPr1 _) (PullbackPr2 _))).
 exact (isBinProductCone_PullbackCone c d).
Defined.

Definition BinProductsFromPullbacks : BinProducts C := BinProductCone_PullbackCone.

End binproduct_from_pullback.


(** * Pullbacks in functor_precategory
    We construct pullbacks in the functor category [D, C, hs] from pullbacks of C. *)
Section pullbacks_functor_category.

  Variable D C : precategory.
  Hypothesis hs : has_homsets C.
  Hypothesis hpb : @Pullbacks C.

  Local Lemma FunctorcategoryPullbacks_eq (F G H : functor D C) (α : nat_trans G F)
        (β : nat_trans H F) (a b : D) (f : D ⟦a, b⟧) :
    PullbackPr1 (hpb _ _ _ (α a) (β a)) · # G f · α b =
    PullbackPr2 (hpb _ _ _ (α a) (β a)) · # H f · β b.
  Proof.
    set (pba := hpb _ _ _ (α a) (β a)).
    repeat rewrite <- assoc.
    rewrite (nat_trans_ax α a b f).
    rewrite (nat_trans_ax β a b f).
    repeat rewrite assoc.
    apply cancel_postcomposition.
    exact (PullbackSqrCommutes pba).
  Qed.

  Local Lemma FunctorcategoryPullbacks_isfunctor (F G H : functor D C) (α : nat_trans G F)
        (β : nat_trans H F) :
    is_functor
      (mk_functor_data
         (λ d : D, hpb (F d) (G d) (H d) (α d) (β d))
         (λ (a b : D) (f : D ⟦ a, b ⟧),
          PullbackArrow
            (hpb (F b) (G b) (H b) (α b) (β b))
            (hpb (F a) (G a) (H a) (α a) (β a))
            (PullbackPr1 (hpb (F a) (G a) (H a) (α a) (β a)) · # G f)
            (PullbackPr2 (hpb (F a) (G a) (H a) (α a) (β a)) · # H f)
            (FunctorcategoryPullbacks_eq F G H α β a b f))).
  Proof.
    split.
    intros x. apply pathsinv0. cbn.
    use PullbackArrowUnique.
    rewrite functor_id. rewrite id_left. rewrite id_right. apply idpath.
    rewrite functor_id. rewrite id_left. rewrite id_right. apply idpath.
    intros x y z f g.
    set (px := hpb (F x) (G x) (H x) (α x) (β x)).
    set (py := hpb (F y) (G y) (H y) (α y) (β y)).
    set (pz := hpb (F z) (G z) (H z) (α z) (β z)).
    set (pz1 := PullbackArrow_PullbackPr1 pz py (PullbackPr1 py · # G g)
                                          (PullbackPr2 py · # H g)
                                          (FunctorcategoryPullbacks_eq
                                             F G H α β y z g)).
    set (pz2 := PullbackArrow_PullbackPr2 pz py (PullbackPr1 py · # G g)
                                          (PullbackPr2 py · # H g)
                                          (FunctorcategoryPullbacks_eq
                                             F G H α β y z g)).
    set (py1 := PullbackArrow_PullbackPr1 py px (PullbackPr1 px · # G f)
                                          (PullbackPr2 px · # H f)
                                          (FunctorcategoryPullbacks_eq
                                             F G H α β x y f)).
    set (py2 := PullbackArrow_PullbackPr2 py px (PullbackPr1 px · # G f)
                                          (PullbackPr2 px · # H f)
                                          (FunctorcategoryPullbacks_eq
                                             F G H α β x y f)).
    apply pathsinv0. cbn. fold px. fold py. fold pz.
    use PullbackArrowUnique.
    rewrite functor_comp. rewrite assoc.
    rewrite <- assoc. rewrite pz1. rewrite assoc.
    apply cancel_postcomposition.
    apply py1.

    rewrite functor_comp. rewrite assoc.
    rewrite <- assoc. rewrite pz2. rewrite assoc.
    apply cancel_postcomposition.
    apply py2.
  Qed.

  Local Definition FunctorcategoryPullbacks_functor (F G H : functor D C) (α : nat_trans G F)
        (β : nat_trans H F) : functor D C.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + intros d.
        exact (PullbackObject (hpb _ _ _ (α d) (β d))).
      + intros a b f.
        use (PullbackArrow (hpb _ _ _ (α b) (β b)) _
                           (PullbackPr1 (hpb _ _ _ (α a) (β a)) · (# G f))
                           (PullbackPr2 (hpb _ _ _ (α a) (β a)) · (# H f))
                           (FunctorcategoryPullbacks_eq F G H α β a b f)).
    - exact (FunctorcategoryPullbacks_isfunctor F G H α β).
  Defined.

  Local Lemma FunctorcategoryPullbacks_is_nat_trans1 (F G H : functor D C) (α : nat_trans G F)
        (β : nat_trans H F) :
    is_nat_trans (FunctorcategoryPullbacks_functor F G H α β) G
                 (λ x : D, PullbackPr1 (hpb (F x) (G x) (H x) (α x) (β x))).
  Proof.
    intros x x' f. cbn.
    set (px := hpb (F x) (G x) (H x) (α x) (β x)).
    set (px' := hpb (F x') (G x') (H x') (α x') (β x')).
    apply (PullbackArrow_PullbackPr1 px' px (PullbackPr1 px · # G f)
                                     (PullbackPr2 px · # H f)
                                     (FunctorcategoryPullbacks_eq
                                        F G H α β x x' f)).
  Qed.

  Local Definition FunctorcategoryPullbacks_nat_trans1 (F G H : functor D C) (α : nat_trans G F)
        (β : nat_trans H F) : nat_trans (FunctorcategoryPullbacks_functor F G H α β) G.
  Proof.
    use mk_nat_trans.
    - intros x. exact (PullbackPr1 (hpb (F x) (G x) (H x) (α x) (β x))).
    - exact (FunctorcategoryPullbacks_is_nat_trans1 F G H α β).
  Defined.

  Local Lemma FunctorcategoryPullbacks_is_nat_trans2 (F G H : functor D C) (α : nat_trans G F)
        (β : nat_trans H F) :
    is_nat_trans (FunctorcategoryPullbacks_functor F G H α β) H
                 (λ x : D, PullbackPr2 (hpb (F x) (G x) (H x) (α x) (β x))).
  Proof.
    intros x x' f. cbn.
    set (px := hpb (F x) (G x) (H x) (α x) (β x)).
    set (px' := hpb (F x') (G x') (H x') (α x') (β x')).
    apply (PullbackArrow_PullbackPr2 px' px (PullbackPr1 px · # G f)
                                     (PullbackPr2 px · # H f)
                                     (FunctorcategoryPullbacks_eq
                                        F G H α β x x' f)).
  Qed.


  Local Definition FunctorcategoryPullbacks_nat_trans2 (F G H : functor D C) (α : nat_trans G F)
        (β : nat_trans H F) : nat_trans (FunctorcategoryPullbacks_functor F G H α β) H.
  Proof.
    use mk_nat_trans.
    - intros x. exact (PullbackPr2 (hpb (F x) (G x) (H x) (α x) (β x))).
    - exact (FunctorcategoryPullbacks_is_nat_trans2 F G H α β).
  Defined.

  Local Lemma FunctorcategoryPullbacks_comm (F G H : functor D C) (α : nat_trans G F)
        (β : nat_trans H F) :
    nat_trans_comp _ _ _ (FunctorcategoryPullbacks_nat_trans1 F G H α β) α =
    nat_trans_comp _ _ _ (FunctorcategoryPullbacks_nat_trans2 F G H α β) β.
  Proof.
    use (nat_trans_eq hs). intros x.
    apply (PullbackSqrCommutes (hpb (F x) (G x) (H x) (α x) (β x))).
  Qed.

  Definition FunctorcategoryPullbacks : @Pullbacks (functor_precategory D C hs).
  Proof.
    intros F G H α β. cbn in F, G, H, α, β.
    use mk_Pullback.
    (* Pullback object *)
    - exact (FunctorcategoryPullbacks_functor F G H α β).
    (* Pr1 *)
    - exact (FunctorcategoryPullbacks_nat_trans1 F G H α β).
    (* Pr2 *)
    - exact (FunctorcategoryPullbacks_nat_trans2 F G H α β).
    (* Commutativity of the square *)
    - exact (FunctorcategoryPullbacks_comm F G H α β).
    (* isPullback *)
    - apply pb_if_pointwise_pb. intros x. cbn. apply isPullback_Pullback.
  Defined.

End pullbacks_functor_category.


Section pullback_up_to_iso.

  Context {C : precategory}.
  Context {hs : has_homsets C}.

  Local Lemma isPullback_up_to_iso_eq {a' a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 · f = p2 · g) (i : iso a a') :
    p1 · (f · i) = p2 · (g · i).
  Proof.
    rewrite assoc. rewrite assoc. rewrite H. apply idpath.
  Qed.

  Lemma isPullback_up_to_iso {a' a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 · f = p2 · g) (i : iso a a')
        (iPb : isPullback (f · i) (g · i) p1 p2 (isPullback_up_to_iso_eq f g p1 p2 H i)) :
    isPullback f g p1 p2 H.
  Proof.
    set (Pb := mk_Pullback _ _ _ _ _ _ iPb).
    use mk_isPullback.
    intros e h k Hk.
    use unique_exists.
    - use (PullbackArrow Pb).
      + exact h.
      + exact k.
      + use isPullback_up_to_iso_eq. exact Hk.
    - cbn. split.
      + exact (PullbackArrow_PullbackPr1 Pb e h k (isPullback_up_to_iso_eq f g h k Hk i)).
      + exact (PullbackArrow_PullbackPr2 Pb e h k (isPullback_up_to_iso_eq f g h k Hk i)).
    - intros y. apply isapropdirprod.
      + apply hs.
      + apply hs.
    - intros y X. cbn in X.
      use PullbackArrowUnique.
      + exact (dirprod_pr1 X).
      + exact (dirprod_pr2 X).
  Qed.

End pullback_up_to_iso.

Section pullback_paths.

  Context {C : precategory}.
  Context {hs : has_homsets C}.

  Lemma isPullback_mor_paths {a b c d : C} {f1 f2 : b --> a} {g1 g2 : c --> a} {p11 p21 : d --> b}
        {p12 p22 : d --> c} (e1 : f1 = f2) (e2 : g1 = g2) (e3 : p11 = p21) (e4 : p12 = p22)
        (H1 : p11 · f1 = p12 · g1) (H2 : p21 · f2 = p22 · g2)
        (iPb : isPullback f1 g1 p11 p12 H1) : isPullback f2 g2 p21 p22 H2.
  Proof.
    induction e1, e2, e3, e4.
    assert (e5 : H1 = H2) by apply hs.
    induction e5.
    exact iPb.
  Qed.

End pullback_paths.
