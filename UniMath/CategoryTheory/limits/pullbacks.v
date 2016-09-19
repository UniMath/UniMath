(* Direct implementation of pullbacks *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.Monics.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).


Section def_pb.

Context {C : precategory}.
Variable hs: has_homsets C.

Definition isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 ;; f = p2;; g) : UU :=
   Π e (h : e --> b) (k : e --> c)(H : h ;; f = k ;; g ),
      iscontr (total2 (fun hk : e --> d => dirprod (hk ;; p1 = h)(hk ;; p2 = k))).

Lemma isaprop_isPullback {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 ;; f = p2 ;; g) :
       isaprop (isPullback f g p1 p2 H).
Proof.
  repeat (apply impred; intro).
  apply isapropiscontr.
Qed.

Lemma PullbackArrowUnique {a b c d : C} (f : b --> a) (g : c --> a)
        (p1 : d --> b) (p2 : d --> c) (H : p1 ;; f = p2;; g)
     (P : isPullback f g p1 p2 H) e (h : e --> b) (k : e --> c)
     (Hcomm : h ;; f = k ;; g)
     (w : e --> d)
     (H1 : w ;; p1 = h) (H2 : w ;; p2 = k) :
     w = (pr1 (pr1 (P e h k Hcomm))).
Proof.
  set (T := tpair (fun hk : e --> d => dirprod (hk ;; p1 = h)(hk ;; p2 = k))
                    w (dirprodpair H1 H2)).
  set (T' := pr2 (P e h k Hcomm) T).
  exact (base_paths _ _ T').
Qed.

Definition Pullback {a b c : C} (f : b --> a)(g : c --> a) :=
     total2 (fun pfg : total2 (fun p : C => dirprod (p --> b) (p --> c)) =>
         total2 (fun H : pr1 (pr2 pfg) ;; f = pr2 (pr2 pfg) ;; g =>
        isPullback f g (pr1 (pr2 pfg)) (pr2 (pr2 pfg)) H)).

Definition Pullbacks := Π (a b c : C)(f : b --> a)(g : c --> a),
       Pullback f g.

Definition hasPullbacks := Π (a b c : C) (f : b --> a) (g : c --> a),
         ishinh (Pullback f g).


Definition PullbackObject {a b c : C} {f : b --> a} {g : c --> a}:
   Pullback f g -> C := fun H => pr1 (pr1 H).
Coercion PullbackObject : Pullback >-> ob.

Definition PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) : Pb --> b := pr1 (pr2 (pr1 Pb)).

Definition PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) : Pb --> c := pr2 (pr2 (pr1 Pb)).

Definition PullbackSqrCommutes {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) :
    PullbackPr1 Pb ;; f = PullbackPr2 Pb ;; g .
Proof.
  exact (pr1 (pr2 Pb)).
Qed.

Definition isPullback_Pullback {a b c : C} {f : b --> a}{g : c --> a}
   (P : Pullback f g) :
  isPullback f g (PullbackPr1 P) (PullbackPr2 P) (PullbackSqrCommutes P).
Proof.
  exact (pr2 (pr2 P)).
Qed.

Definition PullbackArrow {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h ;; f = k ;; g) : e --> Pb :=
   pr1 (pr1 (isPullback_Pullback Pb e h k H)).

Lemma PullbackArrow_PullbackPr1 {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h ;; f = k ;; g) :
   PullbackArrow Pb e h k H ;; PullbackPr1 Pb = h.
Proof.
  exact (pr1 (pr2 (pr1 (isPullback_Pullback Pb e h k H)))).
Qed.

Lemma PullbackArrow_PullbackPr2 {a b c : C} {f : b --> a} {g : c --> a}
   (Pb : Pullback f g) e (h : e --> b) (k : e --> c)(H : h ;; f = k ;; g) :
   PullbackArrow Pb e h k H ;; PullbackPr2 Pb = k.
Proof.
  exact (pr2 (pr2 (pr1 (isPullback_Pullback Pb e h k H)))).
Qed.

Definition mk_Pullback {a b c : C} (f : C⟦b, a⟧)(g : C⟦c, a⟧)
    (d : C) (p1 : C⟦d,b⟧) (p2 : C ⟦d,c⟧)
    (H : p1 ;; f = p2 ;; g)
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
           (p1 : C⟦d,b⟧) (p2 : C⟦d,c⟧) (H : p1 ;; f = p2;; g) :
  (Π e (h : C ⟦e, b⟧) (k : C⟦e,c⟧)(Hk : h ;; f = k ;; g ),
      iscontr (total2 (fun hk : C⟦e,d⟧ => dirprod (hk ;; p1 = h)(hk ;; p2 = k))))
  →
  isPullback f g p1 p2 H.
Proof.
  intros H' x cx k sqr.
  apply H'. assumption.
Defined.

Lemma MorphismsIntoPullbackEqual {a b c d : C} {f : b --> a} {g : c --> a}
        {p1 : d --> b} {p2 : d --> c} {H : p1 ;; f = p2;; g}
        (P : isPullback f g p1 p2 H) {e}
        (w w': e --> d)
        (H1 : w ;; p1 = w' ;; p1) (H2 : w ;; p2 = w' ;; p2)
     : w = w'.
Proof.
  assert (Hw : w ;; p1 ;; f = w ;; p2 ;; g).
  { rewrite <- assoc , H, assoc; apply idpath. }
  assert (Hw' : w' ;; p1 ;; f = w' ;; p2 ;; g).
  { rewrite <- assoc , H, assoc; apply idpath. }
  set (Pb := mk_Pullback _ _ _ _ _ _ P).
  set (Xw := PullbackArrow Pb e (w;;p1) (w;;p2) Hw).
  pathvia Xw; [ apply PullbackArrowUnique; apply idpath |].
  apply pathsinv0.
  apply PullbackArrowUnique. apply pathsinv0. apply H1.
  apply pathsinv0. apply H2.
Qed.


Definition identity_is_Pullback_input {a b c : C}{f : b --> a} {g : c --> a} (Pb : Pullback f g) :
 total2 (fun hk : Pb --> Pb =>
   dirprod (hk ;; PullbackPr1 Pb = PullbackPr1 Pb)(hk ;; PullbackPr2 Pb = PullbackPr2 Pb)).
Proof.
  exists (identity Pb).
  apply dirprodpair; apply id_left.
Defined.

Lemma PullbackEndo_is_identity {a b c : C}{f : b --> a} {g : c --> a}
   (Pb : Pullback f g) (k : Pb --> Pb) (kH1 : k ;; PullbackPr1 Pb = PullbackPr1 Pb)
                                       (kH2 : k ;; PullbackPr2 Pb = PullbackPr2 Pb) :
       identity Pb = k.
Proof.
  set (H1 := tpair ((fun hk : Pb --> Pb => dirprod (hk ;; _ = _)(hk ;; _ = _))) k (dirprodpair kH1 kH2)).
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
      is_isomorphism (from_Pullback_to_Pullback Pb Pb').
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
Hypothesis H1 : h ;; f = k ;; g.
Hypothesis H2 : m ;; i = j ;; h.
Hypothesis P1 : isPullback _ _ _ _ H1.
Hypothesis P2 : isPullback _ _ _ _ H2.

Lemma glueSquares : m ;; (i ;; f) = (j ;; k) ;; g.
Proof.
  rewrite assoc.
  rewrite H2.
  repeat rewrite <- assoc.
  rewrite H1.
  apply idpath.
Qed.

Lemma isPullbackGluedSquare : isPullback (i ;; f) g m (j ;; k) glueSquares.
Proof.
  unfold isPullback.
  intros y p q.
  intro Hrt.
  assert (ex : (p;; i);; f = q;; g).
   { rewrite <- Hrt.
     rewrite assoc; apply idpath.
   }
  set (rt := P1 _ (p ;; i) q ex).
  set (Ppiq := pr1 (pr1 (rt))).
  assert (owiej : p ;; i = Ppiq ;; h).
   { apply pathsinv0. apply (pr1 (pr2 (pr1 rt))). }
  set (rt' := P2 _ p Ppiq owiej).
  set (awe := pr1 (pr1 rt')).
  assert (Hawe1 : awe ;; m = p).
   { exact (pr1 (pr2 (pr1 rt'))). }
  assert (Hawe2 : awe ;; (j ;; k) = q).
   { rewrite assoc.
     set (X := pr2 (pr2 (pr1 rt'))). simpl in X.
           unfold awe. rewrite X.
           exact (pr2 (pr2 (pr1 rt))).
   }
  exists (tpair _ awe (dirprodpair Hawe1 Hawe2)).
  intro t.
  apply subtypeEquality.
  - intro a0. apply isapropdirprod;
    apply hs.
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

Hypothesis H : is_category C.


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
    + apply hs.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths  (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))).
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


(** In this section we prove that the pullback of a monomorphism is a
  monomorphism. *)
Section monic_pb.

  Variable C : precategory.

  (** The pullback of a Monic is isMonic. *)
  Lemma MonicPullbackisMonic {a b c : C} (M : Monic _ b a) (g : c --> a)
        (PB : Pullback M g) : isMonic _ (PullbackPr2 PB).
  Proof.
    apply mk_isMonic. intros x g0 h X.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback PB) _ _ _ X).

    set (X0 := maponpaths (fun f => f ;; g) X); simpl in X0.
    rewrite <- assoc in X0. rewrite <- assoc in X0.
    rewrite <- (PullbackSqrCommutes PB) in X0.
    rewrite assoc in X0. rewrite assoc in X0.
    apply (pr2 M _ _ _) in X0. apply X0.
  Defined.

  (** Same result for the other morphism. *)
  Lemma MonicPullbackisMonic' {a b c : C} (f : b --> a) (M : Monic _ c a)
        (PB : Pullback f M) : isMonic _ (PullbackPr1 PB).
  Proof.
    apply mk_isMonic. intros x g h X.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback PB) _ _ X).

    set (X0 := maponpaths (fun f' => f' ;; f) X); simpl in X0.
    rewrite <- assoc in X0. rewrite <- assoc in X0.
    rewrite (PullbackSqrCommutes PB) in X0.
    rewrite assoc in X0. rewrite assoc in X0.
    apply (pr2 M _ _ _) in X0. apply X0.
  Defined.

End monic_pb.

Arguments glueSquares {_ _ _ _ _ _ _ _ _ _ _ _ _ _ } _ _ .


(** Criteria for existence of pullbacks. *)
Section pb_criteria.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition Pullback_from_Equalizer_BinProduct_eq (X Y Z : C)
             (f : X --> Z) (g : Y --> Z) (BinProd : BinProductCone C X Y)
             (Eq : Equalizer ((BinProductPr1 C BinProd) ;; f)
                             ((BinProductPr2 C BinProd) ;; g)) :
    EqualizerArrow Eq ;; (BinProductPr1 C BinProd) ;; f
    = EqualizerArrow Eq ;; (BinProductPr2 C BinProd) ;; g.
  Proof.
    repeat rewrite <- assoc. apply EqualizerEqAr.
  Qed.

  Definition Pullback_from_Equalizer_BinProduct_isPullback (X Y Z : C)
             (f : X --> Z) (g : Y --> Z) (BinProd : BinProductCone C X Y)
             (Eq : Equalizer ((BinProductPr1 C BinProd) ;; f)
                             ((BinProductPr2 C BinProd) ;; g)) :
    isPullback f g (EqualizerArrow Eq ;; BinProductPr1 C BinProd)
               (EqualizerArrow Eq ;; BinProductPr2 C BinProd)
               (Pullback_from_Equalizer_BinProduct_eq
                  X Y Z f g BinProd Eq).
  Proof.
    use mk_isPullback.
    intros e h k Hk.
    set (com1 := BinProductPr1Commutes C _ _ BinProd _ h k).
    set (com2 := BinProductPr2Commutes C _ _ BinProd _ h k).
    apply (maponpaths (fun l : _ => l ;; f)) in com1.
    apply (maponpaths (fun l : _ => l ;; g)) in com2.
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
             (Eq : Equalizer ((BinProductPr1 C BinProd) ;; f)
                             ((BinProductPr2 C BinProd) ;; g)) :
    Pullback f g.
  Proof.
    use (mk_Pullback f g Eq (EqualizerArrow Eq ;; (BinProductPr1 C BinProd))
                     (EqualizerArrow Eq ;; (BinProductPr2 C BinProd))).
    apply Pullback_from_Equalizer_BinProduct_eq.
    apply Pullback_from_Equalizer_BinProduct_isPullback.
  Defined.

  Definition Pullbacks_from_Equalizers_BinProducts (BinProds : BinProducts C)
             (Eqs : @Equalizers C) :
    @Pullbacks C.
  Proof.
    intros Z X Y f g.
    use (Pullback_from_Equalizer_BinProduct X Y Z f g).
    apply BinProds.
    apply Eqs.
  Defined.
End pb_criteria.
