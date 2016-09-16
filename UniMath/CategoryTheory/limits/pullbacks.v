(**

Direct implementation of pullbacks together with:

- Proof that pullbacks form a property in a (saturated/univalent) category ([isaprop_Pullbacks])
- The pullback of a monic is monic ([MonicPullbackisMonic])
- Symmetry ([is_symmetric_isPullback])
- Construction of pullbacks from equalizers and binary products
  ([Pullbacks_from_Equalizers_BinProducts])
- A fully faithfull and essentially surjects functor preserves pullbacks ([isPullback_image_square]
- Construction of binary products from pullbacks ([BinProductsFromPullbacks])

*)
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
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

(** Definition of pullbacks *)
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
   Π {a b c d : C}
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
  : (Π x : C, isPullback _ _ _ _ (nat_trans_eq_pointwise Hcomm x)) -> isPullback _ _ _ _ Hcomm.
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

Section binproduct_from_pullback.

Context {C : precategory} (Pb : @Pullbacks C).
Variable T : Terminal C.

Definition UnivProductFromPullback (c d a : C) (f : a --> c) (g : a --> d):
total2
     (fun fg : a --> Pb T c d (TerminalArrow c) (TerminalArrow d) =>
      dirprod (fg;; PullbackPr1 (Pb T c d (TerminalArrow c) (TerminalArrow d)) = f)
        (fg;; PullbackPr2 (Pb T c d (TerminalArrow c) (TerminalArrow d)) = g)).
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
