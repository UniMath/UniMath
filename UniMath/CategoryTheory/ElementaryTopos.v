(** **
  Following Saunders Mac Lane & Ieke Moerdijk
  Sheaves in Geometry and Logic - A First Introduction to Topos theory.
  Chapter IV.1 and IV.2

  Contents :
  - definition of elementary topos ([Topos]) as a category which has:
    -) finite limits meaning:
      --) Terminal Object
      --) Binary Pullbacks
    -) Power Object
    -) Subobject Classifier
  - definition of the [KroneckerDelta] predicate and the [SingletonArrow]
  - proof that [SingletonArrow] is monic ([SingletonArrow_isMonic])
  - derivation of exponentials [Exponentials_from_Topos]
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.PowerObject.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.

Local Open Scope cat.

(*
An elementary topos is a category which has:
  -) finite limits meaning:
    --) Terminal Object
    --) Binary Pullbacks
  -) Power Object
  -) Subobject Classifier
*)

Definition Topos_Structure (C : category) :=
  ∑ (PB : Pullbacks C) (T : Terminal C) (Ω : subobject_classifier T),
    (PowerObject (BinProductsFromPullbacks PB T) Ω).

Definition Topos := ∑ (C:category), Topos_Structure C.

Definition make_Topos_Structure {C:category} (PB : Pullbacks C) (T : Terminal C)
  (Ω: subobject_classifier T) (P: PowerObject (BinProductsFromPullbacks PB T) Ω)
  : Topos_Structure C.
Proof.
  split with PB.
  split with T.
  split with Ω.
  exact P.
Defined.

Definition make_Topos {C:category} (str: Topos_Structure C)
  : Topos.
Proof.
  split with C.
  exact str.
Defined.

Section ToposAccessor.

Context (C : Topos).

Definition Topos_category : category := pr1 C.
Definition Topos_Pullbacks : Pullbacks Topos_category := pr1 (pr2 C).
Definition Topos_Terminal : Terminal Topos_category := pr1 (pr2 (pr2 C)).
Definition Topos_SubobjectClassifier : subobject_classifier (Topos_Terminal) := pr1 (pr2 (pr2 (pr2 C))).
Definition Topos_BinProducts : BinProducts Topos_category := BinProductsFromPullbacks (Topos_Pullbacks) (Topos_Terminal).
Definition Topos_PowerObject : PowerObject (Topos_BinProducts) (Topos_SubobjectClassifier) := pr2 (pr2 (pr2 (pr2 C))).

End ToposAccessor.

Coercion Topos_category : Topos >->category.

Section Topos.

Context {C:Topos}.
Let T := Topos_Terminal C.
Let PB := Topos_Pullbacks C.
Let BinProd := Topos_BinProducts C.
Let P := Topos_PowerObject C.
Let Ω := Topos_SubobjectClassifier C.
Local Notation "c ⨉ d"
  := (BinProductObject C (BinProd c d))(at level 5).
  (*\bigtimes*)
Local Notation "f ⨱ g"
  := (BinProductOfArrows _ (BinProd _ _) (BinProd _ _) f g) (at level 10).
  (*\timesbar*)

Section KroneckerDelta.
(*The [KroneckerDelta] predicate is defined as
the chraracteristic morphis of the [diagonalMap],
The [SingletonArrow] is defined as
the [PowerObject_transpose] of the [KroneckerDelta]*)

Definition KroneckerDelta (B : C) : C⟦ B ⨉ B , Ω⟧.
Proof.
  use characteristic_morphism.
  + exact B.
  + use diagonalMap.
Defined.
Local Notation "'δ' B" := (KroneckerDelta B)(at level 8).

Definition SingletonArrow (B : C) : C⟦ B , (PowerObject_on_ob P) B⟧.
Proof.
  use PowerObject_transpose.
  use KroneckerDelta.
Defined.
Local Notation "'{⋅}' B" := (SingletonArrow B)(at level 8).

(*Proof that [SingletonArrow] is Monic and
  definition of his characteristic map [SingletonPred]*)

Local Definition auxpb {X B: C} (b: C⟦ X , B⟧) : Pullback (identity B ⨱ b) (diagonalMap BinProd B).
Proof.
  use make_Pullback.
  + exact X.
  + use BinProductArrow.
    - exact b.
    - exact (identity X).
  + exact b.
  + simpl.
    rewrite postcompWithBinProductArrow.
    use pathsinv0.
    use BinProductArrowUnique.
    - rewrite !assoc'.
      unfold diagonalMap'.
      now rewrite BinProductPr1Commutes.
    - rewrite !assoc'.
      unfold diagonalMap'.
      now rewrite BinProductPr2Commutes, id_left, id_right.
  + use make_isPullback.
    intros Y y1 y2 r.
    set (y11 := (y1 · (BinProductPr1 _ (BinProd B X)))).
    set (y12 := (y1 · (BinProductPr2 _ (BinProd B X)))).
    (* rewrite (BinProductArrowEta _ _ _ _ _ y1). *)
    assert (r1 := maponpaths (λ f, compose f (BinProductPr1 C (BinProd B B))) r).
    assert (r2 := maponpaths (λ f, compose f (BinProductPr2 C (BinProd B B))) r).
    simpl in r1, r2.
    unfold diagonalMap' in r1, r2.
    rewrite
      !assoc',
      BinProductOfArrowsPr1,
      BinProductPr1Commutes,
      !id_right
      in r1.
    rewrite
      !assoc',
      BinProductOfArrowsPr2,
      BinProductPr2Commutes,
      !id_right,
      assoc in r2.
    fold y11 in r1.
    fold y12 in r2.
    use make_iscontr.
    - split with y12.
      use (tpair _ _ r2).
      rewrite precompWithBinProductArrow.
      use pathsinv0.
      use BinProductArrowUnique.
      * now rewrite r2, <-r1.
      * now rewrite id_right.
    - intro t.
      induction t as (t,(tri1,tri2)).
      use subtypePath.
      * unfold isPredicate.
        intro.
        use isofhleveldirprod.
        ++ use homset_property. ++ use homset_property.
      * cbn.
        assert (Ts := maponpaths (λ f, compose f (BinProductPr2 C (BinProd B X))) tri1).
        simpl in Ts.
        rewrite assoc', BinProductPr2Commutes, id_right in Ts.
        exact Ts.
Defined.

Lemma SingletonArrow_isMonic (B: C) : isMonic ({⋅} B).
Proof.
  use make_isMonic.
  intros X b b' p.
  assert (q : (((identity B) ⨱ b) · (δ B) = ((identity B) ⨱ b') · (δ B))). {
    rewrite (PowerObject_transpose_tri P (δ B)).
    fold BinProd.
    rewrite !assoc, !BinProductOfArrows_idxcomp.
    use (maponpaths (( nat_z_iso_inv
    (PowerObject_nat_z_iso P)) (X,,B))).
    exact p.
  }
  (** Consider this diagram
    <<
                        b               !
                X   -------->   B   --------> T
                |               |             |
         b x id |    diagonalMap|             | true
                v               v             v
              B x X --------> B x B --------> Ω
                    id x b              δB
    >>
    We prove the left-hand square is a pullback
      (even when we substitue b with b') in [pbl] and [pbl'],
    the right-hand square is the definition of [KroneckerDelta]
      and it is a Pullback,
    so the whole rectangle is a pullback ([pb] [pb'])

    using [q] we note b x id and b' x id are [pullbackPr1]
    of the same diagram, thus they differ by an isomorphism [h]
  *)
  set (pbr := subobject_classifier_pullback Ω (diagonalMap BinProd B)).
  set (pbl := auxpb b).
  set (pbl' := auxpb b').
  set (pb := pullback_glue_pullback C pbr pbl).
  set (pb' := pullback_glue_pullback C pbr pbl').
  fold δ B in pb, pb'.
  transparent assert (pb'' : (Pullback ((identity B) ⨱ b' · δ B) Ω)). {
    use (Pullback_mor_paths q (idpath _)).
    exact pb.
  }
  induction (pullbackiso _ pb' pb'') as (h,(h_tri1,h_tri2)).
  cbn - [BinProd] in h, h_tri1.
  rewrite (precompWithBinProductArrow _ (BinProd B X)) in h_tri1.
  assert (h_tri11 := (maponpaths (λ f, compose f (BinProductPr1 C (BinProd B X))) h_tri1)).
  cbn beta in h_tri11.
  rewrite !BinProductPr1Commutes in h_tri11.
  assert (h_tri12 := (maponpaths (λ f, compose f (BinProductPr2 C (BinProd B X))) h_tri1)).
  cbn beta in h_tri12.
  rewrite !BinProductPr2Commutes, id_right in h_tri12.
  rewrite h_tri12, id_left in h_tri11.
  exact h_tri11.
Defined.

Definition SingletonArrow_Monic (B: C) := make_Monic C (SingletonArrow B) (SingletonArrow_isMonic B).

Definition SingletonPred (B: C) : C ⟦ PowerObject_on_ob P B , Ω ⟧.
Proof.
  use characteristic_morphism.
  { exact B. }
  use SingletonArrow_Monic.
Defined.
End KroneckerDelta.

(*In this section we show that an elementary topos has exponentials*)
Section Exponentials.

Local Notation "'δ' B" := (KroneckerDelta B)(at level 8).
Local Notation "'{⋅}' B" := (SingletonArrow B)(at level 8).

(*[v b c] in Sets would be, given an element x of b and a relation as a subset of c x b, the subset of c of all the element in relation with x*)
Let v (b c : C)
  : C ⟦ (b ⨉ (PowerObject_on_ob P (c ⨉ b))) , (PowerObject_on_ob P c) ⟧.
Proof.
  use (PowerObject_transpose).
  use (compose (BinProduct_assoc BinProd c b (PowerObject_on_ob P (c ⨉ b)))).
  use PowerObject_inPred.
Defined.

(*[u b c] in Sets would be, given a relation as a subset of c x b, the subset of b of all the element x such that (v b c) x is a Singleton*)
Let u (b c : C)
  : C ⟦ PowerObject_on_ob P (c ⨉ b) , (PowerObject_on_ob P b) ⟧.
Proof.
  use (PowerObject_transpose).
  use (compose (b:= (PowerObject_on_ob P c))).
  - use v.
  - use SingletonPred.
Defined.

Let name_true (b : C) : C ⟦ T, PowerObject_on_ob P b ⟧.
Proof.
  use (PowerObject_charname_nat_z_iso P).
  exact (TerminalArrow T b · true Ω).
Defined.

(*we are going to use [left_adjoint_from_partial], so, given (b c : C) we set up:
  Subobject_dom G0  (the object c^b : C)
  ev                (the evaluation morphism : C ⟦ b x c^b , c ⟧
  universality      (a proof which show e b c is universal)
*)

(*G0 is defined as the pullback of name_true through u*)
Let G0 (b c : C) : Subobjectscategory
  (PowerObject_on_ob P (c ⨉ b)).
Proof.
  use (PullbackSubobject PB).
  { exact (PowerObject_on_ob P b). }
  { use Subobjectscategory_ob.
    - exact T.
    - exact (name_true b).
    - use global_element_isMonic.
  }
  - use u.
Defined.

Local Lemma G0_Sqr (b c : C) : (Subobject_mor (G0 b c) · (u b c) = (TerminalArrow T _ ) · (name_true b)).
Proof.
  cbn.
  rewrite PullbackSqrCommutes.
  repeat use cancel_postcomposition.
  use TerminalArrowUnique.
Qed.

(** Consider this diagram
  <<
                                      ev
              ----------------------------------------------------
              |                                                  |
              |      id x G0                  v           {·}    v
            b x c^b --------> b x P(c x b) ------> Pc <--------- C
              |                 |                   |            |
       id x ! |          id x u |      SingletonPred|            |!
              v                 v                   v            v
            b x T   -------->   b x Pb -----------> Ω <--------- T
              |   id x name_true            inmap          true  ʌ
              |                                                  |
              ----------------------------------------------------
                                    !
  >>
  The left-hand square is b x (def of c^b),
  the middle square is the definition of v from u,
  the right-hand square is the definition of SingletonPred and it is a Pullback,
  the bottom distorted square is the definition of name_true.
  Every square commutes.
  We define [ev] as the [PullbackArrow] of the right-hand square
 *)

Local Definition ev_aux (b c: C) :
  (identity b) ⨱ (Subobject_mor (G0 b c)) · v b c · characteristic_morphism Ω (SingletonArrow_Monic c) =
  (identity b) ⨱ (TerminalArrow T (Subobject_dom (G0 b c))) · TerminalArrow T (BinProd b T) · Ω.
Proof.
  rewrite assoc'.
    assert (p :
      (identity b) ⨱ (u b c) · PowerObject_inPred P b =
      v b c · characteristic_morphism Ω (SingletonArrow_Monic c)).
    { use pathsinv0.
      use (PowerObject_transpose_tri P). }
    induction p.
    rewrite assoc, BinProductOfArrows_idxcomp.
    rewrite G0_Sqr.
    rewrite !assoc', <-BinProductOfArrows_idxcomp, !assoc'.
    use cancel_precomposition.
    unfold name_true.
    rewrite (PowerObject_charname_nat_z_iso_tri(b:=b) P).
    rewrite !assoc.
    use cancel_postcomposition.
    use TerminalArrowUnique.
Qed.

Let ev (b c: C) : C ⟦ b ⨉ (Subobject_dom (G0 b c)), c ⟧.
Proof.
  assert (p : PullbackObject (subobject_classifier_pullback Ω (SingletonArrow_Monic c)) = c).
  { apply idpath. }
  induction p.
  use PullbackArrow.
  - exact ((identity _) ⨱ (Subobject_mor (G0 b c)) · (v b c)).
  - exact ((identity b) ⨱ (TerminalArrow T (Subobject_dom (G0 b c)))·
      (TerminalArrow T _)).
  - apply ev_aux.
Defined.

Local Lemma ev_tri (b c : C) : ev b c · SingletonArrow_Monic c =
                                 (identity _) ⨱ ( Subobject_mor (G0 b c)) · (v b c).
Proof.
  use (PullbackArrow_PullbackPr1 (subobject_classifier_pullback Ω (SingletonArrow_Monic c))).
Qed.

(*UNIVERSALITY
  Given f : C ⟦ b x a , c ⟧ we need to show
  there is a unique g : C ⟦ a , c^b ⟧ such that f = (id x g)·ev

  we define such g as the [PullbackArrow] the following diagram
  <<
                          !
                c^b -------------> T
                 |                 |
              G0 |                 | name_true
         h       v                 v
      a --->P (c x b) ----------> Pb
                        u b c
  >>
  where h is the transpose of ((id c) x f)·(δ c)
    but as a morphism C ⟦ (c x b) x a , Ω ⟧
    (so we need to precompose [BinProduct_assoc])
*)
Let h {c b a : C} (f: C ⟦ b ⨉ a, c ⟧)
    := PowerObject_transpose P ((z_iso_inv (BinProduct_assoc BinProd c b a)) ·
                                  (identity c) ⨱ f · (δ c)).

Local Lemma h_sq {c b a : C} (f: C ⟦ b ⨉ a, c ⟧) :
  f · SingletonArrow_Monic c = (identity b) ⨱ (h f) · v b c.
Proof.
  use (invmaponpathsweq (hset_z_iso_equiv _ _ (nat_z_iso_pointwise_z_iso  (nat_z_iso_inv (PowerObject_nat_z_iso P)) (b ⨉ a,,c)))).
  simpl. fold BinProd.
  rewrite <-!BinProductOfArrows_idxcomp, !assoc'.
  intermediate_path ((identity c) ⨱ f · KroneckerDelta c).
  { use cancel_precomposition.
    apply pathsinv0.
    use PowerObject_transpose_tri. }
  use pathsinv0.
  intermediate_path (
    (identity c) ⨱ ((identity b) ⨱ (h f)) ·
    ((BinProduct_assoc BinProd c b (PowerObject_on_ob P c ⨉ b)) ·
    PowerObject_inPred P c ⨉ b)).
  { use cancel_precomposition.
    use pathsinv0.
    use (PowerObject_transpose_tri P). }
  rewrite assoc.
  rewrite BinProduct_OfArrows_assoc.
  use pathsinv0.
  rewrite !assoc'.
  use z_iso_inv_to_left.
  rewrite assoc.
  rewrite BinProductOfArrows_id.
  use PowerObject_transpose_tri.
Qed.

Local Lemma g_aux (c b a : C) (f: C ⟦ constprod_functor1 BinProd b a, c ⟧) : h f · u b c =
  TerminalArrow T a
  · Subobject_mor
      (Subobjectscategory_ob (name_true b)
         (global_element_isMonic T (PowerObject_on_ob P b) (name_true b))).
Proof.
  assert (p : name_true b = Subobject_mor
    (Subobjectscategory_ob (name_true b)
        (global_element_isMonic T (PowerObject_on_ob P b) (name_true b)))). { apply idpath. }
    induction p.
    use (invmaponpathsweq (hset_z_iso_equiv _ _ (nat_z_iso_pointwise_z_iso  (nat_z_iso_inv (PowerObject_nat_z_iso P)) (a,,b)))).
    simpl.
    fold BinProd.
    rewrite <-!BinProductOfArrows_idxcomp, !assoc'.
    intermediate_path ((identity b) ⨱ (h f) ·
    (v b c · SingletonPred c)).
    { use cancel_precomposition.
      use pathsinv0.
      use PowerObject_transpose_tri. }
    use pathsinv0.
    intermediate_path ((identity b) ⨱ (TerminalArrow T a)
    · (BinProductPr1 C (BinProd b T) · ((TerminalArrow T b · Ω)))).
    { use cancel_precomposition.
      use PowerObject_charname_nat_z_iso_tri. }
    intermediate_path (f · SingletonArrow_Monic c · SingletonPred c).
    {
      rewrite !assoc', subobject_classifier_square_commutes, !assoc.
      use cancel_postcomposition.
      use TerminalArrowEq. }
    rewrite !assoc.
    use cancel_postcomposition.
    use h_sq.
Qed.

Let g (c b a : C) (f: C ⟦ constprod_functor1 BinProd b a, c ⟧) : C ⟦ a, Subobject_dom (G0 b c) ⟧.
Proof.
  use PullbackArrow.
  + exact (h f).
  + use TerminalArrow.
  + apply g_aux.
Defined.

Local Lemma h_tri {c b a : C} (f: C ⟦ b ⨉ a, c ⟧): (g c b a f
· Subobject_mor (G0 b c) = h f).
Proof.
  use PullbackArrow_PullbackPr1.
Qed.

Local Lemma g_tri {c b a : C} (f: C ⟦ b ⨉ a, c ⟧) :
  f = (identity b) ⨱ (g c b a f) · ev b c.
Proof.
  use (MonicisMonic _ (SingletonArrow_Monic c)).
  now rewrite !assoc',
    ev_tri,
    !assoc,
    BinProductOfArrows_idxcomp,
    h_tri,
    h_sq.
Qed.

(* Opaque isBinProduct_Pullback. *)

Local Lemma universality (b c : C): is_universal_arrow_from (constprod_functor1 BinProd b) c (Subobject_dom (G0 b c)) (ev b c).
Proof.
  intros a f.
  use unique_exists.
  + exact (g c b a f).
  + use g_tri.
  + intro.
    use homset_property.
  + intros g' g_tri'.
    simpl in g_tri'.
    unfold BinProduct_of_functors_mor in g_tri'.
    simpl in g_tri'.
    use (MonicisMonic _ (Subobject_Monic (G0 b c))).
    use (invmaponpathsweq (hset_z_iso_equiv _ _ (nat_z_iso_pointwise_z_iso  (nat_z_iso_inv (PowerObject_nat_z_iso P)) (a,,c ⨉ b)))).
    unfold hset_z_iso_equiv.
    cbn - [BinProd G0 Subobject_mor isBinProduct_Pullback].
    fold BinProd.
    rewrite <-BinProductOfArrows_id.
    use (cancel_z_iso' (BinProduct_assoc BinProd _ _ _)).
    rewrite !assoc.
    intermediate_path (
      (identity c) ⨱ ((identity b) ⨱ (g' · Subobject_mor (G0 b c)))·
      BinProduct_assoc BinProd _ _ _ · PowerObject_inPred _ _).
    { use cancel_postcomposition.
      use pathsinv0.
      use (BinProduct_OfArrows_assoc BinProd). }
    use pathsinv0.
    intermediate_path (
      (identity c) ⨱ ((identity b) ⨱ ((g c b a f) · Subobject_mor (G0 b c)))·
      BinProduct_assoc BinProd _ _ _ · PowerObject_inPred _ _).
    { use cancel_postcomposition.
      use pathsinv0.
      use (BinProduct_OfArrows_assoc BinProd). }
    rewrite !assoc'.
    use (invmaponpathsweq (hset_z_iso_equiv _ _ (nat_z_iso_pointwise_z_iso  ( (PowerObject_nat_z_iso P)) (b⨉a,,c)))).
    unfold hset_z_iso_equiv.
    cbn - [BinProd G0 Subobject_mor BinProduct_assoc].
    unfold PowerObject_nt_data.
    rewrite !PowerObject_transpose_precomp.
    fold (v b c).
    rewrite <-!(BinProductOfArrows_idxcomp _ BinProd _ (Subobject_mor _)).
    rewrite !assoc'.
    rewrite <-!ev_tri.
    rewrite !assoc.
    use cancel_postcomposition.
    rewrite <-g_tri.
    use g_tri'.
Defined.

Definition Exponentials_from_Topos : Exponentials (BinProd).
Proof.
  intro b.
  use left_adjoint_from_partial.
  + intro c.
    exact (Subobject_dom (G0 b c)).
  + exact (ev b).
  + exact (universality b).
Defined.

End Exponentials.

End Topos.
