(** * Coequalizers defined in terms of colimits *)
(** ** Contents
- Definition of coequalizers
- Coincides with the direct definition
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Local Open Scope cat.

(** * Definition of coequalizers in terms of colimits *)
Section def_coequalizers.

  Variable C : precategory.
  Variable hs: has_homsets C.

  Local Open Scope stn.
  Definition One : two := ● 0.
  Definition Two : two := ● 1.

  Definition Coequalizer_graph : graph.
  Proof.
    exists two.
    use (@two_rec (two -> UU)).
    - apply two_rec.
      + apply empty.
      + apply (unit ⨿ unit).
    - apply (λ _, empty).
  Defined.

  Definition Coequalizer_diagram {a b : C} (f g : C⟦a, b⟧) : diagram Coequalizer_graph C.
  Proof.
    exists (two_rec a b).
    use two_rec_dep.
    - use two_rec_dep; simpl.
      + apply fromempty.
      + intro x. induction x.
        exact f. exact g.
    - intro. apply fromempty.
  Defined.

  Definition Coequalizer_cocone {a b : C} (f g : C⟦a, b⟧) (d : C) (h : C⟦b, d⟧)
             (H : f · h = g · h) : cocone (Coequalizer_diagram f g) d.
  Proof.
    use mk_cocone.
    - use two_rec_dep.
      + exact (f · h).
      + exact h.
    - use two_rec_dep; use two_rec_dep.
      + exact (Empty_set_rect _).
      + intro e. induction e.
        * apply idpath.
        * apply (! H).
      + exact (Empty_set_rect _).
      + exact (Empty_set_rect _).
  Defined.

  Definition isCoequalizer {a b : C} (f g : C⟦a, b⟧) (d : C) (h : C⟦b, d⟧)
             (H : f · h = g · h) : UU := isColimCocone (Coequalizer_diagram f g) d
                                                         (Coequalizer_cocone f g d h H).

  Definition mk_isCoequalizer {a b : C} (f g : C⟦a, b⟧) (d : C) (h : C⟦b, d⟧)
             (H : f · h = g · h) :
    (∏ e (h' : C⟦b, e⟧) (H' : f · h' = g · h'),
     iscontr (total2 (fun hk : C⟦d, e⟧ => h · hk = h'))) ->
    isCoequalizer f g d h H.
  Proof.
    intros H' x cx.
    assert (H1 : f · coconeIn cx Two = g · coconeIn cx Two).
    {
      use (pathscomp0 (coconeInCommutes cx One Two (ii1 tt))).
      use (pathscomp0 _ (!(coconeInCommutes cx One Two (ii2 tt)))).
      apply idpath.
    }
    set (H2 := (H' x (coconeIn cx Two) H1)).
    use tpair.
    - use (tpair _ (pr1 (pr1 H2)) _).
      use two_rec_dep.
      + use (pathscomp0 _ (coconeInCommutes cx One Two (ii1 tt))).
        change (coconeIn (Coequalizer_cocone f g d h H) _) with (f · h).
        change (dmor _ _) with f.
        rewrite <- assoc.
        apply cancel_precomposition, (pr2 (pr1 H2)).
      + apply (pr2 (pr1 H2)).
    - abstract (intro t; apply subtypeEquality;
               [intros y; apply impred; intros t0; apply hs
               |induction t as [t p]; apply path_to_ctr, (p Two)]).
  Defined.

  Definition Coequalizer {a b : C} (f g : C⟦a, b⟧) : UU := ColimCocone (Coequalizer_diagram f g).

  Definition mk_Coequalizer {a b : C} (f g : C⟦a, b⟧) (d : C) (h : C⟦b, d⟧) (H : f · h = g · h)
             (isCEq : isCoequalizer f g d h H) : Coequalizer f g.
  Proof.
    use tpair.
    - use tpair.
      + exact d.
      + use Coequalizer_cocone.
        * exact h.
        * exact H.
    - exact isCEq.
  Defined.

  Definition Coequalizers : UU := ∏ (a b : C) (f g : C⟦a, b⟧), Coequalizer f g.

  Definition hasCoequalizers : UU := ∏ (a b : C) (f g : C⟦a, b⟧), ishinh (Coequalizer f g).

  Definition CoequalizerObject {a b : C} {f g : C⟦a, b⟧} :
    Coequalizer f g -> C := λ H, colim H.

  Definition CoequalizerArrow {a b : C} {f g : C⟦a, b⟧} (E : Coequalizer f g) :
    C⟦b, colim E⟧ := colimIn E Two.

  Definition CoequalizerArrowEq {a b : C} {f g : C⟦a, b⟧} (E : Coequalizer f g) :
    f · CoequalizerArrow E = g · CoequalizerArrow E.
  Proof.
    use (pathscomp0 (colimInCommutes E One Two (ii1 tt))).
    use (pathscomp0 _ (!(colimInCommutes E One Two (ii2 tt)))).
    apply idpath.
  Qed.

  Definition CoequalizerOut {a b : C} {f g : C⟦a, b⟧} (E : Coequalizer f g) e (h : C⟦b, e⟧)
             (H : f · h = g · h) : C⟦colim E, e⟧.
  Proof.
    now use colimArrow; use Coequalizer_cocone.
  Defined.

  Lemma CoequalizerArrowComm {a b : C} {f g : C⟦a, b⟧} (E : Coequalizer f g) (e : C) (h : C⟦b, e⟧)
        (H : f · h = g · h) : CoequalizerArrow E · CoequalizerOut E e h H = h.
  Proof.
    exact (colimArrowCommutes E e _ Two).
  Qed.

  Lemma CoequalizerOutUnique {a b : C} {f g : C⟦a, b⟧} (E : Coequalizer f g) (e : C) (h : C⟦b, e⟧)
        (H : f · h = g · h) (w : C⟦colim E, e⟧) (H' : CoequalizerArrow E · w = h) :
    w = CoequalizerOut E e h H.
  Proof.
    apply path_to_ctr.
    use two_rec_dep.
    - set (X := colimInCommutes E One Two (ii1 tt)).
      apply (maponpaths (λ h : _, h · w)) in X.
      use (pathscomp0 (!X)); rewrite <- assoc.
      change (dmor _ _) with f.
      change (coconeIn _ _) with (f · h).
      apply cancel_precomposition, H'.
    - apply H'.
  Qed.

  Definition isCoequalizer_Coequalizer {a b : C} {f g : C⟦a, b⟧} (E : Coequalizer f g) :
    isCoequalizer f g (CoequalizerObject E) (CoequalizerArrow E)
                  (CoequalizerArrowEq E).
  Proof.
    apply mk_isCoequalizer.
    intros e h H.
    use (unique_exists (CoequalizerOut E e h H)).
    (* Commutativity *)
    - exact (CoequalizerArrowComm E e h H).
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y t. cbn in t.
      use CoequalizerOutUnique.
      exact t.
  Qed.

  (** ** Coequalizers to coequalizers *)

  Definition identity_is_Coequalizer_input {a b : C} {f g : C⟦a, b⟧} (E : Coequalizer f g) :
    total2 (fun hk : C⟦colim E, colim E⟧ => CoequalizerArrow E · hk = CoequalizerArrow E).
  Proof.
    use tpair.
    exact (identity _).
    apply id_right.
  Defined.

  Lemma CoequalizerEndo_is_identity  {a b : C} {f g : C⟦a, b⟧} (E : Coequalizer f g)
        (k : C⟦colim E, colim E⟧) (kH :CoequalizerArrow E · k = CoequalizerArrow E) :
    identity (colim E) = k.
  Proof.
    apply colim_endo_is_identity.
    unfold colimIn.
    use two_rec_dep; cbn.
    + set (X := (coconeInCommutes (colimCocone E) One Two (ii1 tt))).
      use (pathscomp0 (! (maponpaths (λ h' : _, h' · k) X))).
      use (pathscomp0 _ X).
      rewrite <- assoc. apply cancel_precomposition.
      apply kH.
    + apply kH.
  Qed.

  Definition from_Coequalizer_to_Coequalizer {a b : C} {f g : C⟦a, b⟧} (E1 E2 : Coequalizer f g) :
    C⟦colim E1, colim E2⟧.
  Proof.
    apply (CoequalizerOut E1 (colim E2) (CoequalizerArrow E2)).
    exact (CoequalizerArrowEq E2).
  Defined.

  Lemma are_inverses_from_Coequalizer_to_Coequalizer {a b : C} {f g : C⟦a, b⟧}
        (E1 E2 : Coequalizer f g) :
    is_inverse_in_precat (from_Coequalizer_to_Coequalizer E2 E1)
                         (from_Coequalizer_to_Coequalizer E1 E2).
  Proof.
    split; apply pathsinv0.
    - apply CoequalizerEndo_is_identity.
      rewrite assoc.
      unfold from_Coequalizer_to_Coequalizer.
      repeat rewrite CoequalizerArrowComm.
      apply idpath.
    - apply CoequalizerEndo_is_identity.
      rewrite assoc.
      unfold from_Coequalizer_to_Coequalizer.
      repeat rewrite CoequalizerArrowComm.
      apply idpath.
  Qed.

  Lemma isiso_from_Coequalizer_to_Coequalizer {a b : C} {f g : C⟦a, b⟧} (E1 E2 : Coequalizer f g) :
    is_iso (from_Coequalizer_to_Coequalizer E1 E2).
  Proof.
    apply (is_iso_qinv _ (from_Coequalizer_to_Coequalizer E2 E1)).
    apply are_inverses_from_Coequalizer_to_Coequalizer.
  Qed.

  Definition iso_from_Coequalizer_to_Coequalizer {a b : C} {f g : C⟦a, b⟧}
             (E1 E2 : Coequalizer f g) : iso (colim E1) (colim E2) :=
    tpair _ _ (isiso_from_Coequalizer_to_Coequalizer E1 E2).

  Lemma inv_from_iso_iso_from_Pullback {a b : C} {f g : C⟦a , b⟧} (E1 E2 : Coequalizer f g):
    inv_from_iso (iso_from_Coequalizer_to_Coequalizer E1 E2) =
    from_Coequalizer_to_Coequalizer E2 E1.
  Proof.
    apply pathsinv0.
    apply inv_iso_unique'.
    apply (pr1 (are_inverses_from_Coequalizer_to_Coequalizer E2 E1)).
  Qed.


  (** ** Connections to other colimits *)

  Lemma Coequalizers_from_Colims : Colims C -> Coequalizers.
  Proof.
    intros H a b f g. apply H.
  Defined.

End def_coequalizers.


(** * Definitions coincide
    In this section we show that the definition of coequalizer as a colimit coincides with the
    direct definition. *)
Section coequalizers_coincide.

  Variable C : precategory.
  Variable hs: has_homsets C.


  (** ** isCoequalizers *)

  Lemma equiv_isCoequalizer1 {a b : C} {f g : C⟦a, b⟧} (e : C) (h : C⟦b, e⟧) (H : f · h = g · h) :
    limits.coequalizers.isCoequalizer f g h H -> isCoequalizer C f g e h H.
  Proof.
    intros X.
    set (E := limits.coequalizers.mk_Coequalizer f g h H X).
    use (mk_isCoequalizer C hs).
    intros e' h' H'.
    use (unique_exists (limits.coequalizers.CoequalizerOut E e' h' H')).
    (* Commutativity *)
    - exact (limits.coequalizers.CoequalizerCommutes E e' h' H').
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T.
      use (limits.coequalizers.CoequalizerOutsEq E).
      use (pathscomp0 T).
      exact (!(limits.coequalizers.CoequalizerCommutes E e' h' H')).
  Qed.

  Lemma equiv_isCoequalizer2 {a b : C} (f g : C⟦a, b⟧) (e : C) (h : C⟦b, e⟧) (H : f · h = g · h) :
    limits.coequalizers.isCoequalizer f g h H <- isCoequalizer C f g e h H.
  Proof.
    intros X.
    set (E := mk_Coequalizer C f g e h H X).
    intros e' h' H'.
    use (unique_exists (CoequalizerOut C E e' h' H')).
    (* Commutativity *)
    - exact (CoequalizerArrowComm C E e' h' H').
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T.
      use (CoequalizerOutUnique C E).
      exact T.
  Qed.

  (** ** Coequalizers *)

  Definition equiv_Coequalizer1 {a b : C} (f g : C⟦a, b⟧) :
    limits.coequalizers.Coequalizer f g -> Coequalizer C f g.
  Proof.
    intros E.
    exact (mk_Coequalizer
             C f g _ _ _
             (equiv_isCoequalizer1
                (limits.coequalizers.CoequalizerObject E)
                (limits.coequalizers.CoequalizerArrow E)
                (limits.coequalizers.CoequalizerEqAr E)
                (limits.coequalizers.isCoequalizer_Coequalizer E))).
  Defined.

  Definition equiv_Coequalizer2 {a b : C} (f g : C⟦a, b⟧) :
    limits.coequalizers.Coequalizer f g <- Coequalizer C f g.
  Proof.
    intros E.
    exact (@limits.coequalizers.mk_Coequalizer
             C a b (CoequalizerObject C E) f g
             (CoequalizerArrow C E)
             (CoequalizerArrowEq C E)
             (@equiv_isCoequalizer2
                a b f g (CoequalizerObject C E)
                (CoequalizerArrow C E)
                (CoequalizerArrowEq C E)
                (isCoequalizer_Coequalizer C hs E))).
  Defined.

End coequalizers_coincide.
