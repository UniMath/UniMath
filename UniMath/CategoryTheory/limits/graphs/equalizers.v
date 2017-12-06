(** * Equalizers defined in terms of limits *)
(** ** Contents
- Definition of equalizers
- Coincides with the direct definition
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.

(** * Definition of equalizers in terms of limits *)
Section def_equalizers.

  Variable C : precategory.
  Variable hs: has_homsets C.

  Open Scope stn.
  Definition One : two := ● 0.
  Definition Two : two := ● 1.
  Close Scope stn.

  Definition Equalizer_graph : graph.
  Proof.
    exists two.
    use (@two_rec (two -> UU)).
    - apply two_rec.
      + apply empty.
      + apply (unit ⨿ unit).
    - apply (λ _, empty).
  Defined.

  Definition Equalizer_diagram {a b : C} (f g : C⟦a, b⟧) : diagram Equalizer_graph C.
  Proof.
    exists (two_rec a b).
    use two_rec_dep.
    - use two_rec_dep; simpl.
      + apply fromempty.
      + intro x. induction x.
        exact f. exact g.
    - intro. apply fromempty.
  Defined.

  Definition Equalizer_cone {a b : C} (f g : C⟦a, b⟧) (d : C) (h : C⟦d, a⟧) (H : h · f = h · g) :
    cone (Equalizer_diagram f g) d.
  Proof.
    use mk_cone.
    - use two_rec_dep.
      + exact h.
      + exact (h · f).
    - use two_rec_dep; use two_rec_dep.
      + exact (Empty_set_rect _).
      + intro e. unfold idfun. induction e.
        * apply idpath.
        * apply (! H).
      + exact (Empty_set_rect _).
      + exact (Empty_set_rect _).
  Defined.

  Definition isEqualizer {a b : C} (f g : C⟦a, b⟧) (d : C) (h : C⟦d, a⟧) (H : h · f = h · g) :
    UU := isLimCone (Equalizer_diagram f g) d (Equalizer_cone f g d h H).

  Definition mk_isEqualizer {a b : C} (f g : C⟦a, b⟧) (d : C) (h : C⟦d, a⟧) (H : h · f = h · g) :
    (∏ e (h' : C⟦e, a⟧) (H' : h' · f = h' · g),
     iscontr (total2 (fun hk : C⟦e, d⟧ => hk · h = h'))) -> isEqualizer f g d h H.
  Proof.
    intros H' x cx.
    assert (H1 : coneOut cx One · f = coneOut cx One · g).
    {
      use (pathscomp0 (coneOutCommutes cx One Two (ii1 tt))).
      use (pathscomp0 _ (!(coneOutCommutes cx One Two (ii2 tt)))).
      apply idpath.
    }
    set (H2 := (H' x (coneOut cx One) H1)).
    use tpair.
    - use (tpair _ (pr1 (pr1 H2)) _).
      use two_rec_dep.
      + apply (pr2 (pr1 H2)).
      + use (pathscomp0 _ (coneOutCommutes cx One Two (ii1 tt))).
        change (coneOut (Equalizer_cone f g d h H) (● 1)%stn) with (h · f).
        rewrite assoc.
        apply cancel_postcomposition, (pr2 (pr1 H2)).
    - abstract (intro t; apply subtypeEquality;
                [ intros y; apply impred; intros t0; apply hs
                | induction t as [t p]; apply path_to_ctr, (p One)]).
  Defined.

  Definition Equalizer {a b : C} (f g : C⟦a, b⟧) := LimCone (Equalizer_diagram f g).

  Definition mk_Equalizer {a b : C} (f g : C⟦a, b⟧) (d : C) (h : C⟦d, a⟧)
             (H : h · f = h · g) (isEq : isEqualizer f g d h H) :
    Equalizer f g.
  Proof.
    use tpair.
    - use tpair.
      + exact d.
      + use Equalizer_cone.
        * exact h.
        * exact H.
    - exact isEq.
  Defined.

  Definition Equalizers : UU := ∏ (a b : C) (f g : C⟦a, b⟧), Equalizer f g.

  Definition hasEqualizers : UU := ∏ (a b : C) (f g : C⟦a, b⟧), ishinh (Equalizer f g).

  Definition EqualizerObject {a b : C} {f g : C⟦a, b⟧} : Equalizer f g -> C := λ H, lim H.

  Definition EqualizerArrow {a b : C} {f g : C⟦a, b⟧} (E : Equalizer f g) :
    C⟦lim E, a⟧ := limOut E One.

  Definition EqualizerArrowEq {a b : C} {f g : C⟦a, b⟧} (E : Equalizer f g) :
    EqualizerArrow E · f = EqualizerArrow E · g.
  Proof.
    use (pathscomp0 (limOutCommutes E One Two (ii1 tt))).
    use (pathscomp0 _ (!(limOutCommutes E One Two (ii2 tt)))).
    apply idpath.
  Qed.

  Definition EqualizerIn {a b : C} {f g : C⟦a, b⟧} (E : Equalizer f g) (e : C) (h : C⟦e, a⟧)
             (H : h · f = h · g) : C⟦e, lim E⟧.
  Proof.
    now use limArrow; use Equalizer_cone.
  Defined.

  Lemma EqualizerArrowComm {a b : C} {f g : C⟦a, b⟧} (E : Equalizer f g) (e : C) (h : C⟦e, a⟧)
        (H : h · f = h · g) : EqualizerIn E e h H · EqualizerArrow E = h.
  Proof.
    exact (limArrowCommutes E e _ One).
  Qed.

  Lemma EqualizerInUnique {a b : C} {f g : C⟦a, b⟧} (E : Equalizer f g) (e : C) (h : C⟦e, a⟧)
        (H : h · f = h · g) (w : C⟦e, lim E⟧) (H' : w · EqualizerArrow E = h) :
    w = EqualizerIn E e h H.
  Proof.
    apply path_to_ctr.
    use two_rec_dep.
    - apply H'.
    - set (X := limOutCommutes E One Two (ii1 tt)).
      apply (maponpaths (λ h : _, w · h)) in X.
      use (pathscomp0 (!X)); rewrite assoc.
      change (dmor _ _) with f.
      change (coneOut _ _) with (h · f).
      apply cancel_postcomposition, H'.
  Qed.

  Definition isEqualizer_Equalizer {a b : C} {f g : C⟦a, b⟧} (E : Equalizer f g) :
    isEqualizer f g (EqualizerObject E) (EqualizerArrow E) (EqualizerArrowEq E).
  Proof.
    apply mk_isEqualizer.
    intros e h H.
    use (unique_exists (EqualizerIn E e h H)).
    (* Commutativity *)
    - exact (EqualizerArrowComm E e h H).
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y t. cbn in t.
      use EqualizerInUnique.
      exact t.
  Qed.

  (** ** Equalizers to equalizers *)

  Definition identity_is_Equalizer_input {a b : C} {f g : C⟦a, b⟧} (E : Equalizer f g) :
    total2 (fun hk : C⟦lim E, lim E⟧ => hk · EqualizerArrow E = EqualizerArrow E).
  Proof.
    use tpair.
    exact (identity _).
    apply id_left.
  Defined.

  Lemma EqualizerEndo_is_identity  {a b : C} {f g : C⟦a, b⟧} (E : Equalizer f g)
        (k : C⟦lim E, lim E⟧) (kH : k · EqualizerArrow E = EqualizerArrow E) :
    identity (lim E) = k.
  Proof.
    apply lim_endo_is_identity.
    unfold limOut.
    use two_rec_dep; cbn.
    + apply kH.
    + set (X := (coneOutCommutes (limCone E) One Two (ii1 tt))).
      use (pathscomp0 (! (maponpaths (λ h' : _, k · h') X))).
      use (pathscomp0 _ X).
      rewrite assoc; change (dmor _ _) with f.
      apply cancel_postcomposition, kH.
  Qed.

  Definition from_Equalizer_to_Equalizer {a b : C} {f g : C⟦a, b⟧} (E1 E2 : Equalizer f g) :
    C⟦lim E1, lim E2⟧.
  Proof.
    apply (EqualizerIn E2 (lim E1) (EqualizerArrow E1)).
    exact (EqualizerArrowEq E1).
  Defined.

  Lemma are_inverses_from_Equalizer_to_Equalizer {a b : C} {f g : C⟦a, b⟧} (E1 E2 : Equalizer f g) :
    is_inverse_in_precat (from_Equalizer_to_Equalizer E2 E1)
                         (from_Equalizer_to_Equalizer E1 E2).
  Proof.
    split; apply pathsinv0.
    - apply EqualizerEndo_is_identity.
      rewrite <- assoc.
      unfold from_Equalizer_to_Equalizer.
      repeat rewrite EqualizerArrowComm.
      apply idpath.
    - apply EqualizerEndo_is_identity.
      rewrite <- assoc.
      unfold from_Equalizer_to_Equalizer.
      repeat rewrite EqualizerArrowComm.
      apply idpath.
  Qed.

  Lemma isiso_from_Equalizer_to_Equalizer {a b : C} {f g : C⟦a, b⟧} (E1 E2 : Equalizer f g) :
    is_iso (from_Equalizer_to_Equalizer E1 E2).
  Proof.
    apply (is_iso_qinv _ (from_Equalizer_to_Equalizer E2 E1)).
    apply are_inverses_from_Equalizer_to_Equalizer.
  Qed.

  Definition iso_from_Equalizer_to_Equalizer {a b : C} {f g : C⟦a, b⟧} (E1 E2 : Equalizer f g) :
    iso (lim E1) (lim E2) := tpair _ _ (isiso_from_Equalizer_to_Equalizer E1 E2).

  Lemma inv_from_iso_iso_from_Pullback {a b : C} {f g : C⟦a , b⟧} (E1 E2 : Equalizer f g):
    inv_from_iso (iso_from_Equalizer_to_Equalizer E1 E2) = from_Equalizer_to_Equalizer E2 E1.
  Proof.
    apply pathsinv0.
    apply inv_iso_unique'.
    apply (pr1 (are_inverses_from_Equalizer_to_Equalizer E2 E1)).
  Qed.


  (** ** Connections to other limits *)

  Lemma Equalizers_from_Lims :
    Lims C -> Equalizers.
  Proof.
    intros H a b f g. apply H.
  Defined.

End def_equalizers.


(** * Definitions coincide
  In this section we show that the definition of equalizer as a limit
  coincides with the direct definition. *)
Section equalizers_coincide.

  Variable C : precategory.
  Variable hs: has_homsets C.


  (** ** isEqualizers *)

  Lemma equiv_isEqualizer1 {a b : C} {f g : C⟦a, b⟧} (e : C) (h : C⟦e, a⟧) (H : h · f = h · g) :
    limits.equalizers.isEqualizer f g h H -> isEqualizer C f g e h H.
  Proof.
    intros X.
    set (E := limits.equalizers.mk_Equalizer f g h H X).
    use (mk_isEqualizer C hs).
    intros e' h' H'.
    use (unique_exists (limits.equalizers.EqualizerIn E e' h' H')).
    (* Commutativity *)
    - exact (limits.equalizers.EqualizerCommutes E e' h' H').
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T.
      use (limits.equalizers.EqualizerInsEq E).
      use (pathscomp0 T).
      exact (!(limits.equalizers.EqualizerCommutes E e' h' H')).
  Qed.

  Lemma equiv_isEqualizer2 {a b : C} (f g : C⟦a, b⟧) (e : C) (h : C⟦e, a⟧) (H : h · f = h · g) :
    limits.equalizers.isEqualizer f g h H <- isEqualizer C f g e h H.
  Proof.
    intros X.
    set (E := mk_Equalizer C f g e h H X).
    intros e' h' H'.
    use (unique_exists (EqualizerIn C E e' h' H')).
    (* Commutativity *)
    - exact (EqualizerArrowComm C E e' h' H').
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T.
      use (EqualizerInUnique C E).
      exact T.
  Qed.


  (** ** Equalizers *)

  Definition equiv_Equalizer1 {a b : C} (f g : C⟦a, b⟧) :
    limits.equalizers.Equalizer f g -> Equalizer C f g.
  Proof.
    intros E.
    exact (mk_Equalizer
             C f g _ _ _
             (equiv_isEqualizer1
                (limits.equalizers.EqualizerObject E)
                (limits.equalizers.EqualizerArrow E)
                (limits.equalizers.EqualizerEqAr E)
                (limits.equalizers.isEqualizer_Equalizer E))).
  Defined.

  Definition equiv_Equalizers1 : @limits.equalizers.Equalizers C -> Equalizers C.
  Proof.
    intros E' a b f g.
    set (E := E' a b f g).
    exact (mk_Equalizer
             C f g _ _ _
             (equiv_isEqualizer1
                (limits.equalizers.EqualizerObject E)
                (limits.equalizers.EqualizerArrow E)
                (limits.equalizers.EqualizerEqAr E)
                (limits.equalizers.isEqualizer_Equalizer E))).
  Defined.

  Definition equiv_Equalizer2 {a b : C} (f g : C⟦a, b⟧) :
    limits.equalizers.Equalizer f g <- Equalizer C f g.
  Proof.
    intros E.
    exact (@limits.equalizers.mk_Equalizer
             C (EqualizerObject C E) a b f g
             (EqualizerArrow C E)
             (EqualizerArrowEq C E)
             (@equiv_isEqualizer2
                a b f g (EqualizerObject C E)
                (EqualizerArrow C E)
                (EqualizerArrowEq C E)
                (isEqualizer_Equalizer C hs E))).
  Defined.

  Definition equiv_Equalizers2 : @limits.equalizers.Equalizers C <- Equalizers C.
  Proof.
    intros E' a b f g.
    set (E := E' a b f g).
    exact (@limits.equalizers.mk_Equalizer
             C (EqualizerObject C E) a b f g
             (EqualizerArrow C E)
             (EqualizerArrowEq C E)
             (@equiv_isEqualizer2
                a b f g (EqualizerObject C E)
                (EqualizerArrow C E)
                (EqualizerArrowEq C E)
                (isEqualizer_Equalizer C hs E))).
  Defined.

End equalizers_coincide.
