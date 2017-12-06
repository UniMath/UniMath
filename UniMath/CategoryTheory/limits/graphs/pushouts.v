(** * Pushouts defined in terms of colimits *)
(** ** Contents
- Definition of pushouts
- Coincides with the direct definition
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.pushouts.

Local Open Scope cat.

(** * Definition of pushouts in terms of colimits *)
Section def_po.

  Variable C : precategory.
  Variable hs: has_homsets C.

  Local Open Scope stn.
  Definition One : three := ● 0.
  Definition Two : three := ● 1.
  Definition Three : three := ● 2.

  Definition pushout_graph : graph.
  Proof.
    exists three.
    use three_rec.
    - apply three_rec.
      + apply empty.
      + apply unit.
      + apply unit.
    - apply (λ _, empty).
    - apply three_rec.
      + apply empty.
      + apply empty.
      + apply empty.
  Defined.

  Definition pushout_diagram {a b c : C} (f : C ⟦a, b⟧) (g : C⟦a, c⟧) :
    diagram pushout_graph C.
  Proof.
    exists (three_rec a b c).
    use three_rec_dep; cbn.
    - use three_rec_dep; cbn.
      + apply fromempty.
      + intros _; exact f.
      + intros _; exact g.
    - intros x; apply fromempty.
    - use three_rec_dep; cbn; apply fromempty.
  Defined.

  Definition PushoutCocone {a b c : C} (f : C ⟦a, b⟧) (g : C⟦a, c⟧) (d : C)
             (f' : C ⟦b, d⟧) (g' : C ⟦c, d⟧) (H : f · f' = g · g') :
    cocone (pushout_diagram f g) d.
  Proof.
    use mk_cocone.
    - use three_rec_dep; try assumption.
      apply (f · f').
    - use three_rec_dep; use three_rec_dep.
      + exact (Empty_set_rect _).
      + intros x; apply idpath.
      + intros x; apply (! H).
      + exact (Empty_set_rect _).
      + exact (Empty_set_rect _).
      + exact (Empty_set_rect _).
      + exact (Empty_set_rect _).
      + exact (Empty_set_rect _).
      + exact (Empty_set_rect _).
  Defined.

  Definition isPushout {a b c d : C} (f : C ⟦a, b⟧) (g : C ⟦a, c⟧)
             (i1 : C⟦b, d⟧) (i2 : C⟦c, d⟧) (H : f · i1 = g · i2) : UU :=
    isColimCocone (pushout_diagram f g) d (PushoutCocone f g d i1 i2 H).

  Definition mk_isPushout {a b c d : C} (f : C ⟦a, b⟧) (g : C ⟦a, c⟧)
             (i1 : C⟦b, d⟧) (i2 : C⟦c, d⟧) (H : f · i1 = g · i2) :
    (∏ e (h : C ⟦b, e⟧) (k : C⟦c, e⟧)(Hk : f · h = g · k ),
     iscontr (total2 (fun hk : C⟦d, e⟧ => dirprod (i1 · hk = h)(i2 · hk = k)))) →
    isPushout f g i1 i2 H.
  Proof.
    intros H' x cx; simpl in *.
    set (H1 := H' x (coconeIn cx Two) (coconeIn cx Three)).
    use (let p : f · coconeIn cx Two = g · coconeIn cx Three
                       := _ in _ ).
    { eapply pathscomp0; [apply (coconeInCommutes cx One Two tt)|].
      apply pathsinv0, (coconeInCommutes cx One Three tt). }
    set (H2 := H1 p).
    use tpair.
    + exists (pr1 (pr1 H2)).
      use three_rec_dep.
      * abstract (use (pathscomp0 _ (coconeInCommutes cx One Two tt));
        change (three_rec_dep _ _ _ _ _) with (f · i1);
        change (dmor _ _) with f; rewrite <- assoc;
        apply cancel_precomposition, (pr1 (pr2 (pr1 H2)))).
      * abstract ( apply (pr1 (pr2 (pr1 H2)))).
      * abstract (now use (pathscomp0 _ (pr2 (pr2 (pr1 H2))))).
    + abstract (intro t; apply subtypeEquality;
               [ intro; apply impred; intro; apply hs
               | destruct t as [t p0];
                 apply path_to_ctr; split; [ apply (p0 Two) | apply (p0 Three) ]]).
  Defined.

  Definition Pushout {a b c : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧) : UU :=
    ColimCocone (pushout_diagram f g).

  Definition mk_Pushout {a b c : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧) (d : C)
             (i1 : C⟦b,d⟧) (i2 : C ⟦c,d⟧) (H : f · i1 = g · i2)
             (ispo : isPushout f g i1 i2 H) : Pushout f g.
  Proof.
    use tpair.
    - exists d.
      use PushoutCocone; assumption.
    - apply ispo.
  Defined.

  Definition Pushouts : UU := ∏ (a b c : C) (f : C⟦a, b⟧)(g : C⟦a, c⟧), Pushout f g.

  Definition hasPushouts : UU := ∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦a, c⟧), ishinh (Pushout f g).

  Definition PushoutObject {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧}:
    Pushout f g -> C := λ H, colim H.
  (* Coercion PushoutObject : Pushout >-> ob. *)

  Definition PushoutIn1 {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧} (Po : Pushout f g) :
    C⟦b, colim Po⟧ := colimIn Po Two.

  Definition PushoutIn2 {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧} (Po : Pushout f g) :
    C⟦c, colim Po⟧ := colimIn Po Three.

  Definition PushoutSqrCommutes {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧} (Po : Pushout f g) :
    f · PushoutIn1 Po = g · PushoutIn2 Po.
  Proof.
    eapply pathscomp0; [apply (colimInCommutes Po One Two tt) |].
    apply (!colimInCommutes Po One Three tt).
  Qed.

  Definition PushoutArrow {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧} (Po : Pushout f g) (e : C)
             (h : C⟦b, e⟧) (k : C⟦c, e⟧) (H : f · h = g · k) : C⟦colim Po, e⟧.
  Proof.
    now use colimArrow; use PushoutCocone.
  Defined.

  Lemma PushoutArrow_PushoutIn1 {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧}  (Po : Pushout f g)
        (e : C) (h : C⟦b , e⟧) (k : C⟦c, e⟧) (H : f · h = g · k) :
    PushoutIn1 Po · PushoutArrow Po e h k H = h.
  Proof.
    exact (colimArrowCommutes Po e _ Two).
  Qed.

  Lemma PushoutArrow_PushoutIn2 {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧} (Po : Pushout f g)
        (e : C) (h : C⟦b, e⟧) (k : C⟦c, e⟧) (H : f · h = g · k) :
    PushoutIn2 Po · PushoutArrow Po e h k H = k.
  Proof.
    exact (colimArrowCommutes Po e _ Three).
  Qed.

  Lemma PushoutArrowUnique {a b c d : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧) (Po : Pushout f g) (e : C)
        (h : C⟦b, e⟧) (k : C⟦c, e⟧) (Hcomm : f · h = g · k) (w : C⟦PushoutObject Po, e⟧)
        (H1 : PushoutIn1 Po · w = h) (H2 : PushoutIn2 Po · w = k) :
    w = PushoutArrow Po _ h k Hcomm.
  Proof.
    apply path_to_ctr.
    use three_rec_dep; try assumption.
    set (X := colimInCommutes Po One Two tt).
    use (pathscomp0 (! (maponpaths (λ h' : _, h' · w) X))).
    now rewrite <- assoc; simpl; rewrite <- H1.
  Qed.

  Definition isPushout_Pushout {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧} (P : Pushout f g) :
    isPushout f g (PushoutIn1 P) (PushoutIn2 P) (PushoutSqrCommutes P).
  Proof.
    apply mk_isPushout.
    intros e h k HK.
    use tpair.
    - use tpair.
      + apply (PushoutArrow P _ h k HK).
      + split.
        * apply PushoutArrow_PushoutIn1.
        * apply PushoutArrow_PushoutIn2.
    - intro t.
      apply subtypeEquality.
      + intro. apply isapropdirprod; apply hs.
      + destruct t as [t p]. simpl.
        use (PushoutArrowUnique _ _ P).
        * apply e.
        * apply (pr1 p).
        * apply (pr2 p).
  Qed.


  (** ** Pushouts to Pushouts *)

  Definition identity_is_Pushout_input {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧} (Po : Pushout f g) :
    total2 (fun hk : C⟦colim Po, colim Po⟧ => dirprod (PushoutIn1 Po · hk = PushoutIn1 Po)
                                                   (PushoutIn2 Po · hk = PushoutIn2 Po)).
  Proof.
    exists (identity (colim Po)).
    apply dirprodpair; apply id_right.
  Defined.

  (* was PushoutArrowUnique *)
  Lemma PushoutArrowUnique' {a b c d : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧) (i1 : C⟦b, d⟧) (i2 : C⟦c, d⟧)
        (H : f · i1 = g · i2) (P : isPushout f g i1 i2 H) e (h : C⟦b, e⟧) (k : C⟦c, e⟧)
        (Hcomm : f · h = g · k) (w : C⟦d, e⟧) (H1 : i1 · w = h) (H2 : i2 · w = k) :
    w =  (pr1 (pr1 (P e (PushoutCocone f g _ h k Hcomm)))).
  Proof.
    apply path_to_ctr.
    use three_rec_dep; try assumption; simpl.
    change (three_rec_dep (λ n, C⟦three_rec a b c n, d⟧) _ _ _ _) with (f · i1).
    change (three_rec_dep (λ n, C⟦three_rec a b c n, e⟧) _ _ _ _) with (f · h).
    now rewrite <- assoc, H1.
  Qed.

  Lemma PushoutEndo_is_identity {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧} (Po : Pushout f g)
        (k : C⟦colim Po , colim Po⟧)
        (kH1 : PushoutIn1 Po · k = PushoutIn1 Po) (kH2 : PushoutIn2 Po · k = PushoutIn2 Po) :
    identity (colim Po) = k.
  Proof.
    apply colim_endo_is_identity.
    use three_rec_dep; cbn.
    - unfold colimIn.
      set (T := (coconeInCommutes (colimCocone Po) One Three tt)).
      use (pathscomp0 (! (maponpaths (λ h' : _, h' · k) T))).
      use (pathscomp0 _ (coconeInCommutes (colimCocone Po) One Three tt)).
      rewrite <- assoc. apply cancel_precomposition.
      apply kH2.
    - apply kH1.
    - apply kH2.
  Qed.

  Definition from_Pushout_to_Pushout {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧}
             (Po Po': Pushout f g) : C⟦colim Po , colim Po'⟧.
  Proof.
    apply (PushoutArrow Po (colim Po') (PushoutIn1 _ ) (PushoutIn2 _)).
    exact (PushoutSqrCommutes _ ).
  Defined.

  Lemma are_inverses_from_Pushout_to_Pushout {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧}
        (Po Po': Pushout f g) :
    is_inverse_in_precat (from_Pushout_to_Pushout Po Po') (from_Pushout_to_Pushout Po' Po).
  Proof.
    split; apply pathsinv0;
      apply PushoutEndo_is_identity;
      rewrite assoc;
      unfold from_Pushout_to_Pushout;
      repeat rewrite PushoutArrow_PushoutIn1;
      repeat rewrite PushoutArrow_PushoutIn2;
      auto.
  Qed.

  Lemma isiso_from_Pushout_to_Pushout {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧}
        (Po Po': Pushout f g) : is_iso (from_Pushout_to_Pushout Po Po').
  Proof.
    apply (is_iso_qinv _ (from_Pushout_to_Pushout Po' Po)).
    apply are_inverses_from_Pushout_to_Pushout.
  Defined.

  Definition iso_from_Pushout_to_Pushout {a b c : C} {f : C⟦a, b⟧} {g : C⟦a, c⟧}
             (Po Po': Pushout f g) : iso (colim Po) (colim Po') :=
    tpair _ _ (isiso_from_Pushout_to_Pushout Po Po').


  (** pushout lemma *)

  Section pushout_lemma.

    Variables a b c d e x : C.
    Variables (f : C⟦a, b⟧) (g : C⟦a, c⟧) (h : C⟦b, e⟧) (k : C⟦c, e⟧)
              (i : C⟦b, d⟧) (j : C⟦e, x⟧) (m : C⟦d, x⟧).
    Hypothesis H1 : f · h = g · k.
    Hypothesis H2 : i · m = h · j.
    Hypothesis P1 : isPushout _ _ _ _ H1.
    Hypothesis P2 : isPushout _ _ _ _ H2.

    Lemma glueSquares : f · i · m = g · k · j.
    Proof.
      rewrite <- assoc.
      rewrite H2.
      rewrite <- H1.
      repeat rewrite <- assoc.
      apply idpath.
    Qed.

    (** TODO: isPushoutGluedSquare : isPushout (f · i) g m (k · j) glueSquares. *)

  End pushout_lemma.

  Section Universal_Unique.

    Hypothesis H : is_univalent C.

    Lemma inv_from_iso_iso_from_Pushout (a b c : C) (f : C⟦a, b⟧) (g : C⟦a, c⟧)
          (Po : Pushout f g) (Po' : Pushout f g):
      inv_from_iso (iso_from_Pushout_to_Pushout Po Po') = from_Pushout_to_Pushout Po' Po.
    Proof.
      apply pathsinv0.
      apply inv_iso_unique'.
      set (T := are_inverses_from_Pushout_to_Pushout Po Po').
      apply (pr1 T).
    Qed.

  End Universal_Unique.


  (** ** Connections to other colimits *)

  Lemma Pushout_from_Colims : Colims C -> Pushouts.
  Proof.
    intros H a b c f g; apply H.
  Defined.

End def_po.


(** * Definitions coincide
  In this section we show that pushouts defined as special colimits coincide
  with the direct definition. *)
Section pushout_coincide.

  Variable C : precategory.
  Variable hs: has_homsets C.


  (** ** isPushout *)

  Lemma equiv_isPushout1 {a b c d : C} (f : C ⟦a, b⟧) (g : C ⟦a, c⟧)
        (i1 : C⟦b, d⟧) (i2 : C⟦c, d⟧) (H : f · i1 = g · i2) :
    limits.pushouts.isPushout f g i1 i2 H -> isPushout C f g i1 i2 H.
  Proof.
    intros X R cc.
    set (XR := limits.pushouts.mk_Pushout f g d i1 i2 H X).
    use unique_exists.
    + use (limits.pushouts.PushoutArrow XR).
      - exact (coconeIn cc Two).
      - exact (coconeIn cc Three).
      - use (pathscomp0 ((coconeInCommutes cc One Two tt))).
        apply (!(coconeInCommutes cc One Three tt)).
    + use three_rec_dep; simpl.
      - change (three_rec_dep (λ n, C⟦three_rec a b c n, d⟧) _ _ _ _) with (f · i1).
        rewrite <- assoc, (limits.pushouts.PushoutArrow_PushoutIn1 XR).
        apply (coconeInCommutes cc One Two tt).
      - apply (limits.pushouts.PushoutArrow_PushoutIn1 XR).
      - apply (limits.pushouts.PushoutArrow_PushoutIn2 XR).
    + intros y; apply impred_isaprop; intros t; apply hs.
    + intros y T.
      use limits.pushouts.PushoutArrowUnique.
      - apply (T Two).
      - apply (T Three).
  Qed.

  Lemma equiv_isPushout2 {a b c d : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧)
        (i1 : C⟦b, d⟧) (i2 : C⟦c, d⟧) (H : f · i1 = g · i2) :
    limits.pushouts.isPushout f g i1 i2 H <- isPushout C f g i1 i2 H.
  Proof.
    intros X R k h HH.
    set (XR := mk_Pushout C f g d i1 i2 H X).
    use unique_exists.
    + use (PushoutArrow C XR).
      - exact k.
      - exact h.
      - exact HH.
    + split.
      - exact (PushoutArrow_PushoutIn1 C XR R k h HH).
      - exact (PushoutArrow_PushoutIn2 C XR R k h HH).
    + intros y; apply isapropdirprod; apply hs.
    + intros y T.
      use (PushoutArrowUnique C _ _ XR).
      - exact R.
      - exact (pr1 T).
      - exact (pr2 T).
  Qed.


  (** ** Pushout *)

  Definition equiv_Pushout1 {a b c : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧) :
    limits.pushouts.Pushout f g -> Pushout C f g.
  Proof.
    intros X.
    exact (mk_Pushout
             C f g X
             (limits.pushouts.PushoutIn1 X)
             (limits.pushouts.PushoutIn2 X)
             (limits.pushouts.PushoutSqrCommutes X)
             (equiv_isPushout1 _ _ _ _ _ (limits.pushouts.isPushout_Pushout X))).
  Defined.

  Definition equiv_Pushout2 {a b c : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧) :
    limits.pushouts.Pushout f g <- Pushout C f g.
  Proof.
    intros X.
    exact (limits.pushouts.mk_Pushout
             f g
             (PushoutObject C X)
             (PushoutIn1 C X)
             (PushoutIn2 C X)
             (PushoutSqrCommutes C X)
             (equiv_isPushout2 _ _ _ _ _ (isPushout_Pushout C hs X))).
  Defined.

End pushout_coincide.
