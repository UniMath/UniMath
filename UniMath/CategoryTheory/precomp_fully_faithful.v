(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents :

Precomposition with a fully faithful and
           essentially surjective functor yields
           a full and faithful, i.e. a fully faithful,
           functor



************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Local Open Scope cat.

Ltac simp_rew lem := let H:=fresh in
     assert (H:= lem); simpl in *; rewrite H; clear H.
Ltac simp_rerew lem := let H:=fresh in
     assert (H:= lem); simpl in *; rewrite <- H; clear H.
Ltac inv_functor HF x y :=
   let H:=fresh in
   set (H:= homotweqinvweq (weq_from_fully_faithful HF x y));
     simpl in H;
     unfold fully_faithful_inv_hom; simpl;
     rewrite H; clear H.


Local Notation "G 'O' F" := (functor_compose _ _ _ F G : functor _ _ ) (at level 25).
Local Notation "FF ^-1" := (fully_faithful_inv_hom FF _ _ ) (at level 20).
Local Notation "F '^-i'" := (iso_from_fully_faithful_reflection F _ _) (at level 20).

(** * Precomposition with an essentially surjective functor is faithful. *)

Lemma pre_composition_with_ess_surj_is_faithful (A B C : precategory) (hsB: has_homsets B)
      (hsC: has_homsets C) (H : [A, B, hsB]) (p : essentially_surjective H) :
           faithful (pre_composition_functor A B C hsB hsC H).
Proof.
  intros F G.
  apply isinclbetweensets.
  - apply isaset_nat_trans. apply hsC.
  - apply isaset_nat_trans. apply hsC.
  - simpl in *.
    intros gamma delta ex .
    apply nat_trans_eq.
    + apply hsC.
    + intro b.
      assert (Heq : isaprop (gamma b = delta b)).
      { apply hsC . }
      apply (p b (tpair (λ x, isaprop x) (gamma b = delta b) Heq)).
      simpl in *; clear Heq.
      intros [a f].
      apply (pre_comp_with_iso_is_inj C (F (H a)) (F b) (G b) (# F f)
         (functor_on_iso_is_iso _ _ _ _ _ f)).
      repeat rewrite nat_trans_ax.
      change (gamma (H a)) with (pr1 gamma ((pr1 H) a)).
      apply cancel_postcomposition.
      apply (nat_trans_eq_pointwise ex a).
Qed.


(** * Precomposition with an essentially surjective and f. f. functor is full *)

Section precomp_with_ess_surj_ff_functor_is_full.

(** Section variables *)

Variables A B C : precategory.
Variable hsB: has_homsets B.
Variable hsC: has_homsets C.
Variable H : functor A B.
Hypothesis p : essentially_surjective H.
Hypothesis Hff : fully_faithful H.


(** We prove that [_ O H] yields a full functor. *)

Section full.

Variables F G : functor B C.

(** We have to show that for [F] and [G], the map
     [(_ O H) (F,G) : (F --> G) -> (F O H --> G O H)]  is full. *)

Section preimage.

(** Fixing a [gamma], we produce its preimage. *)

Variable gamma : nat_trans
     (functor_composite H F)
     (functor_composite H G).

Lemma isaprop_aux_space (b : B) :
    isaprop (total2 (fun g : F b --> G b =>
      ∏ a : A, ∏ f : iso (H a) b,
           gamma a = #F f · g · #G (inv_from_iso f))).
Proof.
  apply invproofirrelevance.
  intros x x'.
  apply subtypeEquality.
    intro; repeat (apply impred; intro).
    apply hsC.
  destruct x as [g q].
  destruct x' as [g' q'].
  simpl.
    assert (T: isaprop (g = g')). { apply hsC. }
    apply (p b (hProppair (g = g') T  )).
    intro anoth.
    destruct anoth as [anot h].
    set (qanoth := q anot h).
    assert (H1 : g = iso_inv_from_iso (functor_on_iso F h) ·
                      gamma anot · functor_on_iso G h).
      apply (pre_comp_with_iso_is_inj _ _ _ _ (functor_on_iso F h)
                                          (pr2 (functor_on_iso F h))).
     repeat rewrite assoc.
     set (TH:=iso_inv_after_iso (functor_on_iso F h)).
     simpl in TH. simpl. rewrite TH.
     rewrite id_left.
      apply (post_comp_with_iso_is_inj _ _ _
          (iso_inv_from_iso (functor_on_iso G h))
                     (pr2 (iso_inv_from_iso (functor_on_iso G h)))).
      simpl.
      simp_rerew (base_paths _ _ (functor_on_iso_inv _ _  G _ _ h)).
      repeat rewrite <- assoc.
      rewrite <- functor_comp.
      rewrite iso_inv_after_iso, functor_id, id_right.
      apply pathsinv0.
      rewrite assoc.
      apply qanoth.
    set (q'anoth := q' anot h).
    assert (H2 : g' = iso_inv_from_iso (functor_on_iso F h) ·
                      pr1 gamma anot · functor_on_iso G h).
      apply (pre_comp_with_iso_is_inj _ _ _ _ (functor_on_iso F h)
                                          (pr2 (functor_on_iso F h))).
      repeat rewrite assoc.
     set (TH:=iso_inv_after_iso (functor_on_iso F h)).
     simpl in TH. simpl. rewrite TH.
      rewrite id_left.
      apply ( post_comp_with_iso_is_inj _ _ _
            (iso_inv_from_iso (functor_on_iso G h))
                     (pr2 (iso_inv_from_iso (functor_on_iso G h)))).
      simpl.
      simp_rerew(base_paths _ _ (functor_on_iso_inv _ _  G _ _ h)).
      repeat rewrite <- assoc.
      rewrite <- functor_comp.
      rewrite iso_inv_after_iso, functor_id, id_right.
      apply pathsinv0.
      rewrite assoc; apply q'anoth.
    simpl.
    rewrite H1, H2.
    apply idpath.
Qed.



Lemma iscontr_aux_space (b : B) :
   iscontr (total2 (fun g : F b --> G b =>
      ∏ a : A, ∏ f : iso (H a) b,
           gamma a = #F f · g · #G (inv_from_iso f)  )).
Proof.
  set (X := isapropiscontr (total2
     (fun g : F b --> G b =>
      ∏ (a : A) (f : iso (H a) b),
      gamma a = (#F f· g)· #G (inv_from_iso f)))).
  apply (p b (tpair (λ x, isaprop x) _ X)).
  intros [anot h].
  simpl in *.
  set (g := #F (inv_from_iso h) · gamma anot · #G h).
  assert (gp : ∏ (a : A)
                     (f : iso (H a) b),
                 gamma a = #F f · g · #G (inv_from_iso f)).
    clear X.
    intros a f.
    set (k := iso_from_fully_faithful_reflection Hff
             (iso_comp f (iso_inv_from_iso h))).
    set (GHk := functor_on_iso G
                (functor_on_iso H k)).
    intermediate_path (#F (#H k) · gamma anot · iso_inv_from_iso GHk).
      apply (post_comp_with_iso_is_inj _ _ _ GHk (pr2 GHk)).
      rewrite <- assoc.
      change (iso_inv_from_iso GHk · GHk) with (inv_from_iso GHk · GHk).
      rewrite iso_after_iso_inv, id_right.
      simp_rew (nat_trans_ax gamma).
      apply idpath.
    unfold GHk.
    rewrite <- functor_on_iso_inv.
    unfold k; simpl.
    rewrite functor_on_iso_iso_from_fully_faithful_reflection.
    simp_rew (base_paths _ _ (iso_inv_of_iso_comp _  _ _  _ f (iso_inv_from_iso h))).
    rewrite functor_comp.
    inv_functor Hff a anot.
    simp_rew (base_paths _ _ (iso_inv_iso_inv _ _ _ h)).
    rewrite functor_comp.
    unfold g; repeat rewrite assoc.
    apply idpath.
  apply iscontraprop1.
  apply isaprop_aux_space.
  exists g.
  apply gp.
Defined.


Definition pdelta : ∏ b : B, F b --> G b :=
         λ b, pr1 (pr1 (iscontr_aux_space b)).

Lemma is_nat_trans_pdelta :
     is_nat_trans F G pdelta.
Proof.
  intros b b' f.
  apply pathsinv0.
  assert (T: isaprop (pdelta b· #G f = #F f· pdelta b')).
   { apply hsC. }
  apply (p b (hProppair (pdelta b· #G f =
                         #F f· pdelta b') T )).
  intro t; destruct t as [a h].
  simpl in *.
  apply (p b' (tpair (λ x, isaprop x)
                       (pdelta b· #G f =
                         #F f· pdelta b')
                       (T ))).
  simpl in *.
  intro t; destruct t as [a' h'].
  assert (Hb : pdelta b = inv_from_iso (functor_on_iso F h) ·
                                gamma a · #G h).
    apply (pre_comp_with_iso_is_inj _ _ _ _ (functor_on_iso F h)
                                          (pr2 (functor_on_iso F h))).
    repeat rewrite assoc.
    rewrite iso_inv_after_iso, id_left.
    apply ( post_comp_with_iso_is_inj _ _ _
          (iso_inv_from_iso (functor_on_iso G h))
                     (pr2 (iso_inv_from_iso (functor_on_iso G h)))).
    simpl.
    simp_rerew (base_paths _ _ (functor_on_iso_inv _ _  G _ _ h)).
    repeat rewrite <- assoc.
    rewrite <- functor_comp.
    rewrite iso_inv_after_iso, functor_id, id_right.
    apply pathsinv0.
    rewrite assoc.
    apply (pr2 ((pr1 (iscontr_aux_space b))) a h).
  assert (Hb' : pdelta b' = inv_from_iso (functor_on_iso F h') ·
                                gamma a' · #G h').
    apply (pre_comp_with_iso_is_inj _ _ _ _ (functor_on_iso F h')
                                          (pr2 (functor_on_iso F h'))).
    repeat rewrite assoc.
    rewrite iso_inv_after_iso, id_left.
    apply ( post_comp_with_iso_is_inj _ _ _
          (iso_inv_from_iso (functor_on_iso G h'))
                     (pr2 (iso_inv_from_iso (functor_on_iso G h')))).
    simpl.
    simp_rerew (base_paths _ _ (functor_on_iso_inv _ _  G _ _ h')).
    repeat rewrite <- assoc.
    rewrite <- functor_comp.
    rewrite iso_inv_after_iso, functor_id, id_right.
    apply pathsinv0.
    rewrite assoc.
    apply (pr2 (pr1 (iscontr_aux_space b')) a' h').
  rewrite Hb.
  repeat rewrite <- assoc.
  simpl in *.
  rewrite <- functor_comp.
  intermediate_path (inv_from_iso (functor_on_iso F h)·
       (gamma a· #G (h· f · iso_inv_from_iso h' · h')) ).
    repeat rewrite <- assoc.
    simpl. rewrite iso_after_iso_inv, id_right.
    apply idpath.
  repeat rewrite precategory_assoc.
  rewrite functor_comp.
  set (k := Hff^-1
             (h · (f · (iso_inv_from_iso h')))).
  assert (P := nat_trans_ax gamma _ _ k). simpl in *.
      unfold k in P. simpl in P.
  set (H3 := homotweqinvweq (weq_from_fully_faithful Hff a a')).
  simpl in H3.
  unfold fully_faithful_inv_hom in P. simpl in P.
  rewrite H3 in P. clear H3.
  repeat rewrite <- assoc.
  rewrite (assoc (gamma a)).
  simpl in *.
  rewrite <- P; clear P.
  assert (H4 := functor_on_iso_inv _ _  F _ _ h).
  assert (H5 := base_paths _ _ H4).
  simpl in H5.
  rewrite <- H5.
  repeat rewrite assoc.
  rewrite <- functor_comp.
  repeat rewrite assoc.
  rewrite iso_after_iso_inv, id_left, functor_comp,
      functor_on_inv_from_iso.
  apply pathsinv0.
  rewrite Hb'.
  repeat rewrite assoc.
  apply idpath.
Qed.


Definition delta : nat_trans F G.
Proof.
  exists pdelta.
  apply is_nat_trans_pdelta.
Defined.

Lemma pdelta_preimage : pre_whisker  H delta = gamma.
Proof.
  simpl in *.
  apply nat_trans_eq; intro a.
  apply hsC.
  unfold pre_whisker.
  simpl.
  set (tr := pr1 (iscontr_aux_space (H a))).
  change (gamma a) with (pr1 gamma a).
  intermediate_path ((#F (identity (H a))· pr1 tr)·
       #G (inv_from_iso (identity_iso (H a)))).
  rewrite functor_id.
  rewrite id_left.
  set (P := iso_inv_of_iso_id _ (H a)).
  set (Pr := base_paths _ _ P); simpl in Pr.
  rewrite Pr. clear Pr P. simpl in *.
  rewrite functor_id.
  rewrite id_right.
  apply idpath.

  apply pathsinv0.
  apply (pr2 tr a (identity_iso _ )).
Qed.


End preimage.

End full.

(** * Precomposition with an essentially surjective and f. f. functor is fully faithful *)

Lemma pre_composition_with_ess_surj_and_fully_faithful_is_full :
  full (pre_composition_functor A B C hsB hsC H).
Proof.
  unfold full.
  intros F G gamma.
  apply hinhpr.
  exists (delta F G gamma).
  apply pdelta_preimage.
Defined.

Lemma pre_composition_with_ess_surj_and_fully_faithful_is_full_and_faithful :
   full_and_faithful (pre_composition_functor A B C hsB hsC H).
Proof.
  split.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_full.
  apply pre_composition_with_ess_surj_is_faithful. assumption.
Defined.

Lemma pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful :
   fully_faithful (pre_composition_functor A B C hsB hsC H).
Proof.
  apply full_and_faithful_implies_fully_faithful.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_full_and_faithful.
Defined.


End precomp_with_ess_surj_ff_functor_is_full.
