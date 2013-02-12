
(************************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(************************************************************

Contents : 

Precomposition with a fully faithful and  
           essentially surjective functor yields
           a full and faithful, i.e. a fully faithful, 
           functor
	
	  

************************************************************)

Require Import uu0.
Require Import hProp.
Require Import hSet.

Require Import auxiliary_lemmas_HoTT.

Require Import precategories.
Require Import functors_transformations.
Require Import whiskering.

Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
Local Notation "f ;; g" := (compose f g)(at level 50).
Notation "[ C , D ]" := (functor_precategory C D).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).





(** * Precomposition with an essentially surjective functor is faithful. *)

Lemma pre_composition_with_ess_surj_is_faithful (A B C : precategory) 
      (H : ob [A, B]) (p : essentially_surjective H) : 
           faithful (pre_composition_functor A B C H).
Proof.
  intros F G gamma delta ex.
  simpl in *.
  apply nat_trans_eq.
  intro b.

  assert (Heq : isaprop (gamma b == delta b)). 
    apply (F b --> G b).

  set (pb := p b (tpair (fun x => isaprop x) (gamma b == delta b) Heq)).
  
  apply pb. simpl in *.
  clear pb. clear Heq.
  intro af.
  destruct af as [a f].
  set (P := pre_comp_with_iso_is_inj C (pr1 F (pr1 H a)) (pr1 F b) (pr1 G b) (# F f)
         (functor_on_iso_is_iso _ _ _ _ _ f)).
  apply P.
  rewrite nat_trans_ax.
  set (EX := nat_trans_eq_pointwise _ _ _ _ _ _ ex a).
  simpl in EX.
  rewrite nat_trans_ax.
  change (gamma (H a)) with (pr1 gamma ((pr1 H) a)).
  rewrite EX.
  apply idpath.
Qed.
  

(** * Precomposition with an essentially surjective and f. f. functor is full *)

Section precomp_with_ess_surj_ff_functor_is_full.

(** Section variables *)

Variables A B C : precategory.
Variable H : ob [A, B].
Hypothesis p : essentially_surjective H.
Hypothesis Hff : fully_faithful H.


(** We prove that [_ O H] yields a full functor. *)

Section full.

Variables F G : ob [B, C].

(** We have to show that for [F] and [G], the map 
     [(_ O H) (F,G) : (F --> G) -> (F O H --> G O H)]  is full. *)

Section preimage.

(** Fixing a [gamma], we produce its preimage. *)

Variable gamma : F O H --> G O H.


Lemma isaprop_aux_space (b : ob B) : 
    isaprop (total2 (fun g : pr1 F b --> pr1 G b => 
      forall a : ob A, forall f : iso (pr1 H a) b,
           pr1 gamma a == #(pr1 F) f ;; g ;; #(pr1 G) (inv_from_iso f))).
Proof.
  apply invproofirrelevance.
  intros x x'.
  destruct x as [g q].
  destruct x' as [g' q'].
  assert (Hgg' : g == g'). Focus 1.
  set (pbg := p b (tpair (fun x => isaprop x) (g == g') (pr2 (pr1 F b --> pr1 G b) _ _ ))).
  simpl in pbg.
  apply pbg.
  intro anoth.
  destruct anoth as [anot h].
  set (qanoth := q anot h).
  assert (H1 : g == iso_inv_from_iso (functor_on_iso _ _ F _ _ h) ;; 
                      pr1 gamma anot ;; functor_on_iso _ _ G _ _ h).
  apply (pre_comp_with_iso_is_inj _ _ _ _ (functor_on_iso _ _ F _ _ h)
                                          (pr2 (functor_on_iso _ _ F _ _ h))).
                                          
  repeat rewrite assoc.
     rewrite iso_inv_after_iso. rewrite id_left.
  apply ( post_comp_with_iso_is_inj _ _ _  
          (iso_inv_from_iso (functor_on_iso _ _ G _ _ h))
                     (pr2 (iso_inv_from_iso (functor_on_iso _ _ G _ _ h)))).
                     simpl.
  set (H3 :=  base_paths _ _ (functor_on_iso_inv _ _ G _ _ h)).
  simpl in H3.
  rewrite <- H3.
  repeat rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  rewrite functor_id.
  rewrite id_right.
  apply pathsinv0.
  rewrite assoc.
  apply qanoth.
  
  set (q'anoth := q' anot h).
  
  assert (H2 : g' == iso_inv_from_iso (functor_on_iso _ _ F _ _ h) ;; 
                      pr1 gamma anot ;; functor_on_iso _ _ G _ _ h).
  apply (pre_comp_with_iso_is_inj _ _ _ _ (functor_on_iso _ _ F _ _ h)
                                          (pr2 (functor_on_iso _ _ F _ _ h))).
                                          
  repeat rewrite assoc.
     rewrite iso_inv_after_iso. rewrite id_left.
  apply ( post_comp_with_iso_is_inj _ _ _  
          (iso_inv_from_iso (functor_on_iso _ _ G _ _ h))
                     (pr2 (iso_inv_from_iso (functor_on_iso _ _ G _ _ h)))).
                     simpl.
  set (H3 :=  base_paths _ _ (functor_on_iso_inv _ _ G _ _ h)).
  simpl in H3.
  rewrite <- H3.
  repeat rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  rewrite functor_id.
  rewrite id_right.
  apply pathsinv0.
  rewrite assoc.
  apply q'anoth.
  rewrite H1.
  rewrite H2.
  apply idpath.

  apply (total2_paths2 Hgg').
  apply proofirrelevance.
  apply impred. intro a.
  apply impred. intro a'.
  apply (pr2 (pr1 (F O H) a --> pr1 (G O H) a)).
Qed.
  


Lemma iscontr_aux_space (*F G : ob [B, C]) (gamma : F O H --> G O H) *)
        (b : ob B) : 
   iscontr (total2 (fun g : pr1 F b --> pr1 G b => 
      forall a : ob A, forall f : iso (pr1 H a) b,
           pr1 gamma a == #(pr1 F) f ;; g ;; #(pr1 G) (inv_from_iso f)  )).
Proof.
  set (X := isapropiscontr (total2
     (fun g : (pr1 F) b --> (pr1 G) b =>
      forall (a : ob A) (f : iso ((pr1 H) a) b),
      pr1 gamma a == (#(pr1 F) f;; g);; #(pr1 G) (inv_from_iso f)))).
  set (pbX := p b (tpair (fun x => isaprop x) _ X)).
  simpl.
  apply pbX. clear pbX. simpl. clear X.
  intro anoth.
  destruct anoth as [anot h].
  simpl in *.
  set (g := #F (inv_from_iso h) ;; gamma anot ;; #G h).

  assert (gp : forall (a : ob A) 
                     (f : iso (H a) b),
                 gamma a == #F f ;; g ;; #G (inv_from_iso f)).
  intros a f.
  set (k := iso_from_fully_faithful_reflection _ _ _ Hff _ _ 
             (iso_comp f (iso_inv_from_iso h))).
  set (GHk := functor_on_iso _ _ G _ _ 
                (functor_on_iso _ _ H _ _ k)).
  pathvia (#F (#H k) ;; gamma anot ;; iso_inv_from_iso GHk).
  
  set (P := post_comp_with_iso_is_inj _ _ _ GHk (pr2 GHk)).
  apply P.
  rewrite <- assoc.
  change (iso_inv_from_iso GHk ;; GHk) with (inv_from_iso GHk ;; GHk).
  rewrite iso_after_iso_inv. rewrite id_right.
  set (Hgamma := nat_trans_ax _ _ gamma).
  simpl in Hgamma.
  rewrite Hgamma. apply idpath.
  unfold GHk.
  rewrite <- functor_on_iso_inv.
  unfold k. simpl.
  rewrite functor_on_iso_iso_from_fully_faithful_reflection.
  set (Hr := iso_inv_of_iso_comp _ _ _ _ f (iso_inv_from_iso h)).
  simpl in Hr. 
  set (Hrp := base_paths _ _ Hr). simpl in Hrp.
  rewrite Hrp.
  rewrite functor_comp.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a anot)).
  simpl in H3. unfold fully_faithful_inv_hom.
  simpl. rewrite H3. clear H3.
  set (H4 := base_paths _ _ (iso_inv_iso_inv _ _ _ h)).
  simpl in H4. rewrite H4.
  rewrite functor_comp.
  unfold g.
  repeat rewrite assoc.
  apply idpath.
  apply iscontraprop1.
  apply isaprop_aux_space.
  
  exists g.
  apply gp.
Qed.
  
 
Definition pdelta : forall b : ob B, pr1 F b --> pr1 G b :=
         fun b => pr1 (pr1 (iscontr_aux_space b)).

Lemma is_nat_trans_pdelta : 
     is_nat_trans (pr1 F) (pr1 G) pdelta.
Proof.
  intros b b' f.
  apply pathsinv0. 
  set (pb1 := p b (tpair (fun x => isaprop x) 
                       (pdelta b;; #(pr1 G) f == 
                         #(pr1 F) f;; pdelta b')
                       (pr2 ((pr1 F) b --> (pr1 G) b') _ _ ))).
  simpl in *.
  apply pb1. clear pb1.
  intro t; destruct t as [a h].
  set (pb1 := p b' (tpair (fun x => isaprop x) 
                       (pdelta b;; # (G) f == 
                         #(pr1 F) f;; pdelta b')
                       (pr2 ((pr1 F) b --> (pr1 G) b') _ _ ))).
  simpl in *.
  apply pb1. clear pb1.
  intro t; destruct t as [a' h'].
  
  set (k := fully_faithful_inv_hom _ _ H Hff _ _ 
             (h ;; (f ;; (iso_inv_from_iso h')))).
  
  set (gq := pr1 (iscontr_aux_space b)). 
  set (g := pr1 gq).
  set (q := pr2 gq). simpl in *. unfold gq in *.
  
  set (HH := (q a h)). simpl in *.
  
  assert (Hb : pdelta b == inv_from_iso (functor_on_iso _ _ F _ _ h) ;; 
                                gamma a ;; #G h).
  apply (pre_comp_with_iso_is_inj _ _ _ _ (functor_on_iso _ _ F _ _ h)
                                          (pr2 (functor_on_iso _ _ F _ _ h))).
  repeat rewrite assoc.
     rewrite iso_inv_after_iso. rewrite id_left.
  apply ( post_comp_with_iso_is_inj _ _ _  
          (iso_inv_from_iso (functor_on_iso _ _ G _ _ h))
                     (pr2 (iso_inv_from_iso (functor_on_iso _ _ G _ _ h)))).
                     simpl.
  set (H3 :=  base_paths _ _ (functor_on_iso_inv _ _ G _ _ h)).
  simpl in H3.
  rewrite <- H3.
  repeat rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  rewrite functor_id.
  rewrite id_right.
  apply pathsinv0.
  clear H3.
  rewrite assoc.
  apply HH.
  
  
  assert (Hb' : pdelta b' == inv_from_iso (functor_on_iso _ _ F _ _ h') ;; 
                                gamma a' ;; #G h').
  apply (pre_comp_with_iso_is_inj _ _ _ _ (functor_on_iso _ _ F _ _ h')
                                          (pr2 (functor_on_iso _ _ F _ _ h'))).
  repeat rewrite assoc.
     rewrite iso_inv_after_iso. rewrite id_left.
  apply ( post_comp_with_iso_is_inj _ _ _  
          (iso_inv_from_iso (functor_on_iso _ _ G _ _ h'))
                     (pr2 (iso_inv_from_iso (functor_on_iso _ _ G _ _ h')))).
                     simpl.
  set (H3 :=  base_paths _ _ (functor_on_iso_inv _ _ G _ _ h')).
  simpl in H3.
  rewrite <- H3.
  repeat rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  rewrite functor_id.
  rewrite id_right.
  apply pathsinv0.
  clear H3.
  rewrite assoc.
  set (gq' := pr1 (iscontr_aux_space b')).
  set (q' := pr2 gq').
  set (HH' := q' a' h').
  apply HH'.
  
  rewrite Hb.
  repeat rewrite <- assoc.
  simpl in *.
  rewrite <- (functor_comp _ _ G _ _ _ h f).
  clear HH q g gq.
  pathvia (inv_from_iso (functor_on_iso B C F (H a) b h);;
       (gamma a;; #G (h;; f ;; iso_inv_from_iso h' ;; h')) ).
    repeat rewrite <- assoc.
    simpl. rewrite iso_after_iso_inv. 
           rewrite id_right.
           apply idpath.
  repeat rewrite precategory_assoc.
  rewrite (functor_comp _ _ G).
  set (P := nat_trans_ax _ _ gamma _ _ k). simpl in *.
      unfold k in P. simpl in P.
  set (H3 := homotweqinvweq (weq_from_fully_faithful _ _ _ Hff a a')).
  simpl in H3. 
  unfold fully_faithful_inv_hom in P. simpl in P.
  rewrite H3 in P.
  repeat rewrite <- assoc.
  rewrite (assoc _ _ _ _ _ (gamma a)).
  simpl in *.
  rewrite <- P.
  clear H3 P.
  set (H4 := functor_on_iso_inv _ _ F _ _ h).
  set (H5 := base_paths _ _ H4). simpl in H5.
  rewrite <- H5.
  repeat rewrite assoc.
  rewrite <- (functor_comp _ _ F).
  repeat rewrite assoc.
  rewrite iso_after_iso_inv.
  rewrite id_left.
  rewrite (functor_comp _ _ F).
  rewrite functor_on_inv_from_iso.
  apply pathsinv0.
  rewrite Hb'.
  repeat rewrite assoc.
  apply idpath.
Qed.


Definition delta : F --> G.
Proof.
  exists pdelta.
  apply is_nat_trans_pdelta.
Defined.

Lemma pdelta_preimage : pre_whisker _ _ _ H _ _ delta == gamma.
Proof.
  simpl in *.
  apply nat_trans_eq.
  intro a.
  unfold pre_whisker.
  simpl.
  set (tr := pr1 (iscontr_aux_space (H a))).
  set (g := pr1 tr).
  set (q := pr2 tr).
  simpl in *. 
  set (gaid := q a (identity_iso _ )).
  simpl in *.
  change (gamma a) with (pr1 gamma a). 
  pathvia ((#(pr1 F) (identity ((pr1 H) a));; pr1 tr);;
       #(pr1 G) (inv_from_iso (identity_iso ((pr1 H) a)))).
       Focus 2. apply pathsinv0. apply gaid.
  rewrite (functor_id _ _ F).
  rewrite id_left.
  set (P := iso_inv_of_iso_id _ (pr1 H a)).
  set (Pr := base_paths _ _ P); simpl in Pr.
  rewrite Pr. clear Pr P. simpl in *.
  rewrite (functor_id _ _ G) .
  rewrite id_right.
  apply idpath.
Qed.
  

End preimage.

End full.

(** * Precomposition with an essentially surjective and f. f. functor is fully faithful *)

Lemma pre_composition_with_ess_surj_and_fully_faithful_is_full :
  full (pre_composition_functor A B C H).
Proof.
  unfold full.
  intros F G gamma.
  exists (delta F G gamma).
  apply pdelta_preimage.
Defined.

Lemma pre_composition_with_ess_surj_and_fully_faithful_is_full_and_faithful : 
   full_and_faithful (pre_composition_functor A B C H).
Proof.
  split.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_full.
  apply pre_composition_with_ess_surj_is_faithful. assumption.
Qed.

Lemma pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful : 
   fully_faithful (pre_composition_functor A B C H).
Proof.
  apply full_and_faithful_implies_fully_faithful.
  apply pre_composition_with_ess_surj_and_fully_faithful_is_full_and_faithful.
Qed.


End precomp_with_ess_surj_ff_functor_is_full.



