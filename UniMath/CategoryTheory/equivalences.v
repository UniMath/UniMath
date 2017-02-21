(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman
january 2013

Extended by: Anders Mörtberg, 2016

************************************************************)


(** **********************************************************

Contents :  Definition of adjunction

	    Definition of equivalence of precategories

	    Equivalence of categories yields weak equivalence
            of object types

            A fully faithful and ess. surjective functor induces
            equivalence of precategories, if the source
            is a category.

            Post-composition with a left adjoint is a left
            adjoint ([is_left_adjoint_post_composition_functor])

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

(** * Adjunctions *)
Section adjunctions.

Definition form_adjunction {A B : precategory} (F : functor A B) (G : functor B A)
  (eta : nat_trans (functor_identity A) (functor_composite F G))
  (eps : nat_trans (functor_composite G F) (functor_identity B)) : UU :=
    (∏ a : A, # F (eta a) ;; eps (F a) = identity (F a)) ×
    (∏ b : B, eta (G b) ;; # G (eps b) = identity (G b)).

Definition are_adjoints {A B : precategory} (F : functor A B) (G : functor B A) : UU :=
  ∑ (etaeps : (nat_trans (functor_identity A) (functor_composite F G)) ×
              (nat_trans (functor_composite G F) (functor_identity B))),
      form_adjunction F G (pr1 etaeps) (pr2 etaeps).

(** Note that this makes the second component opaque for efficiency reasons *)
Definition mk_are_adjoints {A B : precategory}
  (F : functor A B) (G : functor B A)
  (eta : nat_trans (functor_identity A) (functor_composite F G))
  (eps : nat_trans (functor_composite G F) (functor_identity B))
  (HH : form_adjunction F G eta eps) : are_adjoints F G.
Proof.
exists (eta,,eps).
abstract (exact HH).
Defined.

Definition unit_from_are_adjoints {A B : precategory}
   {F : functor A B} {G : functor B A} (H : are_adjoints F G) :
  nat_trans (functor_identity A) (functor_composite F G)
  := pr1 (pr1 H).

Definition counit_from_are_adjoints {A B : precategory}
  {F : functor A B} {G : functor B A} (H : are_adjoints F G)  :
   nat_trans (functor_composite G F) (functor_identity B)
   := pr2 (pr1 H).

Definition is_left_adjoint {A B : precategory} (F : functor A B) : UU :=
  ∑ (G : functor B A), are_adjoints F G.

Definition is_right_adjoint {A B : precategory} (G : functor B A) : UU :=
  ∑ (F : functor A B), are_adjoints F G.

Definition are_adjoints_to_is_left_adjoint {A B : precategory} (F : functor A B) (G : functor B A)
           (H : are_adjoints F G) : is_left_adjoint F := (G,,H).

Coercion are_adjoints_to_is_left_adjoint : are_adjoints >-> is_left_adjoint.

Definition are_adjoints_to_is_right_adjoint {A B : precategory} (F : functor A B) (G : functor B A)
           (H : are_adjoints F G) : is_right_adjoint G := (F,,H).

Coercion are_adjoints_to_is_right_adjoint : are_adjoints >-> is_right_adjoint.

Definition right_adjoint {A B : precategory}
  {F : functor A B} (H : is_left_adjoint F) : functor B A := pr1 H.

Lemma is_right_adjoint_right_adjoint {A B : precategory}
      {F : functor A B} (H : is_left_adjoint F) : is_right_adjoint (right_adjoint H).
Proof.
exact (F,,pr2 H).
Defined.

Definition left_adjoint {A B : precategory}
  {G : functor B A} (H : is_right_adjoint G) : functor A B := pr1 H.

Lemma is_left_adjoint_left_adjoint {A B : precategory}
      {G : functor B A} (H : is_right_adjoint G) : is_left_adjoint (left_adjoint H).
Proof.
exact (G,,pr2 H).
Defined.

Definition unit_from_left_adjoint {A B : precategory}
   {F : functor A B}  (H : is_left_adjoint F) :
  nat_trans (functor_identity A) (functor_composite F (right_adjoint H))
  := unit_from_are_adjoints (pr2 H).

Definition unit_from_right_adjoint {A B : precategory}
   {G : functor B A}  (H : is_right_adjoint G) :
  nat_trans (functor_identity A) (functor_composite (left_adjoint H) G)
  := unit_from_are_adjoints (pr2 H).

Definition counit_from_left_adjoint {A B : precategory}
  {F : functor A B}   (H : is_left_adjoint F)  :
 nat_trans (functor_composite (right_adjoint H) F) (functor_identity B)
   := counit_from_are_adjoints (pr2 H).

Definition counit_from_right_adjoint {A B : precategory}
  {G : functor B A} (H : is_right_adjoint G)  :
 nat_trans (functor_composite G (left_adjoint H)) (functor_identity B)
   := counit_from_are_adjoints (pr2 H).

Definition triangle_id_left_ad {A B : precategory} {F : functor A B} {G : functor B A}
  (H : are_adjoints F G) :
  ∏ a, # F (unit_from_are_adjoints H a) ;; counit_from_are_adjoints H (F a) = identity (F a)
   := pr1 (pr2 H).

Definition triangle_id_right_ad {A B : precategory} {F : functor A B} {G : functor B A}
  (H : are_adjoints F G) :
  ∏ b, unit_from_are_adjoints H (G b) ;; # G (counit_from_are_adjoints H b) = identity (G b)
  := pr2 (pr2 H).

Lemma are_adjoints_functor_composite
  {A B C : precategory} {F1 : functor A B} {F2 : functor B C}
  {G1 : functor B A} {G2 : functor C B}
  (H1 : are_adjoints F1 G1) (H2 : are_adjoints F2 G2) :
  are_adjoints (functor_composite F1 F2) (functor_composite G2 G1).
Proof.
destruct H1 as [[eta1 eps1] [H11 H12]].
destruct H2 as [[eta2 eps2] [H21 H22]].
simpl in *.
use mk_are_adjoints.
- apply (nat_trans_comp _ _ _ eta1).
  use (nat_trans_comp _ _ _ _ (nat_trans_functor_assoc_inv _ _ _)).
  apply pre_whisker.
  apply (nat_trans_comp _ _ _ (nat_trans_functor_id_right_inv _)
                              (post_whisker eta2 G1)).
- use (nat_trans_comp _ _ _ _ eps2).
  apply (nat_trans_comp _ _ _ (nat_trans_functor_assoc _ _ _)).
  apply pre_whisker.
  apply (nat_trans_comp _ _ _ (nat_trans_functor_assoc_inv _ _ _)).
  apply (nat_trans_comp _ _ _ (post_whisker eps1 _)
                              (nat_trans_functor_id_left _)).
- split; intros a; simpl.
  + rewrite !id_left, !id_right, <-functor_id, <- H11, !functor_comp, <-!assoc.
    apply maponpaths; rewrite assoc.
    etrans; [eapply cancel_postcomposition, pathsinv0, functor_comp|].
    etrans.
      apply cancel_postcomposition, maponpaths.
      apply (nat_trans_ax eps1 (F1 a) (G2 (F2 (F1 a))) (eta2 (F1 a))).
    simpl; rewrite functor_comp, <- assoc.
    etrans; [eapply maponpaths, H21|].
    now apply id_right.
  + rewrite !id_left, !id_right, <- functor_id, <- H22, !functor_comp, assoc.
    apply cancel_postcomposition; rewrite <- assoc.
    etrans; [eapply maponpaths, pathsinv0, functor_comp|].
    etrans.
      eapply maponpaths, maponpaths, pathsinv0.
      apply (nat_trans_ax eta2 (F1 (G1 (G2 a))) (G2 a) (eps1 _)).
    simpl; rewrite functor_comp, assoc.
    etrans; [apply cancel_postcomposition, H12|].
    now apply id_left.
Defined.

Lemma is_left_adjoint_functor_composite
  {A B C : precategory} {F1 : functor A B} {F2 : functor B C}
  (H1 : is_left_adjoint F1) (H2 : is_left_adjoint F2) :
  is_left_adjoint (functor_composite F1 F2).
Proof.
mkpair.
- apply (functor_composite (pr1 H2) (pr1 H1)).
- apply are_adjoints_functor_composite.
  + apply (pr2 H1).
  + apply (pr2 H2).
Defined.

Lemma is_left_adjoint_iso {A B : precategory} (hsB : has_homsets B)
  (F G : functor A B) (αiso : @iso [A,B,hsB] F G) (HF : is_left_adjoint F) :
  is_left_adjoint G.
Proof.
set (α := pr1 αiso : nat_trans F G).
set (αinv := inv_from_iso αiso : nat_trans G F).
destruct HF as [F' [[α' β'] [HF1 HF2]]]; simpl in HF1, HF2.
mkpair.
- apply F'.
- use mk_are_adjoints.
  + apply (nat_trans_comp _ _ _ α' (post_whisker α F')).
  + apply (nat_trans_comp _ _ _ (pre_whisker F' αinv) β').
  + split.
    * simpl; intro a; rewrite assoc, functor_comp.
      etrans; [ apply cancel_postcomposition; rewrite <- assoc;
                apply maponpaths, (nat_trans_ax αinv)|].
      etrans; [ rewrite assoc, <- !assoc;
                apply maponpaths, maponpaths, (nat_trans_ax β')|].
      simpl; rewrite assoc.
      etrans; [ apply cancel_postcomposition, (nat_trans_ax αinv)|].
      rewrite assoc.
      etrans; [ apply cancel_postcomposition; rewrite <- assoc;
                apply maponpaths, HF1|].
      now rewrite id_right; apply (nat_trans_eq_pointwise (iso_after_iso_inv αiso)).
    * simpl; intro b; rewrite functor_comp, assoc.
      etrans; [ apply cancel_postcomposition; rewrite <- assoc;
                eapply maponpaths, pathsinv0, functor_comp|].
      etrans; [ apply cancel_postcomposition, maponpaths, maponpaths,
                      (nat_trans_eq_pointwise (iso_inv_after_iso αiso))|].
      now rewrite (functor_id F'), id_right, (HF2 b).
Defined.

(** * Equivalence of (pre)categories *)

Definition adj_equivalence_of_precats {A B : precategory} (F : functor A B) : UU :=
   ∑ (H : is_left_adjoint F), (∏ a, is_isomorphism (unit_from_left_adjoint H a)) ×
                              (∏ b, is_isomorphism (counit_from_left_adjoint H b)).

Definition adj_equivalence_inv {A B : precategory}
  {F : functor A B} (HF : adj_equivalence_of_precats F) : functor B A :=
    right_adjoint (pr1 HF).

Local Notation "HF ^^-1" := (adj_equivalence_inv  HF)(at level 3).

Definition unit_pointwise_iso_from_adj_equivalence {A B : precategory}
   {F : functor A B} (HF : adj_equivalence_of_precats F) :
    ∏ a, iso a (HF^^-1 (F a)).
Proof.
intro a.
exists (unit_from_left_adjoint (pr1 HF) a).
exact (pr1 (pr2 HF) a).
Defined.

Definition counit_pointwise_iso_from_adj_equivalence {A B : precategory}
  {F : functor A B} (HF : adj_equivalence_of_precats F) :
    ∏ b, iso (F (HF^^-1 b)) b.
Proof.
  intro b.
  exists (counit_from_left_adjoint (pr1 HF) b).
  exact (pr2 (pr2 HF) b).
Defined.

Definition unit_iso_from_adj_equivalence_of_precats {A B : precategory}
  (hsA: has_homsets A)
  {F : functor A B} (HF : adj_equivalence_of_precats F) :
       iso (C:=[A, A, hsA]) (functor_identity A)
        (functor_composite F (right_adjoint  (pr1 HF))).
Proof.
  exists (unit_from_left_adjoint (pr1 HF)).
  apply functor_iso_if_pointwise_iso.
  apply (pr1 (pr2 HF)).
Defined.

Definition counit_iso_from_adj_equivalence_of_precats {A B : precategory}
  (hsB: has_homsets B)
  {F : ob [A, B, hsB]} (HF : adj_equivalence_of_precats F) :
       iso (C:=[B, B, hsB])
   (functor_composite  (right_adjoint (pr1 HF)) F)
                (functor_identity B).
Proof.
  exists (counit_from_left_adjoint (pr1 HF)).
  apply functor_iso_if_pointwise_iso.
  apply (pr2 (pr2 HF)).
Defined.

(** * Identity functor is an equivalence *)

Lemma identity_functor_is_adj_equivalence {A : precategory} :
  adj_equivalence_of_precats (functor_identity A).
Proof.
  mkpair.
  - mkpair.
    + exact (functor_identity A).
    + exists (nat_trans_id _,, nat_trans_id _).
      abstract (now split; [intros a; apply id_left| intros a; apply id_left]).
  - abstract (now split; intros a; apply identity_is_iso).
Defined.

(** * Equivalence of categories yields equivalence of object types *)
(**  Fundamentally needed that both source and target are categories *)

Lemma adj_equiv_of_cats_is_weq_of_objects (A B : precategory)
   (HA : is_category A) (HB : is_category B) (F : [A, B, pr2 HB ])
   (HF : adj_equivalence_of_precats F) : isweq (pr1 (pr1 F)).
Proof.
  set (G := right_adjoint (pr1 HF)).
  set (et := unit_iso_from_adj_equivalence_of_precats (pr2 HA)  HF).
  set (ep := counit_iso_from_adj_equivalence_of_precats _ HF).
  set (AAcat := is_category_functor_category A _ HA).
  set (BBcat := is_category_functor_category B _ HB).
  set (Et := isotoid _ AAcat et).
  set (Ep := isotoid _ BBcat ep).
  apply (gradth _ (fun b => pr1 (right_adjoint (pr1 HF)) b)); intro a.
  apply (!toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Et)) a).
  now apply (toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Ep))).
Defined.

Definition weq_on_objects_from_adj_equiv_of_cats (A B : precategory)
   (HA : is_category A) (HB : is_category B) (F : ob [A, B, pr2 HB])
   (HF : adj_equivalence_of_precats F) : weq
          (ob A) (ob B).
Proof.
  exists (pr1 (pr1 F)).
  now apply (@adj_equiv_of_cats_is_weq_of_objects _ _  HA).
Defined.


(** If the source precategory is a category, then being split essentially surjective
     is a proposition *)


Lemma isaprop_sigma_iso (A B : precategory) (HA : is_category A) (*hsB: has_homsets B*)
     (F : functor A B) (HF : fully_faithful F) :
      ∏ b : ob B,
  isaprop (total2 (fun a : ob A => iso (pr1 F a) b)).
Proof.
  intro b.
  apply invproofirrelevance.
  intros x x'.
  destruct x as [a f].
  destruct x' as [a' f'].
  set (fminusf := iso_comp f (iso_inv_from_iso f')).
  set (g := iso_from_fully_faithful_reflection HF fminusf).
  apply (two_arg_paths_f (B:=fun a' => iso ((pr1 F) a') b) (isotoid _ HA g)).
  pathvia (iso_comp (iso_inv_from_iso
    (functor_on_iso F (idtoiso (isotoid _ HA g)))) f).
    generalize (isotoid _ HA g).
    intro p0; destruct p0.
    rewrite <- functor_on_iso_inv.
    rewrite iso_inv_of_iso_id.
    apply eq_iso.
    simpl; rewrite functor_id.
    rewrite id_left.
    apply idpath.
  rewrite idtoiso_isotoid.
  unfold g; clear g.
  unfold fminusf; clear fminusf.
  assert (HFg : functor_on_iso F
        (iso_from_fully_faithful_reflection HF
           (iso_comp f (iso_inv_from_iso f'))) =
           iso_comp f (iso_inv_from_iso f')).
    generalize (iso_comp f (iso_inv_from_iso f')).
    intro h.
    apply eq_iso; simpl.
    set (H3:= homotweqinvweq (weq_from_fully_faithful HF a a')).
    simpl in H3. unfold fully_faithful_inv_hom.
    unfold invweq; simpl.
    rewrite H3; apply idpath.
  rewrite HFg.
  rewrite iso_inv_of_iso_comp.
  apply eq_iso; simpl.
  repeat rewrite <- assoc.
  rewrite iso_after_iso_inv.
  rewrite id_right.
  set (H := iso_inv_iso_inv _ _ _ f').
  now apply (base_paths _ _ H).
Qed.


Lemma isaprop_pi_sigma_iso (A B : precategory) (HA : is_category A) (hsB: has_homsets B)
     (F : ob [A, B, hsB]) (HF : fully_faithful F) :
  isaprop (∏ b : ob B,
             total2 (fun a : ob A => iso (pr1 F a) b)).
Proof.
  apply impred; intro b.
  now apply isaprop_sigma_iso.
Qed.


(** * From full faithfullness and ess surj to equivalence *)

(** A fully faithful and ess. surjective functor induces an
   equivalence of precategories, if the source is a
    category.
*)

Section from_fully_faithful_and_ess_surj_to_equivalence.

Variables A B : precategory.
Hypothesis HA : is_category A.
Variable F : functor A B.
Hypothesis HF : fully_faithful F.
Hypothesis HS : essentially_surjective F.

(** Definition of a functor which will later be the right adjoint. *)

Definition rad_ob : ob B -> ob A.
Proof.
  intro b.
  apply (pr1 (HS b (tpair (fun x => isaprop x) _
               (isaprop_sigma_iso A B HA F HF b)) (fun x => x))).
Defined.

(** Definition of the epsilon transformation *)

Definition rad_eps (b : ob B) : iso (pr1 F (rad_ob b)) b.
Proof.
  apply (pr2 (HS b (tpair (fun x => isaprop x) _
               (isaprop_sigma_iso A B HA F HF b)) (fun x => x))).
Defined.

(** The right adjoint on morphisms *)

Definition rad_mor (b b' : ob B) (g : b --> b') : rad_ob b --> rad_ob b'.
Proof.
  set (epsgebs' := rad_eps b ;; g ;; iso_inv_from_iso (rad_eps b')).
  set (Gg := fully_faithful_inv_hom HF (rad_ob b) _ epsgebs').
  exact Gg.
Defined.

(** Definition of the eta transformation *)

Definition rad_eta (a : ob A) : a --> rad_ob (pr1 F a).
Proof.
  set (epsFa := inv_from_iso (rad_eps (pr1 F a))).
  exact (fully_faithful_inv_hom HF _ _ epsFa).
Defined.

(** Above data specifies a functor *)

Definition rad_functor_data : functor_data B A.
Proof.
  exists rad_ob.
  exact rad_mor.
Defined.

Lemma rad_is_functor : is_functor rad_functor_data.
Proof.
  split. simpl.
  intro b. simpl . unfold rad_mor .  simpl .
  rewrite id_right,
  iso_inv_after_iso,
  fully_faithful_inv_identity.
  apply idpath.

  intros a b c f g. simpl .
  unfold rad_mor; simpl.
  rewrite <- fully_faithful_inv_comp.
  apply maponpaths.
  repeat rewrite <- assoc.
  repeat apply maponpaths.
  rewrite assoc.
  rewrite iso_after_iso_inv, id_left.
  apply idpath.
Qed.

Definition rad : ob [B, A, pr2 HA].
Proof.
  exists rad_functor_data.
  apply rad_is_functor.
Defined.


(** Epsilon is natural *)

Lemma rad_eps_is_nat_trans : is_nat_trans
    (functor_composite rad F) (functor_identity B)
       (fun b => rad_eps b).
Proof.
  unfold is_nat_trans.
  simpl.
  intros b b' g.
  unfold rad_mor; unfold fully_faithful_inv_hom.
  set (H3 := homotweqinvweq (weq_from_fully_faithful HF (pr1 rad b) (pr1 rad b'))).
  simpl in *.
  rewrite H3; clear H3.
  repeat rewrite <- assoc.
  rewrite iso_after_iso_inv, id_right.
  apply idpath.
Qed.

Definition rad_eps_trans : nat_trans _ _ :=
   tpair (is_nat_trans _ _ ) _ rad_eps_is_nat_trans.

(** Eta is natural *)

Ltac inv_functor x y :=
   let H:=fresh in
   set (H:= homotweqinvweq (weq_from_fully_faithful HF x y));
     simpl in H;
     unfold fully_faithful_inv_hom; simpl;
     rewrite H; clear H.

Lemma rad_eta_is_nat_trans : is_nat_trans
         (functor_identity A) (functor_composite F rad)
       (fun a => rad_eta a).
Proof.
  unfold is_nat_trans.
  simpl.
  intros a a' f.
  unfold rad_mor. simpl.
  apply (invmaponpathsweq
          (weq_from_fully_faithful HF a (rad_ob ((pr1 F) a')))).
  simpl; repeat rewrite functor_comp.
  unfold rad_eta.
  set (HHH := rad_eps_is_nat_trans (pr1 F a) (pr1 F a')).
  simpl in HHH; rewrite <- HHH; clear HHH.
  inv_functor a' (rad_ob ((pr1 F) a')).
  inv_functor a (rad_ob ((pr1 F) a)).
  inv_functor (rad_ob (pr1 F a)) (rad_ob ((pr1 F) a')).
  unfold rad_mor. simpl.
  repeat rewrite <- assoc.
  rewrite iso_inv_after_iso.
  rewrite id_right.
  inv_functor (rad_ob (pr1 F a)) (rad_ob ((pr1 F) a')).
  repeat rewrite assoc.
  rewrite iso_after_iso_inv.
  rewrite id_left.
  apply idpath.
Qed.

Definition rad_eta_trans : nat_trans _ _ :=
   tpair (is_nat_trans _ _ ) _ rad_eta_is_nat_trans.


(** The data [rad], [eta], [eps] forms an adjunction *)

Lemma rad_form_adjunction : form_adjunction F rad rad_eta_trans rad_eps_trans.
Proof.
  split; simpl.
  intro a.
  unfold rad_eta.
  inv_functor a (rad_ob (pr1 F a)).
  rewrite iso_after_iso_inv.
  apply idpath.

  intro b.
  apply (invmaponpathsweq
          (weq_from_fully_faithful HF (rad_ob b) (rad_ob b))).
  simpl; rewrite functor_comp.
  unfold rad_eta.
  inv_functor (rad_ob b) (rad_ob (pr1 F (rad_ob b))).
  unfold rad_mor.
  inv_functor (rad_ob (pr1 F (rad_ob b))) (rad_ob b).
  repeat rewrite assoc.
  rewrite iso_after_iso_inv.
  rewrite <- assoc.
  rewrite iso_inv_after_iso.
  rewrite id_left.
  rewrite functor_id.
  apply idpath.
Qed.

Definition rad_are_adjoints : are_adjoints F rad.
Proof.
  exists (dirprodpair rad_eta_trans rad_eps_trans).
  apply rad_form_adjunction.
Defined.

Definition rad_is_left_adjoint : is_left_adjoint F.
Proof.
  exists rad.
  apply rad_are_adjoints.
Defined.

(** Get an equivalence of precategories:

    remains to show that [eta], [eps] are isos
*)

Lemma rad_equivalence_of_precats : adj_equivalence_of_precats F.
Proof.
  exists rad_is_left_adjoint.
  split; simpl.
  intro a.
  unfold rad_eta.
  set (H := fully_faithful_reflects_iso_proof _ _ _ HF
       a (rad_ob ((pr1 F) a))).
  simpl in *.
  set (H' := H (iso_inv_from_iso (rad_eps ((pr1 F) a)))).
  change ((fully_faithful_inv_hom HF a (rad_ob ((pr1 F) a))
     (inv_from_iso (rad_eps ((pr1 F) a))))) with
      (fully_faithful_inv_hom HF a (rad_ob ((pr1 F) a))
     (iso_inv_from_iso (rad_eps ((pr1 F) a)))).
  apply H'.
  intro b. apply (pr2 (rad_eps b)).
Defined.

End from_fully_faithful_and_ess_surj_to_equivalence.


(** * Construction of an adjunction from some partial data (Theorem 2 (iv) of Chapter IV.1 of
      MacLane) *)
Section adjunction_from_partial.

Definition is_universal_arrow_from {D C : precategory}
  (S : functor D C) (c : C) (r : D) (v : C⟦S r, c⟧) : UU :=
  ∏ (d : D) (f : C⟦S d,c⟧), ∃! (f' : D⟦d,r⟧), f = # S f' ;; v.

Variables (X A : precategory) (F : functor X A).
Variables (G0 : ob A -> ob X) (eps : ∏ a, A⟦F (G0 a),a⟧).
Hypothesis (Huniv : ∏ a, is_universal_arrow_from F a (G0 a) (eps a)).

Local Definition G_data : functor_data A X.
Proof.
mkpair.
+ apply G0.
+ intros a b f.
  apply (pr1 (pr1 (Huniv b (G0 a) (eps a ;; f)))).
Defined.

Local Definition G_is_functor : is_functor G_data.
Proof.
split.
+ intro a; simpl.
  assert (H : eps a ;; identity a = # F (identity (G0 a)) ;; eps a).
  { now rewrite functor_id, id_left, id_right. }
  set (H2 := Huniv a (G0 a) (eps a ;; identity a)).
  apply (pathsinv0 (maponpaths pr1 (pr2 H2 (_,,H)))).
+ intros a b c f g; simpl.
  set (H2 := Huniv c (G0 a) (eps a ;; (f ;; g))).
  destruct H2 as [[fac Hfac] p]; simpl.
  set (H1 := Huniv b (G0 a) (eps a ;; f)).
  destruct H1 as [[fab Hfab] p1]; simpl.
  set (H0 := Huniv c (G0 b) (eps b ;; g)).
  destruct H0 as [[fbc Hfbc] p2]; simpl.
  assert (H : eps a ;; (f ;; g) = # F (fab ;; fbc) ;; eps c).
  { now rewrite assoc, Hfab, <- assoc, Hfbc, assoc, <- functor_comp. }
  apply (pathsinv0 (maponpaths pr1 (p (_,,H)))).
Qed.

Local Definition G : functor A X := tpair _ G_data G_is_functor.

Local Definition unit : nat_trans (functor_identity X) (functor_composite F G).
Proof.
 mkpair.
* intro x.
  apply (pr1 (pr1 (Huniv (F x) x (identity _)))).
* abstract (intros x y f; simpl;
            destruct (Huniv (F y) y (identity (F y))) as [t p], t as [t p0]; simpl;
            destruct (Huniv (F x) x (identity (F x))) as [t0 p1], t0 as [t0 p2]; simpl;
            destruct (Huniv (F y) (G0 (F x)) (eps (F x) ;; # F f)) as [t1 p3], t1 as [t1 p4]; simpl;
            assert (H1 : # F f = # F (t0 ;; t1) ;; eps (F y));
            [now rewrite functor_comp, <- assoc, <- p4, assoc, <- p2, id_left|];
            destruct (Huniv (F y) x (# F f)) as [t2 p5];
            set (HH := (maponpaths pr1 (p5 (_,,H1))));
            simpl in HH; rewrite HH;
            assert (H2 : # F f = # F (f ;; t) ;; eps (F y));
            [now rewrite functor_comp, <- assoc, <- p0, id_right|];
            set (HHH := (maponpaths pr1 (p5 (_,,H2)))); simpl in HHH;
            now rewrite HHH).
Defined.

Local Definition counit :  nat_trans (functor_composite G F) (functor_identity A).
Proof.
mkpair.
* apply eps.
* abstract (intros a b f; simpl; apply (pathsinv0 (pr2 (pr1 (Huniv b (G0 a) (eps a ;; f)))))).
Defined.

Local Lemma form_adjunctionFG : form_adjunction F G unit counit.
Proof.
mkpair; simpl.
+ intros x.
  destruct (Huniv (F x) x (identity (F x))) as [[f hf] H]; simpl.
  now rewrite hf.
+ intros a; simpl.
  destruct (Huniv (F (G0 a)) (G0 a) (identity (F (G0 a)))) as [[f hf] H]; simpl.
  destruct ((Huniv a (G0 (F (G0 a))) (eps (F (G0 a)) ;; eps a))) as [[g hg] Hg]; simpl.
  destruct (Huniv _ _ (eps a)) as [t p].
  assert (H1 : eps a = # F (identity _) ;; eps a).
    now rewrite functor_id, id_left.
  assert (H2 : eps a = # F (f ;; g) ;; eps a).
    now rewrite functor_comp, <- assoc, <- hg, assoc, <- hf, id_left.
  set (HH := maponpaths pr1 (p (_,,H1))); simpl in HH.
  set (HHH := maponpaths pr1 (p (_,,H2))); simpl in HHH.
  now rewrite HHH, <- HH.
Qed.

Definition left_adjoint_from_partial : is_left_adjoint F := (G,, (unit,, counit),, form_adjunctionFG).
Definition right_adjoint_from_partial : is_right_adjoint G := (F,, (unit,, counit),, form_adjunctionFG).

End adjunction_from_partial.

(** * Post-composition with a left adjoint is a left adjoint *)
Section postcomp.

Context {C D E : precategory} (hsD : has_homsets D) (hsE : has_homsets E)
        (F : functor D E) (HF : is_left_adjoint F).

Let G : functor E D := right_adjoint HF.
Let H : are_adjoints F G := pr2 HF.
Let η : nat_trans (functor_identity D) (functor_composite F G):= unit_from_left_adjoint H.
Let ε : nat_trans (functor_composite G F) (functor_identity E) := counit_from_left_adjoint H.
Let H1 : ∏ a : D, # F (η a) ;; ε (F a) = identity (F a) := triangle_id_left_ad H.
Let H2 : ∏ b : E, η (G b) ;; # G (ε b) = identity (G b) := triangle_id_right_ad H.

Lemma is_left_adjoint_post_composition_functor :
  is_left_adjoint (post_composition_functor C D E hsD hsE F).
Proof.
exists (post_composition_functor _ _ _ _ _ G).
mkpair.
- split.
  + use mk_nat_trans.
    * simpl; intros F'.
      apply (nat_trans_comp _ _ _
              (nat_trans_comp _ _ _ (nat_trans_functor_id_right_inv F') (pre_whisker F' η))
              (nat_trans_functor_assoc_inv _ _ _)).
    * abstract (intros F1 F2 α; apply (nat_trans_eq hsD); intro c; simpl in *;
                now rewrite !id_right, !id_left; apply (nat_trans_ax η (F1 c) _ (α c))).
  + use mk_nat_trans.
    * simpl; intros F'.
      apply (nat_trans_comp _ _ _
              (nat_trans_functor_assoc _ _ _)
              (nat_trans_comp _ _ _ (pre_whisker F' ε) (nat_trans_functor_id_left _))).
  * abstract (intros F1 F2 α; apply (nat_trans_eq hsE); intro c; simpl in *;
              now rewrite !id_right, !id_left; apply (nat_trans_ax ε _ _ (α c))).
- abstract (split; simpl; intro F';
    [ apply (nat_trans_eq hsE); simpl; intro c;
      now rewrite !id_left, !id_right; apply H1
    | apply (nat_trans_eq hsD); simpl; intro c;
      now rewrite !id_left, !id_right; apply H2]).
Defined.

End postcomp.

End adjunctions.