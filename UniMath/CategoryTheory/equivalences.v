(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman
january 2013

************************************************************)


(** **********************************************************

Contents:

- Definition of equivalence of precategories
- Equivalence of categories yields weak equivalence of object types
- A fully faithful and ess. surjective functor induces equivalence of precategories, if the source is a category.

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).


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

(** * Identity functor is an adjoint equivalence *)

Lemma identity_functor_is_adj_equivalence {A : precategory} :
  adj_equivalence_of_precats (functor_identity A).
Proof.
  mkpair.
  - exact is_left_adjoint_functor_identity.
  - now split; intros a; apply identity_is_iso.
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
  - intro a.
    cbn; unfold rad_eta.
    inv_functor a (rad_ob (pr1 F a)).
    apply iso_after_iso_inv.
  - intro b.
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
