(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman
january 2013

************************************************************)


(** **********************************************************

Contents:

- Definition of equivalence of precategories
- Equivalence of categories yields weak equivalence of object types
- A fully faithful and ess. surjective functor induces equivalence of precategories, if the source is a univalent_category.

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.

Local Open Scope cat.

(** * Sloppy equivalence of (pre)categories *)

Definition forms_equivalence {A B : precategory} (X : adjunction_data A B)
  (η := adjunit X) (ε := adjcounit X) : UU
  := (∏ a, is_iso (η a)) × (∏ b, is_iso (ε b)).

Definition equivalence_of_precats (A B : precategory) : UU
  := ∑ (X : adjunction_data A B), forms_equivalence X.

Coercion adjunction_data_from_equivalence_of_precats {A B}
         (X : equivalence_of_precats A B) : adjunction_data A B := pr1 X.

(** * Equivalence of (pre)categories *)

Definition adj_equivalence_of_precats {A B : precategory} (F : functor A B) : UU :=
   ∑ (H : is_left_adjoint F), forms_equivalence H.

Definition adj_from_equiv (D1 D2 : precategory) (F : functor D1 D2):
    adj_equivalence_of_precats F → is_left_adjoint F := λ x, pr1 x.
Coercion adj_from_equiv : adj_equivalence_of_precats >-> is_left_adjoint.

Definition mk_adj_equivalence_of_precats {A B : precategory} (F : functor A B)
           (G : functor B A) η ε
           (H1 : form_adjunction F G η ε)
           (H2 : forms_equivalence ((F,,G,,η,,ε)))
  : adj_equivalence_of_precats F.
Proof.
  use tpair.
  - exists G. exists (η,,ε). apply H1.
  - apply H2.
Defined.

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

(** * Adjointification of a sloppy equivalence *)


(** ** One triangle equality is enough *)

(** Proof ported from Peter Lumsdaine's proof of the analog for displayed categories
    see UniMath/TypeTheory
*)
Lemma triangle_2_from_1 {C D}
  (A : adjunction_data C D)
  (E : forms_equivalence A)
: triangle_1_statement A -> triangle_2_statement A.
Proof.
  destruct A as [F [G [η ε]]].
  destruct E as [Hη Hε]; cbn in Hη, Hε.
  unfold triangle_1_statement, triangle_2_statement; cbn.
  intros T1 x.
  assert (etaH := nat_trans_ax η); cbn in etaH.
  assert (epsH := nat_trans_ax ε); cbn in epsH.

  (* Algebraically, this goes as follows:
  η G ; G ε
  = G ε^ ; η^ G ; η G ; G ε ; η G ; G ε          [by inverses, 1]
  = G ε^ ; η^ G ; η G ; η G F G ; G F G ε ; G ε  [by naturality, 2]
  = G ε^ ; η^ G ; η G ; η G F G ; G ε F G ; G ε  [by naturality, 3]
  = G ε^ ; η^ G ; η G ; G F η G ; G ε F G ; G ε  [by naturality, 4]
  = G ε^ ; η^ G ; η G ; G (F η ; ε F ) G ; G ε   [by functoriality, 5]
  = G ε^ ; η^ G ; η G ; G ε                      [by T1, 6]
  = 1                                            [by inverses, 7]
*)

  apply (invmaponpathsweq (weqpair _ (iso_comp_left_isweq (isopair _ (Hη _ )) _ ))).
  cbn.
  apply pathsinv0. etrans. apply id_left. etrans. apply (! id_right _ ).
  apply pathsinv0.
  apply (iso_inv_to_left _ _ _ _  (isopair _ (Hη _ ))).
  apply (invmaponpathsweq (weqpair _ (iso_comp_left_isweq (functor_on_iso G (isopair _ (Hε _ ))) _ ))).
  cbn.
  set (XR := functor_on_iso_is_iso _ _ G _ _ (isopair _ (Hε x))).
  set (XR' := isopair (#G (ε x)) XR). cbn in XR'.
  apply pathsinv0. etrans. apply id_left. etrans. apply (! id_right _ ).
  apply pathsinv0.
  apply (iso_inv_to_left _ _ _  _ XR').
  unfold XR', XR; clear XR' XR.

  repeat rewrite assoc.
  match goal with |[ |- ?i1 · ?i2 · _ · _ · _ · _ = _ ] =>
                   set (i := i1); set (i':= i2) end.

  etrans. apply cancel_postcomposition. repeat rewrite <- assoc.
          rewrite etaH. apply idpath.
  etrans. repeat rewrite <- assoc. rewrite <- functor_comp.
          rewrite (epsH). rewrite functor_comp. apply idpath.
  etrans. apply maponpaths. apply maponpaths. repeat rewrite assoc. rewrite etaH.
          apply cancel_postcomposition. rewrite <- assoc. rewrite <- functor_comp.
          rewrite T1. rewrite functor_id. apply id_right.
  etrans. apply maponpaths. rewrite assoc. apply cancel_postcomposition.
          use (iso_after_iso_inv (isopair _ (Hη _ ))).
  rewrite id_left.
  apply (iso_after_iso_inv ).
Defined.


(** ** Adjointification *)

Section adjointification.

Context {C D : category} (E : equivalence_of_precats C D).
Let F : functor C D := left_functor E.
Let G : functor D C := right_functor E.

Let ηntiso : iso (C:= [C,C,homset_property _ ]) (functor_identity _ ) (F ∙ G).
Proof.
  use functor_iso_from_pointwise_iso.
  use (adjunit E).
  apply (pr1 (pr2 E)).
Defined.

Let εntiso : iso (C:= [D,D,homset_property _ ]) (G ∙ F) (functor_identity _ ).
Proof.
  use functor_iso_from_pointwise_iso.
  use (adjcounit E).
  apply (pr2 (pr2 E)).
Defined.

Let FF : functor [D,D,homset_property _ ] [C, D, homset_property _ ]
  := (pre_composition_functor _ _ _ (homset_property _ ) (homset_property _ ) F).

Let GG : functor [C,D,homset_property _ ] [D, D, homset_property _ ]
  := (pre_composition_functor _ _ _ (homset_property _ ) (homset_property _ ) G).


Definition ε'ntiso : iso (C:= [D,D,homset_property _ ]) (G ∙ F) (functor_identity _ ).
Proof.
  eapply iso_comp.
    set (XR := functor_on_iso GG (functor_on_iso FF εntiso)).
    set (XR':= iso_inv_from_iso XR). apply XR'.
  eapply iso_comp.
     Focus 2. apply εntiso.
  set (XR := functor_on_iso (pre_composition_functor _ _ _ (homset_property _) (homset_property _ ) G) (iso_inv_from_iso ηntiso)).
  set (XR':= functor_on_iso (post_composition_functor _ _ _ (homset_property _ )(homset_property _ ) F) XR).
  apply XR'.
Defined.


Definition adjointification_triangle_1
  : triangle_1_statement (F,,G,,pr1 ηntiso,,pr1 ε'ntiso).
Proof.
  intro x. cbn. rewrite id_right. rewrite id_right. rewrite id_right. rewrite id_right.
              repeat rewrite assoc.
  assert (ηinvH := nat_trans_ax (inv_from_iso ηntiso)).
  cbn in ηinvH. simpl in ηinvH.
  assert (εinvH := nat_trans_ax (inv_from_iso εntiso)).
  cbn in εinvH. simpl in εinvH.
  etrans. apply cancel_postcomposition. apply cancel_postcomposition.
          etrans. apply maponpaths. apply (! (id_right _ )).
          apply εinvH.
          rewrite id_right.
  repeat rewrite assoc. rewrite assoc4.
  apply id_conjugation.
  - etrans. eapply pathsinv0. apply functor_comp.
    etrans. apply maponpaths. etrans. apply maponpaths. eapply pathsinv0. apply id_right.
            apply ηinvH.
    etrans. apply maponpaths.
    apply (nat_trans_inv_pointwise_inv_before _ _ _ _ _ ηntiso (pr2 ηntiso)).
    apply functor_id.
  - assert (XR := nat_trans_inv_pointwise_inv_before _ _ _ _ _ εntiso (pr2 εntiso)).
    cbn in XR.
    etrans. apply cancel_postcomposition. eapply pathsinv0. apply id_right. apply XR.
Qed.

Lemma adjointification_forms_equivalence :
  forms_equivalence (F,, G,, pr1 ηntiso,, pr1 ε'ntiso).
Proof.
  split.
  - cbn. apply (is_functor_iso_pointwise_if_iso _ _ _ _ _ ηntiso (pr2 ηntiso)).
  - cbn. apply (is_functor_iso_pointwise_if_iso _ _ _ _ _ ε'ntiso (pr2 ε'ntiso)).
Qed.

Definition adjointification_triangle_2
  : triangle_2_statement (F,,G,,pr1 ηntiso,,pr1 ε'ntiso).
Proof.
  use triangle_2_from_1.
  - apply adjointification_forms_equivalence.
  - apply adjointification_triangle_1.
Qed.

Definition adjointificiation : adj_equivalence_of_precats F.
Proof.
  use mk_adj_equivalence_of_precats.
  - exact G.
  - apply ηntiso.
  - apply ε'ntiso.
  - exists adjointification_triangle_1.
    apply adjointification_triangle_2.
  - apply adjointification_forms_equivalence.
Defined.

End adjointification.

(** * Identity functor is an adjoint equivalence *)

Lemma identity_functor_is_adj_equivalence {A : precategory} :
  adj_equivalence_of_precats (functor_identity A).
Proof.
  use tpair.
  - exact is_left_adjoint_functor_identity.
  - now split; intros a; apply identity_is_iso.
Defined.

(** * Equivalence of categories yields equivalence of object types *)
(**  Fundamentally needed that both source and target are categories *)

Lemma adj_equiv_of_cats_is_weq_of_objects (A B : precategory)
   (HA : is_univalent A) (HB : is_univalent B) (F : [A, B, pr2 HB ])
   (HF : adj_equivalence_of_precats F) : isweq (pr1 (pr1 F)).
Proof.
  set (G := right_adjoint (pr1 HF)).
  set (et := unit_iso_from_adj_equivalence_of_precats (pr2 HA)  HF).
  set (ep := counit_iso_from_adj_equivalence_of_precats _ HF).
  set (AAcat := is_univalent_functor_category A _ HA).
  set (BBcat := is_univalent_functor_category B _ HB).
  set (Et := isotoid _ AAcat et).
  set (Ep := isotoid _ BBcat ep).
  apply (gradth _ (λ b, pr1 (right_adjoint (pr1 HF)) b)); intro a.
  apply (!toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Et)) a).
  now apply (toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Ep))).
Defined.

Definition weq_on_objects_from_adj_equiv_of_cats (A B : precategory)
   (HA : is_univalent A) (HB : is_univalent B) (F : ob [A, B, pr2 HB])
   (HF : adj_equivalence_of_precats F) : weq
          (ob A) (ob B).
Proof.
  exists (pr1 (pr1 F)).
  now apply (@adj_equiv_of_cats_is_weq_of_objects _ _  HA).
Defined.


(** If the source precategory is a univalent_category, then being split essentially surjective
     is a proposition *)


Lemma isaprop_sigma_iso (A B : precategory) (HA : is_univalent A) (*hsB: has_homsets B*)
     (F : functor A B) (HF : fully_faithful F) :
      ∏ b : ob B,
  isaprop (total2 (λ a : ob A, iso (pr1 F a) b)).
Proof.
  intro b.
  apply invproofirrelevance.
  intros x x'.
  destruct x as [a f].
  destruct x' as [a' f'].
  set (fminusf := iso_comp f (iso_inv_from_iso f')).
  set (g := iso_from_fully_faithful_reflection HF fminusf).
  apply (two_arg_paths_f (B:=λ a', iso ((pr1 F) a') b) (isotoid _ HA g)).
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


Lemma isaprop_pi_sigma_iso (A B : precategory) (HA : is_univalent A) (hsB: has_homsets B)
     (F : ob [A, B, hsB]) (HF : fully_faithful F) :
  isaprop (∏ b : ob B,
             total2 (λ a : ob A, iso (pr1 F a) b)).
Proof.
  apply impred; intro b.
  now apply isaprop_sigma_iso.
Qed.


(** * From full faithfullness and ess surj to equivalence *)

(** A fully faithful and ess. surjective functor induces an
   equivalence of precategories, if the source is a
    univalent_category.
*)

Section from_fully_faithful_and_ess_surj_to_equivalence.

Variables A B : precategory.
Hypothesis HA : is_univalent A.
Variable F : functor A B.
Hypothesis HF : fully_faithful F.
Hypothesis HS : essentially_surjective F.

(** Definition of a functor which will later be the right adjoint. *)

Definition rad_ob : ob B -> ob A.
Proof.
  intro b.
  apply (pr1 (HS b (tpair (λ x, isaprop x) _
               (isaprop_sigma_iso A B HA F HF b)) (λ x, x))).
Defined.

(** Definition of the epsilon transformation *)

Definition rad_eps (b : ob B) : iso (pr1 F (rad_ob b)) b.
Proof.
  apply (pr2 (HS b (tpair (λ x, isaprop x) _
               (isaprop_sigma_iso A B HA F HF b)) (λ x, x))).
Defined.

(** The right adjoint on morphisms *)

Definition rad_mor (b b' : ob B) (g : b --> b') : rad_ob b --> rad_ob b'.
Proof.
  set (epsgebs' := rad_eps b · g · iso_inv_from_iso (rad_eps b')).
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
       (λ b, rad_eps b).
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
       (λ a, rad_eta a).
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
  - intro a. cbn.
    unfold rad_eta.
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
