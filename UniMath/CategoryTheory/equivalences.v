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

************************************************************)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
(* Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g"). *)
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Arguments functor_composite {_ _ _} _ _ .


(** * Adjunction *)

Definition form_adjunction {A B : precategory}
       (F : functor A B) (G : functor B A)
       (eta : nat_trans (functor_identity A) (functor_composite F G))
       (eps : nat_trans (functor_composite G F) (functor_identity B)) : UU :=
dirprod
  (Π a : ob A,
       #F (eta a) ;; eps (F a) = identity (F a))
  (Π b : ob B,
       eta (G b) ;; #G (eps b) = identity (G b)).


Definition are_adjoints {A B : precategory}
   (F : functor A B)  (G : functor B A) : UU :=
  total2 (fun etaeps : dirprod
            (nat_trans (functor_identity A) (functor_composite F G))
            (nat_trans (functor_composite G F) (functor_identity B)) =>
      form_adjunction  F G (pr1 etaeps) (pr2 etaeps)).


Definition is_left_adjoint {A B : precategory}
  (F : functor A B) : UU :=
   total2 (fun G : functor B A => are_adjoints F G).


Definition right_adjoint {A B : precategory}
  {F : functor A B} (H : is_left_adjoint F) : functor B A := pr1 H.


Definition unit_from_left_adjoint {A B : precategory}
   {F : functor A B}  (H : is_left_adjoint F) :
  nat_trans (functor_identity A) (functor_composite F (right_adjoint H))
  := pr1 (pr1 (pr2 H)).


Definition counit_from_left_adjoint {A B : precategory}
  {F : functor A B}   (H : is_left_adjoint F)  :
 nat_trans (functor_composite (right_adjoint H) F) (functor_identity B)
   := pr2 (pr1 (pr2 H)).


Definition triangle_id_left_ad (A B : precategory)
  (F : functor A B) (H : is_left_adjoint F) :
  Π (a : ob A),
       #F (unit_from_left_adjoint H a);;
       counit_from_left_adjoint H (F a)
       =
      identity (F a)
   := pr1 (pr2 (pr2 H)).

Definition triangle_id_right_ad (A B : precategory)
   (F : functor A B)  (H : is_left_adjoint F) :
  Π b : ob B,
         unit_from_left_adjoint H (right_adjoint H b);;
        #(right_adjoint H) (counit_from_left_adjoint H b) =
        identity (right_adjoint H b)
  := pr2 (pr2 (pr2 H)).

(** * Equivalence of (pre)categories *)

Definition adj_equivalence_of_precats {A B : precategory}
  (F : functor A B) : UU :=
   total2 (fun H : is_left_adjoint F =>
     dirprod (Π a, is_isomorphism
                    (unit_from_left_adjoint H a))
             (Π b, is_isomorphism
                    (counit_from_left_adjoint H b))
             ).

Definition adj_equivalence_inv {A B : precategory}
  {F : functor A B} (HF : adj_equivalence_of_precats F) : functor B A :=
    right_adjoint (pr1 HF).

Local Notation "HF ^^-1" := (adj_equivalence_inv  HF)(at level 3).

Definition unit_pointwise_iso_from_adj_equivalence {A B : precategory}
   {F : functor A B} (HF : adj_equivalence_of_precats F) :
    Π a, iso a (HF^^-1 (F a)).
  intro a.
  exists (unit_from_left_adjoint (pr1 HF) a).
  exact (pr1 (pr2 HF) a).
Defined.

Definition counit_pointwise_iso_from_adj_equivalence {A B : precategory}
  {F : functor A B} (HF : adj_equivalence_of_precats F) :
    Π b, iso (F (HF^^-1 b)) b.
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
  use tpair.
  - use tpair.
    + exact (functor_identity A).
    + unfold are_adjoints.
      use tpair.
        exact (dirprodpair (nat_trans_id _) (nat_trans_id _)).
        split. intros a. rewrite id_left. reflexivity.
               intros a. rewrite id_left. reflexivity.
  - split. intros a. unfold is_isomorphism. apply identity_is_iso.
           intros a. unfold is_isomorphism. apply identity_is_iso.
Defined.

(** * Equivalence of categories yields equivalence of object types *)
(**  Fundamentally needed that both source and target are categories *)

Lemma adj_equiv_of_cats_is_weq_of_objects (A B : precategory)
   (HA : is_category A) (HB : is_category B) (F : ob [A, B, pr2 HB ])
   (HF : adj_equivalence_of_precats F) : isweq (pr1 (pr1 F)).
Proof.
  set (G := right_adjoint (pr1 HF)).
  set (et := unit_iso_from_adj_equivalence_of_precats (pr2 HA)  HF).
  set (ep := counit_iso_from_adj_equivalence_of_precats _ HF).
  set (AAcat := is_category_functor_category A _ HA).
  set (BBcat := is_category_functor_category B _ HB).
  set (Et := isotoid _ AAcat et).
  set (Ep := isotoid _ BBcat ep).
  apply (gradth _ (fun b => pr1 (right_adjoint (pr1 HF)) b)).
  intro a.
  set (ou := toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Et)) a).
  simpl in ou.
  apply (! ou).
  intro y.
  set (ou := toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Ep)) y).
  apply ou.
Defined.

Definition weq_on_objects_from_adj_equiv_of_cats (A B : precategory)
   (HA : is_category A) (HB : is_category B) (F : ob [A, B, pr2 HB])
   (HF : adj_equivalence_of_precats F) : weq
          (ob A) (ob B).
Proof.
  exists (pr1 (pr1 F)).
  apply (@adj_equiv_of_cats_is_weq_of_objects _ _  HA); assumption.
Defined.


(** If the source precategory is a category, then being split essentially surjective
     is a proposition *)


Lemma isaprop_sigma_iso (A B : precategory) (HA : is_category A) (*hsB: has_homsets B*)
     (F : functor A B) (HF : fully_faithful F) :
      Π b : ob B,
  isaprop (total2 (fun a : ob A => iso (pr1 F a) b)).
Proof.
  intro b.
  apply invproofirrelevance.
  intros x x'.
  destruct x as [a f].
  destruct x' as [a' f'].
  set (fminusf := iso_comp f (iso_inv_from_iso f')).
  set (g := iso_from_fully_faithful_reflection HF fminusf).
  apply (total2_paths2 (B:=fun a' => iso ((pr1 F) a') b) (isotoid _ HA g)).
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
  set (h':= base_paths _ _ H).
  assumption.
Qed.


Lemma isaprop_pi_sigma_iso (A B : precategory) (HA : is_category A) (hsB: has_homsets B)
     (F : ob [A, B, hsB]) (HF : fully_faithful F) :
  isaprop (Π b : ob B,
             total2 (fun a : ob A => iso (pr1 F a) b)).
Proof.
  apply impred.
  intro b.
  apply isaprop_sigma_iso; assumption.
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
  Π (d : D) (f : C⟦S d,c⟧), ∃! (f' : D⟦d,r⟧), f = # S f' ;; v.

Variables (X A : precategory) (F : functor X A).
Variables (G0 : ob A -> ob X) (eps : Π a, A⟦F (G0 a),a⟧).
Hypothesis (Huniv : Π a, is_universal_arrow_from F a (G0 a) (eps a)).

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

Definition adjunction_from_partial : is_left_adjoint F := (G,, (unit,, counit),, form_adjunctionFG).

End adjunction_from_partial.
