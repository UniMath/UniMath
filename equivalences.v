(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman
january 2013


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


Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
Local Notation "f ;; g" := (compose f g)(at level 50).
Notation "[ C , D ]" := (functor_precategory C D).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Definition functor_composite (A B C : precategory) (F : ob [A, B])
      (G : ob [B , C]) : ob [A , C] := 
   functor_composite _ _ _ F G.

Notation "G 'O' F" := (functor_composite _ _ _ F G) (at level 25).

(** * Adjunction *)


Definition form_adjunction (A B : precategory) (F : ob [A, B])
       (G : ob [B, A]) 
       (eta : nat_trans (functor_identity A) (pr1 (G O F)))  
       (eps : nat_trans (pr1 (F O G)) (functor_identity B)) : UU :=
dirprod 
  (forall a : ob A,
       # (pr1 F) (pr1 eta a) ;;   pr1 eps (pr1 F a) == identity (pr1 F a))
  (forall b : ob B,
       pr1 eta (pr1 G b) ;; # (pr1 G) (pr1 eps b) == identity (pr1 G b)).

Definition are_adjoints (A B : precategory) (F : ob [A, B])
    (G : ob [B, A]) : UU :=
  total2 (fun etaeps : dirprod 
            (nat_trans (functor_identity A) (pr1 (G O F)))
            (nat_trans (pr1 (F O G)) (functor_identity B)) =>
      form_adjunction A B F G (pr1 etaeps) (pr2 etaeps)).

Definition is_left_adjoint (A B : precategory) (F : ob [A, B]) : UU :=
   total2 (fun G : ob [B, A] => are_adjoints A B F G).

Definition right_adjoint (A B : precategory) (F : ob [A, B]) 
      (H : is_left_adjoint _ _ F) : ob [B, A] := pr1 H.

Definition eta_from_left_adjoint (A B : precategory) (F : ob [A, B]) 
      (H : is_left_adjoint _ _ F) : 
  nat_trans (functor_identity A) (pr1 (pr1 H O F)) := pr1 (pr1 (pr2 H)).


Definition eps_from_left_adjoint (A B : precategory) (F : ob [A, B]) 
      (H : is_left_adjoint _ _ F)  : 
 nat_trans (pr1 (F O pr1 H)) (functor_identity B)
   := pr2 (pr1 (pr2 H)).


Definition triangle_id_left_ad (A B : precategory) (F : ob [A, B]) 
      (H : is_left_adjoint _ _ F) :
  forall (a : ob A),
       #(pr1 F) (pr1 (pr1 (pr1 (pr2 H))) a);;
       pr1 (pr2 (pr1 (pr2 H))) ((pr1 F) a) ==
       identity ((pr1 F) a) := pr1 (pr2 (pr2 H)).

Definition triangle_id_right_ad (A B : precategory) (F : ob [A, B]) 
      (H : is_left_adjoint _ _ F) :
  forall b : ob B,
        pr1 (pr1 (pr1 (pr2 H))) ((pr1 (pr1 H)) b);;
        #(pr1 (pr1 H)) (pr1 (pr2 (pr1 (pr2 H))) b) ==
        identity ((pr1 (pr1 H)) b) := pr2 (pr2 (pr2 H)).

(** * Equivalence of (pre)categories *)

Definition equivalence_of_precats (A B : precategory)(F : ob [A, B]) : UU :=
   total2 (fun H : is_left_adjoint _ _ F =>
     dirprod (forall a, is_isomorphism 
                    (eta_from_left_adjoint A B F H a))
             (forall b, is_isomorphism
                    (eps_from_left_adjoint A B F H b))
             ).


Definition eta_iso_from_equivalence_of_precats (A B : precategory)
  (F : ob [A, B]) (HF : equivalence_of_precats _ _ F) : 
       iso (C:=[A, A]) (functor_identity A) 
                              (right_adjoint _ _ _ (pr1 HF) O F).
Proof.
  exists (eta_from_left_adjoint _ _ _ (pr1 HF)).
  apply functor_iso_if_pointwise_iso.
  apply (pr1 (pr2 HF)).
Defined.

Definition eps_iso_from_equivalence_of_precats (A B : precategory)
  (F : ob [A, B]) (HF : equivalence_of_precats _ _ F) : 
       iso (C:=[B, B]) (F O right_adjoint _ _ _ (pr1 HF))
                (functor_identity B).
Proof.
  exists (eps_from_left_adjoint _ _ _ (pr1 HF)).
  apply functor_iso_if_pointwise_iso.
  apply (pr2 (pr2 HF)).
Defined.


(** * Equivalence of categories yields equivalence of object types *)
(**  Fundamentally needed that both source and target are categories *)

Lemma equiv_of_cats_is_weq_of_objects (A B : precategory)
   (HA : is_category A) (HB : is_category B) (F : ob [A, B])
   (HF : equivalence_of_precats A B F) : 
     isweq (pr1 (pr1 F)).
Proof.
  set (G := right_adjoint _ _ _ (pr1 HF)).
  set (et := eta_iso_from_equivalence_of_precats _ _ _ HF).
  set (ep := eps_iso_from_equivalence_of_precats _ _ _ HF).
  set (AAcat := is_category_functor_category A _ HA).
  set (BBcat := is_category_functor_category B _ HB).
  set (Et := isotoid _ AAcat et).
  set (Ep := isotoid _ BBcat ep).
  apply (gradth _ (fun b => pr1 (right_adjoint A B F (pr1 HF)) b)).
  intro a.
  set (ou := toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Et)) a).
  simpl in ou.
  apply (! ou).
  intro y.
  set (ou := toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Ep)) y).
  apply ou.
Defined.

Definition weq_on_objects_from_equiv_of_cats (A B : precategory)
   (HA : is_category A) (HB : is_category B) (F : ob [A, B])
   (HF : equivalence_of_precats A B F) : weq 
          (ob A) (ob B).
Proof.
  exists (pr1 (pr1 F)).
  apply equiv_of_cats_is_weq_of_objects; assumption.
Defined.

   
(** If the source precategory is a category, then being split essentially surjective 
     is a proposition *)


Lemma isaprop_sigma_iso (A B : precategory) (HA : is_category A)
     (F : ob [A, B]) (HF : fully_faithful F) :
      forall b : ob B,
  isaprop (total2 (fun a : ob A => iso (pr1 F a) b)).
Proof.
  intro b.
  apply invproofirrelevance.
  intros x x'.
  destruct x as [a f].
  destruct x' as [a' f'].
  set (fminusf := iso_comp f (iso_inv_from_iso f')).
  set (g := iso_from_fully_faithful_reflection HF _ _ fminusf).
  apply (total2_paths2 (B:=fun a' => iso ((pr1 F) a') b) (isotoid _ HA g)).
  pathvia (iso_comp (iso_inv_from_iso 
    (functor_on_iso _ _ F _ _ (idtoiso (isotoid _ HA g)))) f).
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
  assert (HFg : functor_on_iso A B F a a'
        (iso_from_fully_faithful_reflection HF a a'
           (iso_comp f (iso_inv_from_iso f'))) == 
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


Lemma isaprop_pi_sigma_iso (A B : precategory) (HA : is_category A)
     (F : ob [A, B]) (HF : fully_faithful F) :
  isaprop (forall b : ob B, 
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
Variable F : ob [A, B].
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
  split; simpl.
  intro b.
  unfold rad_mor; simpl.
  rewrite id_right,
    iso_inv_after_iso,
    fully_faithful_inv_identity.
  apply idpath.
  
  intros a b c f g.
  unfold rad_mor; simpl.
  rewrite <- fully_faithful_inv_comp.
  apply maponpaths.
  repeat rewrite <- assoc.
  repeat apply maponpaths.
  rewrite assoc.
  rewrite iso_after_iso_inv, id_left.
  apply idpath.
Qed.

Definition rad : ob [B, A].
Proof.
  exists rad_functor_data.
  apply rad_is_functor.
Defined.


(** Epsilon is natural *)

Lemma rad_eps_is_nat_trans : is_nat_trans 
    (pr1 (F O rad)) (functor_identity B)
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
   tpair _ _ rad_eps_is_nat_trans.

(** Eta is natural *)

Ltac inv_functor x y :=
   let H:=fresh in 
   set (H:= homotweqinvweq (weq_from_fully_faithful HF x y));
     simpl in H;
     unfold fully_faithful_inv_hom; simpl;
     rewrite H; clear H.

Lemma rad_eta_is_nat_trans : is_nat_trans 
         (functor_identity A) (pr1 (rad O F)) 
       (fun a => rad_eta a).
Proof.
  unfold is_nat_trans.
  simpl.
  intros a a' f.
  unfold rad_mor. simpl.
  apply (equal_transport_along_weq _ _ 
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
   tpair _ _ rad_eta_is_nat_trans.


(** The data [rad], [eta], [eps] forms an adjunction *)

Lemma rad_form_adjunction : form_adjunction A B F rad rad_eta_trans rad_eps_trans.
Proof.
  split; simpl.
  intro a.
  unfold rad_eta.
  inv_functor a (rad_ob (pr1 F a)).
  rewrite iso_after_iso_inv.
  apply idpath.

  intro b.  
  apply (equal_transport_along_weq _ _ 
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
  
Definition rad_are_adjoints : are_adjoints _ _ F rad.
Proof.
  exists (dirprodpair rad_eta_trans rad_eps_trans).
  apply rad_form_adjunction.
Defined.

Definition rad_is_left_adjoint : is_left_adjoint _ _ F.
Proof.
  exists rad.
  apply rad_are_adjoints.
Defined.

(** Get an equivalence of precategories:

    remains to show that [eta], [eps] are isos
*)

Lemma rad_equivalence_of_precats : equivalence_of_precats _ _ F.
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

 
