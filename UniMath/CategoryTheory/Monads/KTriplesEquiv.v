(* ============================================================================================= *)
(* * Equivalence of category between Kleisli monads and multiplicative monads.                   *)
(*                                                                                               *)
(* Contents:                                                                                     *)
(*   - kleislification (functor from multiplicative monads to Kleisli monads).                   *)
(*   - unkleislification (functor from Kleisli monads to multiplicative monads).                 *)
(*   - kleislification/unkleislification is an equivalence of categories.                        *)
(*                                                                                               *)
(* Written by: Marco Maggesi, Cosimo Perini (2017)                                               *)
(* ============================================================================================= *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KTriples.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Local Open Scope cat.


Lemma Monad_Mor_eq {C : category} (T T' : Monad_data C) (α β : Monad_Mor T T')
      (e : ∏ a : C, α a = β a) :
  α = β.
Proof.
  use subtypePath.
  - intro. apply isaprop_Monad_Mor_laws; apply homset_property.
  - now apply (nat_trans_eq_alt).
Defined.

(* ----- Monad associated to a Kleisli monad ----- *)

Definition unkleislify_data {C : category} (T : KleisliMonad C) : Monad_data C :=
  (kleisli_functor T,, nat_trans_μ T) ,, nat_trans_η T.

Lemma unkleislify_laws {C : category} (T : KleisliMonad C) :
  Monad_laws (unkleislify_data T).
Proof.
  split; simpl; intros; unfold μ.
  + split; intros.
    * apply (bind_η T).
    * rewrite (bind_map T). rewrite id_right. apply (η_bind T).
  + rewrite (bind_map T). rewrite id_right.
    rewrite (bind_bind T). now rewrite id_left.
Defined.

Definition unkleislify {C : category} (T : KleisliMonad C) : Monad C :=
  unkleislify_data T ,, unkleislify_laws T.

(* ----- Monad morphism associated to a Kleisli monad morphism ----- *)

Lemma unkleislify_mor_laws {C : category} {T T' : KleisliMonad C} (α : Kleisli_Mor T T') :
  Monad_Mor_laws (T  := unkleislify T)
                 (T' := unkleislify T')
                 (nat_trans_kleisli_mor α).
Proof.
  split; simpl; intros; unfold μ.
  + rewrite <- assoc. rewrite (bind_map T'). rewrite id_right.
    rewrite <- (Kleisli_Mor_bind α). now rewrite id_left.
  + apply Kleisli_Mor_η.
Defined.

Definition unkleislify_mor {C : category} {T T' : KleisliMonad C}
           (α : Kleisli_Mor T T') :
  Monad_Mor (unkleislify T) (unkleislify T') :=
  nat_trans_kleisli_mor α ,, unkleislify_mor_laws α.

(* ----- Functor from KleisliMonad to Monads. ----- *)

Definition functor_data_unkleislify (C : category) :
  functor_data (category_Kleisli C) (category_Monad C).
Proof.
  use make_functor_data.
  - exact (λ T : KleisliMonad C, unkleislify T).
  - intros. apply (unkleislify_mor X).
Defined.

Lemma is_functor_unkleislify {C : category} :
  is_functor (functor_data_unkleislify C).
Proof.
  split; red; simpl; intros.
  - unfold unkleislify_mor.
    apply subtypePath; simpl.
    + intro. apply isaprop_Monad_Mor_laws; apply homset_property.
    + apply subtypePath; simpl.
      * intro. apply isaprop_is_nat_trans; apply homset_property.
      * now apply funextsec.
  - apply subtypePath; simpl.
    + intro. apply isaprop_Monad_Mor_laws; apply homset_property.
    + apply subtypePath; simpl.
      * intro. apply isaprop_is_nat_trans; apply homset_property.
      * now apply funextsec.
Defined.

Definition functor_unkleislify {C : category} :
  functor (category_Kleisli C) (category_Monad C) :=
  (functor_data_unkleislify C) ,, is_functor_unkleislify.

(* ----- Support Lemmas. ----- *)

Lemma Monad_law4 {C : precategory_data} {T : Monad_data C} {a b : C} (f : a --> b) :
  Monads.η T a · # T f = f · Monads.η T b.
Proof.
  apply pathsinv0. apply (nat_trans_ax (Monads.η T) _ _ f).
Defined.

Lemma Monad_law5 {C : precategory_data} {T : Monad_data C} {a b: C} (f: a --> b) :
  # T (# T f) · (Monads.μ T b) = (Monads.μ T a) · (# T f).
Proof.
  apply (nat_trans_ax (Monads.μ T) _ _ f).
Defined.

(* ----- Kleisli monad associated to a Monad. ----- *)

Definition Monad_Kleisli_data {C : category} (T : Monad_data C) : Kleisli_Data C := (pr1(pr1(pr1 (pr1 T))),,
  (Monads.η T: nat_trans_data _ _),, (@Monads.bind C T)).

Lemma Monad_Kleisli_laws {C : category} (T : Monad C) :
  Kleisli_Laws (Monad_Kleisli_data T).
Proof.
  split.
  - exact Monad_law2.
  - split.
    + exact (@Monads.η_bind C T).
    + exact (@Monads.bind_bind C T).
Defined.

(* ----- Kleisli monad morphism associated to a Monad morphism. ----- *)

Definition kleislify {C : category} (M : Monad C) : KleisliMonad C :=
  Monad_Kleisli_data M ,, Monad_Kleisli_laws M.

Lemma kleislify_mor_law {C : category} {M M' : Monad C} (α : Monad_Mor M M') :
  Kleisli_Mor_laws (kleislify M) (kleislify M') (λ x : C, α x).
Proof.
  split; simpl; intros.
  - apply Monad_Mor_η.
  - unfold bind. unfold Monad_Kleisli_data. simpl. unfold Monads.bind.
    rewrite functor_comp. do 2 rewrite assoc.
    set (H := nat_trans_ax α). simpl in H. rewrite <- H. rewrite assoc4.
    rewrite <-H. rewrite <- assoc4. set (H2 :=  Monad_Mor_μ α b).
    simpl in H2. do 3 rewrite <- assoc.
    unfold Monads.μ in H2. simpl in H2.
    unfold Monads.μ. simpl.
    do 3 rewrite assoc. rewrite assoc4.
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    rewrite assoc.
    rewrite H.
    apply pathsinv0.
    apply H2.
Defined.

Definition kleislify_mor {C : category} {M M' : Monad C}
           (α : Monad_Mor M M') :
  Kleisli_Mor (kleislify M) (kleislify M') :=
  (λ x:C, α x) ,, kleislify_mor_law α.

Definition functor_data_kleislify (C : category) :
  functor_data (category_Monad C) (category_Kleisli C).
Proof.
  use make_functor_data.
  - exact (λ T : Monad C, kleislify T).
  - intros. apply (kleislify_mor X).
Defined.

(* ----- Functoriality of [kleislify]. ----- *)

Lemma is_functor_kleislify {C : category} :
  is_functor (functor_data_kleislify C).
Proof.
  split; red; simpl; intros.
  - unfold kleislify_mor.
    apply subtypePath; simpl.
    + intro. apply isaprop_Kleisli_Mor_laws; apply homset_property.
    + reflexivity.
  - apply subtypePath; simpl.
    + intro. apply isaprop_Kleisli_Mor_laws; apply homset_property.
    + reflexivity.
Defined.

Definition functor_kleislify {C : category} :
  functor (category_Monad C) (category_Kleisli C) :=
  (functor_data_kleislify C) ,, is_functor_kleislify.

(* ----- Proof of the isomorphism. ----- *)

Section Adjunction.

  Context {C : category}.

  (* this result could not be preserved with the parameter [F] as field of [Kleisli_Data]:
  Lemma Kleisli_data_eq {F : C → C} (K K' : Kleisli_Data F)
        (η_eq : ∏ a : C, η K a = η K' a)
        (bind_eq : ∏ (a b : C) (f : a --> F b), bind K f = bind K' f) :
    K = K'.
  Proof.
    intros. apply dirprod_paths.
    - change (η K = η K'). apply funextsec. intro a. apply η_eq.
    - apply funextsec. intro a. apply funextsec. intro b. apply funextfun.
      intro f. apply bind_eq.
  Defined.
*)

  Lemma unkleislify_data_eq  (T : KleisliMonad C) : Monad_Kleisli_data (unkleislify_data T) = T.
  Proof.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply (maponpaths (λ p, tpair _ _ p )).
    apply pair_path_in2.
    simpl. apply funextsec. intro a. apply funextsec. intro b.
    apply funextfun. intro f.
    unfold Monads.bind.
    abstract (simpl; unfold μ; rewrite (bind_map T); rewrite id_right; apply idpath).
  Defined.

  Lemma kleislify_unkleislify (T : KleisliMonad C) :
    kleislify (unkleislify T) = T.
  Proof.
    unfold unkleislify, kleislify. simpl.
    destruct T as (D, L). simpl.
    use total2_paths_f; simpl.
    apply unkleislify_data_eq.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply (isaprop_Kleisli_Laws D).
  Defined.

  Lemma unkleislify_kleislify (M : Monad C) :
    unkleislify (kleislify M) = M.
  Proof.
    apply Monad_eq_raw_data.
    unfold Monad_to_raw_data. simpl.
    apply (pair_path_in2). apply total2_paths2.
    2: apply idpath.
    apply total2_paths2.
    - apply funextsec. intro a.
      apply funextsec; intro b.
      apply funextfun; intro f.
      simpl. unfold map. unfold bind. unfold η. simpl.
      unfold Monads.bind, Monads.η.
      rewrite functor_comp. rewrite <- assoc.
      set (H:= Monad_law2 (T:=M) b). simpl in H.
      unfold Monads.η, Monads.μ in H. simpl in H.
      unfold Monads.μ.
      etrans.
      { apply cancel_precomposition. apply H. }
      apply id_right.
    - apply funextsec; intro x.
      set (H:= functor_id (C:=C) (C':=C) M (M x)). simpl in H.
      unfold μ. simpl.
      unfold bind, Monads.μ. simpl. unfold Monads.bind, Monads.μ.
      etrans.
      { apply cancel_postcomposition. apply H. }
      apply id_left.
  Defined.


  Definition eps (T : KleisliMonad C) (a : C) : C ⟦ T a, T a ⟧ :=
    identity (pr1 T a).

  Lemma eps_morph_law (T : KleisliMonad C) :
    Kleisli_Mor_laws T (kleislify (unkleislify T)) (eps T).
  Proof.
    split; simpl; intros.
    - apply id_right.
    - rewrite id_left, id_right. rewrite id_right.
      unfold μ. unfold bind. simpl. unfold Monads.bind. unfold Monads.μ. simpl.
      unfold μ. rewrite (bind_map T). now rewrite id_right.
  Defined.

  Definition eps_morph (T : KleisliMonad C) :
    Kleisli_Mor T (kleislify (unkleislify T)) :=
    eps T ,, eps_morph_law T.

  Lemma epsinv_morph_law (T : KleisliMonad C) :
    Kleisli_Mor_laws (kleislify (unkleislify T)) T (eps T).
  Proof.
    split; simpl; intros.
    - apply id_right.
    - rewrite id_left, id_right. rewrite id_right.
      unfold μ. unfold bind. simpl. unfold Monads.bind. unfold Monads.μ. simpl.
      unfold μ. rewrite (bind_map T). now rewrite id_right.
  Defined.

  Definition epsinv_morph (T : KleisliMonad C) :
    Kleisli_Mor (kleislify (unkleislify T)) T :=
    eps T ,, epsinv_morph_law T.

  Lemma is_inverse_epsinv (T : KleisliMonad C) :
    is_inverse_in_precat
      (eps_morph T : category_Kleisli C ⟦T, kleislify (unkleislify T)⟧)
      (epsinv_morph T).
  Proof.
    split.
    - apply Kleisli_Mor_eq.
      apply funextsec. intro a. simpl.
      unfold eps. apply id_left.
    - apply Kleisli_Mor_eq.
      apply funextsec. intro a. simpl.
      unfold eps. apply id_left.
  Defined.

  Definition is_z_iso_eps_morph (T : KleisliMonad C) :
    is_z_isomorphism (eps_morph T :
              category_Kleisli C ⟦ T,(kleislify (unkleislify T))⟧) :=
      epsinv_morph T,, is_inverse_epsinv T.

  Lemma is_natural_eps :
    is_nat_trans (functor_identity (category_Kleisli C))
                 (functor_unkleislify ∙ functor_kleislify)
                 eps_morph.
  Proof.
    red. simpl. intros T T' α.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply (Kleisli_Mor_eq(T := T)(T' := kleislify(unkleislify T'))). simpl.
    apply funextsec. intro a.
    unfold nat_trans_from_kleisli_mor, eps.
    rewrite id_left. apply id_right.
  Defined.

  Definition eps_natural :
    functor_identity (category_Kleisli C)
    ⟹ functor_unkleislify ∙ functor_kleislify :=
    eps_morph ,, is_natural_eps.

  Definition eta_arrow (T : Monad C) (a : C) : C ⟦ T a, T a ⟧ := identity (T a).

  Lemma eta_arrow_natural (T : Monad C) :
    is_nat_trans (kleisli_functor_data (kleislify T)) T (eta_arrow T).
  Proof.
    intros a b f. simpl.
    unfold eta_arrow.
    rewrite id_left, id_right.
    unfold map, bind, η. simpl. unfold Monads.bind, Monads.η, Monads.μ.
    rewrite functor_comp.
    rewrite <- assoc.
    set (H := Monad_law2 (T := T) b). progress simpl in H.
    unfold Monads.η, Monads.μ in H.
    etrans.
    { apply cancel_precomposition. apply H. }
    now rewrite id_right.
  Defined.

  Definition eta_data (T : Monad C) : kleisli_functor_data (kleislify T) ⟹ T :=
    eta_arrow T ,, eta_arrow_natural T.

  Lemma is_nat_trans_etainv (T : Monad C) :
    is_nat_trans T (kleisli_functor_data (kleislify T)) (eta_arrow T).
  Proof.
    intros a b f.
    simpl.
    unfold eta_arrow.
    rewrite id_right.
    rewrite id_left.
    unfold map, bind, η. simpl. unfold Monads.bind, Monads.η, Monads.μ.
    rewrite functor_comp.
    rewrite <- assoc.
    set (H := Monad_law2 (T := T) b). progress simpl in H.
    unfold Monads.η, Monads.μ in H.
    etrans.
    2: { apply cancel_precomposition. apply pathsinv0. apply H. }
    now rewrite id_right.
  Defined.

  Definition etainv_data (T : Monad C) : T ⟹ kleisli_functor_data (kleislify T) :=
    eta_arrow T ,, is_nat_trans_etainv T.

  Lemma etainv_data_laws (T : Monad C) :
    @Monad_Mor_laws C
                    (Monad_data_from_Monad C T)
                    (@unkleislify_data C (@kleislify C T)) (etainv_data T).
  Proof.
    split; simpl; intros.
    - unfold eta_arrow.
      rewrite id_right.
      unfold map, μ, Monads.μ, bind. simpl. unfold Monads.bind, η, Monads.μ. simpl.
      unfold Monads.η.
      do 2 rewrite id_left.
      rewrite functor_id, id_left.
      rewrite <- assoc.
      set (H := Monad_law3 (T := T) a). progress simpl in H.
      unfold Monads.μ in H.
      etrans.
      2: { apply cancel_precomposition. apply H. }
      rewrite assoc.
      rewrite <- functor_comp.
      set (H1 := Monad_law1 (T := T) a). progress simpl in H1.
      unfold Monads.η, Monads.μ in H1.
      etrans.
      2: { apply cancel_postcomposition. apply maponpaths. apply pathsinv0.
           (* UniMath.MoreFoundations.Tactics.show_id_type. *) eapply H1. }
      now rewrite functor_id, id_left.
    - apply id_right.
  Defined.

  Definition etainv_morph (T : Monad C) :
    Monad_Mor T (unkleislify (kleislify T)) :=
    etainv_data T ,, etainv_data_laws T.

  Lemma etainv_morph_law (T : Monad C) :
    Monad_Mor_laws (T := T) (T' := (unkleislify (kleislify T))) (etainv_data T).
  Proof.
    split; simpl; intro a.
    - unfold eta_arrow.
      rewrite id_right.
      rewrite id_left.
      unfold Monads.μ, bind, μ, map, μ, bind, map, μ. simpl. unfold Monads.bind; simpl.
      unfold Monads.μ, η.
      rewrite functor_comp. do 2 rewrite functor_id.
      do 2 rewrite id_left.
      set (H1 := Monad_law2 (T := T) (T a)).
      unfold Monads.μ, Monads.η in H1.
      progress simpl in H1.
      simpl. unfold Monads.η.
      etrans.
      2: { apply cancel_postcomposition. apply pathsinv0. apply H1. }
      now rewrite id_left.
    - apply id_right.
  Defined.

  Lemma eta_data_laws (T : Monad C) :
    @Monad_Mor_laws C
                    (@unkleislify_data C (@kleislify C T))
                    (Monad_data_from_Monad C T) (eta_data T).
  Proof.
    split; simpl; intros.
    - unfold eta_arrow.
      rewrite id_right.
      rewrite id_left.
      unfold Monads.μ, μ, bind, μ. simpl. unfold Monads.bind, Monads.μ.
      do 2 rewrite functor_id. do 2 rewrite id_left. apply idpath.
    - apply id_right.
  Defined.

  Definition eta_morph (T : Monad C) :
    Monad_Mor (unkleislify (kleislify T)) T :=
    eta_data T ,, eta_data_laws T.

  Lemma is_inverse_etainv (T : Monad C) :
    is_inverse_in_precat
      (eta_morph T : category_Monad C ⟦unkleislify (kleislify T), T⟧)
      (etainv_morph T : category_Monad C ⟦T, unkleislify (kleislify T)⟧).
  Proof.
    split.
    - apply Monad_Mor_eq.
      intros. simpl.
      unfold eta_arrow. apply id_left.
    - apply Monad_Mor_eq.
      intros. simpl.
      unfold eta_arrow. apply id_left.
  Defined.

  Definition is_z_iso_eta_morph (T : Monad C) :
    is_z_isomorphism (eta_morph T :
              category_Monad C ⟦unkleislify (kleislify T), T⟧)
   := etainv_morph T,, is_inverse_etainv T.

  Lemma is_natural_eta :
    is_nat_trans
      (functor_composite_data (functor_data_kleislify C)
                              (functor_data_unkleislify C))
      (functor_identity_data (precategory_Monad_data C)) eta_morph.
  Proof.
    red; simpl. intros T T' α.
    apply (Monad_Mor_eq (unkleislify (kleislify T))).
    intros. simpl.
    unfold eta_arrow.
    now rewrite id_left, id_right.
  Defined.

  Definition eta_natural :
    functor_kleislify ∙ functor_unkleislify
                               ⟹ functor_identity (category_Monad C) :=
    eta_morph ,, is_natural_eta.

  Lemma form_adjunction_eps_eta :
    form_adjunction functor_unkleislify
                    functor_kleislify
                    eps_natural eta_natural.
  Proof.
    split; red; simpl.
    - intro T.
      apply (Monad_Mor_eq (unkleislify T) (unkleislify T)).
      intros. simpl.
      unfold eps.
      now rewrite id_left.
    - intro T. (* UniMath.MoreFoundations.Tactics.show_id_type. *)
      apply (Kleisli_Mor_eq (T:=kleislify T) (T':=kleislify T)).
      intros. simpl.
      apply funextsec.
      intro a.
      unfold eps.
      now rewrite id_left.
  Defined.

  Definition are_adjoint_monad_form_kleislify :
    are_adjoints functor_unkleislify functor_kleislify :=
    (eps_natural ,, eta_natural) ,, form_adjunction_eps_eta.

  Definition is_left_adjoint_functor_unkleislify :
    is_left_adjoint functor_unkleislify :=
    functor_kleislify ,, are_adjoint_monad_form_kleislify.

  Lemma form_equivalence_unkleislify :
    forms_equivalence is_left_adjoint_functor_unkleislify.
  Proof.
    split; simpl.
    - intros T. apply is_z_iso_eps_morph.
    - intros T. apply is_z_iso_eta_morph.
  Defined.

  Lemma is_catiso : is_catiso (functor_unkleislify(C:=C)).
  Proof.
    split.
    - apply fully_faithful_from_equivalence.
      use (is_left_adjoint_functor_unkleislify,, form_equivalence_unkleislify).
    - apply (isweq_iso _ (λ T : Monad C, kleislify T)).
      + intro T. simpl. apply kleislify_unkleislify.
      + simpl. apply unkleislify_kleislify.
  Defined.

  Corollary weq_Kleisli_Monad_categories:
    (category_Monad C) ≃ (category_Kleisli C).
  Proof.
    set (aux := pr2 is_catiso).
    exact (invweq (make_weq _ aux)).
  Defined.
(** This is the main result of [UniMath.CategoryTheory.Monads.Kleisli]. *)


End Adjunction.
