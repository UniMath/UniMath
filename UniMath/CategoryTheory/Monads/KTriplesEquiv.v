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
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.FunctorCategories.
Require Import UniMath.CategoryTheory.Whiskering.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Bincoproducts.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KTriples.
Require Import UniMath.CategoryTheory.Catiso.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.Equivalences.
Require Import UniMath.CategoryTheory.EquivalencesLemmas.

Local Open Scope cat.


Lemma Monad_Mor_eq {C : precategory} (hs : has_homsets C) (T T' : Monad C) (α β : Monad_Mor T T')
      (e : ∏ a : C, α a = β a) :
  α = β.
Proof.
  use subtypeEquality'.
  - now apply (nat_trans_eq hs).
  - now apply isaprop_Monad_Mor_laws.
Defined.

(* ----- Monad associated to a Kleisli ----- *)

Definition unkleislify_data {C : precategory} (T : Kleisli C) : Monad_data C :=
  (kleisli_functor T,, nat_trans_μ T) ,, nat_trans_η T.

Lemma unkleislify_laws {C : precategory} (T : Kleisli C) :
  Monad_laws (unkleislify_data T).
Proof.
  split; simpl; intros; unfold μ.
  + split; intros.
    * apply (bind_η T).
    * rewrite (bind_map T). rewrite id_right. apply (η_bind T).
  + rewrite (bind_map T). rewrite id_right.
    rewrite (bind_bind T). now rewrite id_left.
Defined.

Definition unkleislify {C : precategory} (T : Kleisli C) : Monad C :=
  unkleislify_data T ,, unkleislify_laws T.

(* ----- Monad morphism associated to a Kleisli morphism ----- *)

Lemma unkleislify_mor_laws {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  Monad_Mor_laws (T  := unkleislify T)
                 (T' := unkleislify T')
                 (nat_trans_kleisli_mor α).
Proof.
  split; simpl; intros; unfold μ.
  + rewrite <- assoc. rewrite (bind_map T'). rewrite id_right.
    rewrite <- (Kleisli_Mor_bind α). now rewrite id_left.
  + apply Kleisli_Mor_η.
Defined.

Definition unkleislify_mor {C : precategory} {T T' : Kleisli C}
           (α : Kleisli_Mor T T') :
  Monad_Mor (unkleislify T) (unkleislify T') :=
  nat_trans_kleisli_mor α ,, unkleislify_mor_laws α.

(* ----- Functor from Kleisli to Monads. ----- *)

Definition functor_data_unkleislify (C : precategory) (hs : has_homsets C) :
  functor_data (precategory_Kleisli C hs) (precategory_Monad C hs).
Proof.
  use mk_functor_data.
  - exact (λ T : Kleisli C, unkleislify T).
  - intros. apply (unkleislify_mor X).
Defined.

Lemma is_functor_unkleislify {C : precategory} (hs : has_homsets C) :
  is_functor (functor_data_unkleislify C hs).
Proof.
  split; red; simpl; intros.
  - unfold unkleislify_mor.
    apply subtypeEquality'; simpl.
    + apply subtypeEquality'; simpl.
      * now apply funextsec.
      * now apply isaprop_is_nat_trans.
    + now apply isaprop_Monad_Mor_laws.
  - apply subtypeEquality'; simpl.
    + apply subtypeEquality'; simpl.
      * now apply funextsec.
      * now apply isaprop_is_nat_trans.
    + now apply isaprop_Monad_Mor_laws.
Defined.

Definition functor_unkleislify {C : precategory} (hs: has_homsets C) :
  functor (precategory_Kleisli C hs) (precategory_Monad C hs) :=
  (functor_data_unkleislify C hs) ,, is_functor_unkleislify hs.

(* ----- Support Lemmas. ----- *)

Lemma Monad_law4 {C : precategory} {T : Monad C} {a b : C} (f : a --> b) :
  Monads.η T a · # T f = f · Monads.η T b.
Proof.
  apply pathsinv0. apply (nat_trans_ax (Monads.η T) _ _ f).
Defined.

Lemma Monad_law5 {C : precategory} {T : Monad C} {a b: C} (f: a --> b) :
  # T (# T f) · (Monads.μ T b) = (Monads.μ T a) · (# T f).
Proof.
  apply (nat_trans_ax (Monads.μ T) _ _ f).
Defined.

(* ----- Kleisli associated to a Monad. ----- *)

Definition Monad_Kleisli_data {C : precategory} (M : Monad_data C) : Kleisli_Data M :=
  nat_trans_data (Monads.η M),, (λ (a b : C) (f : a --> M b), (Monads.μ M) b ∘ # M f).

Lemma Monad_Kleisli_laws {C : precategory} (M : Monad C) :
  Kleisli_Laws (Monad_Kleisli_data M).
Proof.
  split; simpl; intros.
  - rewrite assoc. rewrite (functor_comp M).
    rewrite assoc4. set (H := Monad_law5 (T:=M) g). simpl in H.
    rewrite <- H. rewrite functor_comp. do 2 rewrite <- assoc4.
    set (H2 := Monad_law3 (T:=M) c). simpl in H2.
    do 4 rewrite <- assoc.
    now rewrite <- H2.
  - split; simpl; intros.
    + rewrite assoc. set (H := Monad_law4 (T:= M) f).
      simpl in H. rewrite H. rewrite <- assoc.
      set (H2 := Monad_law1 (T:=M) b). simpl in H2.
      rewrite H2. apply id_right.
    + apply Monad_law2.
Defined.

(* ----- Kleisli morphism associated to a Monad morphism. ----- *)

Definition kleislify {C : precategory} (M : Monad C) : Kleisli C :=
  (λ x, M x) ,, Monad_Kleisli_data M ,, Monad_Kleisli_laws M.

Lemma kleislify_mor_law {C : precategory} {M M' : Monad C} (α : Monad_Mor M M') :
  Kleisli_Mor_laws (λ x : C, α x) (kleislify M) (kleislify M').
Proof.
  split; simpl; intros.
  - apply Monad_Mor_η.
  - rewrite functor_comp. do 2 rewrite assoc.
    set (H := nat_trans_ax α). simpl in H. rewrite <- H. rewrite assoc4.
    rewrite <-H. rewrite <- assoc4. set (H2 :=  Monad_Mor_μ α b).
    simpl in H2. do 3 rewrite <- assoc. rewrite H2.
    do 3 rewrite assoc. rewrite assoc4.
    now rewrite H.
Defined.

Definition kleislify_mor {C : precategory} {M M' : Monad C}
           (α : Monad_Mor M M') :
  Kleisli_Mor (kleislify M) (kleislify M') :=
  (λ x:C, α x) ,, kleislify_mor_law α.

Definition functor_data_kleislify (C : precategory) (hs : has_homsets C) :
  functor_data (precategory_Monad C hs) (precategory_Kleisli C hs).
Proof.
  use mk_functor_data.
  - exact (λ T : Monad C, kleislify T).
  - intros. apply (kleislify_mor X).
Defined.

(* ----- Functoriality of [kleislify]. ----- *)

Lemma is_functor_kleislify {C : precategory} (hs : has_homsets C) :
  is_functor (functor_data_kleislify C hs).
Proof.
  split; red; simpl; intros.
  - unfold kleislify_mor.
    apply subtypeEquality'; simpl.
    + reflexivity.
    + now apply isaprop_Kleisli_Mor_laws.
  - apply subtypeEquality'; simpl.
    + reflexivity.
    + now apply isaprop_Kleisli_Mor_laws.
Defined.

Definition functor_kleislify {C : precategory} (hs: has_homsets C) :
  functor (precategory_Monad C hs) (precategory_Kleisli C hs) :=
  (functor_data_kleislify C hs) ,, is_functor_kleislify hs.

(* ----- Proof of the isomorphism. ----- *)

Section Adjunction.

  Context {C : precategory}.
  Variable (hs : has_homsets C).

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

  Lemma unkleislify_data_eq  (T : Kleisli C) : Monad_Kleisli_data (unkleislify_data T) = T.
  Proof.
    apply pair_path_in2.
    simpl. apply funextsec. intro a. apply funextsec. intro b.
    apply funextfun. intro f.
    abstract (simpl; unfold μ; rewrite (bind_map T); rewrite id_right; apply idpath).
  Defined.

  Lemma kleislify_unkleislify (T : Kleisli C) :
    kleislify (unkleislify T) = T.
  Proof.
    unfold unkleislify, kleislify. simpl.
    destruct T as (F , (K , L)). simpl.
    change (λ x : C, F x) with F.
    apply (pair_path_in2). apply subtypeEquality'.
    2: apply (isaprop_Kleisli_Laws hs K).
    simpl. apply (unkleislify_data_eq (F,, K,, L)).
  Defined.

  Lemma unkleislify_kleislify (M : Monad C) :
    unkleislify (kleislify M) = M.
  Proof.
    apply (Monad_eq_raw_data hs).
    unfold Monad_to_raw_data. simpl.
    change (λ x:C, M x) with (M: ob C → ob C).
    apply (pair_path_in2). apply total2_paths2.
    2: apply idpath.
    apply total2_paths2.
    - apply funextsec. intro a.
      apply funextsec; intro b.
      apply funextfun; intro f.
      simpl. rewrite functor_comp. rewrite <- assoc.
      set (H:= Monad_law2 (T:=M) b). simpl in H.
      rewrite H. apply id_right.
    - apply funextsec; intro x.
      set (H:= functor_id (C:=C) (C':=C) M (M x)). simpl in H.
      unfold μ. simpl. rewrite H. apply id_left.
  Defined.


  Definition eps (K : Kleisli C) (a : C) : C ⟦ kleisli_ob K a, kleisli_ob K a ⟧ :=
    identity (pr1 K a).

  Lemma eps_morph_law (K : Kleisli C) :
    Kleisli_Mor_laws (eps K) K (kleislify (unkleislify K)).
  Proof.
    split; simpl; intros.
    - apply id_right.
    - rewrite id_left, id_right. rewrite id_right.
      unfold μ. rewrite (bind_map K). now rewrite id_right.
  Defined.

  Definition eps_morph (K : Kleisli C) :
    Kleisli_Mor K (kleislify (unkleislify K)) :=
    eps K ,, eps_morph_law K.

  Lemma epsinv_morph_law (K : Kleisli C) :
    Kleisli_Mor_laws (eps K) (kleislify (unkleislify K)) K.
  Proof.
    split; simpl; intros.
    - apply id_right.
    - rewrite id_left, id_right. rewrite id_right.
      unfold μ. rewrite (bind_map K). now rewrite id_right.
  Defined.

  Definition epsinv_morph (K : Kleisli C) :
    Kleisli_Mor (kleislify (unkleislify K)) K :=
    eps K ,, epsinv_morph_law K.

  Lemma is_inverse_epsinv (K : Kleisli C) :
    is_inverse_in_precat
      (eps_morph K : precategory_Kleisli C hs ⟦K, kleislify (unkleislify K)⟧)
      (epsinv_morph K).
  Proof.
    split.
    - apply (Kleisli_Mor_eq hs).
      apply funextsec. intro a. simpl.
      unfold eps. apply id_left.
    - apply (Kleisli_Mor_eq hs).
      apply funextsec. intro a. simpl.
      unfold eps. apply id_left.
  Defined.

  Definition is_iso_eps_morph (K : Kleisli C) :
    is_iso (eps_morph K :
              precategory_Kleisli C hs ⟦ K,(kleislify (unkleislify K))⟧) :=
    is_iso_from_is_z_iso
      (eps_morph K : precategory_Kleisli C hs ⟦K, kleislify (unkleislify K)⟧)
      (epsinv_morph K,, is_inverse_epsinv K).

  Lemma is_natural_eps :
    is_nat_trans (functor_identity (precategory_Kleisli C hs))
                 (functor_unkleislify hs ∙ functor_kleislify hs)
                 eps_morph.
  Proof.
    red. simpl. intros K K' f.
    apply (Kleisli_Mor_eq hs). simpl.
    apply funextsec. intro a.
    unfold nat_trans_from_kleisli_mor, eps.
    rewrite id_left. apply id_right.
  Defined.

  Definition eps_natural :
    functor_identity (precategory_Kleisli C hs)
    ⟹ functor_unkleislify hs ∙ functor_kleislify hs :=
    eps_morph ,, is_natural_eps.

  Definition eta_arrow (T : Monad C) (a : C) : C ⟦ T a, T a ⟧ := identity (T a).

  Lemma eta_arrow_natural (T : Monad C) :
    is_nat_trans (kleisli_functor_data (kleislify T)) T (eta_arrow T).
  Proof.
    intros a b f. simpl.
    unfold eta_arrow.
    rewrite id_left, id_right.
    rewrite functor_comp.
    rewrite <- assoc.
    set (H := Monad_law2 (T := T) b). progress simpl in H.
    rewrite H. now rewrite id_right.
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
    rewrite functor_comp.
    rewrite <- assoc.
    set (H := Monad_law2 (T := T) b). progress simpl in H.
    rewrite H. now rewrite id_right.
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
      do 2 rewrite id_left.
      rewrite functor_id, id_left.
      rewrite <- assoc.
      set (H := Monad_law3 (T := T) a). progress simpl in H. rewrite <- H.
      rewrite assoc.
      rewrite <- functor_comp.
      set (H1 := Monad_law1 (T := T) a). progress simpl in H1. rewrite H1.
      now rewrite functor_id, id_left.
    - apply id_right.
  Defined.

  Definition etainv_morph (T : Monad C) :
    Monad_Mor T (unkleislify (kleislify T)) :=
    etainv_data T ,, etainv_data_laws T.

  Lemma etainv_morph_law (M : Monad C) :
    Monad_Mor_laws (T := M) (T' := (unkleislify (kleislify M))) (etainv_data M).
  Proof.
    split; simpl; intro a.
    - unfold eta_arrow.
      rewrite id_right.
      rewrite id_left.
      rewrite functor_comp, functor_id.
      do 2 rewrite id_left.
      set (H1 := Monad_law2 (T := M) (M a)). progress simpl in H1. rewrite H1.
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
      now rewrite functor_id, id_left.
    - apply id_right.
  Defined.

  Definition eta_morph (T : Monad C) :
    Monad_Mor (unkleislify (kleislify T)) T :=
    eta_data T ,, eta_data_laws T.

  Lemma is_inverse_etainv (M : Monad C) :
    is_inverse_in_precat
      (eta_morph M : precategory_Monad C hs ⟦unkleislify (kleislify M), M⟧)
      (etainv_morph M : precategory_Monad C hs ⟦M, unkleislify (kleislify M)⟧).
  Proof.
    split.
    - apply (Monad_Mor_eq hs).
      intros. simpl.
      unfold eta_arrow. apply id_left.
    - apply (Monad_Mor_eq hs).
      intros. simpl.
      unfold eta_arrow. apply id_left.
  Defined.

  Definition is_iso_eta_morph (M : Monad C) :
    is_iso (eta_morph M :
              precategory_Monad C hs ⟦unkleislify (kleislify M), M⟧)
   := is_iso_from_is_z_iso
      (eta_morph M : precategory_Monad C hs ⟦unkleislify (kleislify M), M⟧)
      (etainv_morph M,, is_inverse_etainv M).

  Lemma is_natural_eta :
    is_nat_trans
      (functor_composite_data (functor_data_kleislify C hs)
                              (functor_data_unkleislify C hs))
      (functor_identity_data (precategory_Monad_data C)) eta_morph.
  Proof.
    red; simpl. intros T T' f.
    apply (Monad_Mor_eq hs).
    intros. simpl.
    unfold eta_arrow.
    now rewrite id_left, id_right.
  Defined.

  Definition eta_natural :
    functor_kleislify hs ∙ functor_unkleislify hs
                               ⟹ functor_identity (precategory_Monad C hs) :=
    eta_morph ,, is_natural_eta.

  Lemma form_adjunction_eps_eta :
    form_adjunction (functor_unkleislify hs)
                    (functor_kleislify hs)
                    eps_natural eta_natural.
  Proof.
    split; red; simpl.
    - intro K. apply (Monad_Mor_eq hs).
      intros. simpl.
      unfold eps.
      now rewrite id_left.
    - intro T. apply (Kleisli_Mor_eq hs).
      intros. simpl.
      apply funextsec.
      intro a.
      unfold eps.
      now rewrite id_left.
  Defined.

  Definition are_adjoint_monad_form_kleislify :
    are_adjoints (functor_unkleislify hs) (functor_kleislify hs) :=
    (eps_natural ,, eta_natural) ,, form_adjunction_eps_eta.

  Definition is_left_adjoint_functor_unkleislify :
    is_left_adjoint (functor_unkleislify hs) :=
    functor_kleislify hs,, are_adjoint_monad_form_kleislify.

  Lemma form_equivalence_unkleislify :
    forms_equivalence is_left_adjoint_functor_unkleislify.
  Proof.
    split; simpl.
    - intros K. apply is_iso_eps_morph.
    - intros M. apply is_iso_eta_morph.
  Defined.

  Lemma is_catiso : is_catiso(functor_unkleislify hs).
  Proof.
    split.
    - apply fully_faithful_from_equivalence.
      use (is_left_adjoint_functor_unkleislify,, form_equivalence_unkleislify).
    - apply (gradth _ (λ T : Monad C, kleislify T)).
      + intro K. simpl. apply kleislify_unkleislify.
      + simpl. apply unkleislify_kleislify.
  Defined.

End Adjunction.
