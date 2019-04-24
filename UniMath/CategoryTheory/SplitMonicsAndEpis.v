(** * Split monics, split epis *)

(** ** Contents
- Split monics
- Split epis
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Local Open Scope cat.

(** ** Split monomorphisms *)

(** The naïve translation of the definition of split monomorphisms into type
    theory is stronger than the classical definition. However, we can recover
    the classical definition using truncation ([is_merely_split_monic]).
    We explore both definitions below.
  *)

Section SplitMonic.
  Context {C : precategory} {A B : ob C}.

  (** A choice of a section for the given morphism *)
  Definition is_split_monic (m : A --> B) : UU :=
    ∑ r : B --> A, is_retraction m r.

  Definition split_monic : UU :=
    ∑ m : A --> B, is_split_monic m.

  Lemma split_monic_is_monic (m : A --> B) :
    is_split_monic m -> isMonic m.
  Proof.
    intros is_split.
    apply (isMonic_postcomp _ m (pr1 is_split)).
    apply (transportf _ (!pr2 is_split)).
    apply identity_isMonic.
  Qed.

  (** We provide a coercion to [Monic C A B], rather than [A --> B], as it is
      more generally useful ([Monic C A B] coerces to [A --> B]). *)
  Definition split_monic_to_monic (m : split_monic) : Monic C A B.
  Proof.
    use mk_Monic.
    - exact (pr1 m).
    - abstract (apply split_monic_is_monic; exact (pr2 m)).
  Defined.

  Coercion split_monic_to_monic : split_monic >-> Monic.

  (** The chosen section is not necessarily unique *)
  Lemma isaset_is_split_monic (m : A --> B) :
    has_homsets C -> isaset (is_split_monic m).
  Proof.
    intro; apply isaset_total2; [auto|].
    intros.
    apply hlevelntosn; apply isaprop_is_retraction.
    assumption.
  Qed.

  (** Now, for the "more classical" definition *)

  Definition is_merely_split_monic (m : A --> B) : hProp.
  Proof.
    use hProppair.
    - exact (∥ ∑ r : B --> A, is_retraction m r ∥).
    - apply isapropishinh.
  Defined.

  Definition merely_split_monic : UU :=
    ∑ m : A --> B, is_merely_split_monic m.

  (** Since coercing this to a [Monic] requires an extra hypothesis
      (that [C]) has homsets, we just coerce to an arrow instead. *)
  Definition merely_split_monic_to_morphism (m : merely_split_monic) : A --> B :=
    pr1 m.
  Coercion merely_split_monic_to_morphism :
    merely_split_monic >-> precategory_morphisms.

  Lemma isaset_merely_split_monic (m : A --> B) :
    has_homsets C -> isaset merely_split_monic.
  Proof.
    intro.
    apply isaset_total2; [auto|].
    intro; apply hlevelntosn, propproperty.
  Qed.

  (** For the purposes of proving a proposition, we can assume a merely split
      monic has a chosen section. *)
  Lemma merely_split_monic_to_split_monic {X : UU} (m : A --> B) :
    isaprop X -> (is_split_monic m -> X) -> is_merely_split_monic m -> X.
  Proof.
    intros isx impl mere.
    refine (factor_through_squash isx _ mere).
    assumption.
  Qed.

  (** Note that this requires that [C] has homsets, in contrast
      to the above statement for "non-mere" monics. *)
  Lemma merely_split_monic_is_monic (m : A --> B) :
    has_homsets C -> is_merely_split_monic m -> isMonic m.
  Proof.
    intros H.
    apply merely_split_monic_to_split_monic.
    - apply isapropisMonic; auto.
    - apply split_monic_is_monic.
  Qed.

  Definition merely_split_monic_to_monic {hsC : has_homsets C} :
    merely_split_monic -> Monic C A B.
  Proof.
    intros m.
    use mk_Monic.
    - exact (pr1 m).
    - abstract (apply merely_split_monic_is_monic; [auto|]; exact (pr2 m)).
  Qed.

  (** Equivalent definitions *)

  (** For the truncated version, this is an equivalence (see below). However,
      in general, choosing a section is stronger. *)
  Lemma is_split_monic_to_precomp_is_surjection (m : A --> B) :
    is_split_monic m -> ∏ c : ob C, issurjective (@precomp_with _ _ _ m c).
  Proof.
    intros is_split c f.
    apply hinhpr.
    unfold hfiber, precomp_with.
    exists (pr1 is_split · f).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (fun z => z · _) (pr2 is_split) @ _).
    apply id_left.
  Qed.

  Lemma is_merely_split_monic_weq_precomp_is_surjection (m : A --> B) :
    is_merely_split_monic m <->
    ∏ c : ob C, issurjective (@precomp_with _ _ _ m c).
  Proof.
    unfold is_split_monic.
    split.
    - intros is_split ?.
      apply (merely_split_monic_to_split_monic m).
      + apply isapropissurjective.
      + intro; apply is_split_monic_to_precomp_is_surjection.
        assumption.
      + assumption.
    - intros is_surjective.
      specialize (is_surjective _ (identity _)).
      refine (factor_through_squash _ _ is_surjective).
      + apply propproperty.
      + intro fib.
        apply hinhpr.
        exists (pr1 fib).
        apply (pr2 fib).
  Qed.
End SplitMonic.

Arguments split_monic {_} _ _.
Arguments merely_split_monic {_} _ _.

(** Functors preserve merely split monomorphisms *)
Lemma functor_preserves_merely_split_monic {C D : precategory} (F : functor C D)
      {A B : ob C} (f : C⟦A,B⟧) :
  is_merely_split_monic f -> is_merely_split_monic (# F f).
Proof.
  apply hinhfun.
  intro hf.
  exists (#F (pr1 hf)).
  unfold is_retraction.
  now rewrite <- functor_id, <- (pr2 hf), <- functor_comp.
Qed.

(** Functors preserve split monomorphisms *)
Lemma functor_preserves_split_monic {C D : precategory} (F : functor C D)
      {A B : ob C} (f : C⟦A,B⟧) :
  is_split_monic f -> is_split_monic (# F f).
Proof.
  intro hf.
  exists (#F (pr1 hf)).
  unfold is_retraction.
  now rewrite <- functor_id, <- (pr2 hf), <- functor_comp.
Qed.

(** An epic split monic is an iso. *)
Lemma merely_split_monic_is_epi_to_is_iso
      {C : category} {A B : ob C} (m : A --> B) :
      is_merely_split_monic m -> isEpi m -> is_iso m.
Proof.
  intros is_monic is_epi c.
  apply isweqinclandsurj.
  - apply precomp_with_epi_isincl; assumption.
  - apply is_merely_split_monic_weq_precomp_is_surjection.
    assumption.
Qed.

(** Definition of a split epimorphism.
It is a morphism f such that there exists a morphism g that satisfies f ∘ g = id
*)
Section SplitEpis.

  Context {C : precategory} {A B : ob C}.

  (** An epi with a chosen retraction *)
  Definition is_split_epi (f : C⟦A,B⟧) :=
    ∑ (g : C⟦B,A⟧), is_retraction g f.

  Definition split_epi : UU :=
    ∑ f : A --> B, is_split_epi f.

  Lemma split_epi_is_epi (f : A --> B) :
    is_split_epi f -> isEpi f.
  Proof.
    intros is_split.
    apply (isEpi_precomp _ (pr1 is_split) f).
    apply (transportf _ (!pr2 is_split)).
    apply identity_isEpi.
  Qed.

  Definition split_epi_to_epi (f : split_epi) : Epi C A B.
  Proof.
    use mk_Epi.
    - exact (pr1 f).
    - abstract (apply split_epi_is_epi; exact (pr2 f)).
  Defined.

  Definition is_merely_split_epi (f : A --> B) :=
    ∥ ∑ (g : C⟦B,A⟧), g · f = identity B ∥.

  Definition merely_split_epi : UU :=
    ∑ (f : A --> B), is_merely_split_epi f.

  Lemma isaset_merely_split_epi :
    has_homsets C -> isaset merely_split_epi.
  Proof.
    intro.
    apply isaset_total2; [auto|].
    intro.
    apply hlevelntosn, isapropishinh.
  Qed.

  (** For the purposes of proving a proposition, we can assume a merely split
      epi has a chosen retraction. *)
  Lemma merely_split_epi_to_split_epi {X : UU} (m : A --> B) :
    isaprop X -> (is_split_epi m -> X) -> is_merely_split_epi m -> X.
  Proof.
    intros isx impl mere.
    refine (factor_through_squash isx _ mere).
    assumption.
  Qed.

  Lemma merely_split_epi_is_epi (f : A --> B) :
    has_homsets C -> is_merely_split_epi f -> isEpi f.
  Proof.
    intros H.
    apply merely_split_epi_to_split_epi.
    - apply isapropisEpi; auto.
    - apply split_epi_is_epi.
  Qed.
End SplitEpis.

(** Functors preserve merely split epimorphisms *)
Lemma functor_preserves_merely_split_epi {C D : precategory} (F : functor C D)
      {A B : ob C} (f : C⟦A,B⟧) :
  is_merely_split_epi f -> is_merely_split_epi (# F f).
Proof.
  apply hinhfun.
  intro hf.
  exists (#F (pr1 hf)).
  now rewrite <-functor_id,<- (pr2 hf), <- functor_comp.
Qed.

(** Functors preserve split epimorphisms *)
Lemma functor_preserves_split_epi {C D : precategory} (F : functor C D)
      {A B : ob C} (f : C⟦A,B⟧) :
  is_split_epi f -> is_split_epi (# F f).
Proof.
  intro hf.
  exists (#F (pr1 hf)).
  unfold is_retraction.
  now rewrite <- functor_id, <- (pr2 hf), <- functor_comp.
Qed.

Definition epis_are_split (C : precategory) :=
  ∏ (A B : C) (f : C⟦A,B⟧), isEpi f -> is_merely_split_epi f.

Arguments split_epi {_} _ _.
Arguments merely_split_epi {_} _ _.