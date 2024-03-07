(** **********************************************************

Contents:

        - Definition of monads ([Monad])
        - category of monads [category_Monad C] on [C]
        - Forgetful functor [forgetfunctor_Monad] from monads
             to endofunctors on [C]
        - Haskell style bind operation ([bind])
        - A substitution operator for monads ([monadSubst])
        - A helper lemma for proving equality of Monads ([Monad_eq_raw_data])
        - Proof that [precategory_Monad C] is univalent if [C] is

Written by: Benedikt Ahrens (started March 2015)
Extended by: Anders Mörtberg, 2016
Extended by: Ralph Matthes, 2017 (Section MonadsUsingCoproducts)
Rewrite by: Ralph Matthes, 2023, defining the category of monads through a displayed category over the endofunctors, this gives the previously missing univalence result nearly for free

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Core.Univalence.


Local Open Scope cat.

Section Monad_disp_def.

  Context {C : category}.

  Definition disp_Monad_data (F : functor C C) : UU :=
    (F ∙ F ⟹ F) × (functor_identity C ⟹ F).

  Definition disp_μ {F : functor C C} (T : disp_Monad_data F) : F ∙ F ⟹ F := pr1 T.
  Definition disp_η {F : functor C C} (T : disp_Monad_data F) : functor_identity C ⟹ F := pr2 T.

  Definition disp_Monad_laws {F : functor C C} (T : disp_Monad_data F) : UU :=
    (
      (∏ c : C, disp_η T (F c) · disp_μ T c = identity (F c))
      ×
      (∏ c : C, #F (disp_η T c) · disp_μ T c = identity (F c)) )
      ×
      (∏ c : C, #F (disp_μ T c) · disp_μ T c = disp_μ T (F c) · disp_μ T c).

  Lemma isaprop_disp_Monad_laws {F : functor C C} (T : disp_Monad_data F) : isaprop (disp_Monad_laws T).
  Proof.
    repeat apply isapropdirprod;
      apply impred; intro c; apply C.
  Qed.

  Definition disp_Monad_Mor_laws {F F' : functor C C} (T : disp_Monad_data F) (T' : disp_Monad_data F') (α : F ⟹ F') : UU :=
    (∏ a : C, disp_μ T a · α a = α (F a) · #F' (α a) · disp_μ T' a) ×
    (∏ a : C, disp_η T a · α a = disp_η T' a).

  Lemma isaprop_disp_Monad_Mor_laws  {F F' : functor C C} (T : disp_Monad_data F) (T' : disp_Monad_data F') (α : F ⟹ F')
    : isaprop (disp_Monad_Mor_laws T T' α).
  Proof.
    apply isapropdirprod;
      apply impred; intro c; apply C.
  Qed.

  (* not needed - is part of [monads_category_displayed]
  Definition monads_disp_cat_ob_mor : disp_cat_ob_mor [C,C].
  Proof.
    use tpair.
    - intro F. exact (∑ T : disp_Monad_data F, disp_Monad_laws T).
    - intros F F' [T Tlaws] [T' T'laws] α. exact (disp_Monad_Mor_laws T T' α).
  Defined.
  *)

  Lemma monads_category_id_subproof {F : functor C C}  (T : disp_Monad_data F) (Tlaws : disp_Monad_laws T) :
    disp_Monad_Mor_laws T T (nat_trans_id F).
  Proof.
    split; intros a; simpl.
    - now rewrite id_left, id_right, functor_id, id_left.
    - now apply id_right.
  Qed.

  Lemma monads_category_comp_subproof {F F' F'' : functor C C}
    (T : disp_Monad_data F) (Tlaws : disp_Monad_laws T)
    (T' : disp_Monad_data F') (T'laws : disp_Monad_laws T')
    (T'' : disp_Monad_data F'') (T''laws : disp_Monad_laws T'')
    (α : F ⟹ F') (α' : F' ⟹ F'') :
    disp_Monad_Mor_laws T T' α → disp_Monad_Mor_laws T' T'' α' → disp_Monad_Mor_laws T T'' (nat_trans_comp _ _ _ α α').
  Proof.
    intros Hα Hα'.
    split; intros; simpl.
    - rewrite assoc.
      set (H:=pr1 Hα a); simpl in H.
      rewrite H; clear H; rewrite <- !assoc.
      set (H:=pr1 Hα' a); simpl in H.
      rewrite H; clear H.
      rewrite functor_comp.
      apply maponpaths.
      now rewrite !assoc, nat_trans_ax.
    - rewrite assoc.
      eapply pathscomp0; [apply cancel_postcomposition, (pr2 Hα)|].
      apply (pr2 Hα').
  Qed.

  Definition monads_category_disp : disp_cat [C,C].
  Proof.
    use disp_cat_from_SIP_data.
    - intro F. exact (∑ T : disp_Monad_data F, disp_Monad_laws T).
    - intros F F' [T Tlaws] [T' T'laws] α. exact (disp_Monad_Mor_laws T T' α).
    - intros F F' [T Tlaws] [T' T'laws] α. apply isaprop_disp_Monad_Mor_laws.
    - intros F [T Tlaws]. apply (monads_category_id_subproof _ Tlaws).
    - intros F F' F'' [T Tlaws] [T' T'laws] [T'' T''laws] α α'.
      apply (monads_category_comp_subproof _ Tlaws _ T'laws _ T''laws).
  Defined.

  Definition category_Monad : category := total_category monads_category_disp.

  Definition Monad : UU := ob category_Monad.

  #[reversible=no] Coercion functor_from_Monad (T : Monad) : functor C C := pr1 T.

  Definition μ (T : Monad) : T ∙ T ⟹ T := pr112 T.
  Definition η (T : Monad) : functor_identity C ⟹ T := pr212 T.

  Lemma Monad_law1 {T : Monad} : ∏ c : C, η T (T c) · μ T c = identity (T c).
  Proof.
    exact (pr1 (pr122 T)).
  Qed.

  Lemma Monad_law2 {T : Monad} : ∏ c : C, #T (η T c) · μ T c = identity (T c).
  Proof.
    exact (pr2 (pr122 T)).
  Qed.

  Lemma Monad_law3 {T : Monad} : ∏ c : C, #T (μ T c) · μ T c = μ T (T c) · μ T c.
  Proof.
    exact (pr222 T).
  Qed.

  Lemma monads_category_disp_eq (F : functor C C) (T T' : monads_category_disp F)  : pr1 T = pr1 T' -> T = T'.
  Proof.
    intro H.
    induction T as [T Tlaws].
    induction T' as [T' T'laws].
    use total2_paths_f; [apply H |].
    apply isaprop_disp_Monad_laws.
  Qed.

  Lemma monads_category_Pisset (F : functor C C) : isaset (∑ T : disp_Monad_data F, disp_Monad_laws T).
  Proof.
    change isaset with (isofhlevel 2).
    apply isofhleveltotal2.
    { apply isasetdirprod; apply [C,C]. }
    intro T.
    apply isasetaprop.
    apply isaprop_disp_Monad_laws.
  Qed.

  Lemma monads_category_Hstandard {F : functor C C}
    (T : disp_Monad_data F) (Tlaws : disp_Monad_laws T)
    (T' : disp_Monad_data F) (T'laws : disp_Monad_laws T') :
    disp_Monad_Mor_laws T T' (nat_trans_id F) → disp_Monad_Mor_laws T' T (nat_trans_id F) → T,, Tlaws = T',, T'laws.
  Proof.
    intros H H'.
    apply subtypeInjectivity.
    { intro T0. apply isaprop_disp_Monad_laws. }
    cbn.
    induction T as [μ η].
    induction T' as [μ' η'].
    apply dirprodeq; cbn.
    - apply nat_trans_eq; [apply C|]. intro a.
      assert (Hinst := pr1 H a).
      cbn in Hinst.
      rewrite id_right in Hinst.
      rewrite id_left in Hinst.
      rewrite functor_id in Hinst.
      rewrite id_left in Hinst.
      exact Hinst.
    - apply nat_trans_eq; [apply C|]. intro a.
      assert (Hinst := pr2 H a).
      cbn in Hinst.
      rewrite id_right in Hinst.
      exact Hinst.
  Qed.

  Definition is_univalent_monads_category_disp : is_univalent_disp monads_category_disp.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - exact monads_category_Pisset.
    - intros F [T Tlaws] [T' T'laws]. apply monads_category_Hstandard.
  Defined.

End Monad_disp_def.

Arguments category_Monad _ : clear implicits.
Arguments Monad _ : clear implicits.

Definition is_univalent_category_Monad (C : univalent_category) :
  is_univalent (category_Monad C).
Proof.
  apply SIP.
  - apply is_univalent_functor_category. apply C.
  - apply monads_category_Pisset.
  - intros F [T Tlaws] [T' T'laws]. apply monads_category_Hstandard.
Defined.

Section pointfree.

  Context (C : category) (T0: functor C C) (T : disp_Monad_data T0).

  Let EndC := [C, C].

  Let η := disp_η T.
  Let μ := disp_μ T.

  Definition Monad_laws_pointfree : UU :=
    (
      (nat_trans_comp _ _ _ (pre_whisker T0 η) μ = identity(C:=EndC) T0)
        ×
      (nat_trans_comp _ _ _ (post_whisker η T0) μ = identity(C:=EndC) T0) )
        ×
      (nat_trans_comp _ _ _ (post_whisker μ T0) μ = nat_trans_comp _ _ _ (pre_whisker T0 μ) μ).

  Lemma pointfree_is_equiv: Monad_laws_pointfree <-> disp_Monad_laws T.
  Proof.
    split.
    - intro H. induction H as [[H1 H2] H3].
      split.
      + split.
        * intro c. apply (maponpaths pr1) in H1. apply toforallpaths in H1. apply H1.
        * intro c. apply (maponpaths pr1) in H2. apply toforallpaths in H2. apply H2.
      + intro c. apply (maponpaths pr1) in H3. apply toforallpaths in H3. apply H3.
    - intro H. induction H as [[H1 H2] H3].
      split.
      + split.
        * apply nat_trans_eq_alt. exact H1.
        * apply nat_trans_eq_alt. exact H2.
      + apply nat_trans_eq; try apply homset_property. exact H3.
  Qed.

  Let T0' := T0 : EndC.
  Let η' := η: EndC⟦functor_identity C, T0'⟧.
  Let μ' := μ: EndC⟦functor_compose T0' T0', T0'⟧.

  Definition Monad_laws_pointfree_in_functor_category : UU :=
    (
      (#(pre_composition_functor _ _ _ T0') η' · μ' = identity(C:=EndC) T0')
        ×
      (#(post_composition_functor _ _ _ T0') η' · μ' = identity(C:=EndC) T0') )
        ×
      (#(post_composition_functor _ _ _ T0') μ' · μ' = (#(pre_composition_functor _ _ _ T0') μ') · μ').

  (** the last variant of the laws is convertible with the one before *)
  Goal
    Monad_laws_pointfree = Monad_laws_pointfree_in_functor_category.
  Proof.
    apply idpath.
  Qed.

End pointfree.

Definition Monad_Mor {C : category} (T T' : Monad C) : UU
  := category_Monad C ⟦T, T'⟧.

#[reversible=no] Coercion nat_trans_from_monad_mor {C : category} (T T' : Monad C) (s : Monad_Mor T T')
  : T ⟹ T' := pr1 s.

Definition Monad_Mor_laws {C : category} {T T' : Monad C} (α : T ⟹ T')
  : UU :=
  (∏ a : C, μ T a · α a = α (T a) · #T' (α a) · μ T' a) ×
    (∏ a : C, η T a · α a = η T' a).

Definition Monad_Mor_η {C : category} {T T' : Monad C} (α : Monad_Mor T T')
  : ∏ a : C, η T a · α a = η T' a.
Proof.
  exact (pr22 α).
Qed.

Definition Monad_Mor_μ {C : category} {T T' : Monad C} (α : Monad_Mor T T')
  : ∏ a : C, μ T a · α a = α (T a) · #T' (α a) · μ T' a.
Proof.
  exact (pr12 α).
Qed.

Definition Monad_Mor_equiv {C : category}
  {T T' : Monad C} (α β : Monad_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_disp_Monad_Mor_laws.
Defined.

Lemma isaset_Monad_Mor {C : category} (T T' : Monad C) : isaset (Monad_Mor T T').
Proof.
  apply homset_property.
Qed.

Definition Monad_composition {C : category} {T T' T'' : Monad C}
  (α : Monad_Mor T T') (α' : Monad_Mor T' T'')
  : Monad_Mor T T'' := α · α'.

Definition forgetfunctor_Monad (C : category) : functor (category_Monad C) [C,C]
  := pr1_category monads_category_disp.

Lemma forgetMonad_faithful (C : category) : faithful (forgetfunctor_Monad C).
Proof.
  apply faithful_pr1_category.
  intros T T' α.
  apply isaprop_disp_Monad_Mor_laws.
Qed.

(** * Definition and lemmas for bind *)
Section bind.

  (** Definition of bind *)

  Context {C : category} {T : Monad C}.

  Definition bind {a b : C} (f : C⟦a,T b⟧) : C⟦T a,T b⟧ := # T f · μ T b.

  Lemma η_bind {a b : C} (f : C⟦a,T b⟧) : η T a · bind f = f.
  Proof.
    unfold bind.
    rewrite assoc.
    eapply pathscomp0;
      [apply cancel_postcomposition, (! (nat_trans_ax (η T) _ _ f))|]; simpl.
    rewrite <- assoc.
    eapply pathscomp0; [apply maponpaths, Monad_law1|].
    apply id_right.
  Qed.

  Lemma bind_η {a : C} : bind (η T a) = identity (T a).
  Proof.
    apply Monad_law2.
  Qed.

  Lemma bind_bind {a b c : C} (f : C⟦a,T b⟧) (g : C⟦b,T c⟧) :
    bind f · bind g = bind (f · bind g).
  Proof.
    unfold bind; rewrite <- assoc.
    eapply pathscomp0; [apply maponpaths; rewrite assoc;
                        apply cancel_postcomposition, (!nat_trans_ax (μ T) _ _ g)|].
    rewrite !functor_comp, <- !assoc.
    now apply maponpaths, maponpaths, (!Monad_law3 c).
  Qed.

End bind.

(** * Operations for monads based on binary coproducts *)
Section MonadsUsingCoproducts.

  Context {C : category} (T : Monad C) (BC : BinCoproducts C).

  Local Notation "a ⊕ b" := (BinCoproductObject (BC a b)).

  (** operation of weakening in a monad *)
  Definition mweak (a b : C): C⟦T b, T (a ⊕ b)⟧ := bind (BinCoproductIn2 (BC _ _) · (η T _)).

  (** operation of exchange in a monad *)
  Definition mexch (a b c : C): C⟦T (a ⊕ (b ⊕ c)), T (b ⊕ (a ⊕ c))⟧.
  Proof.
    set (a1 := BinCoproductIn1 (BC _ _) · BinCoproductIn2 (BC _ _): C⟦a, b ⊕ (a ⊕ c)⟧).
    set (a21 := BinCoproductIn1 (BC _ _): C⟦b, b ⊕ (a ⊕ c)⟧).
    set (a22 := BinCoproductIn2 (BC _ _) · BinCoproductIn2 (BC _ _): C⟦c, b ⊕ (a ⊕ c)⟧).
    exact (bind ((BinCoproductArrow _ a1 (BinCoproductArrow _ a21 a22)) · (η T _))).
  Defined.

  (** * Substitution operation for monads *)
  Section MonadSubst.

    Definition monadSubstGen {b:C} (a : C) (e : C⟦b,T a⟧) : C⟦T (b ⊕ a), T a⟧ :=
      bind (BinCoproductArrow _ e (η T a)).

    Lemma subst_interchange_law_gen (c b a : C) (e : C⟦c,T (b ⊕ a)⟧) (f : C⟦b,T a⟧):
      (monadSubstGen _ e) · (monadSubstGen _ f) =
        (mexch c b a) · (monadSubstGen _ (f · (mweak c a)))
          · (monadSubstGen _ (e · (monadSubstGen _ f))).
    Proof.
      unfold monadSubstGen, mexch.
      do 3 rewrite bind_bind.
      apply maponpaths.
      apply BinCoproductArrowsEq.
      + do 4 rewrite assoc.
        do 2 rewrite BinCoproductIn1Commutes.
        rewrite <- assoc.
        rewrite bind_bind.
        rewrite <- assoc.
        rewrite (η_bind(a:=let (pr1, _) := pr1 (BC b (c ⊕ a)) in pr1)).
        rewrite <- assoc.
        apply pathsinv0.
        eapply pathscomp0.
        * apply cancel_precomposition.
          rewrite assoc.
          rewrite BinCoproductIn2Commutes.
          rewrite (η_bind(a:=(c ⊕ a))).
          apply idpath.
        * now rewrite BinCoproductIn1Commutes.
      + rewrite assoc.
        rewrite BinCoproductIn2Commutes.
        rewrite (η_bind(a:=b ⊕ a)).
        do 3 rewrite assoc.
        rewrite BinCoproductIn2Commutes.
        apply BinCoproductArrowsEq.
        * rewrite BinCoproductIn1Commutes.
          rewrite <- assoc.
          rewrite bind_bind.
          do 2 rewrite assoc.
          rewrite BinCoproductIn1Commutes.
          rewrite <- assoc.
          rewrite (η_bind(a:=let (pr1, _) := pr1 (BC b (c ⊕ a)) in pr1)).
          rewrite assoc.
          rewrite BinCoproductIn1Commutes.
          unfold mweak.
          rewrite <- assoc.
          rewrite bind_bind.
          apply pathsinv0.
          apply remove_id_right; try now idtac.
          rewrite <- bind_η.
          apply maponpaths.
          rewrite <- assoc.
          rewrite (η_bind(a:=let (pr1, _) := pr1 (BC c a) in pr1)).
          now rewrite BinCoproductIn2Commutes.
        * rewrite BinCoproductIn2Commutes.
          rewrite <- assoc.
          rewrite bind_bind.
          do 2 rewrite assoc.
          rewrite BinCoproductIn2Commutes.
          do 2 rewrite <- assoc.
          rewrite (η_bind(a:=let (pr1, _) := pr1 (BC b (c ⊕ a)) in pr1)).
          apply pathsinv0.
          eapply pathscomp0.
      - apply cancel_precomposition.
        rewrite assoc.
        rewrite BinCoproductIn2Commutes.
        rewrite (η_bind(a:=(c ⊕ a))).
        apply idpath.
      - now rewrite BinCoproductIn2Commutes.
    Qed.

    Context (TC : Terminal C).

    Local Notation "1" := TC.

    Definition monadSubst (a : C) (e : C⟦1,T a⟧) : C⟦T (1 ⊕ a), T a⟧ :=
      monadSubstGen a e.

    Lemma subst_interchange_law (a : C) (e : C⟦1,T (1 ⊕ a)⟧) (f : C⟦1,T a⟧):
      (monadSubst _ e) · (monadSubst _ f) =
        (mexch 1 1 a) · (monadSubst _ (f · (mweak 1 a)))
          · (monadSubst _ (e · (monadSubst _ f))).
    Proof.
      apply subst_interchange_law_gen.
    Qed.

  End MonadSubst.

End MonadsUsingCoproducts.

(** * Helper lemma for showing two monads are equal *)
Section Monad_eq_helper.
  (** * Alternate (equivalent) definition of Monad *)
  Section Monad'_def.

    Definition raw_Monad_data (C : category) : UU :=
      ∑ F : C -> C, (((∏ a b : ob C, a --> b -> F a --> F b) ×
                      (∏ a : ob C, F (F a) --> F a)) ×
                     (∏ a : ob C, a --> F a)).

    #[reversible=no] Coercion functor_data_from_raw_Monad_data {C : category} (T : raw_Monad_data C) :
      functor_data C C := make_functor_data (pr1 T) (pr1 (pr1 (pr2 T))).

    Definition Monad'_data_laws {C : category} (T : raw_Monad_data C) :=
      ((is_functor T) ×
       (is_nat_trans (functor_composite_data T T) T (pr2 (pr1 (pr2 T))))) ×
      (is_nat_trans (functor_identity C) T (pr2 (pr2 T))).

    Definition Monad'_data (C : category) := ∑ (T : raw_Monad_data C), Monad'_data_laws T.

    Definition Monad'_data_to_Monad_data {C : category} (T : Monad'_data C) : disp_Monad_data (_,, pr1 (pr1 (pr2 T))) :=
      ((pr2 (pr1 (pr2 (pr1 T))),, (pr2 (pr1 (pr2 T))))),,
       (pr2 (pr2 (pr1 T)),, (pr2 (pr2 T))).

    Definition Monad' (C : category) := ∑ (T : Monad'_data C),
                                             (disp_Monad_laws (Monad'_data_to_Monad_data T)).
  End Monad'_def.

  (** * Equivalence of Monad and Monad' *)
  Section Monad_Monad'_equiv.
    Definition Monad'_to_Monad {C : category} (T : Monad' C) : Monad C :=
      (_,,(Monad'_data_to_Monad_data (pr1 T),, pr2 T)).

    Definition Monad_to_raw_data {C : category} (T : Monad C) : raw_Monad_data C.
    Proof.
      use tpair.
      - exact (functor_on_objects T).
      - use tpair.
        + use tpair.
          * exact (@functor_on_morphisms C C T).
          * exact (μ T).
        + exact (η T).
    Defined.

    Definition Monad_to_Monad'_data {C : category} (T : Monad C) : Monad'_data C :=
      (Monad_to_raw_data T,, ((pr2 (T : functor C C),, (pr2 (μ T))),, pr2 (η T))).

    Definition Monad_to_Monad' {C : category} (T : Monad C) : Monad' C :=
      (Monad_to_Monad'_data T,, pr22 T).

    Definition Monad'_to_Monad_to_Monad' {C : category} (T : Monad' C) :
      Monad_to_Monad' (Monad'_to_Monad T) = T := (idpath T).

    Definition Monad_to_Monad'_to_Monad {C : category} (T : Monad C) :
      Monad'_to_Monad (Monad_to_Monad' T) = T := (idpath T).

  End Monad_Monad'_equiv.

  Lemma Monad'_eq_raw_data (C : category) (T T' : Monad' C) :
    pr1 (pr1 T) = pr1 (pr1 T') -> T = T'.
  Proof.
    intro e.
    apply subtypePath.
    - intro. now apply isaprop_disp_Monad_laws.
    - apply subtypePath.
      + intro. apply isapropdirprod.
        * apply isapropdirprod.
          -- apply (isaprop_is_functor C C), homset_property.
          -- apply (isaprop_is_nat_trans C C), homset_property.
        * apply (isaprop_is_nat_trans C C), homset_property.
      + apply e.
  Qed.

  Lemma Monad_eq_raw_data (C : category) (T T' : Monad C) :
    Monad_to_raw_data T = Monad_to_raw_data T' -> T = T'.
  Proof.
    intro e.
    apply (invmaponpathsweq (_,, (isweq_iso _ _ (@Monad_to_Monad'_to_Monad C)
                                             (@Monad'_to_Monad_to_Monad' C)))).
    now apply (Monad'_eq_raw_data C).
  Qed.

End Monad_eq_helper.

Section Monads_from_adjunctions.

  Definition  functor_from_adjunction {C D : category}
    {L : functor C D} {R : functor D C} (H : are_adjoints L R) : functor C C := L∙R.

  Definition Monad_data_from_adjunction {C D : category} {L : functor C D}
    {R : functor D C} (H : are_adjoints L R) : disp_Monad_data (functor_from_adjunction H).
  Proof.
    use tpair.
    - exact (pre_whisker L (post_whisker (adjcounit H) R)).
    - exact (adjunit H).
  Defined.

  Lemma Monad_laws_from_adjunction {C D : category} {L : functor C D}
    {R : functor D C} (H : are_adjoints L R) : disp_Monad_laws (Monad_data_from_adjunction H).
  Proof.
    cbn.
    use make_dirprod.
    + use make_dirprod.
      * intro c; cbn.
        apply triangle_id_right_ad.
      * intro c; cbn.
        rewrite <- functor_id.
        rewrite <- functor_comp.
        apply maponpaths.
        apply triangle_id_left_ad.
    + intro c; cbn.
      do 2 (rewrite <- functor_comp).
      apply maponpaths.
      apply (nat_trans_ax ((counit_from_are_adjoints H))).
  Qed.


  Definition Monad_from_adjunction {C D : category} {L : functor C D}
    {R : functor D C} (H : are_adjoints L R) : Monad C.
  Proof.
    exists (functor_from_adjunction H).
    exact (Monad_data_from_adjunction H,, Monad_laws_from_adjunction H).
  Defined.

End Monads_from_adjunctions.
