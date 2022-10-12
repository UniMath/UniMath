(** **********************************************************

Contents:

        - Definition of monads ([Monad])
        - category of monads [category_Monad C] on [C]
        - Forgetful functor [forgetfunctor_Monad] from monads
             to endofunctors on [C]
        - Haskell style bind operation ([bind])
        - A substitution operator for monads ([monadSubst])
        - A helper lemma for proving equality of Monads ([Monad_eq_raw_data])

TODO:
        - Proof that [precategory_Monad C] is univalent if [C] is
          (should follow easily from same result for relative monads [RelativeMonads.is_univalent_RelMonad] and
           isomorphism of categories with Kleisli triples [KTriplesEquiv.is_catiso])


Written by: Benedikt Ahrens (started March 2015)
Extended by: Anders Mörtberg, 2016
Extended by: Ralph Matthes, 2017 (Section MonadsUsingCoproducts)

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Local Open Scope cat.

(** * Definition of monads *)
Section Monad_def.

Definition functor_with_μ (C : precategory_data) : UU
  := ∑ F : functor C C, F ∙ F ⟹ F.

Coercion functor_from_functor_with_μ (C : precategory_data) (F : functor_with_μ C)
  : functor C C := pr1 F.

Definition μ {C : precategory_data} (F : functor_with_μ C) : F ∙ F ⟹ F := pr2 F.

Definition Monad_data (C : precategory_data) : UU :=
   ∑ F : functor_with_μ C, functor_identity C ⟹ F.

Coercion functor_with_μ_from_Monad_data (C : precategory_data) (F : Monad_data C)
  : functor_with_μ C := pr1 F.

Definition η {C : precategory_data} (F : Monad_data C)
  : functor_identity C ⟹ F := pr2 F.

Definition Monad_laws {C : precategory_data} (T : Monad_data C) : UU :=
    (
      (∏ c : C, η T (T c) · μ T c = identity (T c))
        ×
      (∏ c : C, #T (η T c) · μ T c = identity (T c)))
        ×
      (∏ c : C, #T (μ T c) · μ T c = μ T (T c) · μ T c).

Section pointfree.

  Context (C : category) (T : Monad_data C).

  Let EndC := [C, C].

  Let η := η T.
  Let μ := μ T.
  Let T0 := functor_from_functor_with_μ C T.

Definition Monad_laws_pointfree : UU :=
    (
      (nat_trans_comp _ _ _ (pre_whisker T0 η) μ = identity(C:=EndC) T0)
        ×
      (nat_trans_comp _ _ _ (post_whisker η T0) μ = identity(C:=EndC) T0))
        ×
      (nat_trans_comp _ _ _ (post_whisker μ T0) μ = nat_trans_comp _ _ _ (pre_whisker T0 μ) μ).

Lemma pointfree_is_equiv: Monad_laws_pointfree <-> Monad_laws T.
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

Let T0' := (functor_from_functor_with_μ C T): EndC.
Let η' := η: EndC⟦functor_identity C, T0'⟧.
Let μ' := μ: EndC⟦functor_compose T0' T0', T0'⟧.

Definition Monad_laws_pointfree_in_functor_category : UU :=
    (
      (#(pre_composition_functor _ _ _ T0') η' · μ' = identity(C:=EndC) T0')
        ×
      (#(post_composition_functor _ _ _ T0') η' · μ' = identity(C:=EndC) T0'))
        ×
      (#(post_composition_functor _ _ _ T0') μ' · μ' = (#(pre_composition_functor _ _ _ T0') μ') · μ').

(** the last variant of the laws is convertible with the one before *)
Goal
  Monad_laws_pointfree = Monad_laws_pointfree_in_functor_category.
Proof.
  apply idpath.
Qed.

End pointfree.

Lemma isaprop_Monad_laws (C : category) (T : Monad_data C) :
   isaprop (Monad_laws T).
Proof.
  repeat apply isapropdirprod;
  apply impred; intro c; apply homset_property.
Qed.

Definition Monad (C : precategory_data) : UU := ∑ T : Monad_data C, Monad_laws T.

Coercion Monad_data_from_Monad (C : precategory_data) (T : Monad C) : Monad_data C := pr1 T.

Lemma Monad_law1 {C : precategory_data} {T : Monad C} : ∏ c : C, η T (T c) · μ T c = identity (T c).
Proof.
  exact (pr1 (pr1 (pr2 T))).
Qed.

Lemma Monad_law2 {C : precategory_data} {T : Monad C} : ∏ c : C, #T (η T c) · μ T c = identity (T c).
Proof.
  exact (pr2 (pr1 (pr2 T))).
Qed.

Lemma Monad_law3 {C : precategory_data} {T : Monad C} : ∏ c : C, #T (μ T c) · μ T c = μ T (T c) · μ T c.
Proof.
  exact (pr2 (pr2 T)).
Qed.

End Monad_def.

(** * Monad precategory *)
Section Monad_precategory.

Definition Monad_Mor_laws {C : precategory_data} {T T' : Monad_data C} (α : T ⟹ T')
  : UU :=
  (∏ a : C, μ T a · α a = α (T a) · #T' (α a) · μ T' a) ×
  (∏ a : C, η T a · α a = η T' a).

Lemma isaprop_Monad_Mor_laws (C : precategory_data) (hs : has_homsets C)
  (T T' : Monad_data C) (α : T ⟹ T')
  : isaprop (Monad_Mor_laws α).
Proof.
  apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition Monad_Mor {C : precategory_data} (T T' : Monad_data C) : UU
  := ∑ α : T ⟹ T', Monad_Mor_laws α.

Coercion nat_trans_from_monad_mor (C : precategory_data) (T T' : Monad_data C) (s : Monad_Mor T T')
  : T ⟹ T' := pr1 s.

Definition Monad_Mor_η {C : precategory_data} {T T' : Monad_data C} (α : Monad_Mor T T')
  : ∏ a : C, η T a · α a = η T' a.
Proof.
  exact (pr2 (pr2 α)).
Qed.

Definition Monad_Mor_μ {C : precategory_data} {T T' : Monad_data C} (α : Monad_Mor T T')
  : ∏ a : C, μ T a · α a = α (T a) · #T' (α a) · μ T' a.
Proof.
  exact (pr1 (pr2 α)).
Qed.

Lemma Monad_identity_laws {C : precategory} (T : Monad_data C)
  : Monad_Mor_laws (nat_trans_id T).
Proof.
  split; intros a; simpl.
  - now rewrite id_left, id_right, functor_id, id_left.
  - now apply id_right.
Qed.

Definition Monad_identity {C : precategory} (T : Monad C)
  : Monad_Mor T T := tpair _ _ (Monad_identity_laws T).

Lemma Monad_composition_laws {C : precategory} {T T' T'' : Monad_data C}
  (α : Monad_Mor T T') (α' : Monad_Mor T' T'') : Monad_Mor_laws (nat_trans_comp _ _ _ α α').
Proof.
  split; intros; simpl.
  - rewrite assoc.
    set (H:=Monad_Mor_μ α a); simpl in H.
    rewrite H; clear H; rewrite <- !assoc.
    set (H:=Monad_Mor_μ α' a); simpl in H.
    rewrite H; clear H.
    rewrite functor_comp.
    apply maponpaths.
    now rewrite !assoc, nat_trans_ax.
  - rewrite assoc.
    eapply pathscomp0; [apply cancel_postcomposition, Monad_Mor_η|].
    apply Monad_Mor_η.
Qed.

Definition Monad_composition {C : precategory} {T T' T'' : Monad C}
  (α : Monad_Mor T T') (α' : Monad_Mor T' T'')
  : Monad_Mor T T'' := tpair _ _ (Monad_composition_laws α α').

Definition Monad_Mor_equiv (C : category)
  {T T' : Monad_data C} (α β : Monad_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_Monad_Mor_laws, homset_property.
Defined.

Definition precategory_Monad_ob_mor (C : precategory_data) : precategory_ob_mor.
Proof.
  exists (Monad C).
  exact (λ T T' : Monad C, Monad_Mor T T').
Defined.

Definition precategory_Monad_data (C : precategory) : precategory_data.
Proof.
  exists (precategory_Monad_ob_mor C).
  exists (@Monad_identity C).
  exact (@Monad_composition C).
Defined.

Lemma precategory_Monad_axioms (C : category)
  : is_precategory (precategory_Monad_data C).
Proof.
  repeat split; simpl; intros.
  - apply (invmap (Monad_Mor_equiv _ _ _ )).
    apply (@id_left (functor_category C C)).
  - apply (invmap (Monad_Mor_equiv _ _ _ )).
    apply (@id_right (functor_category C C)).
  - apply (invmap (Monad_Mor_equiv _ _ _ )).
    apply (@assoc (functor_category C C)).
  - apply (invmap (Monad_Mor_equiv _ _ _ )).
    apply (@assoc' (functor_category C C)).
Qed.

Definition precategory_Monad (C : category) : precategory
  := tpair _ _ (precategory_Monad_axioms C).


Lemma has_homsets_precategory_Monad (C : category) : has_homsets (precategory_Monad C).
Proof.
  intros F G.
  simpl.
  unfold Monad_Mor.
  apply isaset_total2 .
  - apply isaset_nat_trans.
    apply homset_property.
  - intro m.
    apply isasetaprop.
    apply isaprop_Monad_Mor_laws.
    apply homset_property.
Qed.

Corollary has_homsets_Monad (C : category) : has_homsets (precategory_Monad C).
Proof.
  exact (has_homsets_precategory_Monad C).
Qed.

Definition category_Monad (C : category) : category :=
  (precategory_Monad C ,, has_homsets_Monad C ).


Definition forgetfunctor_Monad (C : category) :
  functor (category_Monad C) (functor_category C C).
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (λ M, pr1 M: functor C C).
    + exact (λ M N f, pr1 f).
  - abstract (split; red; intros; reflexivity).
Defined.

Lemma forgetMonad_faithful C : faithful (forgetfunctor_Monad C).
Proof.
  intros M N.
  apply isinclpr1.
  apply isaprop_Monad_Mor_laws.
  apply homset_property.
Qed.

End Monad_precategory.

(** * Definition and lemmas for bind *)
Section bind.

(** Definition of bind *)
Definition bind {C : precategory_data} {T : Monad_data C} {a b : C} (f : C⟦a,T b⟧) : C⟦T a,T b⟧ := # T f · μ T b.

Context {C : precategory} {T : Monad C}.

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
Definition mweak (a b: C): C⟦T b, T (a ⊕ b)⟧ := bind (BinCoproductIn2 (BC _ _) · (η T _)).

(** operation of exchange in a monad *)
Definition mexch (a b c:C): C⟦T (a ⊕ (b ⊕ c)), T (b ⊕ (a ⊕ c))⟧.
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

    Definition raw_Monad_data (C : precategory_ob_mor) : UU :=
      ∑ F : C -> C, (((∏ a b : ob C, a --> b -> F a --> F b) ×
                      (∏ a : ob C, F (F a) --> F a)) ×
                     (∏ a : ob C, a --> F a)).

    Coercion functor_data_from_raw_Monad_data {C : precategory_ob_mor} (T : raw_Monad_data C) :
      functor_data C C := make_functor_data (pr1 T) (pr1 (pr1 (pr2 T))).

    Definition Monad'_data_laws {C : precategory} (T : raw_Monad_data C) :=
      ((is_functor T) ×
       (is_nat_trans (functor_composite_data T T) T (pr2 (pr1 (pr2 T))))) ×
      (is_nat_trans (functor_identity C) T (pr2 (pr2 T))).

    Definition Monad'_data (C : precategory) := ∑ (T : raw_Monad_data C), Monad'_data_laws T.

    Definition Monad'_data_to_Monad_data {C : precategory} (T : Monad'_data C) : Monad_data C :=
      (((_,, pr1 (pr1 (pr2 T))),,
        (pr2 (pr1 (pr2 (pr1 T))),, (pr2 (pr1 (pr2 T))))),,
       (pr2 (pr2 (pr1 T)),, (pr2 (pr2 T)))).

    Definition Monad' (C : precategory) := ∑ (T : Monad'_data C),
                                             (Monad_laws (Monad'_data_to_Monad_data T)).
  End Monad'_def.

  (** * Equivalence of Monad and Monad' *)
  Section Monad_Monad'_equiv.
    Definition Monad'_to_Monad {C : precategory} (T : Monad' C) : Monad C :=
      (Monad'_data_to_Monad_data (pr1 T),, pr2 T).

    Definition Monad_to_raw_data {C : precategory} (T : Monad C) : raw_Monad_data C.
    Proof.
      use tpair.
      - exact (functor_on_objects T).
      - use tpair.
        + use tpair.
          * exact (@functor_on_morphisms C C T).
          * exact (μ T).
        + exact (η T).
    Defined.

    Definition Monad_to_Monad'_data {C : precategory} (T : Monad C) : Monad'_data C :=
      (Monad_to_raw_data T,, ((pr2 (T : functor C C),, (pr2 (μ T))),, pr2 (η T))).

    Definition Monad_to_Monad' {C : precategory} (T : Monad C) : Monad' C :=
      (Monad_to_Monad'_data T,, pr2 T).

    Definition Monad'_to_Monad_to_Monad' {C : precategory} (T : Monad' C) :
      Monad_to_Monad' (Monad'_to_Monad T) = T := (idpath T).

    Definition Monad_to_Monad'_to_Monad {C : precategory} (T : Monad C) :
      Monad'_to_Monad (Monad_to_Monad' T) = T := (idpath T).

  End Monad_Monad'_equiv.

  Lemma Monad'_eq_raw_data (C : category) (T T' : Monad' C) :
    pr1 (pr1 T) = pr1 (pr1 T') -> T = T'.
  Proof.
    intro e.
    apply subtypePath.
    - intro. now apply isaprop_Monad_laws.
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

Definition functor_with_μ_from_adjunction {C D : category}
  {L : functor C D} {R : functor D C} (H : are_adjoints L R) :
  functor_with_μ C.
Proof.
  use tpair.
  - exact (L∙R).
  - exact (pre_whisker L (post_whisker (adjcounit H) R)).
Defined.

Definition Monad_data_from_adjunction {C D : category} {L : functor C D}
  {R : functor D C} (H : are_adjoints L R) : Monad_data C.
Proof.
  use tpair.
  - exact (functor_with_μ_from_adjunction H).
  - cbn.
    exact (adjunit H).
Defined.

Definition Monad_from_adjunction {C D : category} {L : functor C D}
  {R : functor D C} (H : are_adjoints L R) : Monad C.
Proof.
  use tpair.
  - exact (Monad_data_from_adjunction H).
  - cbn.
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
Defined.

End Monads_from_adjunctions.
