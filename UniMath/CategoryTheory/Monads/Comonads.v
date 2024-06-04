(** **********************************************************

Contents:
        - dualization of the contents of [Monads.v], but not the part on substitution (that would become redecoration), i.e., Section [MonadsUsingCoproducts]

Written by Ralph Matthes, 2023

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

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Core.Univalence.


Local Open Scope cat.

Section Comonad_disp_def.

  Context {C : category}.

  Definition disp_Comonad_data (F : functor C C) : UU :=
    (F ⟹ F ∙ F) × (F ⟹ functor_identity C).

  Definition disp_δ {F : functor C C} (T : disp_Comonad_data F) : F ⟹ F ∙ F := pr1 T.
  Definition disp_ε {F : functor C C} (T : disp_Comonad_data F) : F ⟹ functor_identity C := pr2 T.
  (** the names of the components follow Mac Lane *)

  Definition disp_Comonad_laws {F : functor C C} (T : disp_Comonad_data F) : UU :=
    (
      (∏ c : C, disp_δ T c · disp_ε T (F c)  = identity (F c))
      ×
      (∏ c : C, disp_δ T c · #F (disp_ε T c)  = identity (F c)) )
      ×
      (∏ c : C, disp_δ T c · #F (disp_δ T c)  = disp_δ T c · disp_δ T (F c)).

  Lemma isaprop_disp_Comonad_laws {F : functor C C} (T : disp_Comonad_data F) : isaprop (disp_Comonad_laws T).
  Proof.
    repeat apply isapropdirprod;
      apply impred; intro c; apply C.
  Qed.

  Definition disp_Comonad_Mor_laws {F F' : functor C C} (T : disp_Comonad_data F) (T' : disp_Comonad_data F') (α : F ⟹ F') : UU :=
    (∏ a : C, α a · disp_δ T' a  =  disp_δ T a · #F (α a) · α (F' a)) ×
    (∏ a : C, α a · disp_ε T' a  = disp_ε T a).

  Lemma isaprop_disp_Comonad_Mor_laws  {F F' : functor C C} (T : disp_Comonad_data F) (T' : disp_Comonad_data F') (α : F ⟹ F')
    : isaprop (disp_Comonad_Mor_laws T T' α).
  Proof.
    apply isapropdirprod;
      apply impred; intro c; apply C.
  Qed.

  Lemma comonads_category_id_subproof {F : functor C C}  (T : disp_Comonad_data F) (Tlaws : disp_Comonad_laws T) :
    disp_Comonad_Mor_laws T T (nat_trans_id F).
  Proof.
    split; intros a; simpl.
    - now rewrite id_left, id_right, functor_id, id_right.
    - now apply id_left.
  Qed.

  Lemma comonads_category_comp_subproof {F F' F'' : functor C C}
    (T : disp_Comonad_data F) (Tlaws : disp_Comonad_laws T)
    (T' : disp_Comonad_data F') (T'laws : disp_Comonad_laws T')
    (T'' : disp_Comonad_data F'') (T''laws : disp_Comonad_laws T'')
    (α : F ⟹ F') (α' : F' ⟹ F'') :
    disp_Comonad_Mor_laws T T' α → disp_Comonad_Mor_laws T' T'' α' → disp_Comonad_Mor_laws T T'' (nat_trans_comp _ _ _ α α').
  Proof.
    intros Hα Hα'.
    split; intros; simpl.
    - rewrite assoc'.
      set (H:=pr1 Hα' a); simpl in H.
      rewrite H; clear H.
      rewrite functor_comp.
      set (H:=pr1 Hα a); simpl in H.
      do 2 rewrite assoc.
      rewrite H; clear H; rewrite <- !assoc.
      do 2 apply maponpaths.
      now rewrite !assoc, nat_trans_ax.
    - rewrite assoc'.
      etrans.
      { apply maponpaths, (pr2 Hα'). }
      apply (pr2 Hα).
  Qed.

  Definition comonads_category_disp : disp_cat [C,C].
  Proof.
    use disp_cat_from_SIP_data.
    - intro F. exact (∑ T : disp_Comonad_data F, disp_Comonad_laws T).
    - intros F F' [T Tlaws] [T' T'laws] α. exact (disp_Comonad_Mor_laws T T' α).
    - intros F F' [T Tlaws] [T' T'laws] α. apply isaprop_disp_Comonad_Mor_laws.
    - intros F [T Tlaws]. apply (comonads_category_id_subproof _ Tlaws).
    - intros F F' F'' [T Tlaws] [T' T'laws] [T'' T''laws] α α'.
      apply (comonads_category_comp_subproof _ Tlaws _ T'laws _ T''laws).
  Defined.

  Definition category_Comonad : category := total_category comonads_category_disp.

  Definition Comonad : UU := ob category_Comonad.

  #[reversible=no] Coercion functor_from_Comonad (T : Comonad) : functor C C := pr1 T.

  Definition δ (T : Comonad) : T ⟹ T ∙ T := pr112 T.
  Definition ε (T : Comonad) : T ⟹ functor_identity C := pr212 T.

  Lemma Comonad_law1 {T : Comonad} : ∏ c : C, δ T c · ε T (T c) = identity (T c).
  Proof.
    exact (pr1 (pr122 T)).
  Qed.

  Lemma Comonad_law2 {T : Comonad} : ∏ c : C, δ T c · #T (ε T c)  = identity (T c).
  Proof.
    exact (pr2 (pr122 T)).
  Qed.

  Lemma Comonad_law3 {T : Comonad} : ∏ c : C, δ T c · #T (δ T c) = δ T c · δ T (T c).
  Proof.
    exact (pr222 T).
  Qed.

  Lemma comonads_category_disp_eq (F : functor C C) (T T' : comonads_category_disp F)  : pr1 T = pr1 T' -> T = T'.
  Proof.
    intro H.
    induction T as [T Tlaws].
    induction T' as [T' T'laws].
    use total2_paths_f; [apply H |].
    apply isaprop_disp_Comonad_laws.
  Qed.

  Lemma comonads_category_Pisset (F : functor C C) : isaset (∑ T : disp_Comonad_data F, disp_Comonad_laws T).
  Proof.
    change isaset with (isofhlevel 2).
    apply isofhleveltotal2.
    { apply isasetdirprod; apply [C,C]. }
    intro T.
    apply isasetaprop.
    apply isaprop_disp_Comonad_laws.
  Qed.

  Lemma comonads_category_Hstandard {F : functor C C}
    (T : disp_Comonad_data F) (Tlaws : disp_Comonad_laws T)
    (T' : disp_Comonad_data F) (T'laws : disp_Comonad_laws T') :
    disp_Comonad_Mor_laws T T' (nat_trans_id F) → disp_Comonad_Mor_laws T' T (nat_trans_id F) → T,, Tlaws = T',, T'laws.
  Proof.
    intros H H'.
    apply subtypeInjectivity.
    { intro T0. apply isaprop_disp_Comonad_laws. }
    cbn.
    induction T as [δ ε].
    induction T' as [δ' ε'].
    apply dirprodeq; cbn.
    - apply nat_trans_eq; [apply C|]. intro a.
      assert (Hinst := pr1 H a).
      cbn in Hinst.
      rewrite id_right in Hinst.
      rewrite id_left in Hinst.
      rewrite functor_id in Hinst.
      rewrite id_right in Hinst.
      exact (!Hinst).
    - apply nat_trans_eq; [apply C|]. intro a.
      assert (Hinst := pr2 H a).
      cbn in Hinst.
      rewrite id_left in Hinst.
      exact (!Hinst).
  Qed.

  Definition is_univalent_comonads_category_disp : is_univalent_disp comonads_category_disp.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - exact comonads_category_Pisset.
    - intros F [T Tlaws] [T' T'laws]. apply comonads_category_Hstandard.
  Defined.

End Comonad_disp_def.

Arguments category_Comonad _ : clear implicits.
Arguments Comonad _ : clear implicits.

Definition is_univalent_category_Comonad {C : category} (HC : is_univalent C) :
  is_univalent (category_Comonad C).
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_functor_category. apply HC.
  - apply is_univalent_comonads_category_disp.
Defined.

Section pointfree.

  Context (C : category) (T0: functor C C) (T : disp_Comonad_data T0).

  Let EndC := [C, C].

  Let ε := disp_ε T.
  Let δ := disp_δ T.

  Definition Comonad_laws_pointfree : UU :=
    (
      (nat_trans_comp _ _ _ δ (pre_whisker T0 ε) = identity(C:=EndC) T0)
        ×
      (nat_trans_comp _ _ _ δ (post_whisker ε T0) = identity(C:=EndC) T0) )
        ×
      (nat_trans_comp _ _ _ δ (post_whisker δ T0) = nat_trans_comp _ _ _ δ (pre_whisker T0 δ)).

  Lemma pointfree_is_equiv: Comonad_laws_pointfree <-> disp_Comonad_laws T.
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
  Let ε' := ε: EndC⟦T0', functor_identity C⟧.
  Let δ' := δ: EndC⟦T0', functor_compose T0' T0'⟧.

  Definition Comonad_laws_pointfree_in_functor_category : UU :=
    (
      (δ' · #(pre_composition_functor _ _ _ T0') ε' = identity(C:=EndC) T0')
        ×
      (δ' · #(post_composition_functor _ _ _ T0') ε' = identity(C:=EndC) T0') )
        ×
      (δ' · #(post_composition_functor _ _ _ T0') δ' = (δ' · #(pre_composition_functor _ _ _ T0') δ')).

  (** the last variant of the laws is convertible with the one before *)
  Goal
    Comonad_laws_pointfree = Comonad_laws_pointfree_in_functor_category.
  Proof.
    apply idpath.
  Qed.

End pointfree.

Definition Comonad_Mor {C : category} (T T' : Comonad C) : UU
  := category_Comonad C ⟦T, T'⟧.

#[reversible=no] Coercion nat_trans_from_monad_mor {C : category} (T T' : Comonad C) (s : Comonad_Mor T T')
  : T ⟹ T' := pr1 s.

Definition Comonad_Mor_laws {C : category} {T T' : Comonad C} (α : T ⟹ T')
  : UU :=
  (∏ a : C,  α a · δ T' a =  δ T a · #T (α a) · α (T' a)) ×
    (∏ a : C, α a · ε T' a  = ε T a).

Definition Comonad_Mor_ε {C : category} {T T' : Comonad C} (α : Comonad_Mor T T')
  : ∏ a : C,  α a · ε T' a  = ε T a.
Proof.
  exact (pr22 α).
Qed.

Definition Comonad_Mor_δ {C : category} {T T' : Comonad C} (α : Comonad_Mor T T')
  : ∏ a : C, α a · δ T' a =  δ T a · #T (α a) · α (T' a).
Proof.
  exact (pr12 α).
Qed.

Definition Comonad_Mor_equiv {C : category}
  {T T' : Comonad C} (α β : Comonad_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_disp_Comonad_Mor_laws.
Defined.

Lemma isaset_Comonad_Mor {C : category} (T T' : Comonad C) : isaset (Comonad_Mor T T').
Proof.
  apply homset_property.
Qed.

Definition Comonad_composition {C : category} {T T' T'' : Comonad C}
  (α : Comonad_Mor T T') (α' : Comonad_Mor T' T'')
  : Comonad_Mor T T'' := α · α'.

Definition forgetfunctor_Comonad (C : category) : functor (category_Comonad C) [C,C]
  := pr1_category comonads_category_disp.

Lemma forgetComonad_faithful (C : category) : faithful (forgetfunctor_Comonad C).
Proof.
  apply faithful_pr1_category.
  intros T T' α.
  apply isaprop_disp_Comonad_Mor_laws.
Qed.

(** * Definition and lemmas for cobind *)
Section cobind.

  (** Definition of cobind *)

  Context {C : category} {T : Comonad C}.

  Definition cobind {a b : C} (f : C⟦T a,b⟧) : C⟦T a,T b⟧ := δ T a · # T f.

  Lemma ε_cobind {a b : C} (f : C⟦T a,b⟧) : cobind f · ε T b = f.
  Proof.
    unfold cobind.
    rewrite assoc'.
    etrans.
    { apply maponpaths.
      apply (nat_trans_ax (ε T) _ _ f). }
    rewrite assoc.
    etrans.
    { apply cancel_postcomposition, Comonad_law1. }
    apply id_left.
  Qed.

  Lemma cobind_ε {a : C} : cobind (ε T a) = identity (T a).
  Proof.
    apply Comonad_law2.
  Qed.

  Lemma cobind_cobind {a b c : C} (f : C⟦T a,b⟧) (g : C⟦T b,c⟧) :
    cobind f · cobind g = cobind (cobind f · g).
  Proof.
    unfold cobind; rewrite assoc.
    rewrite !functor_comp.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { rewrite assoc'; apply maponpaths, (nat_trans_ax (δ T) _ _ f). }
    rewrite assoc.
    apply cancel_postcomposition.
    apply (!Comonad_law3 a).
  Qed.

End cobind.

(** * Helper lemma for showing two comonads are equal *)
Section Comonad_eq_helper.
  (** * Alternate (equivalent) definition of Comonad *)
  Section Comonad'_def.

    Definition raw_Comonad_data (C : category) : UU :=
      ∑ F : C -> C, (((∏ a b : ob C, a --> b -> F a --> F b) ×
                      (∏ a : ob C, F a --> F (F a))) ×
                     (∏ a : ob C, F a --> a)).

    #[reversible=no] Coercion functor_data_from_raw_Comonad_data {C : category} (T : raw_Comonad_data C) :
      functor_data C C := make_functor_data (pr1 T) (pr1 (pr1 (pr2 T))).

    Definition Comonad'_data_laws {C : category} (T : raw_Comonad_data C) :=
      ((is_functor T) ×
       (is_nat_trans T (functor_composite_data T T) (pr2 (pr1 (pr2 T))))) ×
      (is_nat_trans T (functor_identity C) (pr2 (pr2 T))).

    Definition Comonad'_data (C : category) := ∑ (T : raw_Comonad_data C), Comonad'_data_laws T.

    Definition Comonad'_data_to_Comonad_data {C : category} (T : Comonad'_data C) : disp_Comonad_data (_,, pr1 (pr1 (pr2 T))) :=
      ((pr2 (pr1 (pr2 (pr1 T))),, (pr2 (pr1 (pr2 T))))),,
       (pr2 (pr2 (pr1 T)),, (pr2 (pr2 T))).

    Definition Comonad' (C : category) := ∑ (T : Comonad'_data C),
                                             (disp_Comonad_laws (Comonad'_data_to_Comonad_data T)).
  End Comonad'_def.

  (** * Equivalence of Comonad and Comonad' *)
  Section Comonad_Comonad'_equiv.
    Definition Comonad'_to_Comonad {C : category} (T : Comonad' C) : Comonad C :=
      (_,,(Comonad'_data_to_Comonad_data (pr1 T),, pr2 T)).

    Definition Comonad_to_raw_data {C : category} (T : Comonad C) : raw_Comonad_data C.
    Proof.
      use tpair.
      - exact (functor_on_objects T).
      - use tpair.
        + use tpair.
          * exact (@functor_on_morphisms C C T).
          * exact (δ T).
        + exact (ε T).
    Defined.

    Definition Comonad_to_Comonad'_data {C : category} (T : Comonad C) : Comonad'_data C :=
      (Comonad_to_raw_data T,, ((pr2 (T : functor C C),, (pr2 (δ T))),, pr2 (ε T))).

    Definition Comonad_to_Comonad' {C : category} (T : Comonad C) : Comonad' C :=
      (Comonad_to_Comonad'_data T,, pr22 T).

    Definition Comonad'_to_Comonad_to_Comonad' {C : category} (T : Comonad' C) :
      Comonad_to_Comonad' (Comonad'_to_Comonad T) = T := (idpath T).

    Definition Comonad_to_Comonad'_to_Comonad {C : category} (T : Comonad C) :
      Comonad'_to_Comonad (Comonad_to_Comonad' T) = T := (idpath T).

  End Comonad_Comonad'_equiv.

  Lemma Comonad'_eq_raw_data (C : category) (T T' : Comonad' C) :
    pr1 (pr1 T) = pr1 (pr1 T') -> T = T'.
  Proof.
    intro e.
    apply subtypePath.
    - intro. now apply isaprop_disp_Comonad_laws.
    - apply subtypePath.
      + intro. apply isapropdirprod.
        * apply isapropdirprod.
          -- apply (isaprop_is_functor C C), homset_property.
          -- apply (isaprop_is_nat_trans C C), homset_property.
        * apply (isaprop_is_nat_trans C C), homset_property.
      + apply e.
  Qed.

  Lemma Comonad_eq_raw_data (C : category) (T T' : Comonad C) :
    Comonad_to_raw_data T = Comonad_to_raw_data T' -> T = T'.
  Proof.
    intro e.
    apply (invmaponpathsweq (_,, (isweq_iso _ _ (@Comonad_to_Comonad'_to_Comonad C)
                                             (@Comonad'_to_Comonad_to_Comonad' C)))).
    now apply (Comonad'_eq_raw_data C).
  Qed.

End Comonad_eq_helper.

Section Comonads_from_adjunctions.

  (** This follow a remark of a single line on p.139 in Mac Lane, 2nd edition. *)

  Definition sndfunctor_from_adjunction {C D : category}
    {L : functor C D} {R : functor D C} (H : are_adjoints L R) : functor D D := R ∙ L.

  Definition Comonad_data_from_adjunction {C D : category} {L : functor C D}
    {R : functor D C} (H : are_adjoints L R) : disp_Comonad_data (sndfunctor_from_adjunction H).
  Proof.
    use tpair.
    - exact (pre_whisker R (post_whisker (adjunit H) L)).
    - exact (adjcounit H).
  Defined.

  Lemma Comonad_laws_from_adjunction {C D : category} {L : functor C D}
    {R : functor D C} (H : are_adjoints L R) : disp_Comonad_laws (Comonad_data_from_adjunction H).
  Proof.
    cbn.
    use make_dirprod.
    + use make_dirprod.
      * intro c; cbn.
        apply triangle_id_left_ad.
      * intro c; cbn.
        rewrite <- functor_id.
        rewrite <- functor_comp.
        apply maponpaths.
        apply triangle_id_right_ad.
    + intro c; cbn.
      do 2 (rewrite <- functor_comp).
      apply maponpaths.
      apply pathsinv0.
      apply (nat_trans_ax ((unit_from_are_adjoints H))).
  Qed.


  Definition Comonad_from_adjunction {C D : category} {L : functor C D}
    {R : functor D C} (H : are_adjoints L R) : Comonad D.
  Proof.
    exists (sndfunctor_from_adjunction H).
    exact (Comonad_data_from_adjunction H,, Comonad_laws_from_adjunction H).
  Defined.

End Comonads_from_adjunctions.
