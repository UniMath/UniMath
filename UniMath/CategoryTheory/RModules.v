(** **********************************************************
Contents:
        - Definition of right modules ([RModule R]) over a monad [R] on [C]
        - category of right modules [category_RModule R D] of range [D] over a monad [R] on [C]
        - Tautological right module [tautological_RModule] : a monad is a module over itself
        - Pullback of a module along a monad morphism [pb_RModule]
        - Pullback of a module morphism along a monad morphism [pb_RModule_Mor]

Following the scheme of Monads.v

Written by: Ambroise Lafont (November 2016)

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Monads.

Local Open Scope cat.

Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of module *)
Section RModule_over_monad.

 Context {B:precategory} (M:Monad B) .
  (** Definition of modules over M of codomain D **)

Section RModule_def.




Definition RModule_data (D:precategory) : UU
  := ∑ F : functor B D, F □ M ⟹ F.

Coercion functor_from_RModule_data (C : precategory) (F : RModule_data C)
  : functor B C := pr1 F.

Definition σ {C : precategory} (F : RModule_data C) : F□M ⟹ F := pr2 F.

Definition RModule_laws  {C:precategory} (T : RModule_data C) : UU :=
      (∏ c : B, #T (η M c) · σ T c = identity (T c))
        × (∏ c : B, #T ((μ M) c) · σ T c = σ T (M c) · σ T c).

Lemma isaprop_RModule_laws (C : precategory) (hs : has_homsets C) (T : RModule_data C) :
   isaprop (RModule_laws T).
Proof.
  repeat apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition RModule (C : precategory) : UU := ∑ T : RModule_data C, RModule_laws T.

Coercion RModule_data_from_RModule (C : precategory) (T : RModule C) : RModule_data C := pr1 T.


Lemma RModule_law1 {C : precategory} {T : RModule C} : ∏ c : B, #T (η M c) · σ T c = identity (T c).
Proof.
exact ( (pr1 (pr2 T))).
Qed.

Lemma RModule_law2 {C : precategory} {T : RModule C} :
  ∏ c : B, #T ((μ M) c) · σ T c = σ T (M c) · σ T c.
Proof.
exact (pr2 ( (pr2 T))).
Qed.

End RModule_def.

(** * Monad precategory *)
Section RModule_precategory.

Definition RModule_Mor_laws {C : precategory} {T T' : RModule_data C} (α : T ⟹ T')
  : UU :=
  ∏ a : B, α (M a) · σ T' a = σ T a · α a.


Lemma isaprop_RModule_Mor_laws (C : precategory) (hs : has_homsets C)
  (T T' : RModule_data C) (α : T ⟹ T')
  : isaprop (RModule_Mor_laws α).
Proof.
  apply impred; intro c; apply hs.
Qed.

Definition RModule_Mor {C : precategory} (T T' : RModule C) : UU
  := ∑ α : T ⟹ T', RModule_Mor_laws α.


Coercion nat_trans_from_module_mor (C : precategory) (T T' : RModule C) (s : RModule_Mor T T')
   : T ⟹ T' := pr1 s.

Definition RModule_Mor_σ {C : precategory} {T T' : RModule C} (α : RModule_Mor T T')
           : ∏ a : B, α (M a) · σ T' a = σ T a · α a
  := pr2 α.

Lemma RModule_identity_laws {C : precategory} (T : RModule C)
  : RModule_Mor_laws (nat_trans_id T).
Proof.
  intro x.
  now rewrite id_right, id_left.
Qed.

Definition RModule_identity {C : precategory} (T : RModule C)
: RModule_Mor T T := tpair _ _ (RModule_identity_laws T).

Lemma RModule_composition_laws {C : precategory} {T T' T'' : RModule C}
  (α : RModule_Mor T T') (α' : RModule_Mor T' T'') : RModule_Mor_laws (nat_trans_comp _ _ _ α α').
Proof.
  red;intros; simpl.
  unfold nat_trans_from_module_mor.
  rewrite assoc.
    etrans; revgoals.
    apply cancel_postcomposition.
    apply (RModule_Mor_σ α a).
    rewrite <- !assoc.
    apply cancel_precomposition.
    apply (RModule_Mor_σ α' a).
Qed.

Definition RModule_composition {C : precategory} {T T' T'' : RModule C}
  (α : RModule_Mor T T') (α' : RModule_Mor T' T'')
  : RModule_Mor T T'' := tpair _ _ (RModule_composition_laws α α').

Definition RModule_Mor_equiv {C : precategory} (hs : has_homsets C)
  {T T' : RModule C} (α β : RModule_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_RModule_Mor_laws, hs.
Defined.

Definition precategory_RModule_ob_mor (C : precategory) : precategory_ob_mor.
Proof.
  exists (RModule C).
  exact (λ T T' : RModule C, RModule_Mor T T').
Defined.

Definition precategory_RModule_data (C : precategory) : precategory_data.
Proof.
  exists (precategory_RModule_ob_mor C).
  exists (@RModule_identity C).
  exact (@RModule_composition C).
Defined.


Lemma precategory_RModule_axioms (C : precategory) (hs : has_homsets C)
  : is_precategory (precategory_RModule_data C).
Proof.
    repeat split; simpl; intros.
  - apply (invmap (RModule_Mor_equiv hs _ _ )).
    apply (@id_left (functor_precategory B C hs)).
  - apply (invmap (RModule_Mor_equiv hs _ _ )).
    apply (@id_right (functor_precategory B C hs)).
  - apply (invmap (RModule_Mor_equiv hs _ _ )).
    apply (@assoc (functor_precategory B C hs)).
Qed.

Definition precategory_RModule (C : category) : precategory
  := tpair _ _ (precategory_RModule_axioms C (homset_property C)).

Lemma has_homsets_RModule (C : category) :
  has_homsets (precategory_RModule C).
Proof.
  intros F G.
  apply isaset_total2 .
  - apply isaset_nat_trans.
    apply homset_property.
  - intros m.
    apply isasetaprop.
    apply isaprop_RModule_Mor_laws.
    apply homset_property.
Qed.

Definition category_RModule (C : category) : category :=
  (precategory_RModule C,, has_homsets_RModule C).



End RModule_precategory.

(** Any monad is a right module over itself *)
Definition tautological_RModule_data  : RModule_data B := ((M:functor _ _) ,, μ M).

Lemma tautological_RModule_law  : RModule_laws tautological_RModule_data.
Proof.
  split; intro c.
  - apply Monad_law2.
  - apply Monad_law3.
Qed.

Definition tautological_RModule : RModule B :=
  (tautological_RModule_data ,, tautological_RModule_law).

End RModule_over_monad.

(** Let m : M -> M' a monad morphism.

m induces a functor m* between the category of right modules over M' and the category of
right modules over M

If T is a module over M', we call m* T the pullback module of T along m
*)
Section Pullback_module.


  Context {B:precategory} {M M':Monad B} (m: Monad_Mor M M').
  Context {C:precategory}.

  Variable (T:RModule M' C).
  Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).

  Definition pb_RModule_σ : T □ M ⟹ T :=  nat_trans_comp _ _ _ (T ∘ m)  (σ _ T).

  Definition pb_RModule_data : ∑ F : functor B C, F □ M ⟹ F :=
    tpair _ (T:functor B C) pb_RModule_σ.

  Lemma pb_RModule_laws : RModule_laws M pb_RModule_data.
  Proof.
    split.
    - intro c.
      cbn.
      rewrite <- (RModule_law1 _ (T:=T)).
      rewrite <- (Monad_Mor_η m).
      rewrite functor_comp.
      apply assoc.
    - simpl.
      intro c.
      rewrite assoc.
      rewrite <- (functor_comp T).
      etrans.
      apply cancel_postcomposition.
      apply maponpaths.
      apply Monad_Mor_μ.
      rewrite functor_comp.
      rewrite <- assoc.
      etrans.
      apply cancel_precomposition.
      apply RModule_law2.
      repeat rewrite functor_comp.
      etrans.
      rewrite <- assoc.
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      apply (nat_trans_ax (σ M' T)).
      now repeat rewrite assoc.
  Qed.

  Definition pb_RModule : RModule M C := tpair _ _ pb_RModule_laws.

End Pullback_module.

(**

Let m:M -> M' be a monad morphism et n : T -> T' a morphism in the category of modules over M'.
In this section we construct the morphism m* n : m*T -> m*T' in the category of modules over M
between the pullback modules along m.

*)
Section Pullback_Module_Morphism.

  Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory} {T T' :RModule M' C}
          (n : RModule_Mor _ T T').

  Local Notation pbmT := (pb_RModule m T).
  Local Notation pbmT' := (pb_RModule m T').

  Lemma pb_RModule_Mor_law : RModule_Mor_laws M (T:=pbmT) (T':=pbmT') n.
  Proof.
    intros b.
    cbn.
    eapply pathscomp0;revgoals.
    rewrite <-assoc.
    apply cancel_precomposition.
    apply RModule_Mor_σ.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply nat_trans_ax.
  Qed.

  Definition pb_RModule_Mor  : RModule_Mor _  pbmT pbmT'  := ( _ ,, pb_RModule_Mor_law).

End Pullback_Module_Morphism.