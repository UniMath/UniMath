(** **********************************************************
Contents:
        - Definition of left modules ([LModule R]) over a monad [R] on [C]
        - category of left modules [category_LModule R D] of range [D] over a monad [R] on [C]
        - Tautological left module [tautological_LModule] : a monad is a module over itself
        - Pullback of a module along a monad morphism [pb_LModule]
        - Pullback of a module morphism along a monad morphism [pb_LModule_Mor]

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
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of module *)
Section LModule_over_monad.

 Context {B:precategory} (M:Monad B) .
  (** Definition of modules over M of codomain D **)

Section LModule_def.




Definition LModule_data (D:precategory) : UU
  := ∑ F : functor B D, F □ M ⟹ F.

Coercion functor_from_LModule_data (C : precategory) (F : LModule_data C)
  : functor B C := pr1 F.

Definition lm_mult {C : precategory} (F : LModule_data C) : F□M ⟹ F := pr2 F.
Local Notation σ := lm_mult.

Definition LModule_laws  {C:precategory} (T : LModule_data C) : UU :=
      (∏ c : B, #T (η M c) · σ T c = identity (T c))
        × (∏ c : B, #T ((μ M) c) · σ T c = σ T (M c) · σ T c).

Lemma isaprop_LModule_laws (C : precategory) (hs : has_homsets C) (T : LModule_data C) :
   isaprop (LModule_laws T).
Proof.
  repeat apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition LModule (C : precategory) : UU := ∑ T : LModule_data C, LModule_laws T.

Coercion LModule_data_from_LModule (C : precategory) (T : LModule C) : LModule_data C := pr1 T.


Lemma LModule_law1 {C : precategory} {T : LModule C} : ∏ c : B, #T (η M c) · σ T c = identity (T c).
Proof.
exact ( (pr1 (pr2 T))).
Qed.

Lemma LModule_law2 {C : precategory} {T : LModule C} :
  ∏ c : B, #T ((μ M) c) · σ T c = σ T (M c) · σ T c.
Proof.
exact (pr2 ( (pr2 T))).
Qed.

End LModule_def.

(** * Monad precategory *)
Section LModule_precategory.

Local Notation σ := lm_mult.
Definition LModule_Mor_laws {C : precategory} {T T' : LModule_data C} (α : T ⟹ T')
  : UU :=
  ∏ a : B, α (M a) · σ T' a = σ T a · α a.


Lemma isaprop_LModule_Mor_laws (C : precategory) (hs : has_homsets C)
  (T T' : LModule_data C) (α : T ⟹ T')
  : isaprop (LModule_Mor_laws α).
Proof.
  apply impred; intro c; apply hs.
Qed.

Definition LModule_Mor {C : precategory} (T T' : LModule C) : UU
  := ∑ α : T ⟹ T', LModule_Mor_laws α.


Coercion nat_trans_from_module_mor (C : precategory) (T T' : LModule C) (s : LModule_Mor T T')
   : T ⟹ T' := pr1 s.

Definition LModule_Mor_σ {C : precategory} {T T' : LModule C} (α : LModule_Mor T T')
           : ∏ a : B, α (M a) · σ T' a = σ T a · α a
  := pr2 α.

Lemma LModule_identity_laws {C : precategory} (T : LModule C)
  : LModule_Mor_laws (nat_trans_id T).
Proof.
  intro x.
  now rewrite id_right, id_left.
Qed.

Definition LModule_identity {C : precategory} (T : LModule C)
: LModule_Mor T T := tpair _ _ (LModule_identity_laws T).

Lemma LModule_composition_laws {C : precategory} {T T' T'' : LModule C}
  (α : LModule_Mor T T') (α' : LModule_Mor T' T'') : LModule_Mor_laws (nat_trans_comp _ _ _ α α').
Proof.
  red;intros; simpl.
  unfold nat_trans_from_module_mor.
  rewrite assoc.
    etrans; revgoals.
    apply cancel_postcomposition.
    apply (LModule_Mor_σ α a).
    rewrite <- !assoc.
    apply cancel_precomposition.
    apply (LModule_Mor_σ α' a).
Qed.

Definition LModule_composition {C : precategory} {T T' T'' : LModule C}
  (α : LModule_Mor T T') (α' : LModule_Mor T' T'')
  : LModule_Mor T T'' := tpair _ _ (LModule_composition_laws α α').

Definition LModule_Mor_equiv {C : precategory} (hs : has_homsets C)
  {T T' : LModule C} (α β : LModule_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_LModule_Mor_laws, hs.
Defined.

Definition precategory_LModule_ob_mor (C : precategory) : precategory_ob_mor.
Proof.
  exists (LModule C).
  exact (λ T T' : LModule C, LModule_Mor T T').
Defined.

Definition precategory_LModule_data (C : precategory) : precategory_data.
Proof.
  exists (precategory_LModule_ob_mor C).
  exists (@LModule_identity C).
  exact (@LModule_composition C).
Defined.


Lemma precategory_LModule_axioms (C : precategory) (hs : has_homsets C)
  : is_precategory (precategory_LModule_data C).
Proof.
    repeat split; simpl; intros.
  - apply (invmap (LModule_Mor_equiv hs _ _ )).
    apply (@id_left (functor_precategory B C hs)).
  - apply (invmap (LModule_Mor_equiv hs _ _ )).
    apply (@id_right (functor_precategory B C hs)).
  - apply (invmap (LModule_Mor_equiv hs _ _ )).
    apply (@assoc (functor_precategory B C hs)).
Qed.

Definition precategory_LModule (C : category) : precategory
  := tpair _ _ (precategory_LModule_axioms C (homset_property C)).

Lemma has_homsets_LModule (C : category) :
  has_homsets (precategory_LModule C).
Proof.
  intros F G.
  apply isaset_total2 .
  - apply isaset_nat_trans.
    apply homset_property.
  - intros m.
    apply isasetaprop.
    apply isaprop_LModule_Mor_laws.
    apply homset_property.
Qed.

Definition category_LModule (C : category) : category :=
  (precategory_LModule C,, has_homsets_LModule C).



End LModule_precategory.

(** Any monad is a left module over itself *)
Definition tautological_LModule_data  : LModule_data B := ((M:functor _ _) ,, μ M).

Lemma tautological_LModule_law  : LModule_laws tautological_LModule_data.
Proof.
  split; intro c.
  - apply Monad_law2.
  - apply Monad_law3.
Qed.

Definition tautological_LModule : LModule B :=
  (tautological_LModule_data ,, tautological_LModule_law).

End LModule_over_monad.

(** Let m : M -> M' a monad morphism.

m induces a functor m* between the category of left modules over M' and the category of
left modules over M

If T is a module over M', we call m* T the pullback module of T along m
*)
Section Pullback_module.


  Context {B:precategory} {M M':Monad B} (m: Monad_Mor M M').
  Context {C:precategory}.

  Variable (T:LModule M' C).
  Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).
  Local Notation σ := lm_mult.

  Definition pb_LModule_σ : T □ M ⟹ T :=  nat_trans_comp _ _ _ (T ∘ m)  (σ _ T).

  Definition pb_LModule_data : ∑ F : functor B C, F □ M ⟹ F :=
    tpair _ (T:functor B C) pb_LModule_σ.

  Lemma pb_LModule_laws : LModule_laws M pb_LModule_data.
  Proof.
    split.
    - intro c.
      cbn.
      rewrite <- (LModule_law1 _ (T:=T)).
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
      apply LModule_law2.
      repeat rewrite functor_comp.
      etrans.
      rewrite <- assoc.
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      apply (nat_trans_ax (σ M' T)).
      now repeat rewrite assoc.
  Qed.

  Definition pb_LModule : LModule M C := tpair _ _ pb_LModule_laws.

End Pullback_module.

(**

Let m:M -> M' be a monad morphism et n : T -> T' a morphism in the category of modules over M'.
In this section we construct the morphism m* n : m*T -> m*T' in the category of modules over M
between the pullback modules along m.

*)
Section Pullback_Module_Morphism.

  Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory} {T T' :LModule M' C}
          (n : LModule_Mor _ T T').

  Local Notation pbmT := (pb_LModule m T).
  Local Notation pbmT' := (pb_LModule m T').

  Lemma pb_LModule_Mor_law : LModule_Mor_laws M (T:=pbmT) (T':=pbmT') n.
  Proof.
    intros b.
    cbn.
    eapply pathscomp0;revgoals.
    rewrite <-assoc.
    apply cancel_precomposition.
    apply LModule_Mor_σ.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply nat_trans_ax.
  Qed.

  Definition pb_LModule_Mor  : LModule_Mor _  pbmT pbmT'  := ( _ ,, pb_LModule_Mor_law).

End Pullback_Module_Morphism.
