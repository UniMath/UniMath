(** **********************************************************
Contents:
        - Definition of right modules ([RModule R]) over a monad [R] on [C]
        - Precategory of modules [precategory_Module R D] of range [D] over a monad [R] on [C]

Following the scheme of Monads.v

Written by: Ambroise Lafont (November 2016)

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.Monads.



Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).


Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of module *)
Section RModule_over_monad.

 Context {B:precategory} (M:Monad B) .
  (** Definition of modules over M of codomain D **)

Section RModule_def.




Definition RModule_data (D:precategory) : UU
  := Σ F : functor B D, F □ M ⟶ F.

Coercion functor_from_RModule_data (C : precategory) (F : RModule_data C)
  : functor B C := pr1 F.

Definition σ {C : precategory} (F : RModule_data C) : F□M ⟶ F := pr2 F.

Definition RModule_laws  {C:precategory} (T : RModule_data C) : UU :=
    (
      (Π c : B, #T (η M c) ;; σ T c = identity (T c))
        ×
(Π c : B, #T ((μ M) c) ;; σ T c = σ T (M c) ;; σ T c)).

Lemma isaprop_RModule_laws (C : precategory) (hs : has_homsets C) (T : RModule_data C) :
   isaprop (RModule_laws T).
Proof.
  repeat apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition RModule (C : precategory) : UU := Σ T : RModule_data C, RModule_laws T.

Coercion RModule_data_from_RModule (C : precategory) (T : RModule C) : RModule_data C := pr1 T.


Lemma RModule_law1 {C : precategory} {T : RModule C} :  (Π c : B, #T (η M c) ;; σ T c = identity (T c)).
Proof.
exact ( (pr1 (pr2 T))).
Qed.

Lemma RModule_law2 {C : precategory} {T : RModule C} : (Π c : B, #T ((μ M) c) ;; σ T c = σ T (M c) ;; σ T c).
Proof.
exact (pr2 ( (pr2 T))).
Qed.

End RModule_def.

(** * Monad precategory *)
Section RModule_precategory.

Definition RModule_Mor_laws {C : precategory} {T T' : RModule_data C} (α : T ⟶ T')
  : UU :=
  (Π a : B, α (M a) ;; σ T' a = σ T a ;; α a).


Lemma isaprop_RModule_Mor_laws (C : precategory) (hs : has_homsets C)
  (T T' : RModule_data C) (α : T ⟶ T')
  : isaprop (RModule_Mor_laws α).
Proof.
  apply impred; intro c; apply hs.
Qed.

Definition RModule_Mor {C : precategory} (T T' : RModule C) : UU
  := Σ α : T ⟶ T', RModule_Mor_laws α.


Coercion nat_trans_from_module_mor (C : precategory) (T T' : RModule C) (s : RModule_Mor T T')
   : T ⟶ T' := pr1 s.

Definition RModule_Mor_σ {C : precategory} {T T' : RModule C} (α : RModule_Mor T T') := pr2 α.

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
    set (H:=RModule_Mor_σ α a); simpl in H.
    rewrite <- H; clear H; rewrite <- !assoc.
    set (H:=RModule_Mor_σ α' a); simpl in H.
    now rewrite  H; clear H.
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

Definition precategory_RModule (C : precategory) (hs : has_homsets C) : precategory
  := tpair _ _ (precategory_RModule_axioms C hs).

End RModule_precategory.

End RModule_over_monad.