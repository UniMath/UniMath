(** **********************************************************
Contents:
        - Definition of modules ([Monad])
        - Precategory of monads [precategory_Monad C] on [C]

Following the scheme of Monads.v

Written by: Ambroise Lafont (November 2016)

************************************************************)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

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

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of module *)
Section Module_over_monad.

 Variables (B:precategory) (M:Monad B) .
  (** Definition of modules over M of codomain D **)

Section Module_def.

 
  

Definition Module_data (D:precategory) : UU
  := Σ F : functor B D, F □ M ⟶ F.

Coercion functor_from_Module_data (C : precategory) (F : Module_data C)
  : functor B C := pr1 F.

Definition σ {C : precategory} (F : Module_data C) : F□M ⟶ F := pr2 F.

Definition Module_laws  {C:precategory} (T : Module_data C) : UU :=
    (
      (Π c : B, #T (η M c) ;; σ T c = identity (T c))
        ×
(Π c : B, #T ((μ M) c) ;; σ T c = σ T (M c) ;; σ T c)).

Lemma isaprop_Module_laws (C : precategory) (hs : has_homsets C) (T : Module_data C) :
   isaprop (Module_laws T).
Proof.
  repeat apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition Module (C : precategory) : UU := Σ T : Module_data C, Module_laws T.

Coercion Module_data_from_Module (C : precategory) (T : Module C) : Module_data C := pr1 T.

Lemma Module_law1 {C : precategory} {T : Module C} :  (Π c : B, #T (η M c) ;; σ T c = identity (T c)).  
Proof.
exact ( (pr1 (pr2 T))).
Qed.

Lemma Module_law2 {C : precategory} {T : Module C} : (Π c : B, #T ((μ M) c) ;; σ T c = σ T (M c) ;; σ T c).
Proof.
exact (pr2 ( (pr2 T))).
Qed.

End Module_def.

(** * Monad precategory *)
Section Module_precategory.

Definition Module_Mor_laws {C : precategory} {T T' : Module_data C} (α : T ⟶ T')
  : UU :=
  (Π a : B, α (M a) ;; σ T' a = σ T a ;; α a).


Lemma isaprop_Module_Mor_laws (C : precategory) (hs : has_homsets C)
  (T T' : Module_data C) (α : T ⟶ T')
  : isaprop (Module_Mor_laws α).
Proof.
  (* apply isapropdirprod; *)
  apply impred; intro c; apply hs.
Qed.

Definition Module_Mor {C : precategory} (T T' : Module C) : UU
  := Σ α : T ⟶ T', Module_Mor_laws α.


Local Coercion nat_trans_from_module_mor (C : precategory) (T T' : Module C) (s : Module_Mor T T') 
   : T ⟶ T' := pr1 s. 

Definition Module_Mor_σ {C : precategory} {T T' : Module C} (α : Module_Mor T T') := pr2 α.

Lemma Module_identity_laws {C : precategory} (T : Module C)
  : Module_Mor_laws (nat_trans_id T).
Proof.

  red;
    simpl.
  intro x.
  now rewrite id_right, id_left.
Qed.

Definition Module_identity {C : precategory} (T : Module C)
: Module_Mor T T := tpair _ _ (Module_identity_laws T).

Lemma Module_composition_laws {C : precategory} {T T' T'' : Module C}
  (α : Module_Mor T T') (α' : Module_Mor T' T'') : Module_Mor_laws (nat_trans_comp _ _ _ ( α) ( α')).
Proof.
  red;intros; simpl.
  unfold nat_trans_from_module_mor.
  rewrite assoc.
    set (H:=Module_Mor_σ α a); simpl in H.
    rewrite <- H; clear H; rewrite <- !assoc.
    set (H:=Module_Mor_σ α' a); simpl in H.
    now rewrite  H; clear H.
Qed.

Definition Module_composition {C : precategory} {T T' T'' : Module C}
  (α : Module_Mor T T') (α' : Module_Mor T' T'')
  : Module_Mor T T'' := tpair _ _ (Module_composition_laws α α').

Definition Module_Mor_equiv {C : precategory} (hs : has_homsets C)
  {T T' : Module C} (α β : Module_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_Module_Mor_laws, hs.
Defined.

Definition precategory_Module_ob_mor (C : precategory) : precategory_ob_mor.
Proof.
  exists (Module C).
  exact (λ T T' : Module C, Module_Mor T T').
Defined.

Definition precategory_Module_data (C : precategory) : precategory_data.
Proof.
  exists (precategory_Module_ob_mor C).
  exists (@Module_identity C).
  exact (@Module_composition C).
Defined.


Lemma precategory_Module_axioms (C : precategory) (hs : has_homsets C)
  : is_precategory (precategory_Module_data C).
Proof.
    repeat split; simpl; intros.
  - apply (invmap (Module_Mor_equiv hs _ _ )).
    apply (@id_left (functor_precategory B C hs)).
  - apply (invmap (Module_Mor_equiv hs _ _ )).
    apply (@id_right (functor_precategory B C hs)).
  - apply (invmap (Module_Mor_equiv hs _ _ )).
    apply (@assoc (functor_precategory B C hs)).
Qed.

Definition precategory_Module (C : precategory) (hs : has_homsets C) : precategory
  := tpair _ _ (precategory_Module_axioms C hs).

End Module_precategory.

End Module_over_monad.
