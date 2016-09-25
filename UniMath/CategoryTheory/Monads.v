(** **********************************************************

Benedikt Ahrens
started March 2015


************************************************************)


(** **********************************************************

Contents :

        - precategory of monads [precategory_Monad C] on [C]

TODO :
        - Proof that [precategory_Monad C] is
          saturated if [C] is

************************************************************)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


Definition functor_with_μ (C : precategory) : UU
  := Σ F : functor C C, F □ F ⟶ F.

Coercion functor_from_functor_with_μ (C : precategory) (F : functor_with_μ C)
  : functor C C := pr1 F.

Definition μ {C : precategory} (F : functor_with_μ C) : F□F ⟶ F := pr2 F.

Definition Monad_data (C : precategory) : UU :=
   Σ F : functor_with_μ C, functor_identity C ⟶ F.

Coercion functor_with_μ_from_Monad_data (C : precategory) (F : Monad_data C)
  : functor_with_μ C := pr1 F.

Definition η {C : precategory} (F : Monad_data C)
  : functor_identity C ⟶ F := pr2 F.

Definition Monad_laws {C : precategory} (T : Monad_data C) : UU
  :=
    (
      (Π c : C, η T (T c) ;; μ T c = identity (T c))
        ×
      (Π c : C, #T (η T c) ;; μ T c = identity (T c)))
      ×
    (Π c : C, #T (μ T c) ;; μ T c = μ T (T c) ;; μ T c).

Lemma isaprop_Monad_laws (C : precategory) (hs : has_homsets C) (T : Monad_data C) :
   isaprop (Monad_laws T).
Proof.
  repeat apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition Monad (C : precategory) : UU := Σ T : Monad_data C, Monad_laws T.

Coercion Monad_data_from_Monad (C : precategory) (T : Monad C) : Monad_data C := pr1 T.


Definition Monad_Mor_laws {C : precategory} {T T' : Monad_data C} (α : T ⟶ T')
  : UU :=
  (Π a : C, μ T a ;; α a = α (T a) ;; #T' (α a) ;; μ T' a) ×
  (Π a : C, η T a ;; α a = η T' a).

Lemma isaprop_Monad_Mor_laws (C : precategory) (hs : has_homsets C)
  (T T' : Monad_data C) (α : T ⟶ T')
  : isaprop (Monad_Mor_laws α).
Proof.
  apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition Monad_Mor {C : precategory} (T T' : Monad C) : UU
  := Σ α : T ⟶ T', Monad_Mor_laws α.

Coercion nat_trans_from_monad_mor (C : precategory) (T T' : Monad C) (s : Monad_Mor T T')
  : T ⟶ T' := pr1 s.

Definition Monad_Mor_η {C : precategory} {T T' : Monad C} (α : Monad_Mor T T')
  : Π a : C, η T a ;; α a = η T' a.
Proof.
  exact (pr2 (pr2 α)).
Qed.

Definition Monad_Mor_μ {C : precategory} {T T' : Monad C} (α : Monad_Mor T T')
  : Π a : C, μ T a ;; α a = α (T a) ;; #T' (α a) ;; μ T' a.
Proof.
  exact (pr1 (pr2 α)).
Qed.

Lemma Monad_identity_laws {C : precategory} (T : Monad C)
  : Monad_Mor_laws (nat_trans_id T).
Proof.
  split; intros; simpl.
  - rewrite id_left, id_right.
    rewrite functor_id, id_left.
    apply idpath.
 - apply id_right.
Qed.

Definition Monad_identity {C : precategory} (T : Monad C)
  : Monad_Mor T T := tpair _ _ (Monad_identity_laws T).

Lemma Monad_composition_laws {C : precategory} {T T' T'' : Monad C}
  (α : Monad_Mor T T') (α' : Monad_Mor T' T'') : Monad_Mor_laws (nat_trans_comp _ _ _ α α').
Proof.
  split; intros; simpl.
  - repeat rewrite assoc.
    set (H:=Monad_Mor_μ α a). clearbody H.
    simpl in *.
    rewrite H; clear H.
    repeat rewrite <- assoc.
    set (H:=Monad_Mor_μ α' a). simpl in *.
    rewrite H; clear H.
    rewrite functor_comp.
    apply maponpaths.
    repeat rewrite assoc.
    rewrite nat_trans_ax.
    apply idpath.
  - rewrite assoc.
    set (H := Monad_Mor_η α); simpl in *; rewrite H; clear H.
    apply Monad_Mor_η.
Qed.

Definition Monad_composition {C : precategory} {T T' T'' : Monad C}
  (α : Monad_Mor T T') (α' : Monad_Mor T' T'')
  : Monad_Mor T T'' := tpair _ _ (Monad_composition_laws α α').

Definition Monad_Mor_equiv {C : precategory} (hs : has_homsets C)
  {T T' : Monad C} (α β : Monad_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity.
  intro a. apply isaprop_Monad_Mor_laws, hs.
Defined.

Definition precategory_Monad_ob_mor (C : precategory) : precategory_ob_mor.
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

Lemma precategory_Monad_axioms (C : precategory) (hs : has_homsets C)
  : is_precategory (precategory_Monad_data C).
Proof.
  repeat split; simpl; intros.
  - apply (invmap (Monad_Mor_equiv hs _ _ )).
    apply (@id_left (functor_precategory C C hs)).
  - apply (invmap (Monad_Mor_equiv hs _ _ )).
    apply (@id_right (functor_precategory C C hs)).
  - apply (invmap (Monad_Mor_equiv hs _ _ )).
    apply (@assoc (functor_precategory C C hs)).
Qed.

Definition precategory_Monad (C : precategory) (hs : has_homsets C) : precategory
  := tpair _ _ (precategory_Monad_axioms C hs).
