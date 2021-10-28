(* ============================================================================================= *)
(** * Kleisli Triples                                                                            *)
(*                                                                                               *)
(* Contents:                                                                                     *)
(*                                                                                               *)
(*         - Theory of monads based on the Haskell-style bind operator.                          *)
(*         - Category of Kleisli monads [category_Kleisli C] on [C]                              *)
(*         - Forgetful functor [forgetfunctor_Kleisli] from monads to endofunctors on [C]        *)
(*                                                                                               *)
(* Written by: Marco Maggesi, Cosimo Perini (2017)                                               *)
(* ============================================================================================= *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.RelativeMonads.

Local Open Scope cat.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(* --------------------------------------------------------------------------------------------- *)
(* ** Definition of Kleisli.                                                                     *)
(* --------------------------------------------------------------------------------------------- *)

Section Kleisli_defn.

  Context {C : precategory_data}.

(* ----- Datatype for Kleisli data ----- *)

Definition Kleisli_Data : UU := ∑ T : C → C,
  (∏ a : C, a --> T a) × (∏ a b : C, (a --> T b) → (T a --> T b)).

(* ----- Projections ----- *)

Definition Kleisli_Data_ob (T: Kleisli_Data) (c : C) : C := pr1 T c.
Coercion Kleisli_Data_ob : Kleisli_Data >-> Funclass.

Definition η (T : Kleisli_Data) : ∏ a : C, a --> T a := pr1 (pr2 T).

Definition bind (T : Kleisli_Data) {a b : C} :
  C⟦a,T b⟧ → C⟦T a,T b⟧ := pr2 (pr2 T) a b.

(* ----- Kleisli Laws: Data and Projections ----- *)

Definition Kleisli_Laws (T : Kleisli_Data) :=
  (∏ a, bind T (η T a) = identity (T a)) ×
  (∏ a b (f : C⟦a,T b⟧), bind T f ∘ η T a = f) ×
  (∏ a b c (f : C⟦a,T b⟧) (g : C⟦b,T c⟧), bind T g ∘ bind T f = bind T (bind T g ∘ f)).

Lemma isaprop_Kleisli_Laws (hs : has_homsets C) (T : Kleisli_Data) :
  isaprop (Kleisli_Laws T).
Proof.
  repeat apply isapropdirprod; repeat (apply impred_isaprop; intros); apply hs.
Defined.

Definition bind_bind {T : Kleisli_Data} (H: Kleisli_Laws T) :
  ∏ a b c (f : C⟦a,T b⟧) (g : C⟦b,T c⟧), bind T g ∘ bind T f = bind T (bind T g ∘ f) :=
  pr2 (pr2 H).

Definition bind_η {T : Kleisli_Data} (H : Kleisli_Laws T) :
  ∏ a b (f : C⟦a,T b⟧), bind T f ∘ η T a = f := pr1 (pr2 H).

Definition η_bind {T : Kleisli_Data} (H : Kleisli_Laws T) :
  ∏ a, bind T (η T a) = identity (T a) := pr1 H.

(* ----- Packing the whole data -----*)

Definition KleisliMonad : UU :=
  ∑ (T : Kleisli_Data), Kleisli_Laws T.
(* argument [C] will be set as not implicit after the end of the section *)
Coercion Kleisli_Data_from_Kleisli (T : KleisliMonad) : Kleisli_Data := pr1 T.
Coercion kleisli_laws (T : KleisliMonad) : Kleisli_Laws (pr1 T) := pr2 T.

End Kleisli_defn.

Arguments KleisliMonad: clear implicits.
Arguments Kleisli_Data: clear implicits.

(* --------------------------------------------------------------------------------------------- *)
(* ** KleisliMonad Precategory                                                                        *)
(* --------------------------------------------------------------------------------------------- *)

Section Kleisli_precategory.

(* ----- Morphisms of KleisliMonad Monads ----- *)

Definition Kleisli_Mor_laws {C : precategory_data} (T T': Kleisli_Data C)
             (α : ∏ a : C, T a --> T' a) : UU :=
  (∏ a : C, α a ∘ η T a = η T' a) ×
  (∏ (a b : C) (f : C⟦a,T b⟧), bind T' (α b ∘ f) ∘ α a = α b ∘ (bind T f)).

Lemma isaprop_Kleisli_Mor_laws {C : precategory_data} (hs : has_homsets C) (T T' : Kleisli_Data C)
        (α : ∏ a : C, T a --> T' a) :
  isaprop (Kleisli_Mor_laws T T' α).
Proof.
  apply isapropdirprod; repeat (apply impred_isaprop; intros); apply hs.
Defined.

Definition Kleisli_Mor {C : precategory_data} (T T' : Kleisli_Data C) : UU :=
  ∑ (α : ∏ a : C, T a --> T' a), Kleisli_Mor_laws T T' α.

Definition nat_trans_from_kleisli_mor {C : precategory_data}
           {T T' : Kleisli_Data C} (s : Kleisli_Mor T T') :
  ∏ a : C, T a --> T' a := pr1 s.

Definition Kleisli_Mor_η {C : precategory_data} {T T' : KleisliMonad C} (α : Kleisli_Mor T T') :
  ∏ a : C, η T a · nat_trans_from_kleisli_mor  α a = η T' a :=
  pr1 (pr2 α).

Definition Kleisli_Mor_bind {C : precategory_data} {T T' : KleisliMonad C} (α : Kleisli_Mor T T') :
  ∏ (a b : C) (f : C⟦a,T b⟧),
    bind T' (nat_trans_from_kleisli_mor α b ∘ f) ∘ nat_trans_from_kleisli_mor α a =
    nat_trans_from_kleisli_mor α b ∘ (bind T f) :=
  pr2 (pr2 α).

Definition Kleisli_Mor_equiv {C : precategory_data} (hs : has_homsets C) {T T' : KleisliMonad C}
           (α β : Kleisli_Mor T T') :
  α = β ≃ (nat_trans_from_kleisli_mor α = nat_trans_from_kleisli_mor β).
Proof.
  apply subtypeInjectivity.
  intro a.
  now apply isaprop_Kleisli_Mor_laws.
Defined.

(* ----- Definition of map with some laws ----- *)

Definition map {C : precategory_data} (T : Kleisli_Data C) {a b : C} (f : a --> b) :
  T a --> T b :=
  bind T (η T b ∘ f).

Lemma map_id {C : precategory} {T : Kleisli_Data C} (H : Kleisli_Laws T) :
  ∏ a : C, map T (identity a) = identity (T a).
Proof.
  intro. unfold map.
  rewrite id_left.
  now apply η_bind.
Defined.

Lemma map_map {C : precategory} {T : Kleisli_Data C} (H : Kleisli_Laws T) :
  ∏ (a b c : C) (f : a --> b) (g : b --> c), map T (g ∘ f) = map T g ∘ map T f.
Proof.
  intros. unfold map.
  rewrite (bind_bind H).
  do 2 rewrite <- assoc.
  now rewrite (bind_η H).
Defined.

Lemma map_bind {C : precategory} {T : Kleisli_Data C} (H : Kleisli_Laws T) :
  ∏ (a b c : C) (f : b --> c) (g : a --> T b), map T f ∘ bind T g = bind T (map T f ∘ g).
Proof.
  intros. unfold map.
  now rewrite (bind_bind H).
Defined.

Lemma bind_map {C : precategory} {T : Kleisli_Data C} (H : Kleisli_Laws T) :
  ∏ (a b c : C) (f : b --> T c) (g : a --> b),
  bind T f ∘ map T g = bind T (f ∘ g).
Proof.
  intros. unfold map.
  rewrite (bind_bind H).
  rewrite <- assoc.
  now rewrite (bind_η H).
Defined.

Lemma map_η {C : precategory} {T : Kleisli_Data C} (H : Kleisli_Laws T) :
  ∏ (a b : C) (f : a --> b),
  map T f ∘ η T a = η T b ∘ f.
Proof.
  intros. unfold map.
  now rewrite (bind_η H).
Defined.

Definition μ {C : precategory} (T : Kleisli_Data C) (a : C) :
  T (T a) --> T a :=
  bind T (identity (T a)).

(* -----  Morphisms of KleisliMonad Monads are Natural Transformations ----- *)

Definition kleisli_functor_data {C : precategory} (T : Kleisli_Data C) :
  functor_data C C :=
  make_functor_data T (@map C T).

Definition is_functor_kleisli {C : precategory}
           {T : Kleisli_Data C} (H : Kleisli_Laws T) :
  is_functor(kleisli_functor_data T) :=
  map_id H ,, map_map H.

Definition kleisli_functor {C : precategory} (T : KleisliMonad C) : functor C C :=
  make_functor (kleisli_functor_data T) (is_functor_kleisli T).

Lemma is_nat_trans_kleisli_mor {C : precategory} {T T' : KleisliMonad C} (α : Kleisli_Mor T T') :
  is_nat_trans (kleisli_functor T) (kleisli_functor T') (nat_trans_from_kleisli_mor α).
Proof.
  unfold is_nat_trans. intros. simpl. unfold map.
  rewrite <- (Kleisli_Mor_bind α).
  rewrite <- assoc.
  now rewrite (Kleisli_Mor_η α).
Defined.

Definition nat_trans_kleisli_mor {C : precategory} {T T' : KleisliMonad C} (α : Kleisli_Mor T T') :
  nat_trans (kleisli_functor T) (kleisli_functor T') :=
  make_nat_trans (kleisli_functor T) (kleisli_functor T')
               (nat_trans_from_kleisli_mor α) (is_nat_trans_kleisli_mor α).

Lemma Kleisli_Mor_eq {C : precategory} (hs : has_homsets C)
      {T T' : KleisliMonad C} (α α' : Kleisli_Mor T T') :
  nat_trans_from_kleisli_mor α  = nat_trans_from_kleisli_mor α' → α = α'.
Proof.
  apply Kleisli_Mor_equiv; assumption.
Defined.

(* ----- η natural transformation. ----- *)
Lemma is_nat_trans_η {C : precategory} (T : KleisliMonad C) :
  is_nat_trans (functor_identity C) (kleisli_functor T) (η T).
Proof.
  unfold is_nat_trans. simpl. intros.
  now rewrite (map_η T).
Defined.

Definition nat_trans_η {C : precategory} (T : KleisliMonad C) :
  functor_identity C ⟹ kleisli_functor T :=
  (η T,, is_nat_trans_η T).

(* ----- μ natural transformation. ----- *)

Lemma is_nat_trans_μ {C : precategory} (T : KleisliMonad C) :
  is_nat_trans (kleisli_functor T □ kleisli_functor T) (kleisli_functor T) (μ T).
Proof.
  unfold is_nat_trans, μ. simpl. intros.
  rewrite (map_bind T), (bind_map T).
  now rewrite id_left, id_right.
Defined.

Definition nat_trans_μ {C : precategory} (T : KleisliMonad C) :
  kleisli_functor T □ kleisli_functor T ⟹ kleisli_functor T :=
  μ T,, is_nat_trans_μ T.

(* ----- Identity Morphism ----- *)

Lemma Kleisli_identity_laws {C : precategory} (T : KleisliMonad C) :
  Kleisli_Mor_laws T T (λ a : C, identity (T a)).
Proof.
  split; simpl; intros a.
  - apply id_right.
  - intros. do 2 rewrite id_right; apply id_left.
Defined.

Definition Kleisli_identity {C : precategory} (T : KleisliMonad C) : Kleisli_Mor T T :=
  (λ a : C, identity (T a)),, Kleisli_identity_laws T.

(* ----- Composition of Morphisms ----- *)

Lemma Kleisli_composition_laws {C : precategory} {T T' T'' : KleisliMonad C}
        (α : Kleisli_Mor T T') (α' : Kleisli_Mor T' T'') :
  Kleisli_Mor_laws T T''
    (λ a : C, nat_trans_from_kleisli_mor α a · nat_trans_from_kleisli_mor α' a).
Proof.
  split; intros; simpl.
  - rewrite assoc.
    set (H := Kleisli_Mor_η α). rewrite H.
    apply Kleisli_Mor_η.
  - pathvia (nat_trans_from_kleisli_mor α a ·
             (nat_trans_from_kleisli_mor α' a ·
              bind T'' ((f · nat_trans_from_kleisli_mor α b) ·
                        nat_trans_from_kleisli_mor α' b))).
    * now repeat rewrite assoc.
    * rewrite (Kleisli_Mor_bind α').
      rewrite assoc. rewrite (Kleisli_Mor_bind α).
      apply pathsinv0. apply assoc.
Defined.

Definition Kleisli_composition {C : precategory} {T T' T'' : KleisliMonad C}
           (α : Kleisli_Mor T T') (α' : Kleisli_Mor T' T'') :
  Kleisli_Mor T T'' :=
  (λ a : C, nat_trans_from_kleisli_mor α a · nat_trans_from_kleisli_mor α' a),,
  Kleisli_composition_laws α α'.

(* ----- Precategory of KleisliMonad Monads ----- *)

Definition precategory_Kleisli_ob_mor (C : precategory) : precategory_ob_mor :=
  make_precategory_ob_mor (KleisliMonad C) Kleisli_Mor.

Definition precategory_Kleisli_Data (C : precategory) : precategory_data :=
  make_precategory_data (precategory_Kleisli_ob_mor C)
                        (@Kleisli_identity C)
                        (@Kleisli_composition C).

Lemma precategory_Kleisli_axioms (C : precategory) (hs : has_homsets C) :
  is_precategory (precategory_Kleisli_Data C).
Proof.
  repeat split; simpl; intros.
  - apply (invmap (Kleisli_Mor_equiv hs _ _ )).
    apply funextsec. intros x. apply id_left.
  - apply (invmap (Kleisli_Mor_equiv hs _ _ )).
    apply funextsec. intros x. apply id_right.
  - apply (invmap (Kleisli_Mor_equiv hs _ _ )).
    apply funextsec. intros x. apply assoc.
  - apply (invmap (Kleisli_Mor_equiv hs _ _ )).
    apply funextsec. intros x. apply assoc'.
Defined.

Definition precategory_Kleisli (C : precategory) (hs : has_homsets C) : precategory :=
  precategory_Kleisli_Data C,, precategory_Kleisli_axioms C hs.

Lemma has_homsets_Kleisli (C : category) :
  has_homsets (precategory_Kleisli C (homset_property C)).
Proof.
  intros F G. simpl. unfold Kleisli_Mor.
  apply isaset_total2 .
  - apply impred_isaset.
    intro. apply C.
  - intros.
    apply isasetaprop.
    apply isaprop_Kleisli_Mor_laws.
    apply C.
Defined.

(* ----- Category of KleisliMonad Monads ----- *)

Definition category_Kleisli (C : category) : category :=
  precategory_Kleisli C (homset_property C),, has_homsets_Kleisli C.


Definition forgetfunctor_Kleisli (C : category) :
  functor (category_Kleisli C) (functor_category C C).
Proof.
  use make_functor.
  - simpl.
    use make_functor_data.
    + simpl.
      exact (λ T : KleisliMonad C, kleisli_functor T).
    + simpl. intros T T' α.
      exact (nat_trans_kleisli_mor α).
  - split.
    + red. intros. simpl. apply nat_trans_eq.
      * apply C.
      * intros; apply idpath.
    + unfold functor_compax. simpl. intros. apply nat_trans_eq.
      * apply C.
      * intros. apply idpath.
Defined.

Lemma forgetKleisli_faithful (C : category) : faithful (forgetfunctor_Kleisli C).
Proof.
  intros T T'. simpl.
  apply isinclbetweensets.
  - apply isaset_total2.
    + apply impred_isaset.
      intros. apply C.
    + intros. apply isasetaprop. apply isaprop_Kleisli_Mor_laws. apply C.
  - apply isaset_nat_trans. apply C.
  - intros α α' p.
    apply Kleisli_Mor_eq.
    + apply C.
    + apply funextsec. intro c.
      change (pr1 (nat_trans_kleisli_mor α) c = pr1 (nat_trans_kleisli_mor α') c).
      now rewrite p.
Defined.


(** inherit the univalence result from [precategory_RelMonad] *)
(*
Lemma is_univalent_precategory_Kleisli {C : category}
      (H: is_univalent C) (R R': KleisliMonad C)
  : is_univalent (category_Kleisli C).
Proof.
  exact (is_univalent_RelMonad H (functor_identity C) R R').
Qed.
*)

End Kleisli_precategory.
