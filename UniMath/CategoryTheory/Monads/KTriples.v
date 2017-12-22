(* ============================================================================================= *)
(** * Kleisli Triples                                                                            *)
(*                                                                                               *)
(* Contents:                                                                                     *)
(*                                                                                               *)
(*         - Theory of monads based on the haskell-style bind operartor.                         *)
(*         - Category of Kleisli monads [category_Kleisli C] on [C]                              *)
(*         - Forgetful functor [forgetfunctor_Kleisli] from monads to endofunctors on [C]        *)
(*                                                                                               *)
(* Written by: Marco Maggesi, Cosimo Perini (2017)                                               *)
(* ============================================================================================= *)

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

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(* --------------------------------------------------------------------------------------------- *)
(* ** Definition of Kleisli.                                                                     *)
(* --------------------------------------------------------------------------------------------- *)

Section Kleisli_defn.

(* ----- Datatype for Kleisli data ----- *)

Definition Kleisli_Data {C : precategory} (F : C → C): UU :=
  (∏ a : C, a --> F a) × (∏ a b : C, (a --> F b) → (F a --> F b)).

(* ----- Projections ----- *)

Definition η {C : precategory} {F : C → C} (K : Kleisli_Data F) : ∏ a : C, a --> F a := pr1 K.

Definition bind {C : precategory} {F : C → C} (K : Kleisli_Data F) {a b : C} :
  C⟦a,F b⟧ → C⟦F a,F b⟧ := pr2 K a b.

(* ----- Kleisli Laws: Data and Projections ----- *)

Definition Kleisli_Laws {C : precategory} {T : C → C} (K : Kleisli_Data T) :=
  (∏ a b (f : C⟦a,T b⟧) c (g : C⟦b,T c⟧), bind K g ∘ bind K f = bind K (bind K g ∘ f)) ×
  (∏ a b (f : C⟦a,T b⟧), bind K f ∘ η K a = f) ×
  (∏ a, bind K (η K a) = identity (T a)).

Lemma isaprop_Kleisli_Laws {C : precategory}
        (hs : has_homsets C) {T : C → C} (K : Kleisli_Data T) :
  isaprop (Kleisli_Laws K).
Proof.
  repeat apply isapropdirprod; repeat (apply impred_isaprop; intros); apply hs.
Defined.

Definition bind_bind {C : precategory} {T : C → C} {K : Kleisli_Data T} :
  Kleisli_Laws K
  → ∏ a b (f : C⟦a,T b⟧) c (g : C⟦b,T c⟧), bind K g ∘ bind K f = bind K (bind K g ∘ f) :=
  pr1.

Definition bind_η {C : precategory} {T : C → C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  ∏ a b (f : C⟦a,T b⟧), bind K f ∘ η K a = f := pr1 (pr2 H).

Definition η_bind {C : precategory} {T : C → C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  ∏ a, bind K (η K a) = identity (T a) := pr2 (pr2 H).

(* ----- Packing the whole data -----*)

Definition Kleisli (C : precategory) : UU :=
  ∑ (T : C → C) (K : Kleisli_Data T), Kleisli_Laws K.

Definition kleisli_ob {C : precategory} (T : Kleisli C) : C → C :=
  pr1 T.

Coercion kleisli_data {C : precategory} (T : Kleisli C) : Kleisli_Data (kleisli_ob T) :=
  pr1 (pr2 T).

Coercion kleisli_laws {C : precategory} (T : Kleisli C) : Kleisli_Laws T := pr2 (pr2 T).

End Kleisli_defn.

(* --------------------------------------------------------------------------------------------- *)
(* ** Kleisli Precategory                                                                        *)
(* --------------------------------------------------------------------------------------------- *)

Section Kleisli_precategory.

(* ----- Morphisms of Kleisli Monads ----- *)

Definition Kleisli_Mor_laws {C : precategory} {T T' : C → C}
             (α : ∏ a : C, T a --> T' a) (K : Kleisli_Data T) (K' : Kleisli_Data T') : UU :=
  (∏ a : C, α a ∘ η K a = η K' a) ×
  (∏ (a b : C) (f : C⟦a,T b⟧), bind K' (α b ∘ f) ∘ α a = α b ∘ (bind K f)).

Lemma isaprop_Kleisli_Mor_laws {C : precategory} (hs : has_homsets C) {T T' : C → C}
        (α : ∏ a : C, T a --> T' a) (K : Kleisli_Data T) (K' : Kleisli_Data T') :
  isaprop (Kleisli_Mor_laws α K K').
Proof.
  apply isapropdirprod; repeat (apply impred_isaprop; intros); apply hs.
Defined.

Definition Kleisli_Mor {C : precategory} (T T' : Kleisli C) : UU :=
  ∑ (α : ∏ a : C, kleisli_ob T a --> kleisli_ob T' a), Kleisli_Mor_laws α T T'.

Definition nat_trans_from_kleisli_mor {C : precategory}
           {T T' : Kleisli C} (s : Kleisli_Mor T T') :
  ∏ a : C, kleisli_ob T a --> kleisli_ob T' a := pr1 s.

Definition Kleisli_Mor_η {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  ∏ a : C, η T a · nat_trans_from_kleisli_mor  α a = η T' a :=
  pr1 (pr2 α).

Definition Kleisli_Mor_bind {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  ∏ (a b : C) (f : C⟦a,kleisli_ob T b⟧),
    bind T' (nat_trans_from_kleisli_mor α b ∘ f) ∘ nat_trans_from_kleisli_mor α a =
    nat_trans_from_kleisli_mor α b ∘ (bind T f) :=
  pr2 (pr2 α).

Definition Kleisli_Mor_equiv {C : precategory} (hs : has_homsets C) {T T' : Kleisli C}
           (α β : Kleisli_Mor T T') :
  α = β ≃ (nat_trans_from_kleisli_mor α = nat_trans_from_kleisli_mor β).
Proof.
  apply subtypeInjectivity.
  intro a.
  now apply isaprop_Kleisli_Mor_laws.
Defined.

(* ----- Definition of map with some laws ----- *)

Definition map {C : precategory} {T : C → C} (K : Kleisli_Data T) {a b : C} (f : a --> b) :
  T a --> T b :=
  bind K (η K b ∘ f).

Lemma map_id {C : precategory} {T : C → C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  ∏ a : C, map K (identity a) = identity (T a).
Proof.
  intro. unfold map.
  rewrite id_left.
  now apply η_bind.
Defined.

Lemma map_map {C : precategory} {T : C->C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  ∏ (a b c : C) (f : a --> b) (g : b --> c), map K (g ∘ f) = map K g ∘ map K f.
Proof.
  intros. unfold map.
  rewrite (bind_bind H).
  do 2 rewrite <- assoc.
  now rewrite (bind_η H).
Defined.

Lemma map_bind {C : precategory} {T : C → C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  ∏ (a b c : C) (f : b --> c) (g : a --> T b), map K f ∘ bind K g = bind K (map K f ∘ g).
Proof.
  intros. unfold map.
  now rewrite (bind_bind H).
Defined.

Lemma bind_map {C : precategory} {T : C->C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  ∏ (a b c : C) (f : b --> T c) (g : a --> b),
  bind K f ∘ map K g = bind K (f ∘ g).
Proof.
  intros. unfold map.
  rewrite (bind_bind H).
  rewrite <- assoc.
  now rewrite (bind_η H).
Defined.

Lemma map_η {C : precategory} {T : C → C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  ∏ (a b : C) (f : a --> b),
  map K f ∘ η K a = η K b ∘ f.
Proof.
  intros. unfold map.
  now rewrite (bind_η H).
Defined.

Definition μ {C : precategory} {T : C → C} (K : Kleisli_Data T) (a : C) :
  T (T a) --> T a :=
  bind K (identity (T a)).

(* -----  Morphisms of Kleisli Monads are Natural Transformations ----- *)

Definition kleisli_functor_data {C : precategory} {T : C → C} (K : Kleisli_Data T) :
  functor_data C C :=
  mk_functor_data T (@map C T K).

Definition is_functor_kleisli {C : precategory} {T : C → C}
           {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  is_functor(kleisli_functor_data K) :=
  map_id H ,, map_map H.

Definition kleisli_functor {C : precategory} (K : Kleisli C) : functor C C :=
  mk_functor (kleisli_functor_data K) (is_functor_kleisli K).

Lemma is_nat_trans_kleisli_mor {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  is_nat_trans (kleisli_functor T) (kleisli_functor T') (nat_trans_from_kleisli_mor α).
Proof.
  unfold is_nat_trans. intros. simpl. unfold map.
  rewrite <- (Kleisli_Mor_bind α).
  rewrite <- assoc.
  now rewrite (Kleisli_Mor_η α).
Defined.

Definition nat_trans_kleisli_mor {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  nat_trans (kleisli_functor T) (kleisli_functor T') :=
  mk_nat_trans (kleisli_functor T) (kleisli_functor T')
               (nat_trans_from_kleisli_mor α) (is_nat_trans_kleisli_mor α).

Lemma Kleisli_Mor_eq {C : precategory} (hs : has_homsets C)
      {T T' : Kleisli C} (α α' : Kleisli_Mor T T') :
  nat_trans_from_kleisli_mor α  = nat_trans_from_kleisli_mor α' → α = α'.
Proof.
  intros.
  apply (subtypeEquality' X).
  now apply isaprop_Kleisli_Mor_laws.
Defined.

(* ----- η natural transformation. ----- *)
Lemma is_nat_trans_η {C : precategory} (K : Kleisli C) :
  is_nat_trans (functor_identity C) (kleisli_functor K) (η K).
Proof.
  unfold is_nat_trans. simpl. intros.
  now rewrite (map_η K).
Defined.

Definition nat_trans_η {C : precategory} (K : Kleisli C) :
  functor_identity C ⟹ kleisli_functor K :=
  (η K,, is_nat_trans_η K).

(* ----- μ natural transformation. ----- *)

Lemma is_nat_trans_μ {C : precategory} (K : Kleisli C) :
  is_nat_trans (kleisli_functor K □ kleisli_functor K) (kleisli_functor K) (μ K).
Proof.
  unfold is_nat_trans, μ. simpl. intros.
  rewrite (map_bind K), (bind_map K).
  now rewrite id_left, id_right.
Defined.

Definition nat_trans_μ {C : precategory} (K : Kleisli C) :
  kleisli_functor K □ kleisli_functor K ⟹ kleisli_functor K :=
  μ K,, is_nat_trans_μ K.

(* ----- Identity Morphism ----- *)

Lemma Kleisli_identity_laws {C : precategory} (T : Kleisli C) :
  Kleisli_Mor_laws (λ a : C, identity (kleisli_ob T a)) T T.
Proof.
  split; simpl; intros a.
  - apply id_right.
  - intros. do 2 rewrite id_right; apply id_left.
Defined.

Definition Kleisli_identity {C : precategory} (T : Kleisli C) : Kleisli_Mor T T :=
  (λ a : C, identity (kleisli_ob T a)),, Kleisli_identity_laws T.

(* ----- Composition of Morphisms ----- *)

Lemma Kleisli_composition_laws {C : precategory} {T T' T'' : Kleisli C}
        (α : Kleisli_Mor T T') (α' : Kleisli_Mor T' T'') :
  Kleisli_Mor_laws
    (λ a : C, nat_trans_from_kleisli_mor α a · nat_trans_from_kleisli_mor α' a)
    T T''.
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

Definition Kleisli_composition {C : precategory} {T T' T'' : Kleisli C}
           (α : Kleisli_Mor T T') (α' : Kleisli_Mor T' T'') :
  Kleisli_Mor T T'' :=
  (λ a : C, nat_trans_from_kleisli_mor α a · nat_trans_from_kleisli_mor α' a),,
  Kleisli_composition_laws α α'.

(* ----- Precategory of Kleisli Monads ----- *)

Definition precategory_Kleisli_ob_mor (C : precategory) : precategory_ob_mor :=
  precategory_ob_mor_pair (Kleisli C) Kleisli_Mor.

Definition precategory_Kleisli_Data (C : precategory) : precategory_data :=
  precategory_data_pair (precategory_Kleisli_ob_mor C)
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
Defined.

Definition precategory_Kleisli (C : precategory) (hs : has_homsets C) : precategory :=
  precategory_Kleisli_Data C,, precategory_Kleisli_axioms C hs.

Lemma has_homsets_Kleisli (C : category) :
  has_homsets (precategory_Kleisli C (homset_property C)).
Proof.
  intros F G. simpl. unfold Kleisli_Mor.
  apply isaset_total2 .
  apply impred_isaset.
  intro. apply C.
  intros.
  apply isasetaprop.
  apply isaprop_Kleisli_Mor_laws.
  apply C.
Defined.

(* ----- Category of Kleisli Monads ----- *)

Definition category_Kleisli (C : category) : category :=
  precategory_Kleisli C (homset_property C),, has_homsets_Kleisli C.

Definition forgetfunctor_Kleisli (C : category) :
  functor (category_Kleisli C) (functor_category C C).
Proof.
  use mk_functor.
  - simpl.
    use mk_functor_data.
    + simpl.
      exact (λ K : Kleisli C, kleisli_functor K).
    + simpl. intros T T' K.
      exact  (nat_trans_kleisli_mor K).
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
  intros K K'. simpl.
  apply isinclbetweensets.
  - apply isaset_total2.
    + apply impred_isaset.
      intros. apply C.
    + intros. apply isasetaprop. apply isaprop_Kleisli_Mor_laws. apply C.
  - apply isaset_nat_trans. apply C.
  - intros f g p.
    apply Kleisli_Mor_eq.
    + apply C.
    + apply funextsec. intro X.
      change (pr1 (nat_trans_kleisli_mor f) X = pr1 (nat_trans_kleisli_mor g) X).
      now rewrite p.
Defined.

End Kleisli_precategory.
