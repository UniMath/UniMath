(**********************************************************************************************

 Operations on the subobject classifier

 If `E` is a topos, then the subobject classifier `Ω` forms an internal Heyting algebra. Note
 that by definition there is a morphism `T --> Ω` from the terminal object that represents the
 truth formulate. In this file, we construct the other operations for this internal Heyting
 algebra (falsity, conjunction, disjunction, and implication). Our constructions are based on
 the book by Goldblatt where they are defined as follows (page 139).

 - Falsity.
 If `E` has a strict initial object `I`, then we have a monomorphism `I --> T` where `T` is the
 terminal object in `E`. The characteristic map of this monomorphism is a morphism `T --> Ω`,
 which represents falsity. Note that every topos has a strict initial object, because toposes
 have finite colimits and initial objects in a Cartesian closed category are strict.

 - Conjunction.
 Suppose that `E` has binary products. Then we have a monomorphism `T x T --> Ω × Ω`, which is
 the product of the truth morphism. The characteristic map gives us a morphism `Ω × Ω --> Ω`.

 - Disjunction.
 The construction of the disjunction morphism is more interesting. In this case, we construct
 a morphism `Ω + Ω --> Ω × Ω` (see [subobject_classifier_disj_mor]). However, this morphism is,
 in general, not a monomorphism, and thus we cannot take its characteristic map. We solve this
 by using the epi-mono factorization, which exists because every topos is regular.

 - Implication.
 To construct the implication, we again need to construct a subobject of `Ω × Ω`. Intuitively,
 this subobject represents pairs `(ω₁ , ω₂) : Ω × Ω` such that `ω₁ ≤ ω₂`. To represent this
 subobject, we use that we have `ω₁ ≤ ω₂` if and only if `ω₁ ∧ ω₂ = ω₁`. As such, we define
 this subobject as the equalizer of the conjunction map and the first projection.

 References
 - Topos, The Categorical Analysis of Logic by Robert Goldblatt

 Contents
 1. Falsity
 2. Conjunction
 3. Disjunction
 4. Implication

 **********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.

Local Open Scope cat.

Section Operations.
  Context {E : category}
          {T : Terminal E}
          (Ω : subobject_classifier T).

  (** * 1. Falsity *)
  Section Falsity.
    Context (I : strict_initial_object E).

    Definition Monic_from_strict_initial
               (x : E)
      : Monic E I x.
    Proof.
      use make_Monic.
      - exact (InitialArrow I x).
      - abstract
          (intros w f g p ;
           apply (@InitialArrowEq
                    _
                    (make_Initial _ (is_initial_mor_to_strict_initial I _ f)))).
    Defined.

    Definition subobject_classifier_false
      : T --> Ω.
    Proof.
      use (characteristic_morphism Ω).
      - exact I.
      - exact (Monic_from_strict_initial T).
    Defined.
  End Falsity.

  (** * 2. Conjunction *)
  Section Conjunction.
    Context (BP : BinProducts E).

    Let φ : BP T T --> BP Ω Ω := BinProductOfArrows _ _ _ (true Ω) (true Ω).

    Lemma isMonic_subobject_classifier_conj_mor
      : isMonic φ.
    Proof.
      intros x f g p.
      use BinProductArrowsEq.
      - apply TerminalArrowEq.
      - apply TerminalArrowEq.
    Qed.

    Definition subobject_classifier_conj_monic
      : Monic E (BP T T) (BP Ω Ω).
    Proof.
      use make_Monic.
      - exact φ.
      - exact isMonic_subobject_classifier_conj_mor.
    Defined.

    Definition subobject_classifier_conj
      : BP Ω Ω --> Ω.
    Proof.
      use (characteristic_morphism Ω).
      - exact (BP T T).
      - exact subobject_classifier_conj_monic.
    Defined.
  End Conjunction.

  (** * 3. Disjunction *)
  Section Disjunction.
    Context (HC : is_regular_category E)
            (BP : BinProducts E)
            (BC : BinCoproducts E).

    Definition subobject_classifier_disj_mor
      : BC Ω Ω --> BP Ω Ω.
    Proof.
      use BinCoproductArrow.
      - use BinProductArrow.
        + apply identity.
        + exact (const_true Ω Ω).
      - use BinProductArrow.
        + exact (const_true Ω Ω).
        + apply identity.
    Defined.

    Definition subobject_classifier_disj
      : BP Ω Ω --> Ω.
    Proof.
      refine (characteristic_morphism Ω _).
      exact (regular_category_im_Monic HC subobject_classifier_disj_mor).
    Defined.
  End Disjunction.

  (** * 4. Implication *)
  Section Implication.
    Context (BP : BinProducts E)
            (EE : Equalizers E).

    Definition subobject_classifier_impl_ob
      : Equalizer _ _
      := EE (BP Ω Ω) Ω (subobject_classifier_conj BP) (BinProductPr1 E (BP Ω Ω)).

    Definition subobject_classifier_impl
      : BP Ω Ω --> Ω.
    Proof.
      use (characteristic_morphism Ω).
      - exact subobject_classifier_impl_ob.
      - apply EqualizerArrowMonic.
    Defined.
  End Implication.
End Operations.
