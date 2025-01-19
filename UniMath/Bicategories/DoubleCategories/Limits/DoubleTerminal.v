(*************************************************************************************

 Terminal objects in double categories

 In this file, we define terminal objects in double categories. A double terminal object
 is given by a terminal object in the vertical object that satisfies an additional
 universal property. This additional universal property says that the horizontal identity
 morphism of the terminal object is terminal in the category of horizontal morphisms and
 squares. Concretely, it allows one to make squares from any horizontal morphism to the
 identity morphism on the terminal object. We also give builders and accessors for
 terminal objects, and we give some examples of terminal objects.

 References
 - Section 5.1.5 in "Higher Dimensional Categories, From Double to Multiple Categories"
   by Grandis

 Content
 1. Terminal objects in double categories
 2. Accessors and builders
 3. Terminal object in the double category of relations
 4. Terminal object in the double category of enriched relations
 5. Terminal object in the double category of spans

 *************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.EnrichedRels.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Spans.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Examples.RelationsDoubleCat.
Require Import UniMath.Bicategories.DoubleCategories.Examples.EnrichedRelDoubleCat.
Require Import UniMath.Bicategories.DoubleCategories.Examples.SpansDoubleCat.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Terminal objects in double categories *)
Definition is_double_terminal
           (C : double_cat)
           (T : Terminal C)
  : UU
  := ∏ (x₁ x₂ : C)
       (h : x₁ -->h x₂),
     iscontr (square (TerminalArrow T x₁) (TerminalArrow T x₂) h (identity_h T)).

Proposition isaprop_is_double_terminal
            (C : double_cat)
            (T : Terminal C)
  : isaprop (is_double_terminal C T).
Proof.
  do 3 (use impred ; intro).
  apply isapropiscontr.
Qed.

Definition double_terminal
           (C : double_cat)
  : UU
  := ∑ (T : Terminal C), is_double_terminal C T.

(** * 2. Accessors and builders *)
Proposition make_is_double_terminal_flat_double_cat
            {C : double_cat}
            (H : is_flat_double_cat C)
            (T : Terminal C)
            (HT : ∏ (x₁ x₂ : C)
                    (h : x₁ -->h x₂),
                  square (TerminalArrow T x₁) (TerminalArrow T x₂) h (identity_h T))
  : is_double_terminal C T.
Proof.
  intros x₁ x₂ h.
  refine (HT x₁ x₂ h ,, _).
  intro.
  apply H.
Qed.

Definition make_double_terminal
           {C : double_cat}
           (T : Terminal C)
           (HT : is_double_terminal C T)
  : double_terminal C
  := T ,, HT.

Coercion double_terminal_to_ob
         {C : double_cat}
         (T : double_terminal C)
  : C.
Proof.
  exact (pr11 T).
Defined.

Definition double_terminal_ver
           {C : double_cat}
           (T : double_terminal C)
           (x : C)
  : x -->v T
  := TerminalArrow (pr1 T) x.

Proposition double_terminal_ver_eq
            {C : double_cat}
            {T : double_terminal C}
            {x : C}
            (f g : x -->v T)
  : f = g.
Proof.
  exact (TerminalArrowEq (T := pr1 T) f g).
Qed.

Definition double_terminal_sqr
           {C : double_cat}
           (T : double_terminal C)
           {x₁ x₂ : C}
           (h : x₁ -->h x₂)
  : square
      (double_terminal_ver T x₁)
      (double_terminal_ver T x₂)
      h
      (identity_h T).
Proof.
  exact (pr1 (pr2 T x₁ x₂ h)).
Defined.

Definition double_terminal_sqr'
           {C : double_cat}
           (T : double_terminal C)
           {x₁ x₂ : C}
           (f : x₁ -->v T)
           (g : x₂ -->v T)
           (h : x₁ -->h x₂)
  : square f g h (identity_h T)
  := transportf_square
       (double_terminal_ver_eq _ _)
       (double_terminal_ver_eq _ _)
       (double_terminal_sqr T h).

Proposition double_terminal_sqr_eq
            {C : double_cat}
            (T : double_terminal C)
            {x₁ x₂ : C}
            {h : x₁ -->h x₂}
            (s₁ s₂ : square
                       (double_terminal_ver T x₁)
                       (double_terminal_ver T x₂)
                       h
                       (identity_h T))
  : s₁ = s₂.
Proof.
  exact (proofirrelevance _ (isapropifcontr (pr2 T x₁ x₂ h)) s₁ s₂).
Qed.

(** * 3. Terminal object in the double category of relations *)
Proposition is_double_terminal_rel_double_cat
  : is_double_terminal rel_double_cat TerminalHSET.
Proof.
  intros X₁ X₂ R.
  use make_is_double_terminal_flat_double_cat.
  {
    apply is_flat_rel_double_cat.
  }
  intros ? ? ? ? ? ? ; cbn.
  apply isapropunit.
Qed.

Definition double_terminal_relations
  : double_terminal rel_double_cat.
Proof.
  use make_double_terminal.
  - exact TerminalHSET.
  - exact is_double_terminal_rel_double_cat.
Defined.

(** * 4. Terminal object in the double category of enriched relations *)
Proposition is_double_terminal_enriched_rel_double_cat
            (V : quantale_cosmos)
            (HV : is_semicartesian V)
  : is_double_terminal (enriched_rel_double_cat V) TerminalHSET.
Proof.
  use make_is_double_terminal_flat_double_cat.
  {
    apply is_flat_enriched_rel_double_cat.
  }
  intros ? ? ? ? ? ; cbn.
  refine (_ · CoproductIn _ _ _ (idpath _)).
  apply (semi_cart_to_unit HV).
Qed.

Definition double_terminal_enriched_rel
           (V : quantale_cosmos)
           (HV : is_semicartesian V)
  : double_terminal (enriched_rel_double_cat V).
Proof.
  use make_double_terminal.
  - exact TerminalHSET.
  - exact (is_double_terminal_enriched_rel_double_cat V HV).
Defined.

(** * 5. Terminal object in the double category of spans *)
Definition is_double_terminal_spans_double_cat
           {C : category}
           (T : Terminal C)
           (PC : Pullbacks C)
  : is_double_terminal (spans_double_cat PC) T.
Proof.
  intros x₁ x₂ s.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use span_sqr_eq ;
       apply TerminalArrowEq).
  - use make_span_sqr.
    + apply TerminalArrow.
    + abstract
        (split ; apply TerminalArrowEq).
Defined.

Definition double_terminal_spans
           {C : category}
           (T : Terminal C)
           (PC : Pullbacks C)
  : double_terminal (spans_double_cat PC).
Proof.
  use make_double_terminal.
  - exact T.
  - exact (is_double_terminal_spans_double_cat T PC).
Defined.
