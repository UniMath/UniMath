(*****************************************************************

 Terminal objects in enriched categories

 In this file, we define the notion of a terminal objects in the
 context of enriched category theory.

 The first we formulate, is the universal property of terminal
 objects. This must be done in a slightly differently compared to
 the terminal objects of ordinary categories. Usually, the
 universal property of terminal objects is expressed by saying
 that for each object the set of morphisms between them is
 equivalent to the unit set. This universal property is expressed
 in the category of sets. For enriched categories, we express it
 in the monoidal category `V` over which we enriched. More
 specifically, we say that the hom-object is a terminal object.

 One interesting aspect about limits and colimits in enriched
 category theory is that under certain conditions, we can deduce
 the existence of enriched limits from the existence of ordinary
 limits in the underlying category. A condition that allows us to
 do so, is conservativity of the functor `V(1, -)`. This
 conservativity allows us to prove that a morphism in `V` is
 isomorphic by only looking at the underlying category. Examples
 of monoidal categories that satisfy this condition include the
 category of abelian groups or the category of R-modules. The
 reason why they are conservative, is because a morphism in those
 categories is an isomorphism if and only if the underlying
 morphism between sets is an equivalence.

 We also prove that terminal objects are closed under isomorphism
 and that any two terminal objects are isomorphic.

 Contents
 1. Terminal objects in an enriched category
 2. Being terminal is a proposition
 3. Accessors for terminal objects
 4. Builders for terminal objects
 5. Being terminal is closed under iso
 6. Terminal objects are isomorphic
 7. Enriched categories with a terminal object

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedTerminal.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V).

  (**
   1. Terminal objects in an enriched category
   *)
  Definition is_terminal_enriched
             (x : C)
    : UU
    := ∏ (y : C), isTerminal V (E ⦃ y, x ⦄).

  Definition terminal_enriched
    : UU
    := ∑ (x : C), is_terminal_enriched x.

  #[reversible=no] Coercion terminal_enriched_to_ob
           (x : terminal_enriched)
    : C
    := pr1 x.

  #[reversible=no] Coercion terminal_enriched_to_is_terminal
           (x : terminal_enriched)
    : is_terminal_enriched x
    := pr2 x.

  (**
   2. Being terminal is a proposition
   *)
  Proposition isaprop_is_terminal_enriched
              (x : C)
    : isaprop (is_terminal_enriched x).
  Proof.
    do 2 (use impred ; intro).
    apply isapropiscontr.
  Qed.

  (**
   3. Accessors for terminal objects
   *)
  Section Accessors.
    Context {x : C}
            (Hx : is_terminal_enriched x).

    Definition is_terminal_enriched_arrow
               (y : C)
      : I_{V} --> E ⦃ y , x ⦄
      := TerminalArrow (_ ,, Hx y) I_{V}.

    Definition is_terminal_enriched_eq
               {y : C}
               (f g : I_{V} --> E ⦃ y , x ⦄)
      : f = g.
    Proof.
      apply (@TerminalArrowEq _ (_ ,, Hx y) I_{V}).
    Qed.

    Definition terminal_underlying
      : Terminal C.
    Proof.
      refine (x ,, _).
      intros y.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros f g ;
           refine (!(enriched_to_from_arr E f) @ _ @ enriched_to_from_arr E g) ;
           apply maponpaths ;
           apply is_terminal_enriched_eq).
      - exact (enriched_to_arr E (is_terminal_enriched_arrow y)).
    Defined.
  End Accessors.

  (**
   4. Builders for terminal objects
   *)
  Definition make_is_terminal_enriched
             (x : C)
             (f : ∏ (w : V) (y : C), w --> E ⦃ y , x ⦄)
             (p : ∏ (w : V) (y : C) (f g : w --> E ⦃ y , x ⦄), f = g)
    : is_terminal_enriched x.
  Proof.
    intros y w.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         apply p).
    - apply f.
  Defined.

  Definition make_is_terminal_enriched_from_iso
             (TV : Terminal V)
             (x : C)
             (Hx : ∏ (y : C),
                   is_z_isomorphism (TerminalArrow TV (E ⦃ y, x ⦄)))
    : is_terminal_enriched x.
  Proof.
    intros y.
    use (iso_to_Terminal TV).
    exact (z_iso_inv (TerminalArrow TV (E ⦃ y, x ⦄) ,, Hx y)).
  Defined.

  Definition terminal_enriched_from_underlying
             (TC : Terminal C)
             (TV : Terminal V)
             (HV : conservative_moncat V)
    : is_terminal_enriched TC.
  Proof.
    use (make_is_terminal_enriched_from_iso TV).
    intro y.
    use HV.
    use isweq_iso.
    - intro f.
      apply enriched_from_arr.
      apply (TerminalArrow TC).
    - abstract
        (intros f ; cbn ;
         refine (_ @ enriched_from_to_arr E f) ;
         apply maponpaths ;
         apply TerminalArrowEq).
    - abstract
        (intros f ; cbn ;
         apply TerminalArrowEq).
  Defined.

  (**
   5. Being terminal is closed under iso
   *)
  Definition terminal_enriched_from_iso
             {x y : C}
             (Hx : is_terminal_enriched x)
             (f : z_iso x y)
    : is_terminal_enriched y.
  Proof.
    intros w.
    use (iso_to_Terminal (_ ,, Hx w)) ; cbn.
    exact (postcomp_arr_z_iso E w f).
  Defined.

  (**
   6. Terminal objects are isomorphic
   *)
  Definition iso_between_terminal_enriched
             {x y : C}
             (Hx : is_terminal_enriched x)
             (Hy : is_terminal_enriched y)
    : z_iso x y.
  Proof.
    use make_z_iso.
    - exact (enriched_to_arr E (is_terminal_enriched_arrow Hy x)).
    - exact (enriched_to_arr E (is_terminal_enriched_arrow Hx y)).
    - split.
      + abstract
          (refine (enriched_to_arr_comp E _ _ @ _ @ enriched_to_arr_id E _) ;
           apply maponpaths ;
           apply (is_terminal_enriched_eq Hx)).
      + abstract
          (refine (enriched_to_arr_comp E _ _ @ _ @ enriched_to_arr_id E _) ;
           apply maponpaths ;
           apply (is_terminal_enriched_eq Hy)).
  Defined.

  Definition isaprop_terminal_enriched
             (HC : is_univalent C)
    : isaprop terminal_enriched.
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isaprop_is_terminal_enriched.
    }
    use (isotoid _ HC).
    use iso_between_terminal_enriched.
    - exact (pr2 φ₁).
    - exact (pr2 φ₂).
  Defined.
End EnrichedTerminal.

(**
 7. Enriched categories with a terminal object
 *)
Definition cat_with_enrichment_terminal
           (V : monoidal_cat)
  : UU
  := ∑ (C : cat_with_enrichment V), terminal_enriched C.

#[reversible=no] Coercion cat_with_enrichment_terminal_to_cat_with_enrichment
         {V : monoidal_cat}
         (C : cat_with_enrichment_terminal V)
  : cat_with_enrichment V
  := pr1 C.

Definition terminal_of_cat_with_enrichment
           {V : monoidal_cat}
           (C : cat_with_enrichment_terminal V)
  : terminal_enriched C
  := pr2 C.
