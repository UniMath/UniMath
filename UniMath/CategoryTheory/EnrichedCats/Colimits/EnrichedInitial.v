(*****************************************************************

 Initial objects in enriched categories

 We define the notion of initial objects in the context of
 enriched category theory. In ordinary category theory, an object
 is called initial if there is a unique morphism to every object
 in the category. To translate this concept to enriched category
 theory, we need to phrase this universal property in an arbitrary
 monoidal category instead of for sets.

 The idea is as follows. We want to say that an object `x` is
 initial. For every `y`, we have an object `C ⟦ x , y ⟧` in the
 monoidal category `V`. Then `x` is initial if this hom-object
 is a terminal object in `V`.

 Contents
 1. Initial objects in an enriched category
 2. Being initial is a proposition
 3. Accessors for initial objects
 4. Builders for initial objects
 5. Being initial is closed under iso
 6. Initial objects are isomorphic
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
Require Import UniMath.CategoryTheory.Limits.Initial.

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedInitial.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V).

  (**
   1. Initial objects in an enriched category
   *)
  Definition is_initial_enriched
             (x : C)
    : UU
    := ∏ (y : C), isTerminal V (E ⦃ x , y ⦄).

  Definition initial_enriched
    : UU
    := ∑ (x : C), is_initial_enriched x.

  #[reversible=no] Coercion initial_enriched_to_ob
           (x : initial_enriched)
    : C
    := pr1 x.

  #[reversible=no] Coercion initial_enriched_to_is_initial
           (x : initial_enriched)
    : is_initial_enriched x
    := pr2 x.

  (**
   2. Being initial is a proposition
   *)
  Proposition isaprop_is_initial_enriched
              (x : C)
    : isaprop (is_initial_enriched x).
  Proof.
    do 2 (use impred ; intro).
    apply isapropiscontr.
  Qed.

  (**
   3. Accessors for initial objects
   *)
  Section Accessors.
    Context {x : C}
            (Hx : is_initial_enriched x).

    Definition is_initial_enriched_arrow
               (y : C)
      : I_{V} --> E ⦃ x , y ⦄
      := TerminalArrow (_ ,, Hx y) I_{V}.

    Definition is_initial_enriched_eq
               {y : C}
               (f g : I_{V} --> E ⦃ x , y ⦄)
      : f = g.
    Proof.
      apply (@TerminalArrowEq _ (_ ,, Hx y) I_{V}).
    Qed.

    Definition initial_underlying
      : Initial C.
    Proof.
      refine (x ,, _).
      intros y.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros f g ;
           refine (!(enriched_to_from_arr E f) @ _ @ enriched_to_from_arr E g) ;
           apply maponpaths ;
           apply is_initial_enriched_eq).
      - exact (enriched_to_arr E (is_initial_enriched_arrow y)).
    Defined.
  End Accessors.

  (**
   4. Builders for initial objects
   *)
  Definition make_is_initial_enriched
             (x : C)
             (f : ∏ (w : V) (y : C), w --> E ⦃ x , y ⦄)
             (p : ∏ (w : V) (y : C) (f g : w --> E ⦃ x , y ⦄), f = g)
    : is_initial_enriched x.
  Proof.
    intros y w.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         apply p).
    - apply f.
  Defined.

  Definition make_is_initial_enriched_from_iso
             (TV : Terminal V)
             (x : C)
             (Hx : ∏ (y : C),
                   is_z_isomorphism (TerminalArrow TV (E ⦃ x , y ⦄)))
    : is_initial_enriched x.
  Proof.
    intros y.
    use (iso_to_Terminal TV).
    exact (z_iso_inv (TerminalArrow TV (E ⦃ x , y ⦄) ,, Hx y)).
  Defined.

  Definition initial_enriched_from_underlying
             (TC : Initial C)
             (TV : Terminal V)
             (HV : conservative_moncat V)
    : is_initial_enriched TC.
  Proof.
    use (make_is_initial_enriched_from_iso TV).
    intro y.
    use HV.
    use isweq_iso.
    - intro f.
      apply enriched_from_arr.
      apply (InitialArrow TC).
    - abstract
        (intros f ; cbn ;
         refine (_ @ enriched_from_to_arr E f) ;
         apply maponpaths ;
         apply InitialArrowEq).
    - abstract
        (intros f ; cbn ;
         apply TerminalArrowEq).
  Defined.

  (**
   5. Being initial is closed under iso
   *)
  Definition initial_enriched_from_iso
             {x y : C}
             (Hx : is_initial_enriched x)
             (f : z_iso x y)
    : is_initial_enriched y.
  Proof.
    intros w.
    use (iso_to_Terminal (_ ,, Hx w)) ; cbn.
    exact (precomp_arr_z_iso E w (z_iso_inv f)).
  Defined.

  (**
   6. Initial objects are isomorphic
   *)
  Definition iso_between_initial_enriched
             {x y : C}
             (Hx : is_initial_enriched x)
             (Hy : is_initial_enriched y)
    : z_iso x y.
  Proof.
    use make_z_iso.
    - exact (enriched_to_arr E (is_initial_enriched_arrow Hx y)).
    - exact (enriched_to_arr E (is_initial_enriched_arrow Hy x)).
    - split.
      + abstract
          (refine (enriched_to_arr_comp E _ _ @ _ @ enriched_to_arr_id E _) ;
           apply maponpaths ;
           apply (is_initial_enriched_eq Hx)).
      + abstract
          (refine (enriched_to_arr_comp E _ _ @ _ @ enriched_to_arr_id E _) ;
           apply maponpaths ;
           apply (is_initial_enriched_eq Hy)).
  Defined.

  Definition isaprop_initial_enriched
             (HC : is_univalent C)
    : isaprop initial_enriched.
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isaprop_is_initial_enriched.
    }
    use (isotoid _ HC).
    use iso_between_initial_enriched.
    - exact (pr2 φ₁).
    - exact (pr2 φ₂).
  Defined.
End EnrichedInitial.

(**
 7. Enriched categories with a terminal object
 *)
Definition cat_with_enrichment_initial
           (V : monoidal_cat)
  : UU
  := ∑ (C : cat_with_enrichment V), initial_enriched C.

#[reversible=no] Coercion cat_with_enrichment_initial_to_cat_with_enrichment
         {V : monoidal_cat}
         (C : cat_with_enrichment_initial V)
  : cat_with_enrichment V
  := pr1 C.

Definition initial_of_cat_with_enrichment
           {V : monoidal_cat}
           (C : cat_with_enrichment_initial V)
  : initial_enriched C
  := pr2 C.
