(*****************************************************************

 Colimits in the enriched opposite category

 If an enriched category has limits, then its opposite inherits
 these as colimits.

 Contents
 1. Initial object
 2. Binary coproducts
 3. Coequalizers
 4. Type indexed coproducts
 5. Copowers

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.OppositeEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedTerminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedBinaryProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedEqualizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedInitial.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedBinaryCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoequalizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section OppositeColimits.
  Context {V : sym_monoidal_cat}
          {C : category}
          (E : enrichment C V).

  Let E' : enrichment (C^opp) V := op_enrichment V E.

  (**
   1. Initial object
   *)
  Definition opposite_initial_enriched
             (T : terminal_enriched E)
    : initial_enriched E'.
  Proof.
    exact T.
  Defined.

  (**
   2. Binary coproducts
   *)
  Section OppositeBinaryCoproducts.
    Context {x y : C}
            (s : binary_prod_enriched E x y).

    Definition opposite_binary_coprod_enriched_is_coprod
      : is_binary_coprod_enriched E' x y (pr1 s).
    Proof.
      intro w.
      use (isBinProduct_eq_arrow _ _ (pr2 s w)).
      - abstract
          (unfold E' ;
           rewrite op_enrichment_precomp ;
           apply maponpaths ; cbn ;
           apply idpath).
      - abstract
          (unfold E' ;
           rewrite op_enrichment_precomp ;
           apply maponpaths ; cbn ;
           apply idpath).
    Defined.

    Definition opposite_binary_coprod_enriched
      : binary_coprod_enriched E' x y.
    Proof.
      simple refine (_ ,, _).
      - exact (pr1 s).
      - exact opposite_binary_coprod_enriched_is_coprod.
    Defined.
  End OppositeBinaryCoproducts.

  Definition opposite_enrichment_binary_coprod
             (H : enrichment_binary_prod E)
    : enrichment_binary_coprod E'
    := λ x y, opposite_binary_coprod_enriched (H x y).

  (**
   3. Coequalizers
   *)
  Section OppositeCoequalizers.
    Context {x y : C}
            {f g : x --> y}
            (e : equalizer_enriched E f g).

    Definition opposite_is_coequalizer_enriched
      : is_coequalizer_enriched E' f g (pr1 e).
    Proof.
      intro w.
      use (isEqualizer_eq _ _ _ _ _ (pr2 e w)).
      - abstract
          (refine (!_) ;
           apply op_enrichment_precomp).
      - abstract
          (refine (!_) ;
           apply op_enrichment_precomp).
      - abstract
          (refine (!_) ;
           apply op_enrichment_precomp).
    Defined.

    Definition opposite_coequalizer_enriched : coequalizer_enriched E' f g
      := pr1 e ,, opposite_is_coequalizer_enriched.
  End OppositeCoequalizers.

  (**
   4. Type indexed coproducts
   *)
  Section OppositeCoproducts.
    Context {J : UU}
            (ys : J → C)
            (s : prod_enriched E ys).

    Definition opposite_coprod_enriched_is_coprod
      : is_coprod_enriched E' ys (pr1 s).
    Proof.
      intro w.
      use (isProduct_eq_arrow _ (pr2 s w)).
      abstract
        (intro j ;
         unfold E' ;
         rewrite op_enrichment_precomp ;
         apply maponpaths ; cbn ;
         apply idpath).
    Defined.

    Definition opposite_coprod_enriched
      : coprod_enriched E' ys.
    Proof.
      simple refine (_ ,, _).
      - exact (pr1 s).
      - exact opposite_coprod_enriched_is_coprod.
    Defined.
  End OppositeCoproducts.
End OppositeColimits.

(**
 5. Copowers
 *)
Definition opposite_copower_enriched
           {V : sym_mon_closed_cat}
           {C : category}
           (E : enrichment C V)
           {v : V} {x : C}
           (e : power_cone E v x)
           (He : is_power_enriched E v x e)
  : is_copower_enriched (op_enrichment V E) v x e.
Proof.
  intros w.
  use (is_z_isomorphism_path _ (He w)).
  abstract
    (unfold is_copower_enriched_map, is_power_enriched_map ;
     use internal_funext ;
     intros a h ;
     rewrite tensor_split ;
     rewrite !assoc' ;
     rewrite internal_beta ;
     refine (!_) ;
     rewrite tensor_split ;
     rewrite !assoc' ;
     rewrite internal_beta ;
     apply idpath).
Defined.

Definition opposite_enrichment_copower
           {V : sym_mon_closed_cat}
           {C : category}
           (E : enrichment C V)
           (HE : enrichment_power E)
  : enrichment_copower (op_enrichment V E)
  := λ v x, pr1 (HE v x) ,, opposite_copower_enriched _ _ (pr2 (HE v x)).
