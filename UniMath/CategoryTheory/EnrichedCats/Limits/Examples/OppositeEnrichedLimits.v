(*****************************************************************

 Limits in the enriched opposite category

 If an enriched category has colimits, then its opposite inherits
 these as limits.

 Contents
 1. Terminal object
 2. Binary products
 3. Equalizers
 4. Type indexed products
 5. Powers

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

Section OppositeLimits.
  Context {V : sym_monoidal_cat}
          {C : category}
          (E : enrichment C V).

  Let E' : enrichment (C^opp) V := op_enrichment V E.

  (**
   1. Terminal object
   *)
  Definition opposite_terminal_enriched
             (I : initial_enriched E)
    : terminal_enriched E'.
  Proof.
    exact I.
  Defined.

  (**
   2. Binary products
   *)
  Section OppositeBinaryProducts.
    Context {x y : C}
            (s : binary_coprod_enriched E x y).

    Definition opposite_binary_prod_enriched_is_prod
      : is_binary_prod_enriched E' x y (pr1 s).
    Proof.
      intro w.
      use (isBinProduct_eq_arrow _ _ (pr2 s w)).
      - abstract
          (unfold E' ;
           rewrite op_enrichment_postcomp ;
           apply maponpaths ; cbn ;
           apply idpath).
      - abstract
          (unfold E' ;
           rewrite op_enrichment_postcomp ;
           apply maponpaths ; cbn ;
           apply idpath).
    Defined.

    Definition opposite_binary_prod_enriched
      : binary_prod_enriched E' x y.
    Proof.
      simple refine (_ ,, _).
      - exact (pr1 s).
      - exact opposite_binary_prod_enriched_is_prod.
    Defined.
  End OppositeBinaryProducts.

  Definition opposite_enrichment_binary_prod
             (H : enrichment_binary_coprod E)
    : enrichment_binary_prod E'
    := λ x y, opposite_binary_prod_enriched (H x y).

  (**
   3. Equalizers
   *)
  Section OppositeEqualizers.
    Context {x y : C}
            {f g : x --> y}
            (e : coequalizer_enriched E f g).

    Definition opposite_is_equalizer_enriched
      : is_equalizer_enriched E' f g (pr1 e).
    Proof.
      intro w.
      use (isEqualizer_eq _ _ _ _ _ (pr2 e w)).
      - abstract
          (refine (!_) ;
           apply op_enrichment_postcomp).
      - abstract
          (refine (!_) ;
           apply op_enrichment_postcomp).
      - abstract
          (refine (!_) ;
           apply op_enrichment_postcomp).
    Defined.

    Definition opposite_equalizer_enriched : equalizer_enriched E' f g
      := pr1 e ,, opposite_is_equalizer_enriched.
  End OppositeEqualizers.

  (**
   4. Type indexed products
   *)
  Section OppositeProducts.
    Context {J : UU}
            (ys : J → C)
            (s : coprod_enriched E ys).

    Definition opposite_prod_enriched_is_prod
      : is_prod_enriched E' ys (pr1 s).
    Proof.
      intro w.
      use (isProduct_eq_arrow _ (pr2 s w)).
      abstract
        (intro j ;
         unfold E' ;
         rewrite op_enrichment_postcomp ;
         apply maponpaths ; cbn ;
         apply idpath).
    Defined.

    Definition opposite_prod_enriched
      : prod_enriched E' ys.
    Proof.
      simple refine (_ ,, _).
      - exact (pr1 s).
      - exact opposite_prod_enriched_is_prod.
    Defined.
  End OppositeProducts.
End OppositeLimits.

(**
 5. Powers
 *)
Definition opposite_power_enriched
           {V : sym_mon_closed_cat}
           {C : category}
           (E : enrichment C V)
           {v : V} {x : C}
           (e : copower_cocone E v x)
           (He : is_copower_enriched E v x e)
  : is_power_enriched (op_enrichment V E) v x e.
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
     do 2 apply maponpaths ;
     cbn -[sym_mon_braiding] ;
     rewrite !assoc ;
     rewrite sym_mon_braiding_inv ;
     apply id_left).
Defined.

Definition opposite_enrichment_power
           {V : sym_mon_closed_cat}
           {C : category}
           (E : enrichment C V)
           (HE : enrichment_copower E)
  : enrichment_power (op_enrichment V E)
  := λ v x, pr1 (HE v x) ,, opposite_power_enriched _ _ (pr2 (HE v x)).
