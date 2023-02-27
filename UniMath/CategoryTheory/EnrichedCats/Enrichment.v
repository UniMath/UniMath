(*****************************************************************

 Enrichments of categories

 In this file, we define enrichments of categories, functors, and
 natural transformations. Note that we define these enrichments as
 categories/functors/transformations with extra data and
 properties, whereas the standard definition of enriched category
 does not do so.

 There are a couple of reasons for this choice:
 - It will help use prove the univalence of the bicategory of
   univalent enriched categories. That is because in the whole
   proof, we don't have to prove equality of the type of objects.
   As such, we can reuse the proof that the bicategory of
   univalent categories is univalent.
 - If we would use the usual definition of enriched categories,
   then in order to access the morphisms, we would first need to
   take the underlying category. With this definition, we can use
   a coercion instead.

 Our definition is loosely inspired by the one given by McDermott
 and Uustalu in "What makes a strong monad?"

 https://arxiv.org/pdf/2207.00851.pdf

 We also define faithful monoidal categories. These are monoidal
 categories in which the representable functor is faithful. This
 property is useful, because it implies that every natural
 transformation is actually enriched.

 Contents
 1. Enrichments of categories
 2. Equality of enrichments
 3. Faithfulness

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Opaque mon_lunitor mon_linvunitor.
Opaque mon_runitor mon_rinvunitor.
Opaque mon_lassociator mon_rassociator.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Enrichments of categories
 *)
Definition enrichment_data
           (C : precategory_data)
           (V : monoidal_cat)
  : UU
  := ∑ (arr : C → C → V),
     (∏ (x : C), 𝟙 --> arr x x)
     ×
     (∏ (x y z : C), arr y z ⊗ arr x y --> arr x z)
     ×
     (∏ (x y : C), x --> y → 𝟙 --> arr x y)
     ×
     (∏ (x y : C), 𝟙 --> arr x y → x --> y).

Definition arr_enrichment_data
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           (x y : C)
  : V
  := pr1 E x y.

Notation "E ⦃ x , y ⦄" := (arr_enrichment_data E x y) (at level 49).

Definition enriched_id
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           (x : C)
  : 𝟙 --> E ⦃ x , x ⦄
  := pr12 E x.

Definition enriched_comp
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           (x y z : C)
  : (E ⦃ y , z ⦄) ⊗ (E ⦃ x ,  y ⦄) --> E ⦃ x , z ⦄
  := pr122 E x y z.

Definition enriched_from_arr
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           {x y : C}
           (f : x --> y)
  : 𝟙 --> E ⦃ x , y ⦄
  := pr1 (pr222 E) x y f.

Definition enriched_to_arr
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           {x y : C}
           (f : 𝟙 --> E ⦃ x , y ⦄)
  : x --> y
  := pr2 (pr222 E) x y f.

Definition enrichment_laws
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
  : UU
  := (∏ (x y : C),
      mon_lunitor (E ⦃ x , y ⦄)
      =
      enriched_id E y #⊗ identity _ · enriched_comp E x y y)
     ×
     (∏ (x y : C),
      mon_runitor (E ⦃ x , y ⦄)
      =
      identity _ #⊗ enriched_id E x · enriched_comp E x x y)
     ×
     (∏ (w x y z : C),
      enriched_comp E x y z #⊗ identity (E ⦃ w, x ⦄)
      · enriched_comp E w x z
      =
      mon_lassociator _ _ _
      · identity _ #⊗ enriched_comp E w x y
      · enriched_comp E w y z)
     ×
     (∏ (x y : C) (f : x --> y),
      enriched_to_arr E (enriched_from_arr E f)
      =
      f)
     ×
     (∏ (x y : C) (f : 𝟙 --> E ⦃ x , y ⦄),
      enriched_from_arr E (enriched_to_arr E f)
      =
      f)
     ×
     (∏ (x : C),
      enriched_to_arr E (enriched_id E x)
      =
      identity x)
     ×
     (∏ (x y z : C) (f : x --> y) (g : y --> z),
      f · g
      =
      enriched_to_arr
        E
        (mon_linvunitor 𝟙
         · (enriched_from_arr E g #⊗ enriched_from_arr E f)
         · enriched_comp E x y z)).

Definition isaprop_enrichment_laws
           {C : category}
           {V : monoidal_cat}
           (E : enrichment_data C V)
  : isaprop (enrichment_laws E).
Proof.
  repeat (use isapropdirprod) ; repeat (use impred ; intro) ; apply homset_property.
Qed.

Definition enrichment
           (C : category)
           (V : monoidal_cat)
  : UU
  := ∑ (E : enrichment_data C V), enrichment_laws E.

Coercion enrichment_to_data
         {C : category}
         {V : monoidal_cat}
         (E : enrichment C V)
  : enrichment_data C V
  := pr1 E.

Section EnrichmentLaws.
  Context {C : category}
          {V : monoidal_cat}
          (E : enrichment C V).

  Definition enrichment_id_left
             (x y : C)
    : mon_lunitor (E ⦃ x , y ⦄)
      =
      enriched_id E y #⊗ identity _ · enriched_comp E x y y.
  Proof.
    exact (pr12 E x y).
  Qed.

  Definition enrichment_id_right
             (x y : C)
    : mon_runitor (E ⦃ x , y ⦄)
      =
      identity _ #⊗ enriched_id E x · enriched_comp E x x y.
  Proof.
    exact (pr122 E x y).
  Qed.

  Definition enrichment_assoc
             (w x y z : C)
    : enriched_comp E x y z #⊗ identity _
      · enriched_comp E w x z
      =
      mon_lassociator _ _ _
      · identity _ #⊗ enriched_comp E w x y
      · enriched_comp E w y z.
  Proof.
    exact (pr1 (pr222 E) w x y z).
  Qed.

  Definition enrichment_assoc'
             (w x y z : C)
    : identity _ #⊗ enriched_comp E w x y
      · enriched_comp E w y z
      =
      mon_rassociator _ _ _
      · enriched_comp E x y z #⊗ identity _
      · enriched_comp E w x z.
  Proof.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply enrichment_assoc.
    }
    rewrite !assoc.
    rewrite mon_rassociator_lassociator.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition enriched_to_from_arr
             {x y : C}
             (f : x --> y)
    : enriched_to_arr E (enriched_from_arr E f)
      =
      f.
  Proof.
    exact (pr12 (pr222 E) x y f).
  Qed.

  Definition enriched_from_to_arr
             {x y : C}
             (f : 𝟙 --> E ⦃ x , y ⦄)
    : enriched_from_arr E (enriched_to_arr E f)
      =
      f.
  Proof.
    exact (pr122 (pr222 E) x y f).
  Qed.

  Definition enriched_to_arr_id
             (x : C)
    : enriched_to_arr E (enriched_id E x)
      =
      identity x.
  Proof.
    exact (pr1 (pr222 (pr222 E)) x).
  Qed.

  Definition enriched_from_arr_id
             (x : C)
    : enriched_from_arr E (identity x)
      =
      enriched_id E x.
  Proof.
    refine (_ @ enriched_from_to_arr _).
    apply maponpaths.
    refine (!_).
    apply enriched_to_arr_id.
  Qed.

  Definition enriched_to_arr_comp
             {x y z : C}
             (f : x --> y)
             (g : y --> z)
    : f · g
      =
      enriched_to_arr
        E
        (mon_linvunitor 𝟙
         · (enriched_from_arr E g #⊗ enriched_from_arr E f)
         · enriched_comp E x y z).
  Proof.
    exact (pr2 (pr222 (pr222 E)) x y z f g).
  Qed.

  Definition enriched_from_arr_comp
             {x y z : C}
             (f : x --> y)
             (g : y --> z)
    : enriched_from_arr
        E
        (f · g)
      =
      mon_linvunitor 𝟙
      · (enriched_from_arr E g #⊗ enriched_from_arr E f)
      · enriched_comp E x y z.
  Proof.
    refine (_ @ enriched_from_to_arr _).
    apply maponpaths.
    apply enriched_to_arr_comp.
  Qed.

  Definition isweq_enriched_from_arr
             (x y : C)
    : isweq (@enriched_from_arr _ _ E x y).
  Proof.
    use isweq_iso.
    - exact (enriched_to_arr E).
    - intro f.
      apply enriched_to_from_arr.
    - intro f.
      apply enriched_from_to_arr.
  Defined.

  Definition isweq_enriched_to_arr
             (x y : C)
    : isweq (@enriched_to_arr _ _ E x y).
  Proof.
    exact (pr2 (invweq (_ ,, isweq_enriched_from_arr x y))).
  Defined.
End EnrichmentLaws.

Definition cat_with_enrichment
           (V : monoidal_cat)
  : UU
  := ∑ (C : category), enrichment C V.

Coercion cat_with_enrichment_to_cat
         {V : monoidal_cat}
         (E : cat_with_enrichment V)
  : category
  := pr1 E.

Coercion cat_with_enrichment_to_enrichment
         {V : monoidal_cat}
         (E : cat_with_enrichment V)
  : enrichment E V
  := pr2 E.

(**
 2. Equality of enrichments
 *)
Definition enrichment_data_hom_weq
           {C : precategory_data}
           {V : monoidal_cat}
           (HV : is_univalent V)
           (E₁ E₂ : enrichment_data C V)
  : (pr1 E₁ = pr1 E₂) ≃ ∏ (x y : C), z_iso (pr1 E₁ x y) (pr1 E₂ x y)
  := (weqonsecfibers
        _ _
        (λ x, weqonsecfibers _ _ (λ y, _ ,, HV _ _)
      ∘ weqtoforallpaths _ _ _) ∘ weqtoforallpaths _ _ _)%weq.

Definition enrichment_data_hom_path_help
           {C : precategory_data}
           {V : monoidal_cat}
           (E₁ E₂ : enrichment_data C V)
  : UU
  := ∑ (fs : ∏ (x y : C), z_iso (pr1 E₁ x y) (pr1 E₂ x y)),
     (∏ (x : C),
      enriched_id E₁ x · fs x x
      =
      enriched_id E₂ x)
     ×
     (∏ (x y z : C),
      enriched_comp E₁ x y z · fs x z
      =
      fs y z #⊗ fs x y · enriched_comp E₂ x y z)
     ×
     (∏ (x y : C) (f : x --> y),
      enriched_from_arr E₁ f · fs x y
      =
      enriched_from_arr E₂ f)
     ×
     (∏ (x y : C) (f : 𝟙 --> E₁ ⦃ x , y ⦄),
      enriched_to_arr E₁ f
      =
      enriched_to_arr E₂ (f · fs x y)).

Definition enrichment_data_hom_path
           {C : category}
           {V : monoidal_cat}
           (HV : is_univalent V)
           (E₁ E₂ : enrichment_data C V)
  : E₁ ╝ E₂ ≃ enrichment_data_hom_path_help E₁ E₂.
Proof.
  use (weqbandf (enrichment_data_hom_weq HV E₁ E₂)).
  intros p.
  induction E₁ as [ M₁ E₁ ].
  induction E₂ as [ M₂ E₂ ].
  cbn in *.
  induction p.
  cbn.
  use weqimplimpl.
  - intro p.
    induction p.
    repeat split ; intros.
    + rewrite id_right.
      apply idpath.
    + rewrite id_right.
      rewrite tensor_id_id.
      rewrite id_left.
      apply idpath.
    + apply id_right.
    + rewrite id_right.
      apply idpath.
  - intros p.
    repeat (use pathsdirprod).
    + use funextsec ; intro x.
      pose (pr1 p x) as q.
      rewrite id_right in q.
      exact q.
    + use funextsec ; intro x.
      use funextsec ; intro y.
      use funextsec ; intro z.
      pose (pr12 p x y z) as q.
      rewrite id_right in q.
      rewrite tensor_id_id in q.
      rewrite id_left in q.
      exact q.
    + use funextsec ; intro x.
      use funextsec ; intro y.
      use funextsec ; intro f.
      pose (pr122 p x y f) as q.
      cbn in q.
      rewrite id_right in q.
      exact q.
    + use funextsec ; intro x.
      use funextsec ; intro y.
      use funextsec ; intro f.
      pose (pr222 p x y f) as q.
      cbn in q.
      rewrite id_right in q.
      exact q.
  - repeat (apply isaset_dirprod) ;
    repeat (use impred_isaset ; intro) ;
    apply homset_property.
  - repeat (apply isapropdirprod) ;
      repeat (use impred ; intro) ;
      apply homset_property.
Defined.

(**
 3. Faithfulness
 *)
Definition faithful_moncat
           (V : monoidal_cat)
  : UU
  := ∏ (x y : V)
       (f g : x --> y),
     (∏ (a : 𝟙 --> x), a · f = a · g)
     →
     f = g.
