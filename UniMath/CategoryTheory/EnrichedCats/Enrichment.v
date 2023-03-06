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
 4. Composition operations

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Import MonoidalNotations.

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
     (∏ (x : C), I_{V} --> arr x x)
     ×
     (∏ (x y z : C), arr y z ⊗ arr x y --> arr x z)
     ×
     (∏ (x y : C), x --> y → I_{V} --> arr x y)
     ×
     (∏ (x y : C), I_{V} --> arr x y → x --> y).

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
  : I_{V} --> E ⦃ x , x ⦄
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
  : I_{V} --> E ⦃ x , y ⦄
  := pr1 (pr222 E) x y f.

Definition enriched_to_arr
           {C : precategory_data}
           {V : monoidal_cat}
           (E : enrichment_data C V)
           {x y : C}
           (f : I_{V} --> E ⦃ x , y ⦄)
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
     (∏ (x y : C) (f : I_{V} --> E ⦃ x , y ⦄),
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
        (mon_linvunitor I_{V}
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
             (f : I_{V} --> E ⦃ x , y ⦄)
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
        (mon_linvunitor I_{V}
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
      mon_linvunitor I_{V}
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
     (∏ (x y : C) (f : I_{V} --> E₁ ⦃ x , y ⦄),
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
     (∏ (a : I_{V} --> x), a · f = a · g)
     →
     f = g.

(**
 4. Composition operations
 *)
Definition precomp_arr
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {x y : C}
           (z : C)
           (f : x --> y)
  : E ⦃ y , z ⦄ --> E ⦃ x , z ⦄
  := mon_rinvunitor _
     · (identity _ #⊗ enriched_from_arr E f)
     · enriched_comp E x y z.

Definition precomp_arr_id
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           (x y : C)
  : precomp_arr E _ (identity x) = identity (E ⦃ x , y ⦄).
Proof.
  unfold precomp_arr.
  rewrite enriched_from_arr_id.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply enrichment_id_right.
  }
  apply mon_rinvunitor_runitor.
Qed.

Definition precomp_arr_comp
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {w x y z : C}
           (f : w --> x)
           (g : x --> y)
  : precomp_arr E z (f · g) = precomp_arr E z g · precomp_arr E z f.
Proof.
  unfold precomp_arr.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  rewrite enriched_from_arr_comp.
  etrans.
  {
    apply maponpaths_2.
    apply tensor_comp_id_l.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply enrichment_assoc'.
  }
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply tensor_comp_id_l.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    apply tensor_rassociator.
  }
  etrans.
  {
    rewrite !assoc.
    do 2 apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply mon_inv_triangle.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply mon_lassociator_rassociator.
    }
    apply id_right.
  }
  etrans.
  {
    apply maponpaths_2.
    exact (!(tensor_comp_mor _ _ _ _)).
  }
  refine (!(tensor_comp_mor _ _ _ _) @ _).
  rewrite !id_left, !id_right.
  refine (tensor_split' _ _ @ _).
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply tensor_rinvunitor.
  }
  rewrite !assoc.
  refine (!_).
  refine (tensor_comp_id_r _ _ @ _).
  apply maponpaths_2.
  refine (tensor_comp_id_r _ _ @ _).
  refine (!_).
  etrans.
  {
    apply tensor_rinvunitor.
  }
  apply maponpaths_2.
  refine (!(mon_rinvunitor_triangle _ _) @ _).
  rewrite mon_rinvunitor_I_mon_linvunitor_I.
  etrans.
  {
    apply maponpaths_2.
    apply mon_inv_triangle.
  }
  rewrite !assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  apply mon_lassociator_rassociator.
Qed.

Definition enriched_id_precomp_arr
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {x y : C}
           (f : x --> y)
  : enriched_id E y · precomp_arr E _ f
    =
    enriched_from_arr E f.
Proof.
  unfold precomp_arr.
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply tensor_rinvunitor.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!(tensor_split' _ _) @ _).
    apply tensor_split.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply enrichment_id_left.
    }
    apply tensor_lunitor.
  }
  rewrite !assoc.
  refine (_ @ id_left _).
  apply maponpaths_2.
  rewrite mon_lunitor_I_mon_runitor_I.
  apply mon_rinvunitor_runitor.
Qed.

Definition enriched_from_arr_precomp
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {x y z : C}
           (f : x --> y)
           (g : y --> z)
  : enriched_from_arr E g · precomp_arr E _ f
    =
    enriched_from_arr E (f · g).
Proof.
  unfold precomp_arr.
  rewrite enriched_from_arr_comp.
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply tensor_split'.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  rewrite mon_linvunitor_I_mon_rinvunitor_I.
  apply tensor_rinvunitor.
Qed.

Definition enriched_comp_precomp_arr
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {w x y z : C}
           (f : w --> x)
  : enriched_comp E x y z · precomp_arr E z f
    =
    (identity _ #⊗ precomp_arr E y f) · enriched_comp E w y z.
Proof.
  unfold precomp_arr.
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply tensor_rinvunitor.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!(tensor_split' _ _) @ _).
      apply tensor_split.
    }
    rewrite !assoc'.
    apply maponpaths.
    apply enrichment_assoc.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (_ @ !(tensor_comp_id_l _ _)).
  apply maponpaths_2.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (!(tensor_id_id _ _)).
    }
    apply tensor_lassociator.
  }
  rewrite !assoc.
  refine (_ @ !(tensor_comp_id_l _ _)).
  apply maponpaths_2.
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply mon_rinvunitor_triangle.
  }
  rewrite !assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  apply mon_rassociator_lassociator.
Qed.

Definition postcomp_arr
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {y z : C}
           (x : C)
           (f : y --> z)
  : E ⦃ x , y ⦄ --> E ⦃ x , z ⦄
  := mon_linvunitor _
     · (enriched_from_arr E f #⊗ identity _)
     · enriched_comp E x y z.

Definition postcomp_arr_id
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           (x y : C)
  : postcomp_arr E _ (identity y) = identity (E ⦃ x , y ⦄).
Proof.
  unfold postcomp_arr.
  rewrite enriched_from_arr_id.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply enrichment_id_left.
  }
  apply mon_linvunitor_lunitor.
Qed.

Definition postcomp_arr_comp
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {w x y z : C}
           (f : x --> y)
           (g : y --> z)
  : postcomp_arr E w (f · g) = postcomp_arr E w f · postcomp_arr E w g.
Proof.
  unfold postcomp_arr.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  rewrite enriched_from_arr_comp.
  etrans.
  {
    apply maponpaths_2.
    apply tensor_comp_id_r.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply enrichment_assoc.
  }
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply tensor_comp_id_r.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    apply tensor_lassociator.
  }
  etrans.
  {
    rewrite !assoc.
    do 2 apply maponpaths_2.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    refine (!_).
    apply mon_inv_triangle.
  }
  etrans.
  {
    apply maponpaths_2.
    exact (!(tensor_comp_mor _ _ _ _)).
  }
  refine (!(tensor_comp_mor _ _ _ _) @ _).
  rewrite !id_left, !id_right.
  refine (tensor_split _ _ @ _).
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply tensor_linvunitor.
  }
  rewrite !assoc.
  refine (!_).
  refine (tensor_comp_id_l _ _ @ _).
  apply maponpaths_2.
  refine (tensor_comp_id_l _ _ @ _).
  refine (!_).
  etrans.
  {
    apply tensor_linvunitor.
  }
  apply maponpaths_2.
  refine (!(mon_linvunitor_triangle _ _) @ _).
  rewrite mon_linvunitor_I_mon_rinvunitor_I.
  refine (!_).
  apply mon_inv_triangle.
Qed.

Definition enriched_id_postcomp_arr
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {x y : C}
           (f : x --> y)
  : enriched_id E x · postcomp_arr E _ f
    =
    enriched_from_arr E f.
Proof.
  unfold postcomp_arr.
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply tensor_linvunitor.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!(tensor_split _ _) @ _).
    apply tensor_split'.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply enrichment_id_right.
    }
    apply tensor_runitor.
  }
  rewrite !assoc.
  refine (_ @ id_left _).
  apply maponpaths_2.
  rewrite mon_runitor_I_mon_lunitor_I.
  apply mon_linvunitor_lunitor.
Qed.

Definition enriched_from_arr_postcomp
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {x y z : C}
           (f : x --> y)
           (g : y --> z)
  : enriched_from_arr E f · postcomp_arr E _ g
    =
    enriched_from_arr E (f · g).
Proof.
  unfold postcomp_arr.
  rewrite enriched_from_arr_comp.
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply tensor_split.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (!_).
  apply tensor_linvunitor.
Qed.

Definition enriched_comp_postcomp_arr
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {w x y z : C}
           (f : y --> z)
  : enriched_comp E w x y · postcomp_arr E w f
    =
    (postcomp_arr E x f #⊗ identity _) · enriched_comp E w x z.
Proof.
  unfold postcomp_arr.
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply tensor_linvunitor.
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!(tensor_split _ _) @ _).
      apply tensor_split'.
    }
    rewrite !assoc'.
    apply maponpaths.
    apply enrichment_assoc'.
  }
  rewrite !assoc.
  apply maponpaths_2.
  refine (_ @ !(tensor_comp_id_r _ _)).
  apply maponpaths_2.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      exact (!(tensor_id_id _ _)).
    }
    apply tensor_rassociator.
  }
  rewrite !assoc.
  refine (_ @ !(tensor_comp_id_r _ _)).
  apply maponpaths_2.
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply mon_linvunitor_triangle.
  }
  rewrite !assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  apply mon_lassociator_rassociator.
Qed.

Definition precomp_postcomp_arr
           {C : category}
           {V : monoidal_cat}
           (E : enrichment C V)
           {w x y z : C}
           (f : w --> x)
           (g : y --> z)
  : precomp_arr E y f · postcomp_arr E w g
    =
    postcomp_arr E x g · precomp_arr E z f.
Proof.
  unfold precomp_arr, postcomp_arr.
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply tensor_linvunitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!(tensor_split _ _) @ _).
      apply tensor_split'.
    }
    rewrite !assoc'.
    apply maponpaths.
    apply enrichment_assoc'.
  }
  rewrite !assoc.
  apply maponpaths_2.
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (!(tensor_id_id _ _)).
      }
      apply tensor_rassociator.
    }
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply mon_linvunitor_triangle.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply mon_lassociator_rassociator.
    }
    apply id_right.
  }
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!(tensor_split _ _) @ _).
      apply tensor_split'.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!(tensor_split _ _) @ _).
      apply tensor_split'.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!(tensor_split _ _) @ _).
    apply tensor_split'.
  }
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    do 2 apply maponpaths_2.
    refine (!_).
    apply tensor_rinvunitor.
  }
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply tensor_comp_id_r.
  }
  etrans.
  {
    refine (!_).
    apply tensor_rinvunitor.
  }
  rewrite !assoc'.
  apply idpath.
Qed.
