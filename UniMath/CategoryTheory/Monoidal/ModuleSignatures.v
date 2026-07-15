(***************************************************************************

 (Right) Module Signatures

 In this file, we define signatures as sections of the forgetful functor from
 the total category of right modules to the category of monoids.

 They form a category "module_signature_cat".

 Contents
 1. Definitions
 2. Two examples of module signatures
 3. Evaluation functor (for some fixed monoid R)

 ***************************************************************************)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.RModules.
Require Import UniMath.CategoryTheory.Monoidal.TotalCategoriesOfRModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.DisplayedSections.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope mor_disp_scope.

Section ModuleSignatures.
  Context {C : monoidal_cat}.

  Local Notation "x ⊗l f" := (x ⊗^{C}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{C}_{r} y) (at level 31).

  (**
     1. Definitions
   *)

  (* We use displayed sections, as total_category_of_modules is a displayed category *)

  Definition module_signature_data 
    := @section_disp_data (MON C) total_category_of_modules_disp_cat.

  Definition module_signature_cat : category
    := @section_disp_cat (MON C) total_category_of_modules_disp_cat.

  Definition module_signature_disp_on_objects (Σ : module_signature_data) (R : MON C) 
    : MOD (pr1 R) (pr2 R) := pr1 Σ R.

  Definition module_signature_disp_cat_to_data (Σ : module_signature_cat)
    : module_signature_data := pr1 Σ.

  Coercion module_signature_disp_on_objects : module_signature_data >-> Funclass.
  Coercion module_signature_disp_cat_to_data : ob >-> module_signature_data.

  Definition module_signature_axioms (Σ : module_signature_data)
    := section_disp_axioms Σ.

  Lemma module_signature_equality (Σ Σ' : module_signature_cat)
    (equality_on_objects : ∏ A, Σ A = Σ' A)
    (equality_on_morphisms : ∏ (A A' : MON C) (f : A --> A'),
      transportf
        (λ ΣA : MOD (pr1 A) (pr2 A), C ⟦ pr1 ΣA, pr1 (Σ' A') ⟧)
        (equality_on_objects A)
        (transportf
           (λ ΣA' : MOD (pr1 A') (pr2 A'), C ⟦ pr1 (Σ A), pr1 ΣA' ⟧)
           (equality_on_objects A') (pr1 (section_disp_on_morphisms (pr1 Σ) f))) =
      pr1 (section_disp_on_morphisms (pr1 Σ') f))
    : Σ = Σ'.
  Proof.
    use section_disp_equality.
    - intros; use homset_property.
    - intro; use equality_on_objects.
    - intros; cbn.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      rewrite transportf_total2.
      rewrite transportf_total2.
      use equality_on_morphisms.
  Qed.

  (**
     2. Two examples of module signatures
   *)

  Definition trivial_signature_data : module_signature_data.
  Proof.
    use tpair; cbn.
    - intro; use trivial_module.
    - intros R R' [f H_f].
      exists f.
      abstract (
        unfold is_module_mor; cbn;
        rewrite assoc; use (pr1 H_f)
      ).
  Defined.

  Lemma trivial_signature_axioms 
    : module_signature_axioms trivial_signature_data.
  Proof.
    split; intros; 
    (use invmap; [|use path_sigma_hprop|]);
    now try use isaprop_is_module_mor.
  Qed.

  Definition trivial_signature : module_signature_cat
    := trivial_signature_data ,, trivial_signature_axioms.

  Lemma product_module_signature_lemma (Σ : module_signature_cat) (D : C)
    (R R' : MON C) (f : R --> R') (Σf := section_disp_on_morphisms (pr1 Σ) f)
    : is_module_mor _ _
        (pr2 (product_module _ _ _ _ (pr2 (Σ R))))
        (pullback_functor_funct _ (pr2 (product_module _ _ _ D (pr2 (Σ R')))) _ (pr2 f))
        (D ⊗l pr1 Σf).
  Proof.
    unfold is_module_mor; cbn; do 2 rewrite assoc.
    symmetry; etrans; etrans.
    - rewrite <- assoc; use maponpaths; [shelve|symmetry].
      use (bifunctor_leftcomp C).
    - do 2 (use maponpaths; [shelve|]); 
      use (!pr2 Σf).
    - rewrite (bifunctor_leftcomp C), assoc, (monoidal_associatornatleftright C), <- assoc.
      use maponpaths; [shelve|cbn].
      now rewrite (bifunctor_leftcomp C), assoc, (monoidal_associatornatleft C).
    - now do 2 rewrite assoc.
  Qed.

  Definition product_signature_data (Σ : module_signature_cat) (D : C) 
    : module_signature_data.
  Proof.
    use tpair; cbn.
    - intro R; use (product_module _ _ _ D (pr2 (Σ R))).
    - intros R R' f; pose (section_disp_on_morphisms (pr1 Σ) f) as Σf.
      exists (D ⊗l pr1 Σf); use product_module_signature_lemma.
  Defined.

  Lemma product_signature_axioms (Σ : module_signature_cat) (D : C) 
    : module_signature_axioms (product_signature_data Σ D).
  Proof.
    split.
    - intro R; use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      cbn; etrans.
      + do 2 (use maponpaths; [shelve|]); use (pr12 Σ R).
      + cbn; now rewrite tensor_mor_left, tensor_id_id.
    - intros R R' R'' f g; use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      cbn; etrans.
      + do 2 (use maponpaths; [shelve|]); use (pr22 Σ R).
      + use (bifunctor_leftcomp C).
  Qed.

  Definition product_signature (Σ : module_signature_cat) (D : C) 
    : module_signature_cat
    := product_signature_data Σ D,, product_signature_axioms Σ D.

  (**
     3. Evaluation functor (for some fixed monoid R)
   *)

  Context (R : MON C).
  Let MOD_R := MOD (pr1 R) (pr2 R).


  Definition signature_evaluation_data
    : functor_data module_signature_cat MOD_R.
  Proof.
    use make_functor_data.
    - intro Σ; exact (Σ R).
    - intros Σ Σ' [f _]; induction (f R) as [fR H]. 
      exists fR.
      abstract (
        cbn in fR, H |- *; 
        unfold is_module_mor, pullback_functor_funct in *;
        cbn in fR, H |- *;
        etrans; 
        [|use H];
        now rewrite assoc, tensor_mor_left, tensor_id_id, id_right
      ).
  Defined.

  Lemma signature_evaluation_is_functor
    : is_functor signature_evaluation_data.
  Proof.
    split.
    - intro Σ; use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      easy.
    - intros Σ Σ' Σ'' f g; use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      cbn; unfold Core.mor_disp; cbn.
      now rewrite transportf_total2, transportf_const.
  Qed.


  Definition signature_evaluation : module_signature_cat ⟶ MOD_R
    := make_functor signature_evaluation_data signature_evaluation_is_functor.
End ModuleSignatures.
