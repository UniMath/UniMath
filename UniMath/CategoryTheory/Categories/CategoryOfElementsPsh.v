(**

 The category of elements

 Every presheaf gives rise to a category of elements. If we have a presheaf `F` on `C`,
 then the objects of the category of elements `∫ F` are pairs of objects `c : C` with
 an elements `x : F c`.

 Note: the category of elements for a presheaf is also constructed in ElementsOp.v. The
 main difference is that in this file we use displayed categories. In addition, morphisms
 in this category come with an equality, and we direct this equality differently.

 Contents
 1. The category of elements of a presheaf
 2. Equality of morphisms in the category of elements
 3. Natural transformations between presheaves induce functors

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.

Local Open Scope cat.

Section CategoryOfElementsPsh.
  Context {C : category}
          (F : C^op ⟶ HSET).

  (** * 1. The category of elements of a presheaf *)
  Definition disp_cat_of_elems_ob_mor
    : disp_cat_ob_mor C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ c, (F c : hSet)).
    - exact (λ c₁ c₂ x y f, #F f y = x).
  Defined.

  Definition disp_cat_of_elems_id_comp
    : disp_cat_id_comp C disp_cat_of_elems_ob_mor.
  Proof.
    split.
    - exact (λ c x, eqtohomot (functor_id F c) x).
    - refine (λ c₁ c₂ c₃ f g x₁ x₂ x₃ p q, _) ; cbn in *.
      refine (eqtohomot (functor_comp F g f) x₃ @ _) ; cbn.
      exact (maponpaths (# F f) q @ p).
  Qed.

  Definition disp_cat_of_elems_data
    : disp_cat_data C.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_elems_ob_mor.
    - exact disp_cat_of_elems_id_comp.
  Defined.

  Definition disp_mor_elems_isaprop
             {c₁ c₂ : C}
             (f : c₁ --> c₂)
             (x₁ : disp_cat_of_elems_data c₁)
             (x₂ : disp_cat_of_elems_data c₂)
    : isaprop (x₁ -->[ f ] x₂).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    cbn in *.
    apply (F c₁).
  Qed.

  Definition disp_cat_of_elems_axioms
    : disp_cat_axioms C disp_cat_of_elems_data.
  Proof.
    repeat split ; intros ; cbn.
    - apply disp_mor_elems_isaprop.
    - apply disp_mor_elems_isaprop.
    - apply disp_mor_elems_isaprop.
    - apply isasetaprop.
      apply disp_mor_elems_isaprop.
  Qed.

  Definition disp_cat_of_elems
    : disp_cat C.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_elems_data.
    - exact disp_cat_of_elems_axioms.
  Defined.

  Definition cat_of_elems_psh
    : category
    := total_category disp_cat_of_elems.
End CategoryOfElementsPsh.

Notation "'∫'" := (cat_of_elems_psh) : cat.

(** * 2. Equality of morphisms in the category of elements *)
Definition cat_of_elems_psh_eq_mor
           {C : category}
           {F : C^op ⟶ HSET}
           {x y : ∫ F}
           {f g : x --> y}
           (p : pr1 f = pr1 g)
  : f = g.
Proof.
  use subtypePath.
  {
    intro.
    apply setproperty.
  }
  exact p.
Qed.

(** * 3. Natural transformations between presheaves induce functors *)
Definition cat_of_elems_psh_nat_trans_data
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ SET}
           (τ : Γ₁ ⟹ Γ₂)
  : functor_data (∫ Γ₁) (∫ Γ₂).
Proof.
  use make_functor_data.
  - exact (λ x, pr1 x ,, τ (pr1 x) (pr2 x)).
  - refine (λ x y f, pr1 f ,, _).
    abstract
      (refine (!(eqtohomot (nat_trans_ax τ _ _ (pr1 f)) _) @ _) ;
       cbn ;
       apply maponpaths ;
       apply (pr2 f)).
Defined.

Definition cat_of_elems_psh_nat_trans
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ SET}
           (τ : Γ₁ ⟹ Γ₂)
  : ∫ Γ₁ ⟶ ∫ Γ₂.
Proof.
  use make_functor.
  - exact (cat_of_elems_psh_nat_trans_data τ).
  - abstract
      (split ; intro ; intros ; use cat_of_elems_psh_eq_mor ; apply idpath).
Defined.
