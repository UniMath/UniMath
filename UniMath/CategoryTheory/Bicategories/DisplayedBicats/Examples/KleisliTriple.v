(* ******************************************************************************* *)
(** Kleisli triples
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Definition kleisli_triple
           (C : category)
  : UU
  := ∑ (M : ob C → ob C)
       (η : ∏ (A : C), A --> M A)
       (bind : ∏ (A B : C), A --> M B → M A --> M B),
     (∏ (A : C), bind A A (η A) = id₁ (M A))
       × (∏ (A B : C) (f : A --> M B), η A · bind A B f = f)
       × ∏ (A B C : C) (f : A --> M B) (g : B --> M C),
     bind A B f · bind B C g = bind A C (f · bind B C g).

Definition object_map_kt
           {C : category}
           (M : kleisli_triple C)
  : ob C → ob C
  := pr1 M.

Coercion object_map_kt : kleisli_triple >-> Funclass.

Section Projections.
  Context {C : category}
          (M : kleisli_triple C).

  Definition unit_kt
    : ∏ (A : C), A --> M A
    := pr12 M.

  Definition bind_kt
    : ∏ {A B : C}, A --> M B → M A --> M B
    := pr122 M.

  Definition functor_data_of_kleisli_triple
    : functor_data C C.
  Proof.
    use make_functor_data.
    - exact (pr1 M).
    - exact (λ a b f, bind_kt (f · unit_kt b)).
  Defined.

  Definition bind_unit
    : ∏ (A : C), bind_kt (unit_kt A) = id₁ (M A)
    := pr1 (pr222 M).

  Definition unit_bind
    : ∏ {A B : C} (f : A --> M B), unit_kt A · bind_kt f = f
    := pr12 (pr222 M).

  Definition bind_bind
    : ∏ {A B C : C} (f : A --> M B) (g : B --> M C),
      bind_kt f · bind_kt g = bind_kt (f · bind_kt g)
    := pr22 (pr222 M).

  Definition functor_laws_of_kleisli_triple
    : is_functor functor_data_of_kleisli_triple.
  Proof.
    split.
    - intros X ; cbn.
      rewrite id_left, bind_unit.
      apply idpath.
    - intros X Y Z f g ; cbn.
      rewrite bind_bind.
      rewrite <- !assoc.
      rewrite unit_bind.
      apply idpath.
  Qed.

  Definition functor_of_kleisli_triple
    : functor C C.
  Proof.
    use make_functor.
    - exact functor_data_of_kleisli_triple.
    - exact functor_laws_of_kleisli_triple.
  Defined.
End Projections.

Definition kleisli_triple_on_functor
           {C D : category}
           (MC : kleisli_triple C)
           (MD : kleisli_triple D)
           (F : C ⟶ D)
  : UU
  := ∑ (MF : ∏ (X : C), iso (MD (F X)) (F (MC X))),
     (∏ (A : C), #F (unit_kt MC A) = unit_kt MD (F A) · MF A)
     ×
     (∏ (A B : C) (f : A --> MC B),
      #F (bind_kt MC f) =
      inv_from_iso (MF A) · bind_kt MD (#F f · inv_from_iso (MF B)) · MF B).

Definition kleisli_triple_on_identity_functor
           {C : category}
           (MC : kleisli_triple C)
  : kleisli_triple_on_functor MC MC (functor_identity C).
Proof.
  use tpair.
  - exact (λ X, identity_iso _).
  - split ; cbn.
    + abstract
        (intro ;
         rewrite id_right ;
         apply idpath).
    + abstract
        (intros ;
         rewrite !id_right, id_left ;
         apply idpath).
Defined.

Definition inv_from_iso_iso_comp
           {C : category}
           {x y z : C}
           (f : iso x y) (g : iso y z)
  : inv_from_iso (iso_comp f g) = inv_from_iso g · inv_from_iso f.
Proof.
  refine (!_).
  apply inv_iso_unique'.
  unfold precomp_with ; cbn.
  etrans.
  {
    rewrite <- !assoc.
    apply maponpaths.
    rewrite assoc.
    rewrite iso_inv_after_iso.
    apply id_left.
  }
  apply iso_inv_after_iso.
Qed.

Definition kleisli_triple_disp_cat_data
  : disp_cat_data bicat_of_cats.
Proof.
  use tpair.
  - use tpair ; cbn.
    + exact kleisli_triple.
    + exact @kleisli_triple_on_functor.
  - split ; cbn.
    + exact @kleisli_triple_on_identity_functor.
    + intros C₁ C₂ C₃ F₁ F₂ M₁ M₂ M₃ MF₁ MF₂.
      use tpair.
      * exact (λ X, iso_comp (pr1 MF₂ (F₁ X)) (functor_on_iso F₂ (pr1 MF₁ X))).
      * split.
        ** intros A ; cbn.
           rewrite (pr12 MF₁).
           rewrite functor_comp.
           rewrite (pr12 MF₂).
           rewrite assoc.
           apply idpath.
        ** intros A B f ; simpl.
           rewrite (pr22 MF₁).
           rewrite !functor_comp.
           rewrite (pr22 MF₂).
           rewrite !functor_comp.
           rewrite (inv_from_iso_iso_comp (pr1 MF₂ (F₁ A))).
           rewrite (inv_from_iso_iso_comp (pr1 MF₂ (F₁ B))).
           rewrite <- !functor_on_inv_from_iso.
           rewrite !assoc.
           apply idpath.
Defined.

Definition kleisli_triple_disp_prebicat_1_id_comp_cells
  : disp_prebicat_1_id_comp_cells bicat_of_cats.
Proof.
  use tpair.
  - exact kleisli_triple_disp_cat_data.
  - intros C₁ C₂ F₁ F₂ n MC₁ MC₂ MF₁ MF₂ ; cbn in *.
    exact (∏ (X : C₁),
           pr1 MF₁ X · n (MC₁ X)
           =
           #(functor_data_of_kleisli_triple MC₂) (n X) · pr1 MF₂ X).
Defined.

Definition kleisli_triple_disp_prebicat_ops
  : disp_prebicat_ops kleisli_triple_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split ; cbn.
  - intros ; rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; rewrite ?functor_id, ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; rewrite ?functor_id, ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    rewrite functor_comp.
    rewrite assoc.
    apply idpath.
  - intros ; rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    rewrite functor_comp.
    rewrite assoc.
    apply idpath.
  - intros C₁ C₂ F₁ F₂ F₃ n₁ n₂ MC₁ MC₂ MF₁ MF₂ MF₃ MN₁ MN₂ X ; cbn in *.
    rewrite !assoc.
    rewrite MN₁.
    rewrite <- !assoc.
    rewrite MN₂.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (bind_bind MC₂).
    }
    apply maponpaths_2.
    apply maponpaths.
    rewrite <- !assoc.
    apply maponpaths.
    apply (unit_bind MC₂).
  - intros C₁ C₂ C₃ F G₁ G₂ n MC₁ MC₂ MC₃ MF MG₁ MG₂ Mn X.
    rewrite <- !assoc.
    etrans.
    {
      apply maponpaths.
      apply (pr2 n _ _ (pr1 (pr1 MF X))).
    }
    rewrite !assoc.
    rewrite Mn.
    apply idpath.
  - intros C₁ C₂ C₃ F₁ F₂ G n MC₁ MC₂ MC₃ MF₁ MF₂ MG Mn X.
    rewrite <- !assoc.
    rewrite <- functor_comp.
    rewrite Mn.
    rewrite functor_comp.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite (pr22 MG) ; cbn.
    rewrite !assoc.
    rewrite iso_inv_after_iso, id_left.
    apply maponpaths_2.
    rewrite functor_comp.
    rewrite (pr12 MG) ; cbn.
    rewrite <- !assoc.
    rewrite iso_inv_after_iso, id_right.
    apply idpath.
Qed.

Definition kleisli_triple_disp_prebicat_data: disp_prebicat_data bicat_of_cats.
Proof.
  use tpair.
  - exact kleisli_triple_disp_prebicat_1_id_comp_cells.
  - exact kleisli_triple_disp_prebicat_ops.
Defined.

Definition disp_2cellsisaprop
           {a b : bicat_of_cats}
           {f g : a --> b}
           (η : f ==> g)
           {aa : kleisli_triple_disp_prebicat_data a}
           {bb : kleisli_triple_disp_prebicat_data b}
           (ff : aa -->[ f ] bb)
           (gg : aa -->[ g ] bb)
  : isaprop (disp_2cells η ff gg).
Proof.
  use impred.
  intro.
  apply (pr22 b).
Qed.

Definition kleisli_triple_disp_laws
  : disp_prebicat_laws kleisli_triple_disp_prebicat_data.
Proof.
  repeat split ; intro ; intros ; apply disp_2cellsisaprop.
Qed.

Definition kleisli_triple_disp_prebicat : disp_prebicat bicat_of_cats.
Proof.
  use tpair.
  - exact kleisli_triple_disp_prebicat_data.
  - exact kleisli_triple_disp_laws.
Defined.

Definition kleisli_triple_disp_bicat : disp_bicat bicat_of_cats.
Proof.
  use tpair.
  - exact kleisli_triple_disp_prebicat.
  - cbn ; unfold has_disp_cellset ; intros.
    apply isasetaprop.
    apply disp_2cellsisaprop.
Defined.

Definition kleisli_triple_bicat
  : bicat
  := total_bicat kleisli_triple_disp_bicat.

Definition disp_2cells_isaprop_kleisli
  : disp_2cells_isaprop kleisli_triple_disp_bicat.
Proof.
  exact @disp_2cellsisaprop.
Qed.

(* Improve Qed is slow *)
Definition disp_locally_groupoid_kleisli
  : disp_locally_groupoid kleisli_triple_disp_bicat.
Proof.
  use make_disp_locally_groupoid.
  - intros a b f g x aa bb ff gg xx X.
    pose (pr2 (invertible_2cell_to_nat_iso _ _ (inv_of_invertible_2cell x)) (pr1 aa X)) as q.
    apply (iso_inv_to_right _ _ _ _ _ (_ ,, q)).
    cbn.
    unfold precomp_with.
    rewrite id_right.
    rewrite assoc'.
    rewrite xx.
    rewrite assoc.
    refine (!(_ @ _)).
    { apply maponpaths_2. apply bind_bind. }
    rewrite assoc'.
    etrans.
    { apply maponpaths_2.
      do 2 apply maponpaths.
      apply (unit_bind bb).
    }
    rewrite assoc.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      pose (pr2 (invertible_2cell_to_nat_iso _ _ (inv_of_invertible_2cell x)) X) as q'.
      pose (iso_inv_after_iso (_ ,, q')) as p.
      cbn in p.
      unfold precomp_with in p.
      rewrite id_right in p.
      apply p.
    }
    rewrite id_left.
    rewrite bind_unit.
    rewrite id_left.
    apply idpath.
  - exact disp_2cells_isaprop_kleisli.
Qed.
