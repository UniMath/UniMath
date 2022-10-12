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
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

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

Definition make_kleisli_triple
           {C : category}
           (M : ob C → ob C)
           (η : ∏ (A : C), A --> M A)
           (bind : ∏ (A B : C), A --> M B → M A --> M B)
           (bind_unit : ∏ (A : C), bind A A (η A) = id₁ (M A))
           (unit_bind : ∏ (A B : C) (f : A --> M B), η A · bind A B f = f)
           (bind_bind : ∏ (A B C : C) (f : A --> M B) (g : B --> M C),
                        bind A B f · bind B C g = bind A C (f · bind B C g))
  : kleisli_triple C
  := (M,, η,, bind,, (bind_unit,, unit_bind,, bind_bind)).

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
  := ∑ (MF : ∏ (X : C), z_iso (MD (F X)) (F (MC X))),
     (∏ (A : C), #F (unit_kt MC A) = unit_kt MD (F A) · MF A)
     ×
     (∏ (A B : C) (f : A --> MC B),
      #F (bind_kt MC f) =
      inv_from_z_iso (MF A) · bind_kt MD (#F f · inv_from_z_iso (MF B)) · MF B).

Definition make_kleisli_triple_on_functor
           {C D : category}
           {MC : kleisli_triple C}
           {MD : kleisli_triple D}
           {F : C ⟶ D}
           (MF : ∏ (X : C), z_iso (MD (F X)) (F (MC X)))
           (MFunit : ∏ (A : C),
                     #F (unit_kt MC A) = unit_kt MD (F A) · MF A)
           (MFbind : ∏ (A B : C) (f : A --> MC B),
                     #F (bind_kt MC f)
                     =
                     inv_from_z_iso (MF A) · bind_kt MD (#F f · inv_from_z_iso (MF B)) · MF B)
  : kleisli_triple_on_functor MC MD F
  := (MF,, MFunit,, MFbind).

Section Projections.

Context {C D : category}
        {MC : kleisli_triple C}
        {MD : kleisli_triple D}
        {F : C ⟶ D}
        (MF : kleisli_triple_on_functor MC MD F).

Definition kleisli_triple_on_functor_z_iso
  : ∏ (X : C), z_iso (MD (F X)) (F (MC X))
  := pr1 MF.

Definition kleisli_triple_on_functor_unit_kt
  : ∏ (A : C),
    #F (unit_kt MC A)
    =
    unit_kt MD (F A) · kleisli_triple_on_functor_z_iso A
  := pr12 MF.

Definition kleisli_triple_on_functor_bind_kt
  : ∏ (A B : C) (f : A --> MC B),
    #F (bind_kt MC f)
    =
    inv_from_z_iso (kleisli_triple_on_functor_z_iso A)
                 · bind_kt MD (#F f · inv_from_z_iso (kleisli_triple_on_functor_z_iso B))
                 · kleisli_triple_on_functor_z_iso B
  := pr22 MF.

End Projections.

Definition kleisli_triple_on_identity_functor
           {C : category}
           (MC : kleisli_triple C)
  : kleisli_triple_on_functor MC MC (functor_identity C).
Proof.
  use tpair.
  - exact (λ X, identity_z_iso _).
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

Definition inv_from_z_iso_z_iso_comp
           {C : category}
           {x y z : C}
           (f : z_iso x y) (g : z_iso y z)
  : inv_from_z_iso (z_iso_comp f g) = inv_from_z_iso g · inv_from_z_iso f.
Proof.
  refine (!_).
  apply inv_z_iso_unique'.
  unfold precomp_with ; cbn.
  etrans.
  {
    rewrite <- !assoc.
    apply maponpaths.
    rewrite assoc.
    rewrite z_iso_inv_after_z_iso.
    apply id_left.
  }
  apply z_iso_inv_after_z_iso.
Qed.

Definition kleisli_triple_disp_cat_data
  : disp_cat_data bicat_of_univ_cats.
Proof.
  use tpair.
  - use tpair ; cbn.
    + exact kleisli_triple.
    + exact @kleisli_triple_on_functor.
  - split ; cbn.
    + exact @kleisli_triple_on_identity_functor.
    + intros C₁ C₂ C₃ F₁ F₂ M₁ M₂ M₃ MF₁ MF₂.
      use tpair.
      * exact (λ X, z_iso_comp (pr1 MF₂ (F₁ X)) (functor_on_z_iso F₂ (pr1 MF₁ X))).
      * split.
        ** abstract
             (intros A ; cbn;
              rewrite (pr12 MF₁);
              rewrite functor_comp;
              rewrite (pr12 MF₂);
              rewrite assoc;
              apply idpath).
        ** abstract
             (intros A B f ; simpl;
              rewrite (pr22 MF₁);
              rewrite !functor_comp;
              rewrite (pr22 MF₂);
              rewrite !functor_comp;
              rewrite (inv_from_z_iso_z_iso_comp (pr1 MF₂ (F₁ A)));
              rewrite (inv_from_z_iso_z_iso_comp (pr1 MF₂ (F₁ B)));
              rewrite <- !functor_on_inv_from_z_iso;
              rewrite !assoc;
              apply idpath).
Defined.

Definition kleisli_triple_nat_trans
           {C₁ C₂ : univalent_category}
           {F₁ F₂ : C₁ ⟶ C₂}
           (n : F₁ ⟹ F₂)
           {MC₁ : kleisli_triple C₁}
           {MC₂ : kleisli_triple C₂}
           (MF₁ : kleisli_triple_on_functor MC₁ MC₂ F₁)
           (MF₂ : kleisli_triple_on_functor MC₁ MC₂ F₂)
  : UU
  := ∏ (X : C₁),
     pr1 MF₁ X · n (MC₁ X)
     =
     #(functor_data_of_kleisli_triple MC₂) (n X) · pr1 MF₂ X.

Definition kleisli_triple_disp_prebicat_1_id_comp_cells
  : disp_prebicat_1_id_comp_cells bicat_of_univ_cats.
Proof.
  use tpair.
  - exact kleisli_triple_disp_cat_data.
  - exact @kleisli_triple_nat_trans.
Defined.

Definition kleisli_triple_disp_prebicat_ops
  : disp_prebicat_ops kleisli_triple_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split.
  - intros ; intro ; cbn.
    rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; intro ; cbn.
    rewrite ?functor_id, ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; intro ; cbn.
    rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; intro ; cbn.
    rewrite ?functor_id, ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; intro ; cbn.
    rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    apply idpath.
  - intros ; intro ; cbn.
    rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    rewrite functor_comp.
    rewrite assoc.
    apply idpath.
  - intros ; intro ; cbn.
    rewrite ?id_left, ?id_right.
    rewrite bind_unit, id_left.
    rewrite functor_comp.
    rewrite assoc.
    apply idpath.
  - intros C₁ C₂ F₁ F₂ F₃ n₁ n₂ MC₁ MC₂ MF₁ MF₂ MF₃ MN₁ MN₂ X ; cbn in *.
    rewrite !assoc.
    rewrite MN₁.
    rewrite <- !assoc.
    unfold functor_data_of_kleisli_triple ; cbn.
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
  - intros C₁ C₂ C₃ F G₁ G₂ n MC₁ MC₂ MC₃ MF MG₁ MG₂ Mn X ; cbn.
    rewrite <- !assoc.
    etrans.
    {
      apply maponpaths.
      apply (pr2 n _ _ (pr1 (pr1 MF X))).
    }
    rewrite !assoc.
    rewrite Mn.
    apply idpath.
  - intros C₁ C₂ C₃ F₁ F₂ G n MC₁ MC₂ MC₃ MF₁ MF₂ MG Mn X ; cbn.
    rewrite <- !assoc.
    rewrite <- functor_comp.
    rewrite Mn.
    rewrite functor_comp.
    rewrite !assoc.
    apply maponpaths_2.
    unfold functor_data_of_kleisli_triple ; cbn.
    rewrite (pr22 MG) ; cbn.
    rewrite !assoc.
    rewrite z_iso_inv_after_z_iso, id_left.
    apply maponpaths_2.
    rewrite functor_comp.
    rewrite (pr12 MG) ; cbn.
    rewrite <- !assoc.
    rewrite z_iso_inv_after_z_iso, id_right.
    apply idpath.
Qed.

Definition kleisli_triple_disp_prebicat_data: disp_prebicat_data bicat_of_univ_cats.
Proof.
  use tpair.
  - exact kleisli_triple_disp_prebicat_1_id_comp_cells.
  - exact kleisli_triple_disp_prebicat_ops.
Defined.

Definition disp_2cellsisaprop
           {a b : bicat_of_univ_cats}
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
  apply homset_property.
Qed.

Definition kleisli_triple_disp_laws
  : disp_prebicat_laws kleisli_triple_disp_prebicat_data.
Proof.
  repeat split ; intro ; intros ; apply disp_2cellsisaprop.
Qed.

Definition kleisli_triple_disp_prebicat : disp_prebicat bicat_of_univ_cats.
Proof.
  use tpair.
  - exact kleisli_triple_disp_prebicat_data.
  - exact kleisli_triple_disp_laws.
Defined.

Definition kleisli_triple_disp_bicat : disp_bicat bicat_of_univ_cats.
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

Definition disp_locally_groupoid_kleisli_help
           (a b : univalent_category)
           (f g : bicat_of_univ_cats ⟦ a , b ⟧)
           (x : invertible_2cell f g)
           (aa : kleisli_triple a)
           (bb : kleisli_triple b)
           (ff : kleisli_triple_on_functor aa bb f)
           (gg : kleisli_triple_on_functor aa bb g)
           (xx : kleisli_triple_nat_trans (pr1 x) ff gg)
           (X : a)
  : pr1 (pr1 gg X)
    =
    (bind_kt bb (pr1 (x ^-1) X · unit_kt bb (pr1 f X)))
      · pr1 ff X
      · (pr11 x (pr1 aa X)).
Proof.
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
    pose (pr2 (invertible_2cell_to_nat_z_iso _ _ (inv_of_invertible_2cell x)) X) as q'.
    pose (z_iso_inv_after_z_iso (_ ,, q')) as p.
    cbn in p.
    apply p.
  }
  rewrite id_left.
  rewrite bind_unit.
  rewrite id_left.
  apply idpath.
Qed.

Definition disp_locally_groupoid_kleisli
  : disp_locally_groupoid kleisli_triple_disp_bicat.
Proof.
  use make_disp_locally_groupoid.
  - intros a b f g x aa bb ff gg xx X.
    pose (pr2 (invertible_2cell_to_nat_z_iso
                 _ _
                 (inv_of_invertible_2cell x)) (pr1 aa X)) as q.
    apply (z_iso_inv_to_right _ _ _ _ (_ ,, q)).
    apply disp_locally_groupoid_kleisli_help.
    exact xx.
  - exact disp_2cells_isaprop_kleisli.
Qed.
