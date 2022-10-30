Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Local Open Scope cat.

Local Definition pair_with_object_left_data {C : category} (I : C)
  : functor_data C (C ⊠ C).
Proof.
  exists (λ x, (I,x)).
  exact (λ x y f, (identity I #, f)).
Defined.

Local Definition pair_with_object_left_is_functor {C : category} (I : C)
  : is_functor (pair_with_object_left_data I).
Proof.
  split ; intro ; intros ; simpl.
  - apply idpath.
  - etrans.
    2: { apply binprod_comp. }
    apply maponpaths_2.
    apply (! id_right _).
Qed.

Local Definition pair_with_object_left {C : category} (I : C)
  : functor C (C ⊠ C)
  := pair_with_object_left_data I ,, pair_with_object_left_is_functor I.

Local Definition tensor_after_pair_with_object_left
      {C : category} (T : functor (C ⊠ C) C) (I : C)
  : nat_z_iso (I_pretensor T I)
              (functor_composite (pair_with_object_left I) T).
Proof.
  use make_nat_z_iso.
  - exists (λ _, identity _).
    abstract (intro ; intros ; exact (id_right _ @ ! id_left _)).
  - intro x.
    exists (identity _).
    abstract (split ; apply id_right).
Defined.

Local Definition pair_with_object_right_data {C : category} (I : C)
  : functor_data C (C ⊠ C).
Proof.
  exists (λ x, (x,I)).
  exact (λ x y f, (f #, identity I)).
Defined.

Local Definition pair_with_object_right_is_functor {C : category} (I : C)
  : is_functor (pair_with_object_right_data I).
Proof.
  split ; intro ; intros ; simpl.
  - apply idpath.
  - etrans.
    2: { apply binprod_comp. }
    apply maponpaths.
    apply (! id_right _).
Qed.

Local Definition pair_with_object_right {C : category} (I : C)
  : functor C (C ⊠ C)
  := pair_with_object_right_data I ,, pair_with_object_right_is_functor I.

Local Lemma PairingWithObjectCommutesLeft
      {C D : category} (H : functor C D) (I : C)
  :  nat_z_iso (H ∙ pair_with_object_left (H I)) (pair_with_object_left I ∙ (pair_functor H H)).
Proof.
  use make_nat_z_iso.
  - exists (λ _, identity (H I, H _)).
    abstract (
        intro ; intros ;
        refine (id_right  (id (H I) #, # H f) @ _) ;
        refine (_ @ ! id_left  (# H (id I) #, # H f)) ;
        apply maponpaths_2 ;
        apply (! functor_id H _)).
  - intro.
    exists (identity _).
    abstract (split ; apply (id_right (id (H I, H _)))).
Defined.

Local Lemma PairingWithObjectCommutesRight
      {C D : category} (H : functor C D) (I : C)
  : nat_z_iso (H ∙ pair_with_object_right (H I)) (pair_with_object_right I ∙ (pair_functor H H)).
Proof.
  use make_nat_z_iso.
  - exists (λ _, identity (H _, H I)).
    abstract (
        intro ; intros ;
        refine (id_right  (# H f #, id (H I)) @ _) ;
        refine (_ @ ! id_left  (# H f #, # H (id I))) ;
        apply maponpaths ;
        apply (! functor_id H _)).
  - intro.
    exists (identity _).
    abstract (split ; apply (id_right (id (H _, H I)))).
Defined.

Local Definition tensor_after_pair_with_object_right
      {C : category} (T : functor (C ⊠ C) C) (I : C)
  : nat_z_iso (I_posttensor T I)
              (functor_composite (pair_with_object_right I) T).
Proof.
  use make_nat_z_iso.
  - exists (λ _, identity _).
    abstract (intro ; intros ; exact (id_right _ @ ! id_left _)).
  - intro x.
    exists (identity _).
    abstract (split ; apply id_right).
Defined.

Local Lemma pre_whisker_nat_z_iso
      {C D E : category} (F : functor C D)
      {G1 G2 : functor D E} (α : nat_z_iso G1 G2)
  : nat_z_iso (functor_composite F G1) (functor_composite F G2).
Proof.
  exists (pre_whisker F α).
  exact (pre_whisker_on_nat_z_iso F α (pr2 α)).
Defined.

Local Lemma post_whisker_nat_z_iso
      {C D E : category}
      {G1 G2 : functor C D} (α : nat_z_iso G1 G2) (F : functor D E)
  : nat_z_iso (functor_composite G1 F) (functor_composite G2 F).
Proof.
  exists (post_whisker α F).
  exact (post_whisker_z_iso_is_z_iso α F (pr2 α)).
Defined.

Local Lemma nat_z_iso_functor_comp_assoc
      {C1 C2 C3 C4 : category}
      (F1 : functor C1 C2)
      (F2 : functor C2 C3)
      (F3 : functor C3 C4)
  : nat_z_iso (F1 ∙ (F2 ∙ F3)) ((F1 ∙ F2) ∙ F3).
Proof.
  use make_nat_z_iso.
  - exists (λ _, identity _).
    abstract (intro ; intros ; exact (id_right _ @ ! id_left _)).
  - intro.
    exists (identity _).
    abstract (split ; apply id_right).
Defined.

Local Definition product_of_commuting_squares
           {C1 C2 C3 C4 : category}
           {D1 D2 D3 D4 : category}
           {F1 : functor C1 C2} {F2 : functor C2 C4}
           {F1' : functor C1 C3} {F2' : functor C3 C4}
           {G1 : functor D1 D2} {G2 : functor D2 D4}
           {G1' : functor D1 D3} {G2' : functor D3 D4}
           (α : nat_z_iso (F1  ∙ F2) (F1'  ∙ F2'))
           (β : nat_z_iso (G1  ∙ G2) (G1'  ∙ G2'))
  : nat_z_iso (pair_functor F1 G1  ∙ pair_functor F2 G2)
              (pair_functor F1' G1'  ∙ pair_functor F2' G2').
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + intro.
      use catbinprodmor.
      * apply α.
      * apply β.
    + abstract
        (intro ; intros ; use total2_paths_f ;
         [ apply (pr21 α) |
           rewrite transportf_const ;
           apply (pr21 β)
        ]).
  - intro.
    use is_z_iso_binprod_z_iso.
    + apply (pr2 α (pr1 _)).
    + apply (pr2 β (pr2 _)).
Defined.

Local Lemma functor_commutes_with_id
      {C D : category} (F : functor C D)
  : nat_z_iso (F ∙ functor_identity D) (functor_identity C ∙ F).
Proof.
  use make_nat_z_iso.
  - exists (λ _, identity _).
    abstract (intro ; intros ; exact (id_right _ @ ! id_left _)).
  - intro.
    exists (identity _).
    abstract (split ; apply id_right).
Defined.
