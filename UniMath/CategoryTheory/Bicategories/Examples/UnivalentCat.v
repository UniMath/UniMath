Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.OpCellBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Open Scope cat.

Definition data_cat_eq_1
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : UU
  := transportf (λ z, z → z → UU) Fo (@precategory_morphisms C)
     =
     @precategory_morphisms D.

Definition data_cat_eq_2
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : UU
  := ∏ (a b : ob C), C⟦a,b⟧ = D⟦eqweqmap Fo a,eqweqmap Fo b⟧.

Definition data_cat_eq_1_to_2
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : data_cat_eq_1 C D Fo ≃ data_cat_eq_2 C D Fo.
Proof.
  use weqfibtototal.
  intros p.
  induction p as [p₁ p₂].
  induction C as [CD CH].
  induction CD as [CO CM].
  induction D as [DD DH].
  induction DD as [DO DM].
  cbn in *.
  use weqfibtototal.
  Search ((∑ _ , _) ≃ ∑ _ , _).
  Search weq total2.
  use weqf.
  use tpair.
  - exact p₁.
  - induction p₁, p₂ ; cbn in *.
    reflexivity.
Defined.

Definition data_cat_eq_2_to_1
           (C D : precategory_data)
  : data_cat_eq_2 C D → data_cat_eq_1 C D.
Proof.
  intros p.
  induction p as [p₁ p₂].
  induction C as [CD CH].
  induction CD as [CO CM].
  induction D as [DD DH].
  induction DD as [DO DM].
  cbn in *.
  use tpair ; cbn.
  - exact p₁.
  - induction p₁ ; cbn in *.
    apply funextsec ; intro a.
    apply funextsec ; intro b.
    specialize (p₂ a b).
    induction p₂.
    reflexivity.
Defined.

Definition data_cat_eq_1_to_2_weq
           (C D : precategory_data)
  : data_cat_eq_1 C D ≃ data_cat_eq_2 C D.
Proof.
  refine (data_cat_eq_1_to_2 C D ,, _).
  use isweq_iso.
  - exact (data_cat_eq_2_to_1 C D).
  - intros p.
    induction p as [p₁ p₂].
    induction C as [CD CH].
    induction CD as [CO CM].
    induction D as [DD DH].
    induction DD as [DO DM].
    cbn in *.
    use total2_paths_b.
    + reflexivity.
    + induction p₁, p₂ ; cbn in *.
      admit.
  - intros p.
    induction p as [p₁ p₂].
    induction C as [CD CH].
    induction CD as [CO CM].
    induction D as [DD DH].
    induction DD as [DO DM].
    cbn in *.
    use total2_paths_b.
    + reflexivity.
    + induction p₁.
      apply funextsec ; intro a.
      apply funextsec ; intro b.
      induction (p₂ a b) ; cbn.


Definition cat_eq
           (C D : precategory_data)
  : UU
  := ∑ (F : data_cat_eq_2 C D),
       (∏ (a : C), eqweqmap (pr2 F a a) (identity a) = identity (eqweqmap (pr1 F) a))
     ×
       (∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧),
         eqweqmap (pr2 F a c) (f · g)
         =
         eqweqmap (pr2 F a b) f · eqweqmap (pr2 F b c) g).

Definition cat_equiv
           (C D : precategory_data)
  : UU
  := ∑ (F : ∑ (Fo : ob C ≃ D), ∏ (a b : ob C), C⟦a,b⟧ ≃ D⟦Fo a,Fo b⟧),
       (∏ (a : C), (pr2 F) a a (identity a) = identity (pr1 F a))
     ×
       (∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧), pr2 F a c (f · g) = pr2 F a b f · pr2 F b c g).

Definition eq_to_cat_eq
           (C D : precategory_data)
  : C = D → cat_eq C D.
Proof.
  intros p.
  pose (base_paths _ _ (base_paths _ _ p)).
  pose (fiber_paths (base_paths _ _ p)).
  cbn in p1.
  use total2_paths_equiv.
  Check (total2_paths_equiv _ C D p).
  exact p.
  pose (total2_paths_equiv _ _ _ (base_paths _ _ p)).
  unfold PathPair in p0.
  pose (total2_paths_equiv _ _ _ p).


Definition weq_cat_eq_cat_equiv
           (C D : precategory_data)
  : cat_eq C D ≃ cat_equiv C D.
Proof.
  use weqbandf.
  - use weqbandf.
    + apply univalence.
    + intros p.
      use weqonsecfibers.
      intros x.
      use weqonsecfibers.
      intros y.
      apply univalence.
  - intros q.
    use weqdirprodf.
    + apply idweq.
    + apply idweq.
Defined.

Definition cat_equiv_to_catiso
           (C D : precategory_data)
  : cat_equiv C D → catiso C D.
Proof.
  intros F.
  use tpair.
  - use tpair.
    + use tpair.
      * exact (pr1(pr1 F)).
      * exact (pr2(pr1 F)).
    + split.
      * exact (pr1(pr2 F)).
      * exact (pr2(pr2 F)).
  - split.
    + intros a b.
      apply (pr2(pr1 F)).
    + apply (pr1(pr1 F)).
Defined.

Definition catiso_to_cat_equiv
           (C D : precategory_data)
  : catiso C D → cat_equiv C D.
Proof.
  intros F.
  use tpair.
  - use tpair.
    + use weqpair.
      * exact (functor_on_objects F).
      * apply F.
    + intros a b.
      use weqpair.
      * exact (functor_on_morphisms F).
      * apply F.
  - split.
    + exact (functor_id F).
    + exact (@functor_comp _ _ F).
Defined.

Definition cat_equiv_to_catiso_weq
           (C D : category)
  : cat_equiv C D ≃ catiso C D.
Proof.
  refine (cat_equiv_to_catiso C D ,, _).
  use isweq_iso.
  - exact (catiso_to_cat_equiv C D).
  - reflexivity.
  - reflexivity.
Defined.



Definition path_cat_to_cat_eq
           (C D : precategory_data)
  : C = D → cat_eq C D.
Proof.
  intros p.
  pose (total2_paths_equiv _ _ _ (base_paths _ _ p)) as q.
  unfold PathPair in q.
  cbn in p1.
  cbn in p0.
  pose (C ╝ D).
  unfold PathPair in T.
  Locate "╝".
  red in T.
  cbn in T.
  induction p.
  refine (idpath _ ,, _).
  refine ((λ _ _, idpath _) ,, _).
  split ; reflexivity.
Defined.

Definition path_cat_to_cat_eq_inv
           (C D : precategory_data)
  : cat_eq C D → C = D.
Proof.
  intros p.
  induction p as [po p].
  induction p as [pm p].
  induction p as [pi pc].
  use total2_paths_b.
  - use total2_paths_b.
    + exact po.
    + apply funextsec.
      intro a.
      apply funextsec.
      intro b.
      cbn.
      induction (pm a b).
      cbn.

Definition univalent_cat : bicat
  := fullsubprebicat bicat_of_cats (λ C, is_univalent (pr1 C)).

Definition univalent_cat_is_univalent_2_0
  : is_univalent_2_0 univalent_cat.
Proof.
  intros C D.