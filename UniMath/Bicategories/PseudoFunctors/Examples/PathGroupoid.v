(**
Bequivalence between 1-types and univalent groupoids
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictIdentitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictCompositor.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.

Local Open Scope cat.

Definition one_type_to_groupoid
           (X : one_type)
  : univalent_groupoid
  := path_univalent_groupoid (pr2 X).

(** Action on morphisms *)
Definition function_to_functor_data
           {X Y : one_type}
           (f : X → Y)
  : functor_data (one_type_to_groupoid X) (one_type_to_groupoid Y).
Proof.
  use make_functor_data.
  - exact f.
  - exact (λ _ _ p, maponpaths f p).
Defined.

Definition function_to_functor_laws
           {X Y : one_type}
           (f : X → Y)
  : is_functor (function_to_functor_data f).
Proof.
  split.
  - intros x ; cbn.
    apply idpath.
  - intros x y z p q ; cbn.
    apply maponpathscomp0.
Qed.

Definition function_to_functor
           {X Y : one_type}
           (f : X → Y)
  : one_type_to_groupoid X ⟶ one_type_to_groupoid Y.
Proof.
  use make_functor.
  - exact (function_to_functor_data f).
  - exact (function_to_functor_laws f).
Defined.

(** Action on cells *)
Definition path_to_nattrans
           {X Y : one_type}
           {f g : X → Y}
           (p : homotsec f g)
  : function_to_functor f ⟹ function_to_functor g.
Proof.
  use make_nat_trans.
  - exact p.
  - abstract
      (intros x y q ; cbn in * ;
       induction q ; simpl ;
       refine (!_) ;
       apply pathscomp0rid).
Defined.

(** Identitor *)
Definition path_groupoid_identitor
           (X : one_type)
  : functor_identity _ ⟹ function_to_functor (λ (x : X), x).
Proof.
  use make_nat_trans.
  - exact idpath.
  - abstract
      (intros x y p ; cbn in * ;
       induction p ; cbn ;
       apply idpath).
Defined.

(** Compositor *)
Definition path_groupoid_compositor
           {X Y Z : one_type}
           (f : X → Y)
           (g : Y → Z)
  : (function_to_functor f ∙ function_to_functor g)
      ⟹
      function_to_functor (λ x, g(f x)).
Proof.
  use make_nat_trans.
  - exact (λ x, idpath (g(f x))).
  - abstract
      (intros x y p ; cbn in * ;
       induction p ; cbn ;
       apply idpath).
Defined.

(** Data of path groupoid pseudofunctor *)
Definition path_groupoid_data
  : psfunctor_data one_types grpds.
Proof.
  use make_psfunctor_data.
  - exact one_type_to_groupoid.
  - exact (λ _ _ f, function_to_functor f ,, tt).
  - exact (λ _ _ _ _ p, path_to_nattrans p ,, tt).
  - exact (λ X, path_groupoid_identitor X ,, tt).
  - exact (λ _ _ _ f g, path_groupoid_compositor f g ,, tt).
Defined.

(** Laws *)
Definition path_groupoid_laws
  : psfunctor_laws path_groupoid_data.
Proof.
  repeat split.
  - intros X Y f.
    use subtypePath.
    { intro ; apply isapropunit. }
    apply nat_trans_eq.
    { apply homset_property. }
    intro x ; cbn.
    apply idpath.
  - intros X Y f g h p q.
    use subtypePath.
    { intro ; apply isapropunit. }
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    apply idpath.
  - intros X Y f.
    use subtypePath.
    { intro ; apply isapropunit. }
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    apply idpath.
  - intros X Y f.
    use subtypePath.
    { intro ; apply isapropunit. }
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    apply idpath.
  - intros W X Y Z f g h.
    use subtypePath.
    { intro ; apply isapropunit. }
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    apply idpath.
  - intros X Y Z f g₁ g₂ p.
    use subtypePath.
    { intro ; apply isapropunit. }
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    cbn.
    refine (!_).
    apply pathscomp0rid.
  - intros X Y Z f₁ f₂ g p.
    use subtypePath.
    { intro ; apply isapropunit. }
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    cbn.
    refine (!_).
    apply pathscomp0rid.
Qed.

(** The identitor and compositor are invertible *)
Definition path_groupoid_invertible_cells
  : invertible_cells path_groupoid_data.
Proof.
  split ; intros ; apply locally_groupoid_grpds.
Defined.

(** The pseudofunctor *)
Definition path_groupoid
  : psfunctor one_types grpds.
Proof.
  use make_psfunctor.
  - exact path_groupoid_data.
  - exact path_groupoid_laws.
  - exact path_groupoid_invertible_cells.
Defined.

(** The adjoint *)
Definition objects_of_grpd_data
  : psfunctor_data grpds one_types.
Proof.
  use make_psfunctor_data.
  - refine (λ G, make_one_type _ (univalent_category_has_groupoid_ob _)).
    apply G.
  - exact (λ _ _ F x, (pr1 F : _ ⟶ _) x).
  - intros G₁ G₂ F₁ F₂ α ; simpl.
    intro x.
    apply isotoid.
    { apply (pr1 G₂). }
    use make_iso.
    + exact ((pr1 α : _ ⟹ _) x).
    + exact (pr2 G₂ _ _ ((pr1 α : _ ⟹ _) x)).
  - exact (λ _ _, idpath _).
  - exact (λ _ _ _ _ _ _, idpath _).
Defined.

Definition objects_of_grpd_is_psfunctor
  : psfunctor_laws objects_of_grpd_data.
Proof.
  repeat split.
  - intros G₁ G₂ F ; cbn.
    use funextsec.
    intro x.
    refine (_ @ isotoid_identity_iso _ _ _).
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros G₁ G₂ F₁ F₂ F₃ α₁ α₂ ; cbn.
    use funextsec.
    intro x ; unfold homotcomp.
    rewrite <- isotoid_comp.
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros G₁ G₂ F ; cbn.
    use funextsec.
    intro x ; unfold homotcomp, homotfun ; cbn.
    refine (!_).
    refine (_ @ isotoid_identity_iso _ _ _).
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros G₁ G₂ F ; cbn.
    use funextsec.
    intro x ; unfold homotcomp, homotfun ; cbn.
    refine (!_).
    refine (_ @ isotoid_identity_iso _ _ _).
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros G₁ G₂ G₃ G₄ F₁ F₂ F₃ ; cbn.
    use funextsec.
    intro x ; unfold homotcomp, homotfun ; cbn.
    refine (_ @ isotoid_identity_iso _ _ _).
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α ; cbn.
    use funextsec.
    intro x ; unfold homotcomp, homotfun, funhomotsec ; cbn.
    rewrite pathscomp0rid.
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α ; cbn.
    use funextsec.
    intro x ; unfold homotcomp, homotfun, funhomotsec ; cbn.
    rewrite pathscomp0rid.
    refine (!_).
    etrans.
    {
      apply maponpaths_isotoid.
    }
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
Qed.

Definition objects_of_grpd
  : psfunctor grpds one_types.
Proof.
  use make_psfunctor.
  - exact objects_of_grpd_data.
  - exact objects_of_grpd_is_psfunctor.
  - split ; intros ; apply one_type_2cell_iso.
Defined.

(** The biadjunction *)
Definition path_groupoid_unit_data
  : pstrans_data
      (id_psfunctor one_types)
      (comp_psfunctor objects_of_grpd path_groupoid).
Proof.
  use make_pstrans_data.
  - exact (λ _ x, x).
  - exact (λ _ _ _, id2_invertible_2cell _).
Defined.

Lemma eq_isotoid
      {C : univalent_category}
      {X Y : C}
      (f : iso X Y) (p : X = Y)
  : f = idtoiso p → isotoid C (pr2 C) f = p.
Proof.
  intro H.
  rewrite H.
  apply isotoid_idtoiso.
Qed.

Definition path_groupoid_inv_is_pstrans
  : is_pstrans path_groupoid_unit_data.
Proof.
  repeat split.
  - intros X Y f g p.
    use funextsec ; intro x.
    refine (pathscomp0rid _ @ _ @ !(maponpathsidfun _)).
    cbn ; unfold funhomotsec.
    apply (@eq_isotoid (path_univalent_groupoid _)).
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    cbn.
    induction (p x).
    apply idpath.
  - intros X ; cbn.
    use funextsec ; intro x.
    unfold homotcomp, funhomotsec, homotfun, homotrefl ; cbn.
    rewrite pathscomp0rid ; cbn in *.
    apply (@eq_isotoid (path_univalent_groupoid _)).
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    cbn.
    apply idpath.
  - intros X Y Z f g ; cbn.
    use funextsec ; intro x.
    unfold homotcomp, funhomotsec, homotfun, homotrefl ; cbn.
    rewrite pathscomp0rid ; cbn in *.
    apply (@eq_isotoid (path_univalent_groupoid _)).
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    cbn.
    apply idpath.
Qed.

Definition path_groupoid_unit
  : pstrans
      (id_psfunctor one_types)
      (comp_psfunctor objects_of_grpd path_groupoid).
Proof.
  use make_pstrans.
  - exact path_groupoid_unit_data.
  - exact path_groupoid_inv_is_pstrans.
Defined.

Definition path_groupoid_counit_data_functor_data
           (G : univalent_groupoid)
  : functor_data (path_groupoid (objects_of_grpd G) : univalent_groupoid) G.
Proof.
  use make_functor_data.
  - exact (λ x, x).
  - exact (λ _ _ p, idtoiso p).
Defined.

Definition path_groupoid_counit_data_functor_is_functor
           (G : univalent_groupoid)
  : is_functor (path_groupoid_counit_data_functor_data G).
Proof.
  split.
  - intros x ; apply idpath.
  - intros x y z f g ; cbn.
    exact (maponpaths pr1 (idtoiso_concat _ _ _ _ f g)).
Qed.

Definition path_groupoid_counit_data_functor
           (G : univalent_groupoid)
  : (path_groupoid (objects_of_grpd G) : univalent_groupoid) ⟶ G.
Proof.
  use make_functor.
  - exact (path_groupoid_counit_data_functor_data G).
  - exact (path_groupoid_counit_data_functor_is_functor G).
Defined.

Definition path_groupoid_counit_data_nat_trans_data
           (G₁ G₂ : grpds)
           (F : G₁ --> G₂)
  : nat_trans_data
      (path_groupoid_counit_data_functor G₁ ∙ pr1 F)
      ((function_to_functor (# objects_of_grpd F))
         ∙ path_groupoid_counit_data_functor G₂)
  := λ _, id₁ _.

Definition path_groupoid_counit_data_nat_trans_is_nat_trans
           (G₁ G₂ : grpds)
           (F : G₁ --> G₂)
  : is_nat_trans _ _ (path_groupoid_counit_data_nat_trans_data G₁ G₂ F).
Proof.
  intros x y f ; cbn.
  rewrite id_left, id_right.
  refine (!_).
  exact (maponpaths pr1 (maponpaths_idtoiso _ _ _ _ _ _)).
Qed.

Definition path_groupoid_counit_data_nat_trans
           (G₁ G₂ : grpds)
           (F : G₁ --> G₂)
  : (path_groupoid_counit_data_functor G₁ ∙ pr1 F)
      ⟹
      function_to_functor (#objects_of_grpd F)
      ∙ path_groupoid_counit_data_functor G₂.
Proof.
  use make_nat_trans.
  - exact (path_groupoid_counit_data_nat_trans_data G₁ G₂ F).
  - exact (path_groupoid_counit_data_nat_trans_is_nat_trans G₁ G₂ F).
Defined.

Definition path_groupoid_counit_data
  : pstrans_data
      (comp_psfunctor path_groupoid objects_of_grpd)
      (id_psfunctor grpds).
Proof.
  use make_pstrans_data.
  - exact (λ G, path_groupoid_counit_data_functor G ,, tt).
  - intros G₁ G₂ F.
    use make_invertible_2cell.
    + exact (path_groupoid_counit_data_nat_trans G₁ G₂ F ,, tt).
    + apply locally_groupoid_grpds.
Defined.

Definition path_groupoid_counit_is_pstrans
  : is_pstrans path_groupoid_counit_data.
Proof.
  repeat split.
  - intros G₁ G₂ F₁ F₂ α.
    use subtypePath.
    { intro ; apply isapropunit. }
    use nat_trans_eq.
    { apply homset_property. }
    intro x ; cbn.
    rewrite id_left, id_right.
    rewrite idtoiso_isotoid.
    apply idpath.
  - intros G.
    use subtypePath.
    { intro ; apply isapropunit. }
    use nat_trans_eq.
    { apply homset_property. }
    intro x ; cbn.
    rewrite id_left, !id_right.
    apply idpath.
  - intros G₁ G₂ G₃ F₁ F₂.
    use subtypePath.
    { intro ; apply isapropunit. }
    use nat_trans_eq.
    { apply homset_property. }
    intro x ; cbn.
    rewrite !id_left, !id_right.
    rewrite (functor_id (pr1 F₂)).
    apply idpath.
Qed.

Definition path_groupoid_counit
  : pstrans
      (comp_psfunctor path_groupoid objects_of_grpd)
      (id_psfunctor grpds).
Proof.
  use make_pstrans.
  - exact path_groupoid_counit_data.
  - exact path_groupoid_counit_is_pstrans.
Defined.

Definition path_groupoid_biadj_unit_counit
  : left_biadj_unit_counit path_groupoid.
Proof.
  use make_biadj_unit_counit.
  - exact objects_of_grpd.
  - exact path_groupoid_unit.
  - exact path_groupoid_counit.
Defined.

Definition path_groupoid_biadj_triangle_l_data
  : invertible_modification_data
      (biadj_triangle_l_lhs path_groupoid_biadj_unit_counit)
      (id_pstrans path_groupoid).
Proof.
  intros X.
  use make_invertible_2cell.
  - refine (_ ,, tt).
    use make_nat_trans.
    + exact idpath.
    + abstract
        (intros x y p ; cbn in * ;
         induction p ; simpl ;
         apply idpath).
  - apply locally_groupoid_grpds.
Defined.

Definition path_groupoid_biadj_triangle_l_is_modification
  : is_modification path_groupoid_biadj_triangle_l_data.
Proof.
  intros X Y f.
  use subtypePath.
  { intro ; apply isapropunit. }
  use nat_trans_eq.
  { apply homset_property. }
  intro x.
  apply idpath.
Qed.

Definition path_groupoid_biadj_triangle_l
  : biadj_triangle_l_law path_groupoid_biadj_unit_counit.
Proof.
  use make_invertible_modification.
  - exact path_groupoid_biadj_triangle_l_data.
  - exact path_groupoid_biadj_triangle_l_is_modification.
Defined.

Definition path_groupoid_biadj_triangle_r_data
  : invertible_modification_data
      (biadj_triangle_r_lhs path_groupoid_biadj_unit_counit)
      (id_pstrans path_groupoid_biadj_unit_counit).
Proof.
  intro G.
  use make_invertible_2cell.
  - exact idpath.
  - apply one_type_2cell_iso.
Defined.

Definition path_groupoid_biadj_triangle_r_is_modification
  : is_modification path_groupoid_biadj_triangle_r_data.
Proof.
  intros G₁ G₂ F.
  use funextsec.
  intro x.
  repeat (refine (pathscomp0rid _ @ _)).
  refine (maponpathsidfun _ @ _).
  refine (pathscomp0rid _ @ _).
  cbn ; unfold path_groupoid_counit_data_nat_trans_data.
  use eq_isotoid.
  use subtypePath.
  { intro ; apply isaprop_is_iso. }
  apply idpath.
Qed.

Definition path_groupoid_biadj_triangle_r
  : biadj_triangle_r_law path_groupoid_biadj_unit_counit.
Proof.
  use make_invertible_modification.
  - exact path_groupoid_biadj_triangle_r_data.
  - exact path_groupoid_biadj_triangle_r_is_modification.
Defined.

Definition path_groupoid_biadj_data
  : left_biadj_data path_groupoid.
Proof.
  use make_biadj_data.
  - exact path_groupoid_biadj_unit_counit.
  - exact path_groupoid_biadj_triangle_l.
  - exact path_groupoid_biadj_triangle_r.
Defined.

(** Inverse of unit *)
Definition path_groupoid_unit_inv_data
  : pstrans_data
      (comp_psfunctor objects_of_grpd path_groupoid)
      (id_psfunctor one_types).
Proof.
  use make_pstrans_data.
  - exact (λ _ x, x).
  - exact (λ _ _ _, id2_invertible_2cell _).
Defined.

Definition path_groupoid_unit_inv_is_pstrans
  : is_pstrans path_groupoid_unit_inv_data.
Proof.
  repeat split.
  - intros X Y f g p.
    use funextsec ; intro x.
    refine (pathscomp0rid _ @ _ @ !(maponpathsidfun _)).
    cbn ; unfold funhomotsec.
    refine (!_).
    apply (@eq_isotoid (path_univalent_groupoid _)).
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    cbn.
    induction (p x).
    apply idpath.
  - intros X ; cbn.
    use funextsec ; intro x.
    unfold homotcomp, funhomotsec, homotfun, homotrefl ; cbn.
    refine (!_).
    rewrite maponpathsidfun.
    apply (@eq_isotoid (path_univalent_groupoid _)).
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros X Y Z f g ; cbn.
    use funextsec ; intro x.
    unfold homotcomp, funhomotsec, homotfun, homotrefl ; cbn.
    refine (!_).
    rewrite maponpathsidfun.
    apply (@eq_isotoid (path_univalent_groupoid _)).
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
Qed.

Definition path_groupoid_unit_inv
  : pstrans
      (comp_psfunctor objects_of_grpd path_groupoid)
      (id_psfunctor one_types).
Proof.
  use make_pstrans.
  - exact path_groupoid_unit_inv_data.
  - exact path_groupoid_unit_inv_is_pstrans.
Defined.

Definition path_groupoid_unit_unit_inv
  : invertible_modification
      (comp_pstrans path_groupoid_unit path_groupoid_unit_inv)
      (id_pstrans _).
Proof.
  use make_invertible_modification.
  - intro.
    apply id2_invertible_2cell.
  - abstract
      (intros X Y f ;
       use funextsec ;
       intro ;
       apply idpath).
Defined.

Definition path_groupoid_unit_inv_unit
  : invertible_modification
      (comp_pstrans path_groupoid_unit_inv path_groupoid_unit)
      (id_pstrans _).
Proof.
  use make_invertible_modification.
  - intro.
    apply id2_invertible_2cell.
  - abstract
      (intros X Y f ;
       use funextsec ;
       intro x ;
       apply idpath).
Defined.

(** Inverse of counit *)
Definition path_groupoid_counit_inv_data_functor_data
           (G : univalent_groupoid)
  : functor_data G (path_groupoid (objects_of_grpd G) : univalent_groupoid).
Proof.
  use make_functor_data.
  - exact (λ x, x).
  - exact (λ _ _ p, isotoid G (pr21 G) (p ,, pr2 G _ _ p)).
Defined.

Definition path_groupoid_counit_inv_data_functor_is_functor
           (G : univalent_groupoid)
  : is_functor (path_groupoid_counit_inv_data_functor_data G).
Proof.
  split.
  - intro x ; cbn.
    apply eq_isotoid.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros x y z f g ; cbn.
    apply eq_isotoid.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    rewrite idtoiso_concat.
    rewrite !idtoiso_isotoid.
    apply idpath.
Qed.

Definition path_groupoid_counit_inv_data_functor
           (G : univalent_groupoid)
  : G ⟶ (path_groupoid (objects_of_grpd G) : univalent_groupoid).
Proof.
  use make_functor.
  - exact (path_groupoid_counit_inv_data_functor_data G).
  - exact (path_groupoid_counit_inv_data_functor_is_functor G).
Defined.

Definition path_groupoid_counit_inv_data_nat_trans_data
           (G₁ G₂ : grpds)
           (F : G₁ --> G₂)
  : nat_trans_data
      ((path_groupoid_counit_inv_data_functor G₁)
         ∙ function_to_functor (# objects_of_grpd F))
      (pr1 F ∙ path_groupoid_counit_inv_data_functor G₂)
  := λ _, id₁ _.

Definition path_groupoid_counit_inv_data_nat_trans_is_nat_trans
           (G₁ G₂ : grpds)
           (F : G₁ --> G₂)
  : is_nat_trans _ _ (path_groupoid_counit_inv_data_nat_trans_data G₁ G₂ F).
Proof.
  intros x y f ; cbn.
  rewrite pathscomp0rid.
  rewrite (maponpaths_isotoid _ _ (pr1 F) _ (pr21 G₂)).
  apply maponpaths.
  apply subtypePath.
  { intro ; apply isaprop_is_iso. }
  apply idpath.
Qed.

Definition path_groupoid_counit_inv_data_nat_trans
           (G₁ G₂ : grpds)
           (F : G₁ --> G₂)
  : ((path_groupoid_counit_inv_data_functor G₁)
       ∙ function_to_functor (#objects_of_grpd F))
      ⟹
      (pr1 F∙ path_groupoid_counit_inv_data_functor G₂).
Proof.
  use make_nat_trans.
  - exact (path_groupoid_counit_inv_data_nat_trans_data G₁ G₂ F).
  - exact (path_groupoid_counit_inv_data_nat_trans_is_nat_trans G₁ G₂ F).
Defined.

Definition path_groupoid_counit_inv_data
  : pstrans_data
      (id_psfunctor grpds)
      (comp_psfunctor path_groupoid objects_of_grpd).
Proof.
  use make_pstrans_data.
  - exact (λ G, path_groupoid_counit_inv_data_functor G ,, tt).
  - intros G₁ G₂ F.
    use make_invertible_2cell.
    + exact (path_groupoid_counit_inv_data_nat_trans G₁ G₂ F ,, tt).
    + apply locally_groupoid_grpds.
Defined.

Definition path_groupoid_counit_inv_is_pstrans
  : is_pstrans path_groupoid_counit_inv_data.
Proof.
  repeat split.
  - intros G₁ G₂ F₁ F₂ α.
    use subtypePath.
    { intro ; apply isapropunit. }
    use nat_trans_eq.
    { apply homset_property. }
    intro x ; cbn.
    rewrite pathscomp0rid.
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros G.
    use subtypePath.
    { intro ; apply isapropunit. }
    use nat_trans_eq.
    { apply homset_property. }
    intro x ; cbn.
    refine (!_).
    apply eq_isotoid.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
  - intros G₁ G₂ G₃ F₁ F₂.
    use subtypePath.
    { intro ; apply isapropunit. }
    use nat_trans_eq.
    { apply homset_property. }
    intro x ; cbn.
    refine (!_).
    apply eq_isotoid.
    use subtypePath.
    { intro ; apply isaprop_is_iso. }
    apply idpath.
Qed.

Definition path_groupoid_counit_inv
  : pstrans
      (id_psfunctor grpds)
      (comp_psfunctor path_groupoid objects_of_grpd).
Proof.
  use make_pstrans.
  - exact path_groupoid_counit_inv_data.
  - exact path_groupoid_counit_inv_is_pstrans.
Defined.

Definition path_groupoid_counit_counit_inv
  : invertible_modification
      (comp_pstrans path_groupoid_counit path_groupoid_counit_inv)
      (id_pstrans _).
Proof.
  use make_invertible_modification.
  - intro.
    use make_invertible_2cell.
    + refine (_ ,, tt).
      use make_nat_trans.
      * exact idpath.
      * abstract
          (intros x y p ; cbn ;
           rewrite pathscomp0rid ;
           apply eq_isotoid ;
           use subtypePath ; try (intro ; apply isaprop_is_iso) ;
           apply idpath).
    + apply locally_groupoid_grpds.
  - abstract
      (intros G₁ G₂ F ;
       use subtypePath ; try (intro ; apply isapropunit) ;
       use nat_trans_eq ; try (apply homset_property) ;
       intro ; cbn ;
       rewrite !pathscomp0rid ;
       apply eq_isotoid ;
       use subtypePath ; try (intro ; apply isaprop_is_iso) ;
       apply idpath).
Defined.

Definition path_groupoid_counit_inv_counit
  : invertible_modification
      (comp_pstrans path_groupoid_counit_inv path_groupoid_counit)
      (id_pstrans _).
Proof.
  use make_invertible_modification.
  - intro.
    use make_invertible_2cell.
    + refine (_ ,, tt).
      use make_nat_trans.
      * exact identity.
      * abstract
          (intros x y p ; cbn ;
           rewrite id_right, id_left, idtoiso_isotoid ;
           apply idpath).
    + apply locally_groupoid_grpds.
  - abstract
      (intros G₁ G₂ F ;
       use subtypePath ; try (intro ; apply isapropunit) ;
       use nat_trans_eq ; try (apply homset_property) ;
       intro ; cbn ;
       rewrite !id_left, id_right ;
       rewrite (functor_id (pr1 F)) ;
       apply idpath).
Defined.

Definition is_biequiv_path_groupoid : is_biequivalence path_groupoid.
Proof.
  use make_is_biequivalence.
  - exact objects_of_grpd.
  - exact path_groupoid_unit.
  - exact path_groupoid_unit_inv.
  - exact path_groupoid_counit.
  - exact path_groupoid_counit_inv.
  - exact (inv_of_invertible_2cell path_groupoid_unit_inv_unit).
  - exact path_groupoid_unit_unit_inv.
  - exact (inv_of_invertible_2cell path_groupoid_counit_counit_inv).
  - exact path_groupoid_counit_inv_counit.
Defined.

Definition biequiv_path_groupoid : biequivalence one_types grpds
  := path_groupoid ,, is_biequiv_path_groupoid.
