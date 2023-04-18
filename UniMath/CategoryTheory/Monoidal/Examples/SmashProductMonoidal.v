(*****************************************************************

 Monoidal category from smash products

 We show that every notion of structure that supports a smash
 product, gives rise to a symmetric monoidal closed category. Note
 that in the construction, we give two (equivalent) definitions
 for both of the associators. One of the two definition is
 convenient for calculation, while the other is better for proving
 that it is a structure preserving map.

 Contents
 1. Tensor operation
 2. Unitors
 3. The braiding
 4. The associators
 5. The monoidal structure
 6. It is symmetric
 7. It is closed

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.

Section StructureSmashProduct.
  Context (P : hset_struct_with_smash_closed).

  Local Notation "∁" := (category_of_hset_struct P).

  (**
   1. Tensor operation
   *)
  Definition hset_struct_smash_prod_mor_r
             (PX : ∁)
             {PY₁ PY₂ : ∁}
             (f : PY₁ --> PY₂)
    : PX ∧* PY₁ --> PX ∧* PY₂.
  Proof.
    simple refine (_ ,, _).
    - use map_from_smash.
      + exact (λ x y, setquotpr _ (x ,, pr1 f y)).
      + abstract
          (intros y₁ y₂ ;
           use iscompsetquotpr ;
           apply hinhpr ; cbn ;
           use inr ;
           exact (inl (idpath _) ,, inl (idpath _))).
      + abstract
          (intros x y ;
           use iscompsetquotpr ;
           apply hinhpr ; cbn ;
           use inr ;
           refine (inr _ ,, inl (idpath _)) ;
           apply pointed_hset_struct_preserve_point ;
           exact (pr2 f)).
      + abstract
          (intros x₁ x₂ ;
           use iscompsetquotpr ;
           apply hinhpr ; cbn ;
           use inr ;
           refine (inr _ ,, inr _) ;
           apply (pointed_hset_struct_preserve_point _ (pr2 f))).
    - abstract
        (apply hset_struct_with_smash_map_from_smash ;
         refine (hset_struct_comp
                   P
                   _
                   (hset_struct_with_smash_setquotpr _ (pr2 PX) (pr2 PY₂))) ;
         use hset_struct_pair ;
         [ apply hset_struct_pr1
         | refine (hset_struct_comp P _ (pr2 f)) ;
           apply hset_struct_pr2 ]).
  Defined.

  Definition hset_struct_smash_prod_mor_l
             (PY : ∁)
             {PX₁ PX₂ : ∁}
             (f : PX₁ --> PX₂)
    : PX₁ ∧* PY --> PX₂ ∧* PY.
  Proof.
    simple refine (_ ,, _).
    - use map_from_smash.
      + exact (λ x y, setquotpr _ (pr1 f x ,, y)).
      + abstract
          (intros y₁ y₂ ;
           use iscompsetquotpr ;
           apply hinhpr ; cbn ;
           use inr ;
           refine (inl _ ,, inl _) ;
           apply (pointed_hset_struct_preserve_point _ (pr2 f))).
      + abstract
          (intros x y ;
           use iscompsetquotpr ;
           apply hinhpr ; cbn ;
           use inr ;
           refine (inr (idpath _) ,, inl _) ;
           apply pointed_hset_struct_preserve_point ;
           exact (pr2 f)).
      + abstract
          (intros x₁ x₂ ;
           use iscompsetquotpr ;
           apply hinhpr ; cbn ;
           use inr ;
           exact (inr (idpath _) ,, inr (idpath _))).
    - abstract
        (apply hset_struct_with_smash_map_from_smash ;
         refine (hset_struct_comp
                   P
                   _
                   (hset_struct_with_smash_setquotpr _ (pr2 PX₂) (pr2 PY))) ;
         use hset_struct_pair ;
         [ refine (hset_struct_comp P _ (pr2 f)) ;
           apply hset_struct_pr1
         | apply hset_struct_pr2 ]).
  Defined.

  Definition hset_struct_smash_prod_mor
             {PY₁ PY₂ : ∁}
             {PX₁ PX₂ : ∁}
             (f : PX₁ --> PX₂)
             (g : PY₁ --> PY₂)
    : PX₁ ∧* PY₁ --> PX₂ ∧* PY₂.
  Proof.
    simple refine (_ ,, _).
    - use map_from_smash.
      + exact (λ x y, setquotpr _ (pr1 f x ,, pr1 g y)).
      + abstract
          (intros y₁ y₂ ;
           use iscompsetquotpr ;
           apply hinhpr ; cbn ;
           use inr ;
           refine (inl _ ,, inl _) ;
           apply (pointed_hset_struct_preserve_point _ (pr2 f))).
      + abstract
          (intros x y ;
           use iscompsetquotpr ;
           apply hinhpr ; cbn ;
           use inr ;
           refine (inr _ ,, inl _) ;
           unfold product_point_coordinate ; cbn ;
           apply pointed_hset_struct_preserve_point ;
           [ exact (pr2 g)
           | exact (pr2 f) ]).
        + abstract
            (intros x y ;
             use iscompsetquotpr ;
             apply hinhpr ; cbn ;
             use inr ;
             refine (inr _ ,, inr _) ;
             unfold product_point_coordinate ; cbn ;
             apply pointed_hset_struct_preserve_point ;
             [ exact (pr2 g)
             | exact (pr2 g) ]).
    - abstract
        (apply hset_struct_with_smash_map_from_smash ;
         refine (hset_struct_comp
                   P
                   _
                   (hset_struct_with_smash_setquotpr _ (pr2 PX₂) (pr2 PY₂))) ;
         use hset_struct_pair ;
         [ refine (hset_struct_comp P _ (pr2 f)) ;
           apply hset_struct_pr1
         | refine (hset_struct_comp P _ (pr2 g)) ;
           apply hset_struct_pr2 ]).
  Defined.

  Local Notation "f '#∧*' g" := (hset_struct_smash_prod_mor f g) (at level 30).

  Definition smash_product_tensor_data
    : tensor_data ∁.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (λ X Y, X ∧* Y).
    - exact (λ X Y₁ Y₂ f, hset_struct_smash_prod_mor_r X f).
    - exact (λ Y X₁ X₂ f, hset_struct_smash_prod_mor_l Y f).
  Defined.

  (**
   2. Unitors
   *)
  Definition hset_struct_smash_prod_lunitor
    : leftunitor_data
        smash_product_tensor_data
        (hset_struct_with_smash_closed_unit P).
  Proof.
    intros X.
    simple refine (_ ,, _).
    - use map_from_smash.
      + exact (λ b x, if b then x else hset_struct_point P (pr2 X)).
      + abstract
          (intros x₁ x₂ ; cbn ;
           rewrite hset_struct_with_smash_point_unit ;
           apply idpath).
      + abstract
          (intros b x ; cbn ;
           rewrite hset_struct_with_smash_point_unit ;
           induction b ; apply idpath).
      + abstract
          (intros b₁ b₂ ; cbn ;
           induction b₁ ; induction b₂ ; cbn ;
           apply idpath).
    - apply hset_struct_with_smash_map_from_smash.
      use (hset_struct_with_smash_map_bool (pr122 P)).
      + apply hset_struct_pr1.
      + apply hset_struct_pr2.
  Defined.

  Definition hset_struct_smash_prod_linvunitor
    : leftunitorinv_data
        smash_product_tensor_data
        (hset_struct_with_smash_closed_unit P).
  Proof.
    intros X.
    simple refine (_ ,, _).
    - exact (λ x, setquotpr _ (true ,, x)).
    - apply hset_struct_with_smash_setquotpr_r.
  Defined.

  Definition hset_struct_smash_prod_runitor
    : rightunitor_data
        smash_product_tensor_data
        (hset_struct_with_smash_closed_unit P).
  Proof.
    intros X.
    simple refine (_ ,, _).
    - use map_from_smash.
      + exact (λ x b, if b then x else hset_struct_point P (pr2 X)).
      + abstract
          (intros b₁ b₂ ; cbn ;
           induction b₁ ; induction b₂ ; cbn ;
           apply idpath).
      + abstract
          (intros x b ; cbn ;
           rewrite hset_struct_with_smash_point_unit ;
           induction b ; apply idpath).
      + abstract
          (intros x₁ x₂ ; cbn ;
           rewrite hset_struct_with_smash_point_unit ;
           apply idpath).
    - apply hset_struct_with_smash_map_from_smash.
      use (hset_struct_with_smash_map_bool (pr122 P)).
      + apply hset_struct_pr2.
      + apply hset_struct_pr1.
  Defined.

  Definition hset_struct_smash_prod_rinvunitor
    : rightunitorinv_data
        smash_product_tensor_data
        (hset_struct_with_smash_closed_unit P).
  Proof.
    intros X.
    simple refine (_ ,, _).
    - exact (λ x, setquotpr _ (x ,, true)).
    - apply hset_struct_with_smash_setquotpr_l.
  Defined.

  (**
   3. The braiding
   *)
  Definition smash_product_monoidal_cat_braiding
             (X Y : category_of_hset_struct P)
    : X ∧* Y --> Y ∧* X.
  Proof.
    simple refine (_ ,, _).
    - use map_from_smash.
      + exact (λ x y, setquotpr _ (y ,, x)).
      + abstract
          (intros y₁ y₂ ;
           use iscompsetquotpr ;
           apply hinhpr ;
           use inr ;
           split ; use inr ; apply idpath).
      + abstract
          (intros x y ;
           use iscompsetquotpr ;
           apply hinhpr ;
           use inr ;
           split ; [ use inl | use inr  ] ;
           apply idpath).
      + abstract
          (intros x₁ x₂ ;
           use iscompsetquotpr ;
           apply hinhpr ;
           use inr ;
           split ; use inl ; apply idpath).
    - apply hset_struct_with_smash_map_from_smash.
      refine (hset_struct_comp
                P
                _
                (hset_struct_with_smash_setquotpr _ (pr2 Y) (pr2 X))).
      use hset_struct_pair.
      + apply hset_struct_pr2.
      + apply hset_struct_pr1.
  Defined.

  (**
   4. The associators
   *)

  (**
   Note: `hset_struct_smash_prod_lassociator_mor` is used to prove
   that the associator is structure preserving, whereas
   `hset_struct_smash_prod_lassociator_mor_alt_fun` is used for
   calculations.
   *)
  Definition hset_struct_smash_unlam
             {X Y Z : ∁}
             (f : X --> Y -->* Z)
    : X ∧* Y --> Z
    := f #∧* identity _ · hset_struct_with_smash_closed_eval Y Z.

  Definition hset_struct_smash_unlam'
             {X Y Z : ∁}
             (f : Y --> X -->* Z)
    : X ∧* Y --> Z
    := smash_product_monoidal_cat_braiding _ _ · hset_struct_smash_unlam f.

  Definition hset_struct_smash_prod_lassociator_mor
             (X Y Z : ∁)
    : (X ∧* Y) ∧* Z --> X ∧* (Y ∧* Z).
  Proof.
    use hset_struct_smash_unlam.
    use hset_struct_smash_unlam.
    refine (_ · hset_struct_smash_enriched_uncurry _ _ _).
    use hset_struct_smash_closed_uncurry.
    apply identity.
  Defined.

  Definition hset_struct_smash_prod_lassociator_mor_alt_fun
             {X Y Z : ∁}
             (xy : pr11 (X ∧* Y))
             (z : pr11 Z)
    : pr11 (X ∧* Y ∧* Z).
  Proof.
    revert xy.
    use map_from_smash'.
    - apply setproperty.
    - exact (λ x y, setquotpr _ (x ,, setquotpr _ (y ,, z))).
    - abstract
        (intros y₁ y₂ ;
         use iscompsetquotpr ;
         apply hinhpr ;
         use inr ;
         unfold product_point_coordinate ; cbn ;
         split ; use inl ; apply idpath).
    - abstract
        (intros x y ;
         use iscompsetquotpr ;
         apply hinhpr ;
         use inr ;
         unfold product_point_coordinate ;
         split ; [ | use inl ; apply idpath ] ;
         use inr ;
         refine (_ @ !(hset_struct_with_smash_closed_point_smash _ _)) ;
         use iscompsetquotpr ; cbn ;
         apply hinhpr ;
         use inr ;
         unfold product_point_coordinate ; cbn ;
         split ; use inl ; apply idpath).
    - abstract
        (intros x₁ x₂ ;
         use iscompsetquotpr ;
         apply hinhpr ;
         use inr ;
         unfold product_point_coordinate ; split ; cbn ; use inr ;
         refine (_ @ !(hset_struct_with_smash_closed_point_smash _ _)) ;
         use iscompsetquotpr ; cbn ;
         apply hinhpr ; use inr ;
         unfold product_point_coordinate ; split ; cbn ;
         use inl ;
         apply idpath).
  Defined.

  Proposition hset_struct_smash_prod_lassociator_mor_alt_eq1
              {X Y Z : category_of_hset_struct P}
              (z₁ z₂ : pr11 Z)
    : hset_struct_smash_prod_lassociator_mor_alt_fun
        (hset_struct_point (pr12 P) (pr2 (X ∧* Y)))
        z₁
      =
      hset_struct_smash_prod_lassociator_mor_alt_fun
        (hset_struct_point (pr12 P) (pr2 (X ∧* Y)))
        z₂.
  Proof.
    etrans.
    {
      apply maponpaths_2.
      apply hset_struct_with_smash_closed_point_smash.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply hset_struct_with_smash_closed_point_smash.
    }
    use iscompsetquotpr.
    apply hinhpr.
    use inr ; cbn.
    unfold product_point_coordinate ; cbn.
    split.
    - use inl.
      apply idpath.
    - use inl.
      apply idpath.
  Qed.

  Proposition hset_struct_smash_prod_lassociator_mor_alt_eq2
              {X Y Z : category_of_hset_struct P}
              (xy : pr11 (X ∧* Y))
              (z : pr11 Z)
    : hset_struct_smash_prod_lassociator_mor_alt_fun
        xy
        (hset_struct_point (pr12 P) (pr2 Z))
      =
      hset_struct_smash_prod_lassociator_mor_alt_fun
        (hset_struct_point (pr12 P) (pr2 (X ∧* Y)))
        z.
  Proof.
    revert xy.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros xy.
    induction xy as [ x y ].
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply hset_struct_with_smash_closed_point_smash.
    }
    use iscompsetquotpr.
    apply hinhpr ; cbn.
    use inr.
    unfold product_point_coordinate ; cbn.
    split.
    - use inl.
      apply idpath.
    - use inr.
      refine (_ @ !(hset_struct_with_smash_closed_point_smash _ _)).
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inr.
      unfold product_point_coordinate ; cbn.
      split.
      + use inr.
        apply idpath.
      + use inr.
        apply idpath.
  Qed.

  Proposition hset_struct_smash_prod_lassociator_mor_alt_eq3
              {X Y Z : category_of_hset_struct P}
              (xy₁ xy₂ : pr11 (X ∧* Y))
    : hset_struct_smash_prod_lassociator_mor_alt_fun
        xy₁
        (hset_struct_point (pr12 P) (pr2 Z))
      =
      hset_struct_smash_prod_lassociator_mor_alt_fun
        xy₂
        (hset_struct_point (pr12 P) (pr2 Z)).
  Proof.
    revert xy₁.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros xy₁.
    induction xy₁ as [ x₁ y₁ ].
    revert xy₂.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros xy₂.
    induction xy₂ as [ x₂ y₂ ].
    use iscompsetquotpr.
    apply hinhpr ; cbn.
    use inr.
    unfold product_point_coordinate ; cbn.
    split ; use inr ;
      refine (_ @ !(hset_struct_with_smash_closed_point_smash _ _)).
    - use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inr.
      unfold product_point_coordinate ; cbn.
      split.
      + use inr.
        apply idpath.
      + use inr.
        apply idpath.
    - use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inr.
      unfold product_point_coordinate ; cbn.
      split.
      + use inr.
        apply idpath.
      + use inr.
        apply idpath.
  Qed.

  Definition hset_struct_smash_prod_lassociator_mor_alt
             (X Y Z : ∁)
    : pr11 ((X ∧* Y) ∧* Z) → pr11 (X ∧* (Y ∧* Z)).
  Proof.
    use map_from_smash'.
    - apply setproperty.
    - exact hset_struct_smash_prod_lassociator_mor_alt_fun.
    - exact hset_struct_smash_prod_lassociator_mor_alt_eq1.
    - exact hset_struct_smash_prod_lassociator_mor_alt_eq2.
    - exact hset_struct_smash_prod_lassociator_mor_alt_eq3.
  Defined.

  Definition hset_struct_smash_prod_lassociator_mor_eq_to_alt
             (X Y Z : ∁)
    : pr1 (hset_struct_smash_prod_lassociator_mor X Y Z)
      =
      hset_struct_smash_prod_lassociator_mor_alt X Y Z.
  Proof.
    use funextsec.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros xyz.
    induction xyz as [ xy z ].
    revert xy.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros xy.
    induction xy as [ x y ].
    use iscompsetquotpr ; cbn.
    apply hinhpr.
    use inl.
    apply idpath.
  Qed.

  Definition hset_struct_smash_prod_lassociator
    : associator_data
        smash_product_tensor_data.
  Proof.
    intros X Y Z.
    refine (hset_struct_smash_prod_lassociator_mor_alt X Y Z ,, _).
    abstract
      (exact (transportf
                (mor_hset_struct P _ _)
                (hset_struct_smash_prod_lassociator_mor_eq_to_alt X Y Z)
                (pr2 (hset_struct_smash_prod_lassociator_mor X Y Z)))).
  Defined.

  (**
   Note: `hset_struct_smash_prod_rassociator_mor` is used to prove
   that the associator is structure preserving, whereas
   `hset_struct_smash_prod_rassociator_mor_alt_fun` is used for
   calculations.
   *)
  Definition hset_struct_smash_prod_rassociator_mor
             (X Y Z : ∁)
    : X ∧* (Y ∧* Z) --> (X ∧* Y) ∧* Z.
  Proof.
    use hset_struct_smash_unlam'.
    use hset_struct_smash_unlam'.
    refine (_ · hset_struct_smash_enriched_uncurry _ _ _).
    use hset_struct_smash_closed_uncurry.
    refine (smash_product_monoidal_cat_braiding _ _ · _ #∧* identity _).
    apply smash_product_monoidal_cat_braiding.
  Defined.

  Definition hset_struct_smash_prod_rassociator_mor_alt_fun
             {X Y Z : ∁}
             (x : pr11 X)
             (yz : pr11 (Y ∧* Z))
    : pr11 ((X ∧* Y) ∧* Z).
  Proof.
    revert yz.
    use map_from_smash'.
    - apply setproperty.
    - exact (λ y z, setquotpr _ (setquotpr _ (x ,, y) ,, z)).
    - abstract
        (intros z₁ z₂ ;
         use iscompsetquotpr ;
         apply hinhpr ; cbn ;
         use inr ;
         unfold product_point_coordinate ;
         split ; use inl ; cbn ;
         refine (_ @ !(hset_struct_with_smash_closed_point_smash _ _)) ;
         use iscompsetquotpr ;
         apply hinhpr ; cbn ;
         use inr ;
         unfold product_point_coordinate ;
         split ;
         use inr ;
         apply idpath).
    - abstract
        (intros y z ;
         use iscompsetquotpr ;
         apply hinhpr ; cbn ;
         use inr ;
         unfold product_point_coordinate ;
         split ; cbn ; [ use inr ; apply idpath | ] ;
         use inl ;
         refine (_ @ !(hset_struct_with_smash_closed_point_smash _ _)) ;
         use iscompsetquotpr ;
         apply hinhpr ; cbn ;
         use inr ;
         unfold product_point_coordinate ;
         split ;
         use inr ;
         apply idpath).
    - abstract
        (intros y₁ y₂ ;
         use iscompsetquotpr ;
         apply hinhpr ; cbn ;
         use inr ;
         unfold product_point_coordinate ;
         split ; cbn ;
         use inr ;
         apply idpath).
  Defined.

  Proposition hset_struct_smash_prod_rassociator_mor_alt_eq1
              {X Y Z : ∁}
              (yz₁ yz₂ : pr11 (Y ∧* Z))
    : hset_struct_smash_prod_rassociator_mor_alt_fun
        (hset_struct_point (pr12 P) (pr2 X))
        yz₁
      =
      hset_struct_smash_prod_rassociator_mor_alt_fun
        (hset_struct_point (pr12 P) (pr2 X))
        yz₂.
  Proof.
    revert yz₁.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros yz₁.
    induction yz₁ as [ y₁ z₁ ].
    revert yz₂.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros yz₂.
    induction yz₂ as [ y₂ z₂ ].
    use iscompsetquotpr.
    apply hinhpr ; cbn.
    use inr.
    unfold product_point_coordinate ; cbn.
    split ; use inl ;
      refine (_ @ !(hset_struct_with_smash_closed_point_smash _ _)).
    - use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inr.
      unfold product_point_coordinate ; cbn.
      split.
      + use inl.
        apply idpath.
      + use inr.
        apply idpath.
    - use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inr.
      unfold product_point_coordinate ; cbn.
      split.
      + use inl.
        apply idpath.
      + use inr.
        apply idpath.
  Qed.

  Proposition hset_struct_smash_prod_rassociator_mor_alt_eq2
              {X Y Z : ∁}
              (x : pr11 X)
              (yz : pr11 (Y ∧* Z))
    : hset_struct_smash_prod_rassociator_mor_alt_fun
        x
        (hset_struct_point (pr12 P) (pr2 (Y ∧* Z)))
      =
      hset_struct_smash_prod_rassociator_mor_alt_fun
        (hset_struct_point (pr12 P) (pr2 X))
        yz.
  Proof.
    revert yz.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros yz.
    induction yz as [ y z ].
    etrans.
    {
      apply maponpaths.
      apply hset_struct_with_smash_closed_point_smash.
    }
    use iscompsetquotpr.
    apply hinhpr ; cbn.
    use inr.
    unfold product_point_coordinate ; cbn.
    split.
    - use inr.
      apply idpath.
    - use inl.
      refine (_ @ !(hset_struct_with_smash_closed_point_smash _ _)).
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inr.
      unfold product_point_coordinate ; cbn.
      split.
      + use inl.
        apply idpath.
      + use inl.
        apply idpath.
  Qed.

  Proposition hset_struct_smash_prod_rassociator_mor_alt_eq3
              {X Y Z : ∁}
              (x₁ x₂ : pr11 X)
    : hset_struct_smash_prod_rassociator_mor_alt_fun
        x₁
        (hset_struct_point (pr12 P) (pr2 (Y ∧* Z)))
      =
      hset_struct_smash_prod_rassociator_mor_alt_fun
        x₂
        (hset_struct_point (pr12 P) (pr2 (Y ∧* Z))).
  Proof.
    etrans.
    {
      apply maponpaths.
      apply hset_struct_with_smash_closed_point_smash.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply hset_struct_with_smash_closed_point_smash.
    }
    use iscompsetquotpr.
    apply hinhpr ; cbn.
    use inr.
    unfold product_point_coordinate ; cbn.
    split.
    - use inr.
      apply idpath.
    - use inr.
      apply idpath.
  Qed.

  Definition hset_struct_smash_prod_rassociator_mor_alt
             (X Y Z : ∁)
    : pr11 (X ∧* (Y ∧* Z)) → pr11 ((X ∧* Y) ∧* Z).
  Proof.
    use map_from_smash'.
    - apply setproperty.
    - exact hset_struct_smash_prod_rassociator_mor_alt_fun.
    - exact hset_struct_smash_prod_rassociator_mor_alt_eq1.
    - exact hset_struct_smash_prod_rassociator_mor_alt_eq2.
    - exact hset_struct_smash_prod_rassociator_mor_alt_eq3.
  Defined.

  Definition hset_struct_smash_prod_rassociator_mor_eq_to_alt
             (X Y Z : ∁)
    : pr1 (hset_struct_smash_prod_rassociator_mor X Y Z)
      =
      hset_struct_smash_prod_rassociator_mor_alt X Y Z.
  Proof.
    use funextsec.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros xyz.
    induction xyz as [ x yz ].
    revert yz.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intros yz.
    induction yz as [ y z ].
    use iscompsetquotpr ; cbn.
    apply hinhpr.
    use inl.
    apply idpath.
  Qed.

  Definition hset_struct_smash_prod_rassociator
    : associatorinv_data
        smash_product_tensor_data.
  Proof.
    intros X Y Z.
    refine (hset_struct_smash_prod_rassociator_mor_alt X Y Z ,, _).
    abstract
      (exact (transportf
                (mor_hset_struct P _ _)
                (hset_struct_smash_prod_rassociator_mor_eq_to_alt X Y Z)
                (pr2 (hset_struct_smash_prod_rassociator_mor X Y Z)))).
  Defined.

  (**
   5. The monoidal structure
   *)
  Definition smash_product_monoidal_data
    : monoidal_data (category_of_hset_struct P).
  Proof.
    use make_monoidal_data.
    - exact smash_product_tensor_data.
    - exact (hset_struct_with_smash_closed_unit P).
    - exact hset_struct_smash_prod_lunitor.
    - exact hset_struct_smash_prod_linvunitor.
    - exact hset_struct_smash_prod_runitor.
    - exact hset_struct_smash_prod_rinvunitor.
    - exact hset_struct_smash_prod_lassociator.
    - exact hset_struct_smash_prod_rassociator.
  Defined.

  Proposition smash_product_monoidal_laws
    : monoidal_laws smash_product_monoidal_data.
  Proof.
    repeat split.
    - intros X Y.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros x.
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inl.
      apply idpath.
    - intros X Y.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros x.
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inl.
      apply idpath.
    - intros W X Y Z g₁ g₂.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros x.
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inl.
      apply idpath.
    - intros W X Y Z f₁ f₂.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros x.
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inl.
      apply idpath.
    - intros X₁ X₂ Y₁ Y₂ f g.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros x.
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inl.
      apply idpath.
    - intros X Y f.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros x.
      induction x as [ b x ].
      cbn in *.
      induction b.
      + apply idpath.
      + refine (!_).
        apply pointed_hset_struct_preserve_point.
        exact (pr2 f).
    - use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro z.
      induction z as [ b z ].
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      induction b ; cbn.
      + use inl.
        apply idpath.
      + use inr.
        split ; unfold product_point_coordinate ; cbn.
        * use inr.
          apply idpath.
        * use inl.
          rewrite hset_struct_with_smash_point_unit.
          apply idpath.
    - use eq_mor_hset_struct.
      intro z ; cbn.
      apply idpath.
    - intros X Y f.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros x.
      induction x as [ x b ].
      cbn in *.
      induction b.
      + apply idpath.
      + refine (!_).
        apply pointed_hset_struct_preserve_point.
        exact (pr2 f).
    - use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro z.
      induction z as [ z b ].
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      induction b ; cbn.
      + use inl.
        apply idpath.
      + use inr.
        split ; unfold product_point_coordinate ; cbn.
        * use inl.
          apply idpath.
        * use inr.
          rewrite hset_struct_with_smash_point_unit.
          apply idpath.
    - use eq_mor_hset_struct.
      intro z ; cbn.
      apply idpath.
    - intros X Y Z₁ Z₂ h.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro z.
      induction z as [ xx y ].
      revert xx.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro xx.
      induction xx as [ x₁ x₂ ].
      use iscompsetquotpr ; cbn.
      apply hinhpr.
      use inl.
      apply idpath.
    - intros X₁ X₂ Y Z f.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro z.
      induction z as [ xx y ].
      revert xx.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro xx.
      induction xx as [ x₁ x₂ ].
      use iscompsetquotpr ; cbn.
      apply hinhpr.
      use inl.
      apply idpath.
    - intros X Y₁ Y₂ Z g.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro z.
      induction z as [ xx y ].
      revert xx.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro xx.
      induction xx as [ x₁ x₂ ].
      use iscompsetquotpr ; cbn.
      apply hinhpr.
      use inl.
      apply idpath.
    - use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro xyz.
      induction xyz as [ xy z' ].
      revert xy.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro xy.
      induction xy as [ x' y' ].
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inl.
      apply idpath.
    - use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro xyz.
      induction xyz as [ x' yz ].
      revert yz.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intro yz.
      induction yz as [ y' z' ].
      use iscompsetquotpr.
      apply hinhpr ; cbn.
      use inl.
      apply idpath.
    - intros X Y.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros xby.
      induction xby as [ xb y ].
      revert xb.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros xb.
      induction xb as [ x b ].
      use iscompsetquotpr ; cbn.
      apply hinhpr.
      induction b.
      + exact (inl (idpath _)).
      + use inr.
        unfold product_point_coordinate ; cbn.
        split.
        * exact (inr (idpath _)).
        * exact (inl (idpath _)).
    - intros W X Y Z.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros wxyz.
      induction wxyz as [ wxy z ].
      revert wxy.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros wxy.
      induction wxy as [ wx y ].
      revert wx.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros wx.
      induction wx as [ w x ].
      use iscompsetquotpr ; cbn.
      apply hinhpr.
      use inl.
      apply idpath.
  Qed.

  Definition smash_product_monoidal_cat
    : monoidal_cat
    := category_of_hset_struct P
       ,,
       smash_product_monoidal_data
       ,,
       smash_product_monoidal_laws.

  (**
   6. It is symmetric
   *)
  Proposition smash_product_monoidal_cat_symmetric_laws
    : sym_mon_cat_laws_tensored
        smash_product_monoidal_cat
        smash_product_monoidal_cat_braiding.
  Proof.
    repeat split.
    - intros X Y.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros xy.
      induction xy as [ x y ].
      use iscompsetquotpr ; cbn.
      apply hinhpr.
      exact (inl (idpath _)).
    - intros X₁ X₂ Y₁ Y₂ f g.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros xy.
      induction xy as [ x y ].
      use iscompsetquotpr ; cbn.
      apply hinhpr.
      exact (inl (idpath _)).
    - intros X Y Z.
      use eq_mor_hset_struct.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros xyz.
      induction xyz as [ xy z ].
      revert xy.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros xy.
      induction xy as [ x y ].
      use iscompsetquotpr ; cbn.
      apply hinhpr.
      exact (inl (idpath _)).
  Qed.

  Definition smash_product_monoidal_cat_symmetric
    : symmetric smash_product_monoidal_cat.
  Proof.
    use make_symmetric.
    - exact smash_product_monoidal_cat_braiding.
    - exact smash_product_monoidal_cat_symmetric_laws.
  Defined.

  Definition smash_product_sym_monoidal_cat
    : sym_monoidal_cat
    := smash_product_monoidal_cat
       ,,
       smash_product_monoidal_cat_symmetric.

  (**
   7. It is closed
   *)
  Definition smash_product_sym_mon_closed_cat
    : sym_mon_closed_cat.
  Proof.
    use make_sym_mon_closed_cat.
    - exact smash_product_sym_monoidal_cat.
    - exact (λ X Y, X -->* Y).
    - exact (λ PX PY, hset_struct_with_smash_closed_eval PX PY).
    - exact (λ X Y Z f, hset_struct_smash_closed_uncurry f).
    - abstract
        (intros X Y Z f ;
         use eq_mor_hset_struct ;
         use setquotunivprop' ; [ intro ; apply setproperty | ] ;
         intros zx ;
         induction zx as [ z x ] ;
         cbn ;
         apply idpath).
    - abstract
        (intros X Y Z f ;
         use eq_mor_hset_struct ;
         intros z ;
         use eq_mor_hset_struct ;
         intros x ;
         cbn ;
         apply idpath).
  Defined.
End StructureSmashProduct.
