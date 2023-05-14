(*****************************************************************

 Pointed set structures

 We define the category of pointed sets as a category of
 structured sets. In addition, we construct the smash product.

 Contents
 1. Structures of pointed sets
 2. Limits and colimits of pointed sets
 3. Pointed sets form a pointed structure
 4. The smash product

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.

Local Open Scope cat.

(**
 1. Structures of pointed sets
 *)
Definition struct_pointed_hset_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, X).
  - exact (λ X Y x y f, f x = y).
Defined.

Definition struct_pointed_hset_laws
  : hset_struct_laws struct_pointed_hset_data.
Proof.
  repeat split.
  - intro X.
    apply setproperty.
  - intros X Y px py f.
    apply setproperty.
  - intros X Y Z px py pz f g p q ; cbn in *.
    rewrite p, q.
    apply idpath.
  - intros X px px' p q ; cbn in *.
    exact p.
Qed.

Definition struct_pointed_hset
  : hset_struct
  := struct_pointed_hset_data ,, struct_pointed_hset_laws.

(**
 2. Limits and colimits of pointed sets
 *)
Definition cartesian_struct_pointed_hset_data
  : hset_cartesian_struct_data
  := struct_pointed_hset ,, tt ,, λ X Y x y, x ,, y.

Definition cartesian_struct_pointed_hset_laws
  : hset_cartesian_struct_laws cartesian_struct_pointed_hset_data.
Proof.
  repeat split.
  intros W X Y pw px py f g p q ; cbn in *.
  unfold prodtofuntoprod ; cbn.
  rewrite p, q.
  apply idpath.
Qed.

Definition cartesian_struct_pointed_hset
  : hset_cartesian_struct
  := cartesian_struct_pointed_hset_data ,, cartesian_struct_pointed_hset_laws.

Definition equalizers_struct_pointed_hset
  : hset_equalizer_struct struct_pointed_hset.
Proof.
  simple refine (_ ,, _).
  - refine (λ X Y f g px py p q, px ,, _).
    abstract (exact (p @ !q)).
  - abstract
      (repeat split ; cbn ;
       intros X Y f g px py p q W pw h r s ;
       use subtypePath ; [ intro ; apply setproperty | ] ;
       exact r).
Defined.

Definition coequalizers_struct_pointed_hset
  : hset_coequalizer_struct struct_pointed_hset.
Proof.
  simple refine (_ ,, _).
  - exact (λ X Y f g px py p q, setquotpr _ py).
  - abstract
      (repeat split ; cbn ;
       intros X Y f g px py p q W pw h r s ;
       exact r).
Defined.

Definition type_products_struct_pointed_hset
           (I : UU)
  : hset_struct_type_prod struct_pointed_hset I.
Proof.
  simple refine (_ ,, _).
  - exact (λ D fs, fs).
  - abstract
      (repeat split ; cbn ;
       intros D PD W pw fs pq ;
       use funextsec ;
       exact pq).
Defined.

(**
 3. Pointed sets form a pointed structure
 *)
Definition pointed_struct_pointed_hset_data
  : pointed_hset_struct_data struct_pointed_hset
  := λ X x, x.

Proposition pointed_struct_pointed_hset_laws
  : pointed_hset_struct_laws pointed_struct_pointed_hset_data.
Proof.
  split.
  - intros X Y PX PY ; cbn.
    apply idpath.
  - intros X Y f PX PY Pf ; cbn in *.
    exact Pf.
Qed.

Definition pointed_struct_pointed_hset
  : pointed_hset_struct struct_pointed_hset
  := pointed_struct_pointed_hset_data ,, pointed_struct_pointed_hset_laws.

(**
 4. The smash product
 *)
Definition pointed_struct_pointed_hset_with_smash_data
  : hset_struct_with_smash_data
      cartesian_struct_pointed_hset
      pointed_struct_pointed_hset.
Proof.
  split.
  - exact false.
  - exact (λ X Y x y, setquotpr _ (x ,, y)).
Defined.

Proposition pointed_struct_pointed_hset_with_smash_laws
  : hset_struct_with_smash_laws
      pointed_struct_pointed_hset_with_smash_data.
Proof.
  repeat split.
  - intros X Y x y f pf g pg.
    cbn in *.
    unfold pointed_hset_struct_unit_map.
    rewrite pf.
    apply idpath.
  - intro y.
    use iscompsetquotpr.
    apply hinhpr.
    use inr.
    unfold product_point_coordinate ; cbn.
    unfold pointed_struct_pointed_hset_data.
    split.
    + exact (inl (idpath _)).
    + exact (inl (idpath _)).
  - intro x.
    use iscompsetquotpr.
    apply hinhpr.
    use inr.
    unfold product_point_coordinate ; cbn.
    unfold pointed_struct_pointed_hset_data.
    split.
    + exact (inr (idpath _)).
    + exact (inr (idpath _)).
  - intros Z z h Ph hp₁ hp₂ hp₃ ; cbn in *.
    exact Ph.
Qed.

Definition pointed_struct_pointed_hset_with_smash
  : hset_struct_with_smash
      cartesian_struct_pointed_hset
      pointed_struct_pointed_hset.
Proof.
  use make_hset_struct_with_smash.
  - exact pointed_struct_pointed_hset_with_smash_data.
  - exact pointed_struct_pointed_hset_with_smash_laws.
Defined.

Definition pointed_struct_pointed_hset_with_smash_closed_pointed
  : hset_struct_with_smash_closed_pointed
      pointed_struct_pointed_hset_with_smash.
Proof.
  refine ((λ X Y x y, (λ _, y) ,, idpath _) ,, _).
  intro ; intros.
  apply idpath.
Defined.

Proposition pointed_struct_pointed_hset_with_smash_adj_laws
  : hset_struct_with_smash_closed_adj_laws
      pointed_struct_pointed_hset_with_smash_closed_pointed.
Proof.
  split.
  - intros X Y Z f.
    induction X as [ X x ].
    induction Y as [ Y y ].
    induction Z as [ Z z ].
    induction f as [ f p ].
    cbn in *.
    exact (eqtohomot (maponpaths pr1 p) y).
  - intros X Y Z f.
    induction X as [ X x ].
    induction Y as [ Y y ].
    induction Z as [ Z z ].
    induction f as [ f p ].
    use subtypePath.
    {
      intro.
      apply setproperty.
    }
    use funextsec.
    intro a.
    refine (_ @ p).
    refine (maponpaths f _).
    use iscompsetquotpr.
    apply hinhpr ; cbn.
    use inr.
    unfold product_point_coordinate ; cbn.
    unfold pointed_struct_pointed_hset_data.
    split ; use inl ; apply idpath.
Qed.

Definition pointed_struct_pointed_hset_with_smash_adj
  : hset_struct_with_smash_closed_adj
      pointed_struct_pointed_hset_with_smash
  := pointed_struct_pointed_hset_with_smash_closed_pointed
     ,,
     pointed_struct_pointed_hset_with_smash_adj_laws.

Proposition pointed_struct_pointed_hset_with_smash_laws_enrich
  : hset_struct_with_smash_closed_laws_enrich
      pointed_struct_pointed_hset_with_smash_adj.
Proof.
  split.
  - intros X Y Z.
    induction X as [ X x ].
    induction Y as [ Y y ].
    induction Z as [ Z z ].
    use subtypePath.
    {
      intro ; apply setproperty.
    }
    use funextsec.
    use setquotunivprop'.
    {
      intro ; apply setproperty.
    }
    intro xz.
    cbn in *.
    apply idpath.
  - intros X Y Z.
    induction X as [ X x ].
    induction Y as [ Y y ].
    induction Z as [ Z z ].
    use subtypePath.
    {
      intro ; apply setproperty.
    }
    use funextsec.
    intro a.
    use subtypePath.
    {
      intro ; apply setproperty.
    }
    use funextsec.
    intro b.
    cbn in *.
    apply idpath.
Qed.

Definition pointed_struct_pointed_hset_with_smash_closed
  : hset_struct_with_smash_closed
  := cartesian_struct_pointed_hset
     ,,
     pointed_struct_pointed_hset
     ,,
     pointed_struct_pointed_hset_with_smash
     ,,
     pointed_struct_pointed_hset_with_smash_adj
     ,,
     pointed_struct_pointed_hset_with_smash_laws_enrich.
