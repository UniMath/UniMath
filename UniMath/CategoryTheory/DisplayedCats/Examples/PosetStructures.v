(*****************************************************************

 Poset structure

 Since posets are structured sets, we can define the category of
 posets in a rather convenient way. This approach is taken in this
 file.

 Contents
 1. Poset structures of set
 2. Posets is a cartesian structure
 3. Limits of posets
 4. Exponentials of posets
 5. Binary coproducts of posets

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.

Local Open Scope cat.

(**
 1. Poset structures of set
 *)
Definition struct_poset_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, PartialOrder X).
  - exact (λ X Y PX PY f, is_monotone PX PY f).
Defined.

Definition struct_poset_laws
  : hset_struct_laws struct_poset_data.
Proof.
  repeat split.
  - intro X.
    apply isaset_PartialOrder.
  - intros X Y px py f.
    apply isaprop_is_monotone.
  - intros X PX ; cbn in *.
    apply idfun_is_monotone.
  - intros X Y Z PX PY PZ f g Pf Pg.
    exact (comp_is_monotone Pf Pg).
  - intros X PX PX' p q ; cbn in *.
    exact (eq_PartialOrder p q).
Qed.

Definition struct_poset
  : hset_struct
  := struct_poset_data ,, struct_poset_laws.

(**
 2. Posets is a cartesian structure
 *)
Definition cartesian_struct_poset_data
  : hset_cartesian_struct_data
  := struct_poset
     ,,
     unit_PartialOrder
     ,,
     λ X Y PX PY, prod_PartialOrder PX PY.

Definition cartesian_struct_poset_laws
  : hset_cartesian_struct_laws cartesian_struct_poset_data.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros X PX x y p ; cbn in *.
    exact tt.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr1_is_monotone.
  - intros X Y PX PY ; cbn in *.
    apply dirprod_pr2_is_monotone.
  - intros W X Y PW PY PZ f g Pf Pg ; cbn in *.
    exact (prodtofun_is_monotone Pf Pg).
Qed.

Definition cartesian_struct_poset
  : hset_cartesian_struct
  := cartesian_struct_poset_data ,, cartesian_struct_poset_laws.

(**
 3. Limits of posets
 *)
Definition equalizers_struct_poset
  : hset_equalizer_struct struct_poset.
Proof.
  simple refine (_ ,, _).
  - intros X Y f g PX PY Pf Pg.
    exact (Equalizer_order PX _ f g).
  - repeat split.
    + abstract
        (intros X Y f g PX PY Pf Pg ; cbn in * ;
         exact (Equalizer_pr1_monotone PX Y f g)).
    + abstract
        (intros X Y f g PX PY Pf Pg W PW h Ph q ;
         exact (Equalizer_map_monotone PX Y f g PW Ph (eqtohomot q))).
Defined.

Definition type_products_struct_poset
           (I : UU)
  : hset_struct_type_prod struct_poset I.
Proof.
  simple refine (_ ,, _).
  - exact (λ D fs, depfunction_poset _ fs).
  - repeat split ; cbn.
    + abstract
        (intros D PD i ;
         apply is_monotone_depfunction_poset_pr).
    + abstract
        (intros D PD W PW fs Hfs i ;
         apply is_monotone_depfunction_poset_pair ;
         exact Hfs).
Defined.

(**
 4. Exponentials of posets
 *)
Definition poset_fun_space
           {X Y : hSet}
           (PX : PartialOrder X)
           (PY : PartialOrder Y)
  : PartialOrder (@struct_fun_hSet struct_poset X Y PX PY).
Proof.
  use make_PartialOrder.
  - exact (λ f g, ∀ (x : X), PY (pr1 f x) (pr1 g x)).
  - refine ((_ ,, _) ,, _).
    + abstract
        (intros f g h p q x ;
         exact (trans_PartialOrder PY (p x) (q x))).
    + abstract
        (intros f x ;
         exact (refl_PartialOrder PY (pr1 f x))).
    + abstract
        (intros f g p q ;
         use eq_monotone_function ;
         intro x ;
         exact (antisymm_PartialOrder PY (p x) (q x))).
Defined.

Definition cartesian_closed_struct_poset_data
  : hset_cartesian_closed_struct_data.
Proof.
  refine (cartesian_struct_poset ,, _ ,, _).
  - abstract
      (intros X Y PX PY y x₁ x₂ p ; cbn ;
       apply refl_PartialOrder).
  - exact (λ X Y PX PY, poset_fun_space PX PY).
Defined.

Proposition cartesian_closed_struct_poset_laws
  : closed_under_fun_laws cartesian_closed_struct_poset_data.
Proof.
  repeat split.
  - intros X Y PX PY xf yg p.
    induction xf as [ x [ f Hf ]].
    induction yg as [ y [ g Hg ]].
    cbn in *.
    induction p as [ p q ].
    exact (trans_PartialOrder PY (q x) (Hg _ _ p)).
  - intros X Y Z PX PY PZ f Pf z₁ z₂ p x.
    cbn in *.
    exact (Pf (x ,, z₁) (x ,, z₂) (refl_PartialOrder PX x ,, p)).
Qed.

Definition cartesian_closed_struct_poset
  : hset_cartesian_closed_struct
  := cartesian_closed_struct_poset_data
     ,,
     cartesian_closed_struct_poset_laws.

(**
 5. Binary coproducts of posets
 *)
Definition binary_coproducts_struct_poset
  : hset_binary_coprod_struct struct_poset.
Proof.
  simple refine (_ ,, _).
  - exact (λ X Y PX PY, coproduct_PartialOrder PX PY).
  - simple refine (_ ,, _ ,, _) ; cbn.
    + abstract
        (intros X Y PX PY ; cbn ;
         exact (is_monotone_inl PX PY)).
    + abstract
        (intros X Y PX PY ; cbn ;
         exact (is_monotone_inr PX PY)).
    + abstract
        (intros X Y Z PX PY PZ f g Pf Pg ;
         exact (is_monotone_sumofmaps _ _ Pf Pg)).
Defined.

(**
 6. Set-indexed coproducts of posets
 *)
Definition set_coproducts_struct_poset
           (I : hSet)
  : hset_struct_set_coprod struct_poset I.
Proof.
  simple refine (_ ,, _).
  - exact (λ Y PY, coproduct_set_PartialOrder _ PY).
  - simple refine (_ ,, _) ; cbn.
    + abstract
        (intros Y PY ; cbn ;
         exact (is_monotone_set_in _ PY)).
    + abstract
        (refine (λ Y PY W PW f Pf, _) ;
         exact (is_monotone_set_coproduct_map _ _ Pf)).
Defined.
