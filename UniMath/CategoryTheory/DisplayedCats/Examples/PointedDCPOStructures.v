(*****************************************************************

 Pointed DCPOs

 We construct the category of pointed DCPOs and Scott continuous
 functions (not necessarily strict). Note that since we do not
 look at strict functions, the resulting category does not have
 all limits and colimits. However, it has a terminal object,
 binary products, and it is cartesian closed. In addition, it has
 products indexed by arbitrary types.

 Contents
 1. Pointed DCPO structures
 2. Cartesian structure of pointed DCPOs
 3. Structure on the category of DCPPOs

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.

Local Open Scope cat.
Local Open Scope dcpo.

(**
 1. Pointed DCPO structures
 *)
Definition struct_dcppo_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, dcppo_struct X).
  - exact (λ X Y PX PY f, is_scott_continuous PX PY f).
Defined.

Definition struct_dcppo_laws
  : hset_struct_laws struct_dcppo_data.
Proof.
  split5.
  - intro X.
    apply isaset_dcppo_struct.
  - intros X Y px py f.
    apply isaprop_is_scott_continuous.
  - intros X PX ; cbn in *.
    apply id_is_scott_continuous.
  - intros X Y Z PX PY PZ f g Pf Pg.
    exact (comp_is_scott_continuous Pf Pg).
  - intros X PX PX' p q ; cbn in *.
    exact (eq_dcppo_struct _ _ p q).
Defined.

Definition struct_dcppo
  : hset_struct
  := struct_dcppo_data ,, struct_dcppo_laws.

Definition DCPPO
  : univalent_category
  := univalent_category_of_hset_struct struct_dcppo.

Definition DCPPO_underlying
  : DCPPO ⟶ SET
  := underlying_of_hset_struct struct_dcppo.

(**
 2. Cartesian structure of pointed DCPOs
 *)
Definition cartesian_struct_dcppo_data
  : hset_cartesian_struct_data
  := struct_dcppo
     ,,
     unit_dcppo_struct
     ,,
     λ X Y DX DY, prod_dcppo_struct DX DY.

Definition cartesian_struct_dcppo_laws
  : hset_cartesian_struct_laws cartesian_struct_dcppo_data.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros X DX ; cbn in *.
    exact (is_scott_continuous_to_unit DX).
  - intros X Y DX DY ; cbn in *.
    exact (is_scott_continuous_dirprod_pr1 DX DY).
  - intros X Y DX DY ; cbn in *.
    exact (is_scott_continuous_dirprod_pr2 DX DY).
  - intros W X Y DW DY DZ f g Df Dg ; cbn in *.
    exact (is_scott_continuous_prodtofun Df Dg).
Qed.

Definition cartesian_struct_dcppo
  : hset_cartesian_struct
  := cartesian_struct_dcppo_data ,, cartesian_struct_dcppo_laws.

Definition cartesian_closed_struct_dcppo_data
  : hset_cartesian_closed_struct_data.
Proof.
  refine (cartesian_struct_dcppo ,, _ ,, _).
  - abstract
      (intros X Y DX DY y ; cbn in * ;
       exact (is_scott_continuous_constant DX DY y)).
  - exact (λ X Y DX DY, dcppo_struct_funspace DX DY).
Defined.

Proposition cartesian_closed_struct_dcppo_laws
  : closed_under_fun_laws cartesian_closed_struct_dcppo_data.
Proof.
  split.
  - intros X Y DX DY ; cbn in *.
    exact (is_scott_continuous_eval (X ,, pr1 DX) (Y ,, pr1 DY)).
  - intros X Y Z DX DY DZ f Df ; cbn in *.
    apply (@is_scott_continuous_lam (X ,, pr1 DX) (Y ,, pr1 DY) (Z ,, pr1 DZ) (f ,, Df)).
Qed.

Definition cartesian_closed_struct_dcppo
  : hset_cartesian_closed_struct
  := cartesian_closed_struct_dcppo_data
     ,,
     cartesian_closed_struct_dcppo_laws.

(**
 3. Structure on the category of DCPPOs
 *)
Definition type_products_struct_dcppo
           (I : UU)
  : hset_struct_type_prod struct_dcppo I.
Proof.
  simple refine (_ ,, _).
  - exact (λ D DD, @depfunction_dcppo_struct I (λ i, D i ,, DD i)).
  - split ; cbn.
    + abstract
        (intros D DD i ;
         exact (is_scott_continuous_depfunction_pr (λ i, D i ,, pr1 (DD i)) i)).
    + abstract
        (intros D DD W DW fs Hfs ;
         exact (@is_scott_continuous_depfunction_map
                  _
                  (λ i, D i ,, pr1 (DD i))
                  (W ,, pr1 DW)
                  (λ i, fs i ,, Hfs i))).
Defined.

Definition Terminal_DCPPO
  : Terminal DCPPO
  := Terminal_category_of_hset_struct cartesian_struct_dcppo.

Definition BinProducts_DCPPO
  : BinProducts DCPPO
  := BinProducts_category_of_hset_struct cartesian_struct_dcppo.

Definition Exponentials_DCPPO
  : Exponentials BinProducts_DCPPO
  := Exponentials_struct cartesian_closed_struct_dcppo.

Definition Products_DCPPO
           (I : UU)
  : Products I DCPPO
  := Products_category_of_hset_struct_type_prod (type_products_struct_dcppo I).
