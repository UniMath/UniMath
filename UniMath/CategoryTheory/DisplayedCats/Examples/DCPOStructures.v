(*****************************************************************

 DCPOs

 In this file, we define the category of DCPOs and Scott
 continuous functions as a category of structured sets. We also
 construct limits in this category.

 Contents
 1. DCPO structures
 2. Cartesian structure of DCPOs
 3. Function spaces of DCPOs
 4. Limits of DCPOs
 5. Binary coproducts of DCPOs
 6. Set-indexed coproducts of DCPOs

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.DCPOs.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.

Local Open Scope cat.

(**
 1. DCPO structures
 *)
Definition struct_dcpo_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, dcpo_struct X).
  - exact (λ X Y PX PY f, is_scott_continuous PX PY f).
Defined.

Definition struct_dcpo_laws
  : hset_struct_laws struct_dcpo_data.
Proof.
  split5.
  - intro X.
    apply isaset_dcpo_struct.
  - intros X Y px py f.
    apply isaprop_is_scott_continuous.
  - intros X PX ; cbn in *.
    apply id_is_scott_continuous.
  - intros X Y Z PX PY PZ f g Pf Pg.
    exact (comp_is_scott_continuous Pf Pg).
  - intros X PX PX' p q ; cbn in *.
    exact (eq_dcpo_struct _ _ p q).
Defined.

Definition struct_dcpo
  : hset_struct
  := struct_dcpo_data ,, struct_dcpo_laws.

(**
 2. Cartesian structure of DCPOs
 *)
Definition cartesian_struct_dcpo_data
  : hset_cartesian_struct_data
  := struct_dcpo
     ,,
     unit_dcpo_struct
     ,,
     λ X Y DX DY, prod_dcpo_struct DX DY.

Definition cartesian_struct_dcpo_laws
  : hset_cartesian_struct_laws cartesian_struct_dcpo_data.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros X DX.
    exact (is_scott_continuous_to_unit DX).
  - intros X Y DX DY.
    exact (is_scott_continuous_dirprod_pr1 DX DY).
  - intros X Y DX DY ; cbn in *.
    exact (is_scott_continuous_dirprod_pr2 DX DY).
  - intros W X Y DW DY DZ f g Df Dg ; cbn in *.
    exact (is_scott_continuous_prodtofun Df Dg).
Qed.

(**
 3. Function spaces of DCPOs
 *)
Definition cartesian_struct_dcpo
  : hset_cartesian_struct
  := cartesian_struct_dcpo_data ,, cartesian_struct_dcpo_laws.

Definition cartesian_closed_struct_dcpo_data
  : hset_cartesian_closed_struct_data.
Proof.
  refine (cartesian_struct_dcpo ,, _ ,, _).
  - abstract
      (intros X Y DX DY y ;
       exact (is_scott_continuous_constant DX DY y)).
  - exact (λ X Y DX DY, dcpo_struct_funspace DX DY).
Defined.

Proposition cartesian_closed_struct_dcpo_laws
  : closed_under_fun_laws cartesian_closed_struct_dcpo_data.
Proof.
  split.
  - intros X Y DX DY ; cbn in *.
    exact (is_scott_continuous_eval (X ,, DX) (Y ,, DY)).
  - intros X Y Z DX DY DZ f Df ; cbn in *.
    apply (@is_scott_continuous_lam (X ,, DX) (Y ,, DY) (Z ,, DZ) (f ,, Df)).
Qed.

Definition cartesian_closed_struct_dcpo
  : hset_cartesian_closed_struct
  := cartesian_closed_struct_dcpo_data
     ,,
     cartesian_closed_struct_dcpo_laws.

(**
 4. Limits of DCPOs
 *)
Definition equalizers_struct_dcpo
  : hset_equalizer_struct struct_dcpo.
Proof.
  simple refine (_ ,, _).
  - intros X Y f g DX DY Df Dg.
    exact (@equalizer_dcpo_struct (X ,, DX) (Y ,, DY) (f ,, Df) (g ,, Dg)).
  - refine (_ ,, _).
    + abstract
        (intros X Y f g DX DY Df Dg ;
         exact (@is_scott_continuous_equalizer_pr1
                  (X ,, DX) (Y ,, DY)
                  (f ,, Df) (g ,, Dg))).
    + abstract
        (intros X Y f g DX DY Df Dg W DW h Dh q ;
         exact (@is_scott_continuous_equalizer_map
                  (X ,, DX) (Y ,, DY)
                  (f ,, Df) (g ,, Dg)
                  (W ,, DW) (h ,, Dh)
                  q)).
Defined.

Definition type_products_struct_dcpo
           (I : UU)
  : hset_struct_type_prod struct_dcpo I.
Proof.
  simple refine (_ ,, _).
  - exact (λ D DD, @depfunction_dcpo_struct I (λ i, D i ,, DD i)).
  - split ; cbn.
    + abstract
        (intros D DD i ;
         exact (is_scott_continuous_depfunction_pr (λ i, D i ,, DD i) i)).
    + abstract
        (intros D DD W DW fs Hfs ;
         exact (@is_scott_continuous_depfunction_map
                  _
                  (λ i, D i ,, DD i)
                  (W ,, DW)
                  (λ i, fs i ,, Hfs i))).
Defined.

(**
 5. Binary coproducts of DCPOs
 *)
Definition binary_coproducts_struct_dcpo
  : hset_binary_coprod_struct struct_dcpo.
Proof.
  simple refine (_ ,, _).
  - exact (λ X Y PX PY, coproduct_dcpo_struct (X ,, PX) (Y ,, PY)).
  - simple refine (_ ,, _ ,, _) ; cbn.
    + abstract
        (intros X Y PX PY ; cbn ;
         exact (is_scott_continuous_inl (X ,, PX) (Y ,, PY))).
    + abstract
        (intros X Y PX PY ; cbn ;
         exact (is_scott_continuous_inr (X ,, PX) (Y ,, PY))).
    + abstract
        (intros X Y Z PX PY PZ f g Pf Pg ;
         exact (@is_scott_continuous_sumofmaps
                  (X ,, PX)
                  (Y ,, PY)
                  (Z ,, PZ)
                  f Pf
                  g Pg)).
Defined.

(**
 6. Set-indexed coproducts of DCPOs
 *)
Definition set_coproducts_struct_dcpo
           (I : hSet)
  : hset_struct_set_coprod struct_dcpo I.
Proof.
  simple refine (_ ,, _).
  - exact (λ Y PY, coproduct_set_dcpo_struct (λ i, Y i ,, PY i)).
  - simple refine (_ ,, _) ; cbn.
    + abstract
        (intros Y PY ; cbn ;
         exact (is_scott_continuous_incl (λ i, Y i ,, PY i))).
    + abstract
        (refine (λ Y PY W PW f Pf, _) ;
         exact (@is_scott_continuous_set_coproduct_map
                  I
                  (λ i, Y i ,, PY i)
                  (W ,, PW)
                  f
                  Pf)).
Defined.
