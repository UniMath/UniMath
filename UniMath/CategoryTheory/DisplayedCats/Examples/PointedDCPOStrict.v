(*****************************************************************

 The category of DCPPOs and strict functions

 We construct the category of DCPPos and strict Scott continuous
 functions as a category of structured sets. We show that this
 category has the following structure
 - A terminal object ([Terminal_DCPPO_strict])
 - Binary products ([BinProducts_DCPPO_strict])
 - Products indexed by types ([Products_DCPPO_strict])
 - Equalizers ([Equalizers_DCPPO_strict])
 - An initial object ([Initial_DCPPO_strict])

 Contents
 1. Structures of dcppos with strict functions
 2. The cartesian structure of dcppos
 3. Structure on the category of DCPPOs
 4. Dcppos form a pointed structure

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.

Local Open Scope cat.
Local Open Scope dcpo.

(**
 1. Structures of dcppos with strict functions
 *)
Definition struct_pointed_dcppo_strict_data
  : hset_struct_data.
Proof.
  simple refine (_ ,, _).
  - exact (λ X, dcppo_struct X).
  - exact (λ X Y DX DY f, is_strict_scott_continuous DX DY f).
Defined.

Definition struct_dcpoo_strict_laws
  : hset_struct_laws struct_pointed_dcppo_strict_data.
Proof.
  split5.
  - intro X.
    use isaset_total2.
    + apply isaset_dcpo_struct.
    + intro PX.
      use isaset_total2.
      * apply setproperty.
      * intro.
        use impred_isaset.
        intro.
        apply isasetaprop.
        apply propproperty.
  - intros X Y DX DY f.
    apply isaprop_is_strict_scott_continuous.
  - intros X DX.
    apply id_is_strict_scott_continuous.
  - intros X Y Z DX DY DZ f g Df Dg.
    exact (comp_is_strict_scott_continuous Df Dg).
  - intros X PX PX' p q ; cbn in *.
    exact (eq_dcppo_strict_struct _ _ p q).
Qed.

Definition struct_dcppo_strict
  : hset_struct
  := struct_pointed_dcppo_strict_data ,, struct_dcpoo_strict_laws.

Definition DCPPO_strict
  : univalent_category
  := univalent_category_of_hset_struct struct_dcppo_strict.

Definition DCPPO_strict_underlying
  : DCPPO_strict ⟶ SET
  := underlying_of_hset_struct struct_dcppo_strict.

(**
 2. The cartesian structure of dcppos
 *)
Definition cartesian_struct_dcppo_strict_data
  : hset_cartesian_struct_data
  := struct_dcppo_strict
     ,,
     unit_dcppo_struct
     ,,
     λ X Y DX DY, prod_dcppo_struct DX DY.

Definition cartesian_struct_dcppo_strict_laws
  : hset_cartesian_struct_laws cartesian_struct_dcppo_strict_data.
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros X DX ; cbn in *.
    apply is_strict_scott_continuous_constant.
  - intros X Y DX DY.
    apply is_strict_scott_continuous_dirprod_pr1.
  - intros X Y DX DY.
    apply is_strict_scott_continuous_dirprod_pr2.
  - intros W X Y DW DX DY f g Df Dg.
    exact (is_strict_scott_continuous_prodtofun Df Dg).
Qed.

Definition cartesian_struct_dcppo_strict
  : hset_cartesian_struct
  := cartesian_struct_dcppo_strict_data
     ,,
     cartesian_struct_dcppo_strict_laws.

(**
 3. Structure on the category of DCPPOs
 *)
Definition equalizers_struct_dcppo_strict
  : hset_equalizer_struct struct_dcppo_strict.
Proof.
  simple refine (_ ,, _).
  - intros X Y f g DX DY Df Dg.
    exact (@equalizer_dcppo_struct (X ,, DX) (Y ,, DY) (f ,, Df) (g ,, Dg)).
  - split.
    + abstract
        (intros X Y f g DX DY Df Dg ; cbn in * ;
         exact (@is_strict_scott_continuous_equalizer_pr1
                  (X ,, DX) (Y ,, DY) (f ,, Df) (g ,, Dg))).
    + abstract
        (intros X Y f g DX DY Df Dg W DW h Dh q ;
         exact (@is_strict_scott_continuous_equalizer_map
                  (X ,, DX) (Y ,, DY)
                  (f ,, Df) (g ,, Dg)
                  (W ,, DW)
                  (h ,, Dh)
                  q)).
Defined.

Definition type_products_struct_dcppo_strict
           (I : UU)
  : hset_struct_type_prod struct_dcppo_strict I.
Proof.
  simple refine (_ ,, _).
  - exact (λ D PD, depfunction_dcppo_struct (λ i, D i ,, PD i)).
  - split ; cbn.
    + abstract
        (intros D PD i ;
         exact (@is_strict_scott_continuous_depfunction_pr
                  I
                  (λ i, D i ,, PD i)
                  i)).
    + abstract
        (intros D PD W DW fs Hfs ;
         exact (@is_strict_scott_continuous_depfunction_map
                  I
                  (λ i, D i ,, PD i)
                  (W ,, DW)
                  (λ i, fs i ,, Hfs i))).
Defined.

Definition Terminal_DCPPO_strict
  : Terminal DCPPO_strict
  := Terminal_category_of_hset_struct cartesian_struct_dcppo_strict.

Definition BinProducts_DCPPO_strict
  : BinProducts DCPPO_strict
  := BinProducts_category_of_hset_struct cartesian_struct_dcppo_strict.

Definition Equalizers_DCPPO_strict
  : Equalizers DCPPO_strict
  := Equalizers_category_of_hset_struct equalizers_struct_dcppo_strict.

Definition Products_DCPPO_strict
           (I : UU)
  : Products I DCPPO_strict
  := Products_category_of_hset_struct_type_prod
       (type_products_struct_dcppo_strict I).

Definition Initial_DCPPO_strict
  : Initial DCPPO_strict.
Proof.
  use make_Initial.
  - exact unit_dcppo.
  - intros Y.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros f₁ f₂ ;
         use (@eq_strict_scott_continuous_map unit_dcppo Y f₁ f₂) ;
         intro x ;
         induction x ;
         refine (@strict_scott_continuous_map_on_point unit_dcppo _ f₁ @ !_) ;
         exact (@strict_scott_continuous_map_on_point unit_dcppo _ f₂)).
    + refine ((λ _, ⊥_{Y}) ,, _).
      abstract
        (cbn ;
         apply is_strict_scott_continuous_constant).
Defined.

(**
 4. Dcppos form a pointed structure
 *)
Definition pointed_struct_dcppo_strict_data
  : pointed_hset_struct_data struct_dcppo_strict
  := λ X DX, ⊥_{X ,, DX}.

Proposition pointed_struct_dcppo_strict_laws
  : pointed_hset_struct_laws
      pointed_struct_dcppo_strict_data.
Proof.
  split.
  - intros X Y RX RY.
    apply is_strict_scott_continuous_constant.
  - intros X Y f PX PY Pf ; cbn in *.
    apply Pf.
Qed.

Definition pointed_struct_dcppo_strict
  : pointed_hset_struct struct_dcppo_strict
  := pointed_struct_dcppo_strict_data
     ,,
     pointed_struct_dcppo_strict_laws.
