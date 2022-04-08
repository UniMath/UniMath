(******************************************************************

 Morphism from biinitial objects

 If a bicategory has a strict biinitial object, then we can deduce
 a number of intersting properties of 1-cells from the biinitial
 object to any other object.

 Contents
 1. Faithfulness
 2. Fully faithfulness
 3. Conservativity
 4. Discreteness
 5. It's an internal Street fibration
 6. Preservation of cartesian cells
 7. It's an internal Street opfibration
 8. Preservation of opcartesian cells

 ******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Colimits.Initial.

Local Open Scope cat.

Section FromInitial.
  Context {B : bicat}
          {x y : B}
          (Hx : is_biinitial x)
          (Sx : biinitial_is_strict_biinitial_obj Hx)
          (f : x --> y).

  (**
   1. Faithfulness
   *)
  Definition from_biinitial_faithful_1cell
    : faithful_1cell f.
  Proof.
    intros z g₁ g₂ α₁ α₂ p.
    enough (Hz : is_biinitial z).
    {
      apply (is_biinitial_eq_property Hz).
    }
    exact (equiv_to_biinitial Hx (Sx z g₁)).
  Defined.

  (**
   2. Fully faithfulness
   *)
  Definition from_biinitial_fully_faithful_1cell
    : fully_faithful_1cell f.
  Proof.
    use make_fully_faithful.
    - exact from_biinitial_faithful_1cell.
    - intros z g₁ g₂ αf.
      assert(Hz : is_biinitial z).
      {
        exact (equiv_to_biinitial Hx (Sx z g₁)).
      }
      simple refine (_ ,, _).
      + apply (is_biinitial_2cell_property Hz).
      + apply (is_biinitial_eq_property Hz).
  Defined.

  (**
   3. Conservativity
   *)
  Definition from_biinitial_conservative_1cell
    : conservative_1cell f.
  Proof.
    intros z g₁ g₂ α Hα.
    assert(Hz : is_biinitial z).
    {
      exact (equiv_to_biinitial Hx (Sx z g₁)).
    }
    use make_is_invertible_2cell.
    - apply (is_biinitial_2cell_property Hz).
    - apply (is_biinitial_eq_property Hz).
    - apply (is_biinitial_eq_property Hz).
  Defined.

  (**
   4. Discreteness
   *)
  Definition from_biinitial_discrete_1cell
    : discrete_1cell f.
  Proof.
    split.
    - exact from_biinitial_faithful_1cell.
    - exact from_biinitial_conservative_1cell.
  Defined.

  (**
   5. It's an internal Street fibration
   *)
  Definition from_biinitial_is_cartesian_2cell_sfib
             {z : B}
             {g₁ g₂ : z --> x}
             (α : g₁ ==> g₂)
    : is_cartesian_2cell_sfib f α.
  Proof.
    assert(Hz : is_biinitial z).
    {
      exact (equiv_to_biinitial Hx (Sx z g₁)).
    }
    intros w γ δp p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         apply (is_biinitial_eq_property Hz)).
    - simple refine (_ ,, _ ,, _).
      + apply (is_biinitial_2cell_property Hz).
      + apply (is_biinitial_eq_property Hz).
      + apply (is_biinitial_eq_property Hz).
  Defined.

  Definition from_biinitial_internal_sfib_cleaving
    : internal_sfib_cleaving f.
  Proof.
    intros z g h α.
    assert(Hz : is_biinitial z).
    {
      exact (equiv_to_biinitial Hx (Sx z h)).
    }
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact h.
    - apply id2.
    - use make_invertible_2cell.
      + apply (is_biinitial_2cell_property Hz).
      + use make_is_invertible_2cell.
        * apply (is_biinitial_2cell_property Hz).
        * apply (is_biinitial_eq_property Hz).
        * apply (is_biinitial_eq_property Hz).
    - apply id_is_cartesian_2cell_sfib.
    - apply (is_biinitial_eq_property Hz).
  Defined.

  Definition from_biinitial_lwhisker_is_cartesian
    : lwhisker_is_cartesian f.
  Proof.
    intro ; intros.
    apply from_biinitial_is_cartesian_2cell_sfib.
  Defined.

  Definition from_biinitial_internal_sfib
    : internal_sfib f.
  Proof.
    split.
    - exact from_biinitial_internal_sfib_cleaving.
    - exact from_biinitial_lwhisker_is_cartesian.
  Defined.

  (**
   6. Preservation of cartesian cells
   *)
  Definition from_biinitial_mor_preserves_cartesian
             {x' y' : B}
             (f' : x' --> y')
    : mor_preserves_cartesian
        f
        f'
        (is_biinitial_1cell_property Hx x').
  Proof.
    intros z h₁ h₂ γ Hγ.
    assert(Hz : is_biinitial z).
    {
      exact (equiv_to_biinitial Hx (Sx z h₁)).
    }
    intros w ζ δp p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         apply (is_biinitial_eq_property Hz)).
    - simple refine (_ ,, _ ,, _).
      + apply (is_biinitial_2cell_property Hz).
      + apply (is_biinitial_eq_property Hz).
      + apply (is_biinitial_eq_property Hz).
  Defined.

  (**
   7. It's an internal Street opfibration
   *)
  Definition from_biinitial_is_opcartesian_2cell_sopfib
             {z : B}
             {g₁ g₂ : z --> x}
             (α : g₁ ==> g₂)
    : is_opcartesian_2cell_sopfib f α.
  Proof.
    assert(Hz : is_biinitial z).
    {
      exact (equiv_to_biinitial Hx (Sx z g₁)).
    }
    intros w γ δp p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         apply (is_biinitial_eq_property Hz)).
    - simple refine (_ ,, _ ,, _).
      + apply (is_biinitial_2cell_property Hz).
      + apply (is_biinitial_eq_property Hz).
      + apply (is_biinitial_eq_property Hz).
  Defined.

  Definition from_biinitial_internal_sopfib_cleaving
    : internal_sopfib_opcleaving f.
  Proof.
    intros z g h α.
    assert(Hz : is_biinitial z).
    {
      exact (equiv_to_biinitial Hx (Sx z g)).
    }
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact g.
    - apply id2.
    - use make_invertible_2cell.
      + apply (is_biinitial_2cell_property Hz).
      + use make_is_invertible_2cell.
        * apply (is_biinitial_2cell_property Hz).
        * apply (is_biinitial_eq_property Hz).
        * apply (is_biinitial_eq_property Hz).
    - apply id_is_opcartesian_2cell_sopfib.
    - apply (is_biinitial_eq_property Hz).
  Defined.

  Definition from_biinitial_lwhisker_is_opcartesian
    : lwhisker_is_opcartesian f.
  Proof.
    intro ; intros.
    apply from_biinitial_is_opcartesian_2cell_sopfib.
  Defined.

  Definition from_biinitial_internal_sopfib
    : internal_sopfib f.
  Proof.
    split.
    - exact from_biinitial_internal_sopfib_cleaving.
    - exact from_biinitial_lwhisker_is_opcartesian.
  Defined.

  (**
   8. Preservation of opcartesian cells
   *)
  Definition from_biinitial_mor_preserves_opcartesian
             {x' y' : B}
             (f' : x' --> y')
    : mor_preserves_opcartesian
        f
        f'
        (is_biinitial_1cell_property Hx x').
  Proof.
    intros z h₁ h₂ γ Hγ.
    assert(Hz : is_biinitial z).
    {
      exact (equiv_to_biinitial Hx (Sx z h₁)).
    }
    intros w ζ δp p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         apply (is_biinitial_eq_property Hz)).
    - simple refine (_ ,, _ ,, _).
      + apply (is_biinitial_2cell_property Hz).
      + apply (is_biinitial_eq_property Hz).
      + apply (is_biinitial_eq_property Hz).
  Defined.
End FromInitial.
