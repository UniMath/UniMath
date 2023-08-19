(*
In this file, builders are provided for showing that a monoidal (resp. symmetric monoidal) category is cartesian;
i.e., the tensor product (resp. unit) coincides with the (categorical) product (resp terminal object).
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Tensor.

Local Open Scope cat.
Import MonoidalNotations.
Local Open Scope moncat.

(* Definition make_section_into_comonoids
    : section_disp (comonoid_disp_cat M).
  Proof.
    unfold section_disp.
    use tpair.
    - exists m.
      exact mf.
    - split ; intro ; intros ; apply isaprop_is_comonoid_mor.
  Defined. *)

Section CartesianBuilder.

  Context (V : monoidal_cat).

  Context
    (m : ∏ x : V, disp_cat_of_comonoids V x)
      (mf : ∏ (x y : V) (f : V⟦x,y⟧), comonoid_mor_struct V (_ ,, m x) (_ ,, m y) f).

  Import ComonoidNotations.

  Let εI : V ⟦monoidal_unit V , monoidal_unit V⟧
      := ε_{(monoidal_unit V ,, m _) : comonoid V}.

  Lemma terminal_from_aug_id (x : V)
    : εI = identity (monoidal_unit V)
       → iscontr (V⟦x, monoidal_unit V⟧).
  Proof.
    exists (ε_{(x ,, m x) : comonoid V}).
    abstract (
        intro f
        ; refine (_ @ id_right _)
        ; refine (_ @ ! (pr21 (mf _ _ f)))
        ; refine (! id_right _ @ _)
        ; apply maponpaths, pathsinv0
        ; assumption).
  Defined.

  Definition monoidal_is_semicartesian_from_comonoid
    (pI : εI = identity (monoidal_unit V))
    : is_semicartesian V.
  Proof.
    intro ; apply terminal_from_aug_id.
    assumption.
  Defined.

  Section make_cartesian.

    Context (pI : εI = identity (monoidal_unit V))
      {x y z : V} (fx : V⟦z, x⟧) (fy : V⟦z, y⟧).

    Let δx : V⟦x, x ⊗ x⟧ := δ_{(x ,, m x) : comonoid V}.
    Let δy : V⟦y, y ⊗ y⟧ := δ_{(y ,, m y) : comonoid V}.
    Let δz : V⟦z, z ⊗ z⟧ := δ_{(z ,, m z) : comonoid V}.
    Let εx : V⟦x, monoidal_unit V⟧ := ε_{(x ,, m x) : comonoid V} .
    Let εy : V⟦y, monoidal_unit V⟧ := ε_{(y ,, m y) : comonoid V}.
    Let εz : V⟦z, monoidal_unit V⟧ := ε_{(z ,, m z) : comonoid V}.

    Definition make_isbinprod_from_comonoid_existence_mor
      : V⟦z, x ⊗ y⟧
      := δz · fx #⊗ fy.

    Lemma make_is_binprod_from_comonoids_existence_mor_1
      : δz · fx #⊗ fy · (identity x #⊗ εy · mon_runitor x) = fx.
    Proof.
      rewrite ! assoc'.
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        refine (_ @ idpath ((identity z #⊗ εz) · (fx #⊗ identity _))).
        simpl.
        refine (! tensor_comp_mor _ _ _ _ @ _).
        refine (_ @ tensor_comp_mor _ _ _ _).
        rewrite ! id_right.
        rewrite id_left.
        apply maponpaths.
        apply isapropifcontr.
        apply (terminal_from_aug_id z pI).
      }

      etrans. {
        apply maponpaths.
        rewrite assoc'.
        apply maponpaths.
        apply tensor_runitor.
      }
      rewrite ! assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      refine ( _ @ comonoid_to_law_unit_right V ((z ,, m z) : comonoid V)).
      apply maponpaths_2, maponpaths.
      apply (when_bifunctor_becomes_leftwhiskering V).
    Qed.

    Lemma make_is_binprod_from_comonoids_existence_mor_2
      : δz · fx #⊗ fy · (εx #⊗ identity y · mon_lunitor y) = fy.
    Proof.
      rewrite ! assoc'.
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        refine (_ @ idpath ((εz #⊗ identity z ) · (identity _ #⊗ fy))).
        simpl.
        refine (! tensor_comp_mor _ _ _ _ @ _).
        refine (_ @ tensor_comp_mor _ _ _ _).
        rewrite ! id_right.
        rewrite id_left.
        apply maponpaths_2.
        apply isapropifcontr.
        apply (terminal_from_aug_id z pI).
      }

      etrans. {
        apply maponpaths.
        rewrite assoc'.
        apply maponpaths.
        apply tensor_lunitor.
      }
      rewrite ! assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      refine ( _ @ comonoid_to_law_unit_left V ((z ,, m z) : comonoid V)).
      apply maponpaths_2, maponpaths.
      apply (when_bifunctor_becomes_rightwhiskering V).
    Qed.

    Context (p : identity (x ⊗ y) =
                   δ_{(x ⊗ y ,, m _) : comonoid V}
                     · ((identity x #⊗ εy) #⊗ (εx #⊗ identity y) · mon_runitor x #⊗ mon_lunitor y)).

    Lemma make_is_binprod_from_comonoids_uniqueness
      (f : V⟦z, x ⊗ y⟧)
      (px : f · (identity x #⊗ εy · mon_runitor x) = fx)
      (py : f · (εx #⊗ identity y · mon_lunitor y) = fy)
      : f = δz · fx #⊗ fy.
    Proof.
      rewrite <- px.
      rewrite <- py.
      clear px py.
      etrans.
      2: {
        apply maponpaths.
        apply pathsinv0.
        apply tensor_comp_mor.
      }

      etrans.
      2: {
        do 2 apply maponpaths.
        apply pathsinv0.
        apply tensor_comp_mor.
      }

      rewrite assoc.
      etrans.
      2: {
        apply maponpaths_2.
        apply pathsinv0.
        apply (mf _ _ f).
      }
      refine (! id_right _ @ _).
      rewrite assoc'.
      apply maponpaths.
      apply p.
    Qed.

  End make_cartesian.

  Lemma monoidal_is_binproduct_from_comonoid
    (pI : εI = identity (monoidal_unit V))
    (pT : ∏ x y : V,
          δ_{(x ⊗ y ,, m _) : comonoid V} · ((identity x #⊗ ε_{(y ,, m y) : comonoid V}) #⊗ (ε_{(x ,, m x) : comonoid V} #⊗ identity y) · mon_runitor x #⊗ mon_lunitor y)
          = identity (x ⊗ y))
    : tensor_isBinProduct (monoidal_is_semicartesian_from_comonoid pI).
  Proof.
    intros x y.
    use make_isBinProduct.
    intros z fx fy.
    simple refine ((_ ,, _ ,, _) ,, _).
    - exact (make_isbinprod_from_comonoid_existence_mor fx fy).
    - exact (make_is_binprod_from_comonoids_existence_mor_1 pI fx fy).
    - exact (make_is_binprod_from_comonoids_existence_mor_2 pI fx fy).
    - intro f.
      use subtypePath.
      { intro ; apply isapropdirprod ; apply homset_property. }
      exact (make_is_binprod_from_comonoids_uniqueness fx fy (! pT x y) (pr1 f) (pr12 f) (pr22 f)).
  Qed.

  Definition monoidal_is_cartesian_from_comonoid
    (pI : εI = identity (monoidal_unit V))
    (pT : ∏ x y : V,
          δ_{(x ⊗ y ,, m _) : comonoid V} · ((identity x #⊗ ε_{(y ,, m y) : comonoid V}) #⊗ (ε_{(x ,, m x) : comonoid V} #⊗ identity y) · mon_runitor x #⊗ mon_lunitor y)
          = identity (x ⊗ y))
    : is_cartesian V.
  Proof.
    exists (monoidal_is_semicartesian_from_comonoid pI).
    exact (monoidal_is_binproduct_from_comonoid pI pT).
  Defined.

End CartesianBuilder.

Section CartesianBuilderCommutative.

  Context (V : sym_monoidal_cat).

  Context
    (m : ∏ x : V, disp_cat_of_comonoids V x)
      (is_comonoid_mor : ∏ (x y : V) (f : V⟦x,y⟧), comonoid_mor_struct V (_ ,, m x) (_ ,, m y) f).

  Import ComonoidNotations.

  Let εI : V⟦monoidal_unit V, monoidal_unit V⟧
      := ε_{(monoidal_unit V ,, m _) : comonoid V}.

  Let cm := λ x : V, (x ,, m x) : comonoid V.

  Lemma comonoid_unit_law_right_inv (x : V)
    : mon_runitor x · (δ_{cm x} · x ⊗^{V}_{l} ε_{cm x})
      = identity _.
  Proof.
    etrans. {
      apply maponpaths.
      apply (comonoid_laws_unit_right' V (x ,, m x)).
    }
    apply monoidal_rightunitorisolaw.
  Qed.

  Lemma comonoid_unit_law_left_inv (y : V)
    : mon_lunitor y · (δ_{cm y} · ε_{cm y} ⊗^{V}_{r} y) = identity _.
  Proof.
    etrans. {
      apply maponpaths.
      apply (comonoid_laws_unit_left' V (y ,, m y)).
    }
    apply monoidal_leftunitorisolaw.
  Qed.

  Lemma inner_swap_before_aug (x y : V)
    : inner_swap V x x y y · (x ⊗^{V}_{l} ε_{cm y}) #⊗ (ε_{cm _} ⊗^{V}_{r} y)
      = (_ ⊗^{V}_{l} ε_{cm _}) #⊗ (ε_{cm _} ⊗^{V}_{r} _).
  Proof.
    refine (_ @ naturality_inner_swap V (identity x) ε_{cm x} ε_{cm y} (identity y) @ _).
    {

      now rewrite <- (when_bifunctor_becomes_leftwhiskering V),
        <- (when_bifunctor_becomes_rightwhiskering V).
    }

    rewrite <- (when_bifunctor_becomes_leftwhiskering V),
      <- (when_bifunctor_becomes_rightwhiskering V).
    rewrite inner_swap_along_unit.
    apply id_right.
  Qed.

  Context (aug_of_unit : εI = identity I_{V}).
  Context (diagonal_of_tensor
            : ∏ x y : V, δ_{cm (x ⊗ y)} = (δ_{cm x} #⊗ δ_{cm y}) · inner_swap V x x y y).

  Lemma whisker_to_total'
          (x y : V)
    : mon_runitor x #⊗ mon_lunitor y
        · δ_{cm (x ⊗ y)}
        · (x ⊗^{V}_{l} ε_{cm y}) #⊗ (ε_{cm x} ⊗^{V}_{r} y)
      = identity _.
  Proof.
    rewrite diagonal_of_tensor.
    etrans. {
      rewrite ! assoc'.
      do 2 apply maponpaths.
      apply inner_swap_before_aug.
    }

    etrans. {
      apply maponpaths.
      apply pathsinv0, tensor_comp_mor.
    }
    refine (! tensor_comp_mor _ _ _ _ @ _).
    rewrite comonoid_unit_law_left_inv.
    rewrite comonoid_unit_law_right_inv.
    apply tensor_id_id.
  Qed.

  Lemma whisker_to_total
          (x y : V)
    : δ_{cm (x ⊗ y)}
        · (x ⊗^{V}_{l} ε_{cm y}) #⊗ (ε_{cm x} ⊗^{V}_{r} y)
        · mon_runitor x ⊗^{V} mon_lunitor y
      = identity (x ⊗ y).
  Proof.
    use (z_iso_inv_to_right _ _ _ _ (_,,_)).
    {
      use (is_z_iso_bifunctor_z_iso V).
      - exact (_ ,, monoidal_rightunitorisolaw V x).
      - exact (_ ,, monoidal_leftunitorisolaw V y).
    }
    rewrite id_left.
    refine (_ @ id_right _).
    apply pathsinv0.
    use z_iso_inv_on_right.
    refine (! whisker_to_total' x y @ _).
    now rewrite ! assoc.
  Qed.

  Definition symm_monoidal_is_cartesian_from_comonoid
    : is_cartesian V.
  Proof.
    use monoidal_is_cartesian_from_comonoid.
    - exact m.
    - exact is_comonoid_mor.
    - exact aug_of_unit.
    - abstract (
          intro ; intro
          ; refine (_ @ whisker_to_total x y)
          ; rewrite <- (when_bifunctor_becomes_rightwhiskering V)
          ; rewrite <- (when_bifunctor_becomes_leftwhiskering V)
          ; rewrite ! assoc
          ; apply idpath).
  Defined.

End CartesianBuilderCommutative.
