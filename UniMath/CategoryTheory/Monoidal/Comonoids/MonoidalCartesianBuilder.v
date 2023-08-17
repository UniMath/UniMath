nner_swap
(*
nner_swap
In this file, builders are provided for showing that a monoidal (resp. symmetric monoidal) category is cartesian;
nner_swap
i.e., the tensor product (resp. unit) coincides with the (categorical) product (resp terminal object).
nner_swap
*)
nner_swap

nner_swap
Require Import UniMath.Foundations.All.
nner_swap
Require Import UniMath.MoreFoundations.All.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Core.Categories.
nner_swap
Require Import UniMath.CategoryTheory.Core.Functors.
nner_swap
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
nner_swap
Require Import UniMath.CategoryTheory.Core.Isos.
nner_swap
Require Import UniMath.CategoryTheory.limits.binproducts.
nner_swap
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Categories.
nner_swap
Import BifunctorNotations.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Functors.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
nner_swap

nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
nner_swap
(* Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsCategory. *)
nner_swap
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Tensor.
nner_swap

nner_swap
Local Open Scope cat.
nner_swap
Import MonoidalNotations.
nner_swap

nner_swap
(* Definition make_section_into_comonoids
nner_swap
    : section_disp (comonoid_disp_cat M).
nner_swap
  Proof.
nner_swap
    unfold section_disp.
nner_swap
    use tpair.
nner_swap
    - exists m.
nner_swap
      exact mf.
nner_swap
    - split ; intro ; intros ; apply isaprop_is_comonoid_mor.
nner_swap
  Defined. *)
nner_swap

nner_swap
Section CartesianBuilder.
nner_swap

nner_swap
  Context (V : monoidal_cat).
nner_swap

nner_swap
  Context
nner_swap
    (m : ∏ x : V, disp_cat_of_comonoids V x)
nner_swap
      (mf : ∏ (x y : V) (f : V⟦x,y⟧), comonoid_mor_struct V (_ ,, m x) (_ ,, m y) f).
nner_swap

nner_swap
  Import ComonoidNotations.
nner_swap

nner_swap
  Let εI := ε_{(monoidal_unit V ,, m _) : comonoid V}.
nner_swap

nner_swap
  Lemma terminal_from_aug_id (x : V)
nner_swap
    : εI = identity (monoidal_unit V)
nner_swap
       → iscontr (V⟦x, monoidal_unit V⟧).
nner_swap
  Proof.
nner_swap
    exists (ε_{(x ,, m x) : comonoid V}).
nner_swap
    abstract (
nner_swap
        intro f
nner_swap
        ; refine (_ @ id_right _)
nner_swap
        ; refine (_ @ ! (pr21 (mf _ _ f)))
nner_swap
        ; refine (! id_right _ @ _)
nner_swap
        ; apply maponpaths, pathsinv0
nner_swap
        ; assumption).
nner_swap
  Defined.
nner_swap

nner_swap
  Definition monoidal_is_semicartesian_from_comonoid
nner_swap
    (pI : εI = identity (monoidal_unit V))
nner_swap
    : is_semicartesian V.
nner_swap
  Proof.
nner_swap
    intro ; apply terminal_from_aug_id.
nner_swap
    assumption.
nner_swap
  Defined.
nner_swap

nner_swap
  Section make_cartesian.
nner_swap

nner_swap
    Context (pI : εI = identity (monoidal_unit V))
nner_swap
      {x y z : V} (fx : V⟦z, x⟧) (fy : V⟦z, y⟧).
nner_swap

nner_swap
    Let δx := δ_{(x ,, m x) : comonoid V}.
nner_swap
    Let δy := δ_{(y ,, m y) : comonoid V}.
nner_swap
    Let δz := δ_{(z ,, m z) : comonoid V}.
nner_swap
    Let εx := ε_{(x ,, m x) : comonoid V}.
nner_swap
    Let εy := ε_{(y ,, m y) : comonoid V}.
nner_swap
    Let εz := ε_{(z ,, m z) : comonoid V}.
nner_swap

nner_swap
    Definition make_isbinprod_from_comonoid_existence_mor
nner_swap
      : V⟦z, x ⊗_{V} y⟧
nner_swap
      := δz · fx ⊗^{V} fy.
nner_swap

nner_swap
    Let k := make_isbinprod_from_comonoid_existence_mor.
nner_swap

nner_swap
    Lemma make_is_binprod_from_comonoids_existence_mor_1
nner_swap
      : δz · fx ⊗^{V} fy · (identity x ⊗^{V} εy · ru^{V}_{x}) = fx.
nner_swap
    Proof.
nner_swap
      rewrite ! assoc'.
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        rewrite assoc.
nner_swap
        apply maponpaths_2.
nner_swap
        refine (_ @ idpath ((identity z ⊗^{V} εz) · (fx ⊗^{V} identity _))).
nner_swap
        simpl.
nner_swap
        refine (! tensor_comp_mor _ _ _ _ @ _).
nner_swap
        refine (_ @ tensor_comp_mor _ _ _ _).
nner_swap
        rewrite ! id_right.
nner_swap
        rewrite id_left.
nner_swap
        apply maponpaths.
nner_swap
        apply isapropifcontr.
nner_swap
        apply (terminal_from_aug_id z pI).
nner_swap
      }
nner_swap

nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        rewrite assoc'.
nner_swap
        apply maponpaths.
nner_swap
        apply tensor_runitor.
nner_swap
      }
nner_swap
      rewrite ! assoc.
nner_swap
      refine (_ @ id_left _).
nner_swap
      apply maponpaths_2.
nner_swap
      refine ( _ @ comonoid_to_law_unit_right V _).
nner_swap
      apply maponpaths_2, maponpaths.
nner_swap
      apply (when_bifunctor_becomes_leftwhiskering V).
nner_swap
    Qed.
nner_swap

nner_swap
    Lemma make_is_binprod_from_comonoids_existence_mor_2
nner_swap
      : δz · fx ⊗^{V} fy · (εx ⊗^{V} identity y · lu^{V}_{y}) = fy.
nner_swap
    Proof.
nner_swap
      rewrite ! assoc'.
nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        rewrite assoc.
nner_swap
        apply maponpaths_2.
nner_swap
        refine (_ @ idpath ((εz ⊗^{V} identity z ) · (identity _ ⊗^{V} fy))).
nner_swap
        simpl.
nner_swap
        refine (! tensor_comp_mor _ _ _ _ @ _).
nner_swap
        refine (_ @ tensor_comp_mor _ _ _ _).
nner_swap
        rewrite ! id_right.
nner_swap
        rewrite id_left.
nner_swap
        apply maponpaths_2.
nner_swap
        apply isapropifcontr.
nner_swap
        apply (terminal_from_aug_id z pI).
nner_swap
      }
nner_swap

nner_swap
      etrans. {
nner_swap
        apply maponpaths.
nner_swap
        rewrite assoc'.
nner_swap
        apply maponpaths.
nner_swap
        apply tensor_lunitor.
nner_swap
      }
nner_swap
      rewrite ! assoc.
nner_swap
      refine (_ @ id_left _).
nner_swap
      apply maponpaths_2.
nner_swap
      refine ( _ @ comonoid_to_law_unit_left V _).
nner_swap
      apply maponpaths_2, maponpaths.
nner_swap
      apply (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    Qed.
nner_swap

nner_swap
    Context (p : identity (x ⊗_{V} y) =
nner_swap
                   δ_{(x ⊗_{V} y ,, m _) : comonoid V}
nner_swap
                     · ((identity x ⊗^{V} εy) ⊗^{V} (εx ⊗^{V} identity y) · ru^{V}_{x} ⊗^{V} lu^{V}_{y})).
nner_swap

nner_swap
    Lemma make_is_binprod_from_comonoids_uniqueness
nner_swap
      (f : V⟦z, x ⊗_{V} y⟧)
nner_swap
      (px : f · (identity x ⊗^{V} εy · ru^{V}_{x}) = fx)
nner_swap
      (py : f · (εx ⊗^{V} identity y · lu^{V}_{y}) = fy)
nner_swap
      : f = δz · fx ⊗^{V} fy.
nner_swap
    Proof.
nner_swap
      rewrite <- px.
nner_swap
      rewrite <- py.
nner_swap
      clear px py.
nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        apply maponpaths.
nner_swap
        apply pathsinv0.
nner_swap
        apply tensor_comp_mor.
nner_swap
      }
nner_swap

nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        do 2 apply maponpaths.
nner_swap
        apply pathsinv0.
nner_swap
        apply tensor_comp_mor.
nner_swap
      }
nner_swap

nner_swap
      rewrite assoc.
nner_swap
      etrans.
nner_swap
      2: {
nner_swap
        apply maponpaths_2.
nner_swap
        apply pathsinv0.
nner_swap
        apply (mf _ _ f).
nner_swap
      }
nner_swap
      refine (! id_right _ @ _).
nner_swap
      rewrite assoc'.
nner_swap
      apply maponpaths.
nner_swap
      apply p.
nner_swap
    Qed.
nner_swap

nner_swap
  End make_cartesian.
nner_swap

nner_swap
  Lemma monoidal_is_binproduct_from_comonoid
nner_swap
    (pI : εI = identity (monoidal_unit V))
nner_swap
    (pT : ∏ x y : V,
nner_swap
          δ_{(x ⊗_{V} y ,, m _) : comonoid V} · ((identity x ⊗^{V} ε_{(y ,, m y) : comonoid V}) ⊗^{V} (ε_{(x ,, m x) : comonoid V} ⊗^{V} identity y) · ru^{V}_{x} ⊗^{V} lu^{V}_{y})
nner_swap
          = identity (x ⊗_{V} y))
nner_swap
    : tensor_isBinProduct (monoidal_is_semicartesian_from_comonoid pI).
nner_swap
  Proof.
nner_swap
    intros x y.
nner_swap
    use make_isBinProduct.
nner_swap
    intros z fx fy.
nner_swap
    simple refine ((_ ,, _ ,, _) ,, _).
nner_swap
    - exact (make_isbinprod_from_comonoid_existence_mor fx fy).
nner_swap
    - exact (make_is_binprod_from_comonoids_existence_mor_1 pI fx fy).
nner_swap
    - exact (make_is_binprod_from_comonoids_existence_mor_2 pI fx fy).
nner_swap
    - intro f.
nner_swap
      use subtypePath.
nner_swap
      { intro ; apply isapropdirprod ; apply homset_property. }
nner_swap
      exact (make_is_binprod_from_comonoids_uniqueness fx fy (! pT x y) (pr1 f) (pr12 f) (pr22 f)).
nner_swap
  Qed.
nner_swap

nner_swap
  Definition monoidal_is_cartesian_from_comonoid
nner_swap
    (pI : εI = identity (monoidal_unit V))
nner_swap
    (pT : ∏ x y : V,
nner_swap
          δ_{(x ⊗_{V} y ,, m _) : comonoid V} · ((identity x ⊗^{V} ε_{(y ,, m y) : comonoid V}) ⊗^{V} (ε_{(x ,, m x) : comonoid V} ⊗^{V} identity y) · ru^{V}_{x} ⊗^{V} lu^{V}_{y})
nner_swap
          = identity (x ⊗_{V} y))
nner_swap
    : is_cartesian V.
nner_swap
  Proof.
nner_swap
    exists (monoidal_is_semicartesian_from_comonoid pI).
nner_swap
    exact (monoidal_is_binproduct_from_comonoid pI pT).
nner_swap
  Defined.
nner_swap

nner_swap
End CartesianBuilder.
nner_swap

nner_swap
Section CartesianBuilderCommutative.
nner_swap

nner_swap
  Context (V : sym_monoidal_cat).
nner_swap

nner_swap
  Context
nner_swap
    (m : ∏ x : V, disp_cat_of_comonoids V x)
nner_swap
      (is_comonoid_mor : ∏ (x y : V) (f : V⟦x,y⟧), comonoid_mor_struct V (_ ,, m x) (_ ,, m y) f).
nner_swap

nner_swap
  Import ComonoidNotations.
nner_swap

nner_swap
  Let εI := ε_{(monoidal_unit V ,, m _) : comonoid V}.
nner_swap

nner_swap
  Let cm := λ x : V, (x ,, m x) : comonoid V.
nner_swap

nner_swap
  Lemma comonoid_unit_law_right_inv (x : V)
nner_swap
    : ru^{V}_{x} · (δ_{cm x} · x ⊗^{V}_{l} ε_{cm x})
nner_swap
      = identity _.
nner_swap
  Proof.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply (comonoid_laws_unit_right' V (x ,, m x)).
nner_swap
    }
nner_swap
    apply monoidal_rightunitorisolaw.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma comonoid_unit_law_left_inv (y : V)
nner_swap
    : lu^{V}_{y} · (δ_{cm y} · ε_{cm y} ⊗^{V}_{r} y) = identity _.
nner_swap
  Proof.
nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply (comonoid_laws_unit_left' V (y ,, m y)).
nner_swap
    }
nner_swap
    apply monoidal_leftunitorisolaw.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma rearranging_before_aug (x y : V)
nner_swap
    : rearrange_prod V x x y y · (x ⊗^{V}_{l} ε_{cm y}) ⊗^{V} (ε_{cm _} ⊗^{V}_{r} y)
nner_swap
      = (_ ⊗^{V}_{l} ε_{cm _}) ⊗^{V} (ε_{cm _} ⊗^{V}_{r} _).
nner_swap
  Proof.
nner_swap
    refine (_ @ precompose_rearrange_prod V (identity x) ε_{cm x} ε_{cm y} (identity y) @ _).
nner_swap
    {
nner_swap

nner_swap
      now rewrite <- (when_bifunctor_becomes_leftwhiskering V),
nner_swap
        <- (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    }
nner_swap

nner_swap
    rewrite <- (when_bifunctor_becomes_leftwhiskering V),
nner_swap
      <- (when_bifunctor_becomes_rightwhiskering V).
nner_swap
    rewrite rearrange_along_unit.
nner_swap
    apply id_right.
nner_swap
  Qed.
nner_swap

nner_swap
  Context (aug_of_unit : εI = identity I_{V}).
nner_swap
  Context (diagonal_of_tensor
nner_swap
            : ∏ x y : V, δ_{cm (x ⊗_{V} y)} = (δ_{cm x} ⊗^{V} δ_{cm y}) · rearrange_prod V x x y y).
nner_swap

nner_swap
  Lemma whisker_to_total'
nner_swap
          (x y : V)
nner_swap
    : ru^{V}_{x} ⊗^{V} lu^{V}_{y} · δ_{cm (x ⊗_{V} y)} · (x ⊗^{V}_{l} ε_{cm y}) ⊗^{V} (ε_{cm x} ⊗^{V}_{r} y)
nner_swap
      = identity _.
nner_swap
  Proof.
nner_swap
    rewrite diagonal_of_tensor.
nner_swap
    etrans. {
nner_swap
      rewrite ! assoc'.
nner_swap
      do 2 apply maponpaths.
nner_swap
      apply rearranging_before_aug.
nner_swap
    }
nner_swap

nner_swap
    etrans. {
nner_swap
      apply maponpaths.
nner_swap
      apply pathsinv0, tensor_comp_mor.
nner_swap
    }
nner_swap
    refine (! tensor_comp_mor _ _ _ _ @ _).
nner_swap
    rewrite comonoid_unit_law_left_inv.
nner_swap
    rewrite comonoid_unit_law_right_inv.
nner_swap
    apply tensor_id_id.
nner_swap
  Qed.
nner_swap

nner_swap
  Lemma whisker_to_total
nner_swap
          (x y : V)
nner_swap
    : δ_{cm (x ⊗_{V} y)} · (x ⊗^{V}_{l} ε_{cm y}) ⊗^{V} (ε_{cm x} ⊗^{V}_{r} y) · ru^{V}_{x} ⊗^{V} lu^{V}_{y}
nner_swap
      = identity (x ⊗_{V} y).
nner_swap
  Proof.
nner_swap
    use (z_iso_inv_to_right _ _ _ _ (_,,_)).
nner_swap
    {
nner_swap
      use (is_z_iso_bifunctor_z_iso V).
nner_swap
      - exact (_ ,, monoidal_rightunitorisolaw V x).
nner_swap
      - exact (_ ,, monoidal_leftunitorisolaw V y).
nner_swap
    }
nner_swap
    rewrite id_left.
nner_swap
    refine (_ @ id_right _).
nner_swap
    apply pathsinv0.
nner_swap
    use z_iso_inv_on_right.
nner_swap
    refine (! whisker_to_total' x y @ _).
nner_swap
    now rewrite ! assoc.
nner_swap
  Qed.
nner_swap

nner_swap
  Definition symm_monoidal_is_cartesian_from_comonoid
nner_swap
    : is_cartesian V.
nner_swap
  Proof.
nner_swap
    use monoidal_is_cartesian_from_comonoid.
nner_swap
    - exact m.
nner_swap
    - exact is_comonoid_mor.
nner_swap
    - exact aug_of_unit.
nner_swap
    - abstract (
nner_swap
          intro ; intro
nner_swap
          ; refine (_ @ whisker_to_total x y)
nner_swap
          ; rewrite (when_bifunctor_becomes_rightwhiskering V)
nner_swap
          ; rewrite (when_bifunctor_becomes_leftwhiskering V)
nner_swap
          ; rewrite ! assoc
nner_swap
          ; apply idpath).
nner_swap
  Defined.
nner_swap

nner_swap
End CartesianBuilderCommutative.
