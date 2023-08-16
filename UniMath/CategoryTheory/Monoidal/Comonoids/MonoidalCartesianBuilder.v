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
(* Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsCategory. *)
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Tensor.

Local Open Scope cat.
Import MonoidalNotations.

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
  Let C : category := V.
  Let M : monoidal C := V.

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Context
    (m : ∏ x : C, disp_cat_of_comonoids V x)
      (mf : ∏ (x y : C) (f : C⟦x,y⟧), comonoid_mor_struct M (_ ,, m x) (_ ,, m y) f).

  Import ComonoidNotations.

  Let εI := ε_{(I ,, m I) : comonoid V}.

  Lemma terminal_from_aug_id (x : C)
    :  εI = identity I
       → iscontr (C⟦x, I⟧).
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
    (pI : εI = identity I)
    : is_semicartesian M.
  Proof.
    intro ; apply terminal_from_aug_id.
    assumption.
  Defined.

  Section make_cartesian.

    Context (pI : εI = identity I)
      {x y z : C} (fx : C⟦z, x⟧) (fy : C⟦z, y⟧).

    Let δx := δ_{(x ,, m x) : comonoid V}.
    Let δy := δ_{(y ,, m y) : comonoid V}.
    Let δz := δ_{(z ,, m z) : comonoid V}.
    Let εx := ε_{(x ,, m x) : comonoid V}.
    Let εy := ε_{(y ,, m y) : comonoid V}.
    Let εz := ε_{(z ,, m z) : comonoid V}.

    Definition make_isbinprod_from_comonoid_existence_mor
      : C ⟦ z, x ⊗ y⟧
      := δz · fx ⊗⊗ fy.

    Let k := make_isbinprod_from_comonoid_existence_mor.

    Lemma make_is_binprod_from_comonoids_existence_mor_1
      : δz · fx ⊗⊗ fy · (identity x ⊗^{M} εy · ru x) = fx.
    Proof.
      rewrite ! assoc'.
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        refine (_ @ idpath ((identity z ⊗⊗ εz) · (fx ⊗⊗ identity _))).
        simpl.
        rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
        rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
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
        set (h := tensor_runitor fx); cbn in h.
        (* unfold monoidal_cat_tensor_mor, mon_runitor, monoidal_unit in h ; cbn in h. *)
        exact h.
      }
      rewrite ! assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.

      refine (_ @ pr122 (m z)) ; cbn.
      apply maponpaths_2, maponpaths.
      apply (when_bifunctor_becomes_leftwhiskering M).
    Qed.

    Lemma make_is_binprod_from_comonoids_existence_mor_2
      : δz · fx ⊗⊗ fy · (εx ⊗^{ M} identity y · lu y) = fy.
    Proof.
      rewrite ! assoc'.
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        refine (_ @ idpath ((εz ⊗⊗ identity z ) · (identity _ ⊗⊗ fy))).
        simpl.
        rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
        rewrite <- (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
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
        set (h := tensor_lunitor fy); cbn in h.
        unfold monoidal_cat_tensor_mor, mon_runitor, monoidal_unit in h ; cbn in h.
        exact h.
      }
      rewrite ! assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.

      refine (_ @ pr12 (m z)) ; cbn.
      apply maponpaths_2, maponpaths.
      apply (when_bifunctor_becomes_rightwhiskering M).
    Qed.

    Context (p : identity (x ⊗_{ M} y) =
                   pr11 (m (x ⊗_{ M} y))
                     · ((identity x ⊗^{ M} εy) ⊗^{ M} (εx ⊗^{ M} identity y) · ru x ⊗^{ M} lu y)).

    Lemma make_is_binprod_from_comonoids_uniqueness
      (f : C ⟦ z, x ⊗ y ⟧)
      (px : f · (identity x ⊗^{ M} εy · ru x) = fx)
      (py : f · (εx ⊗^{ M} identity y · lu y) = fy)
      : f = δz · fx ⊗^{ M} fy.
    Proof.
      rewrite <- px.
      rewrite <- py.
      clear px py.

      rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
      rewrite (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
      rewrite assoc.
      etrans.
      2: {
        apply maponpaths_2.
        apply (! pr11 (mf _ _ f)).
      }
      cbn.
      refine (! id_right _ @ _).
      rewrite assoc'.
      apply maponpaths.
      apply p.
    Qed.

  End make_cartesian.

  Lemma monoidal_is_binproduct_from_comonoid
    (pI : εI = identity I)
    (pT : ∏ x y : C,
          δ_{(x ⊗_{ M} y ,, m _) : comonoid V} · ((identity x ⊗^{ M} ε_{(y ,, m y) : comonoid V}) ⊗^{ M} (ε_{(x ,, m x) : comonoid V} ⊗^{ M} identity y) · ru x ⊗^{ M} lu y)
          = identity (x ⊗_{ M} y))
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
    (pI : εI = identity I)
    (pT : ∏ x y : C,
          δ_{(x ⊗_{ M} y ,, m _) : comonoid V} · ((identity x ⊗^{ M} ε_{(y ,, m y) : comonoid V}) ⊗^{ M} (ε_{(x ,, m x) : comonoid V} ⊗^{ M} identity y) · ru x ⊗^{ M} lu y)
          = identity (x ⊗_{ M} y))
    : is_cartesian V.
  Proof.
    exists (monoidal_is_semicartesian_from_comonoid pI).
    exact (monoidal_is_binproduct_from_comonoid pI pT).
  Defined.

End CartesianBuilder.

Section CartesianBuilderCommutative.

  Context (V : sym_monoidal_cat).
  Let C := V : category.
  Let M := V : monoidal C.
  Let S := (pr2 V) : symmetric M.

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Context
    (m : ∏ x : C, disp_cat_of_comonoids V x)
      (mf : ∏ (x y : C) (f : C⟦x,y⟧), comonoid_mor_struct M (_ ,, m x) (_ ,, m y) f).

  Import ComonoidNotations.

  Let εI := ε_{(I ,, m I) : comonoid V}.

  Let cm := λ x : C, (x ,, m x) : comonoid V.

  Lemma comonoid_unit_law_right_inv (x : C)
    : ru x · (δ_{cm x} · x ⊗^{ M}_{l} ε_{cm x})
      = identity _.
  Proof.
    etrans. {
      apply maponpaths.
      apply (comonoid_laws_unit_right' M (x ,, m x)).
    }
    apply monoidal_rightunitorisolaw.
  Qed.

  Lemma comonoid_unit_law_left_inv (y : C)
    : lu y · (δ_{cm y} · ε_{cm y} ⊗^{ M}_{r} y) = identity _.
  Proof.
    etrans. {
      apply maponpaths.
      apply (comonoid_laws_unit_left' M (y ,, m y)).
    }
    apply monoidal_leftunitorisolaw.
  Qed.

  Lemma rearranging_before_aug (x y : C)
    : rearrange_prod S x x y y · (x ⊗^{ M}_{l} ε_{cm y}) ⊗^{ M} (ε_{cm _} ⊗^{ M}_{r} y)
      = (_ ⊗^{ M}_{l} ε_{cm _}) ⊗^{M} (ε_{cm _} ⊗^{M}_{r} _).
  Proof.
    refine (_ @ precompose_rearrange_prod S (identity x) ε_{cm x} ε_{cm y} (identity y) @ _).
    {
      now rewrite (when_bifunctor_becomes_leftwhiskering M),
        (when_bifunctor_becomes_rightwhiskering M).
    }

    rewrite (when_bifunctor_becomes_leftwhiskering M),
      (when_bifunctor_becomes_rightwhiskering M).
    rewrite rearrange_along_unit.
    apply id_right.
  Qed.

  Context (aug_of_unit : εI = identity I_{ M}).
  Context (diagonal_of_tensor
            : ∏ x y : C, δ_{cm (x ⊗ y)} = (δ_{cm x} ⊗⊗ δ_{cm y}) · rearrange_prod S x x y y).

  Lemma whisker_to_total'
          (x y : C)
    : ru x ⊗^{ M} lu y · δ_{cm (x ⊗_{ M} y)} · (x ⊗^{ M}_{l} ε_{cm y}) ⊗^{ M} (ε_{cm x} ⊗^{ M}_{r} y)
      = identity _.
  Proof.
    rewrite diagonal_of_tensor.
    etrans. {
      rewrite ! assoc'.
      do 2 apply maponpaths.
      apply rearranging_before_aug.
    }

    rewrite <- ! (bifunctor_distributes_over_comp (F := M)) ; try (apply M).
    rewrite comonoid_unit_law_left_inv.
    rewrite comonoid_unit_law_right_inv.
    apply (bifunctor_distributes_over_id (F := M)) ; apply M.
  Qed.

  Lemma whisker_to_total
          (x y : C)
    : δ_{cm (x ⊗_{ M} y)} · (x ⊗^{ M}_{l} ε_{cm y}) ⊗^{ M} (ε_{cm x} ⊗^{ M}_{r} y) · ru x ⊗^{ M} lu y
      = identity (x ⊗_{ M} y).
  Proof.
    use (z_iso_inv_to_right _ _ _ _ (_,,_)).
    {
      use (is_z_iso_bifunctor_z_iso M).
      - exact (_ ,, monoidal_rightunitorisolaw M x).
      - exact (_ ,, monoidal_leftunitorisolaw M y).
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
    - exact mf.
    - exact aug_of_unit.
    - abstract (
          intro ; intro
          ; refine (_ @ whisker_to_total x y)
          ; rewrite (when_bifunctor_becomes_rightwhiskering V)
          ; rewrite (when_bifunctor_becomes_leftwhiskering V)
          ; rewrite ! assoc
          ; apply idpath).
  Defined.

End CartesianBuilderCommutative.
