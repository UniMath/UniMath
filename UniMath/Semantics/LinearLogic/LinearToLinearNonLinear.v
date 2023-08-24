(*
In this file, we show how any linear category induces a linear non linear model.
This boils down to proving how the eilenberg moore category of the (symmetric monoidal) comonad, given by a linear category, is cartesian monoidal.
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Adjunctions.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.categories.Dialgebras.

Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.MonoidalCartesianBuilder.

Require Import UniMath.CategoryTheory.categories.CoEilenbergMoore.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SymmetricMonoidalCoEilenbergMoore.

Require Import UniMath.Semantics.LinearLogic.LinearCategory.
Require Import UniMath.Semantics.LinearLogic.LinearNonLinear.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Import ComonoidNotations.

Section ToBeMoved.

  (* In here, I will add some accessors that need to be moved to a more appropriate place *)

  Context (L : linear_category).

  Definition bang_comult_is_mon_nat_trans
    := pr1 (symmetric_monoidal_comonad_extra_laws _ (linear_category_bang L)).

  Definition bang_counit_is_mon_nat_trans
    := pr2 (symmetric_monoidal_comonad_extra_laws _ (linear_category_bang L)).

End ToBeMoved.

(*** **)

Section ConstructionOfComonoidsInLinearCategory.

  Context {L : linear_category}.
  Context (B : comonoid L) (a : L) (i : L⟦a,B⟧) (r : L⟦B,a⟧) (ir : is_retraction i r).
  Context (p : i · δ_{B} · (r #⊗ r) · (i #⊗ i) = i · δ_{B}).

  Definition comonoid_comult_data_in_linear_category
    : L⟦a, a ⊗ a⟧.
  Proof.
    exact (i · δ_{B} · r #⊗ r).
  Defined.

  Definition comonoid_counit_data_in_linear_category
    : L⟦a, monoidal_unit L⟧.
  Proof.
    exact (i · ε_{B}).
  Defined.

  Definition comonoid_data_in_linear_category
    : disp_cat_of_comonoids_data L a.
  Proof.
    split.
    - exact comonoid_comult_data_in_linear_category.
    - exact comonoid_counit_data_in_linear_category.
  Defined.

  Local Lemma diagram_1
    : i · δ_{B} · (r #⊗ r) · (i #⊗ identity a) = i · δ_{B} · identity (pr1 B) #⊗ r.
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      exact p.
    }
    rewrite ! assoc'.
    do 3 apply maponpaths.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply maponpaths.
    apply pathsinv0, ir.
  Qed.

  Local Lemma diagram_2
    : i · δ_{B} · (r #⊗ r) · (identity a #⊗ i) = i · δ_{B} · r #⊗ identity (pr1 B).
  Proof.
    etrans.
    2: {
      apply maponpaths_2.
      exact p.
    }
    rewrite ! assoc'.
    do 3 apply maponpaths.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply maponpaths_2.
    apply pathsinv0, ir.
  Qed.

  Lemma comonoid_laws_unit_left_in_linear_category
    : comonoid_laws_unit_left L (a,, comonoid_data_in_linear_category).
  Proof.
    unfold comonoid_laws_unit_left.
    cbn.
    unfold comonoid_comult_data_in_linear_category.

    etrans. {
      apply maponpaths_2.
      unfold comonoid_counit_data_in_linear_category.
      rewrite tensor_mor_right.
      rewrite tensor_comp_id_r.
      rewrite assoc.
      apply maponpaths_2.
      apply diagram_1.
    }

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_swap'.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_lunitor.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite ! assoc.
      apply maponpaths_2.
      rewrite <- tensor_mor_right.
      apply comonoid_to_law_unit_left.
    }
    rewrite id_left.
    exact ir.
  Qed.

  Lemma comonoid_laws_unit_right_in_linear_category
    : comonoid_laws_unit_right L (a,, comonoid_data_in_linear_category).
  Proof.
    unfold comonoid_laws_unit_right.
    cbn.
    unfold comonoid_comult_data_in_linear_category.

    etrans. {
      apply maponpaths_2.
      unfold comonoid_counit_data_in_linear_category.
      rewrite tensor_mor_left.
      rewrite tensor_comp_id_l.
      rewrite assoc.
      apply maponpaths_2.
      apply diagram_2.
    }

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_swap.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_runitor.
    }

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite ! assoc.
      apply maponpaths_2.
      rewrite <- tensor_mor_left.
      apply comonoid_to_law_unit_right.
    }
    rewrite id_left.
    exact ir.
  Qed.

  Lemma comonoid_laws_assoc_in_linear_category
    : comonoid_laws_assoc L (a,, comonoid_data_in_linear_category).
  Proof.
    unfold comonoid_laws_assoc.
    cbn.
    unfold comonoid_comult_data_in_linear_category.
    (* page 155 *)
  Admitted.

  Definition comonoid_in_linear_category
    : disp_cat_of_comonoids L a.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact comonoid_data_in_linear_category.
    - exact comonoid_laws_unit_left_in_linear_category.
    - exact comonoid_laws_unit_right_in_linear_category.
    - exact comonoid_laws_assoc_in_linear_category.
  Defined.

  Definition comonoid_mor_in_linear_category
    : comonoid_mor_struct L (a,,comonoid_in_linear_category) B i.
  Proof.
    use make_is_comonoid_mor.
    - exact p.
    - apply id_right.
  Qed.

End ConstructionOfComonoidsInLinearCategory.

Section LiftingPropertyCoalgebraMorSection.

  Context (L : linear_category).

  Let EM := (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L)).
  Let bang : sym_monoidal_cmd L
      := linear_category_bang L.

  Context (xx aa bb : EM).

  Let x : L := pr11 xx.
  Let hx : L⟦x, bang x⟧ := pr21 xx.
  Let a : L := pr11 aa.
  Let ha : L⟦a, bang a⟧ := pr21 aa.
  Let b : L := pr11 bb.
  Let hb : L⟦b, bang b⟧ := pr21 bb.

  Context (g : EM⟦xx,bb⟧) (i : EM⟦aa,bb⟧) (f : L⟦x,a⟧).

  Context (f_i_coalg : hx · #(linear_category_bang L) (f · pr11 i) = (f · pr11 i) · hb).
  Context (r : L⟦b,a⟧) (ir_id : is_retraction (pr11 i) r).

  Definition lifting_is_coalg_mor
    : hx · #(linear_category_bang L) f = f · ha.
  Proof.
    assert (p := cancel_postcomposition _ _ (#(linear_category_bang L) r) f_i_coalg).
    rewrite assoc' in p.
    rewrite <- functor_comp in p.
    rewrite assoc' in p.

    refine (_ @ p @ _).
    - do 2 apply maponpaths.
      refine (! id_right _ @ _).
      apply maponpaths.
      apply pathsinv0, ir_id.
    - rewrite ! assoc'.
      apply maponpaths.
      rewrite assoc.
      etrans. {
        apply maponpaths_2.
        exact (! pr21 i).
      }
      rewrite assoc'.
      rewrite <- functor_comp.
      refine (_ @ id_right _).
      apply maponpaths.
      refine (_ @ functor_id (linear_category_bang L) _).
      apply maponpaths.
      exact ir_id.
  Qed.

End LiftingPropertyCoalgebraMorSection.


Section ConstructionOfComonoidsInEilenbergMoore.

  Context (L : linear_category).

  Let EM := (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L)).

  Let bang : sym_monoidal_cmd L
      := linear_category_bang L.

  Context (xx : EM).
  Let x : L := pr11 xx.
  Let hx : L⟦x, bang x⟧ := pr21 xx.

  Let comonoid_on_bang_x := linear_category_cocommutative_comonoid L x.

  Lemma linear_category_comult_factors_through_comult_bang
    :  δ (linear_category_bang L) x
         · (linear_category_comult L (bang x)
              · ε bang (bang x) #⊗ ε bang (bang x))
       = linear_category_comult L x.
  Proof.
    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      apply linear_category_counit_comonoid_mor_comult.
    }
    rewrite assoc'.
    rewrite <- tensor_comp_mor.
    refine (_ @ id_right _).
    apply maponpaths.
    rewrite <- tensor_id_id.
    use two_arg_paths ; apply Comonad_law1.
  Qed.

  Lemma yank
    : hx · δ_{comonoid_on_bang_x} · ε bang x #⊗ ε bang x · hx #⊗ hx
      = hx · δ_{comonoid_on_bang_x}.
  Proof.
    cbn.
    set (t := pr22 xx).
    cbn in t.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite <- tensor_comp_mor.
      apply maponpaths.
      apply pathsinv0.
      apply (pr2 (disp_ε _) _ _ hx).
    }
    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply pathsinv0.
      apply (pr2 (disp_ε _) _ _ hx).
    }

    rewrite tensor_comp_mor.
    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0.
      apply linear_category_comult_nat.
    }
    rewrite assoc.
    etrans. {
      do 2 apply maponpaths_2.
      apply pathsinv0, (pr22 xx).
    }

    rewrite ! assoc'.
    apply maponpaths.
    exact linear_category_comult_factors_through_comult_bang.
  Qed.

  Let comonoid_on_x
    : disp_cat_of_comonoids L x
      := comonoid_in_linear_category comonoid_on_bang_x x hx (ε bang x) (pr12 xx) yank.

  Lemma comonoid_comult_is_coalgebra_mor
    : hx · # ((linear_category_bang L)) δ_{(x,, comonoid_on_x) : comonoid L}
      = δ_{(x,, comonoid_on_x) : comonoid L}
          · MonoidalDialgebras.dialgebra_disp_tensor_op (identity_fmonoidal (pr1 L))
          (lax_monoidal_from_symmetric_monoidal_comonad L (linear_category_bang L))
          hx hx.
  Proof.
    (* page 157 *)

    (* summary *)
    assert (δ_{(x ,, comonoid_on_x) : comonoid L} · hx #⊗ hx = hx · δ_{comonoid_on_bang_x}).
    {
      admit.
    }

    (* The right hand side is a coalgebra morphisms *)
    (* Corollary 20, now gives a criteria to conclude:
       (hx #⊗ hx) coalgebra_mor → δ_x coalgebra_mor.
     *)

    use ((lifting_is_coalg_mor L xx (xx ⊗ xx) ((bang x ⊗ bang x ,, _) ,, _) ((hx #⊗ hx ,, _) ,, tt) δ_{ x,, comonoid_on_x : comonoid L}) _ (ε bang x #⊗ ε bang x)) ; cbn.
    (* The use statement should be cleaned up, e.g., arguments 4 and 5 are part of a larger structure that we should have available. This reduces the amount of goals as well *)

  Admitted.

  Definition comonoid_comult_coalgebra_mor
    : EM⟦xx, xx ⊗ xx⟧.
  Proof.
    use make_mor_co_eilenberg_moore.
    - exact δ_{(x ,, comonoid_on_x) : comonoid L}.
    - exact comonoid_comult_is_coalgebra_mor.
  Defined.

  (* The following lemma is actually an application that coalgebra morphisms are closed under composition, I c(sh)ould use this directly, however, I have to find the proof of that first (in the formalization) *)
  Lemma comonoid_counit_is_coalgebra_mor
    : hx · # (linear_category_bang L) ε_{ x,, comonoid_on_x : comonoid L}
      = ε_{ x,, comonoid_on_x : comonoid L} · pr21 (constant_functor EM EM I_{ EM} xx).
  Proof.
    cbn.
    unfold MonoidalDialgebras.dialgebra_disp_unit.
    cbn.
    rewrite id_left.
    cbn in *.
    unfold comonoid_counit_data_in_linear_category.
    rewrite functor_comp.
    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      apply pathsinv0.
      exact (pr22 xx).
    }

    do 2 rewrite assoc'.
    apply maponpaths.
    apply pathsinv0.
    apply linear_category_counit_coalgebra_mor.
  Qed.

  Definition comonoid_counit_coalgebra_mor
    : EM⟦xx, monoidal_unit EM⟧.
  Proof.
    use make_mor_co_eilenberg_moore.
    - exact ε_{(x ,, comonoid_on_x) : comonoid L}.
    - exact comonoid_counit_is_coalgebra_mor.
  Defined.

  Definition comonoid_data_in_eilenberg_moore
    : disp_cat_of_comonoids_data EM xx.
  Proof.
    split.
    - exact comonoid_comult_coalgebra_mor.
    - exact comonoid_counit_coalgebra_mor.
  Defined.

  Lemma comonoid_laws_unit_left_in_eilenberg_moore
    : comonoid_laws_unit_left EM (xx,, comonoid_data_in_eilenberg_moore).
  Proof.
    use eq_mor_co_eilenberg_moore.
    exact (comonoid_laws_unit_left_in_linear_category comonoid_on_bang_x x hx (ε bang x) (pr12 xx) yank).
  Qed.

  Lemma comonoid_laws_unit_right_in_eilenberg_moore
    : comonoid_laws_unit_right EM (xx,, comonoid_data_in_eilenberg_moore).
  Proof.
    use eq_mor_co_eilenberg_moore.
    exact (comonoid_laws_unit_right_in_linear_category comonoid_on_bang_x x hx (ε bang x) (pr12 xx) yank).
  Qed.

  Lemma comonoid_laws_assoc_in_eilenberg_moore
    : comonoid_laws_assoc EM (xx,, comonoid_data_in_eilenberg_moore).
  Proof.
    use eq_mor_co_eilenberg_moore.
    exact (comonoid_laws_assoc_in_linear_category comonoid_on_bang_x x hx (ε bang x) (pr12 xx) yank).
  Qed.

  Definition comonoid_in_eilenberg_moore
    : disp_cat_of_comonoids EM xx.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact comonoid_data_in_eilenberg_moore.
    - exact comonoid_laws_unit_left_in_eilenberg_moore.
    - exact comonoid_laws_unit_right_in_eilenberg_moore.
    - exact comonoid_laws_assoc_in_eilenberg_moore.
  Defined.

End ConstructionOfComonoidsInEilenbergMoore.

Section EilenbergMooreCartesian.

  Context (L : linear_category).

  (* naturality of the comultiplication and counit *)
  Lemma comonoid_mor_in_eilenberg_moore
    {x y : (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L))}
    (f : _⟦x, y⟧)
    :  comonoid_mor_struct
         (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L))
         (x,, comonoid_in_eilenberg_moore L x)
         (y,, comonoid_in_eilenberg_moore L y)
         f.
  Proof.
    use make_is_comonoid_mor.
    - use eq_mor_co_eilenberg_moore.
      cbn.
      unfold comonoid_comult_data_in_linear_category.
      cbn.
      refine (_ @ assoc' _ _ _).
      etrans.
      2: {
        apply maponpaths_2.
        rewrite assoc.
        apply maponpaths_2.
        exact (pr21 f).
      }
      rewrite ! assoc'.
      apply maponpaths.

      etrans.
      2: {
        rewrite assoc.
        apply maponpaths_2.
        exact (! linear_category_comult_nat (pr11 f)).
      }
      rewrite ! assoc'.
      apply maponpaths.
      rewrite tensor_mor_right.
      rewrite tensor_mor_left.
      etrans. {
        apply maponpaths.
        apply pathsinv0.
        apply tensor_split'.
      }
      refine (! tensor_comp_mor _ _ _ _ @ _).
      refine (_ @ tensor_comp_mor _ _ _ _).
      use two_arg_paths
      ; apply (! pr2 (disp_ε _) _ _ (pr11 f)).
    - use eq_mor_co_eilenberg_moore.
      refine (_ @ assoc' _ _ _).
      etrans.
      2: {
        apply maponpaths_2.
        exact (pr21 f).
      }
      rewrite id_right.
      cbn.
      unfold comonoid_counit_data_in_linear_category.
      rewrite assoc'.
      apply maponpaths.
      exact (! linear_category_counit_nat (pr11 f)).
  Qed.

  Lemma linear_category_counit_of_unit_coincides_with_counit_bang_comonad
    : linear_category_counit L I_{ L} = ε (linear_category_bang L) I_{ L}.
  Proof.
    (* This should follow from the monoidality of the counit natural transformation *)
  Admitted.

  Lemma comonad_preserves_unit_strongly
    :  fmonoidal_preservesunit
         (lax_monoidal_from_symmetric_monoidal_comonad L (linear_category_bang L))
         · linear_category_counit L (monoidal_unit L)
       = identity (monoidal_unit L).
  Proof.
    (* unit law for the monoidal natural transformation *)
    refine (_ @ pr22 (symmetric_monoidal_comonad_extra_laws L (linear_category_bang L))).
    apply maponpaths.
    exact linear_category_counit_of_unit_coincides_with_counit_bang_comonad.
  Qed.

  Definition linear_category_eilenberg_moore_cartesian
    : is_cartesian (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L)).
  Proof.
    use symm_monoidal_is_cartesian_from_comonoid.
    - intro ; apply comonoid_in_eilenberg_moore.
    - intro ; intros ; apply comonoid_mor_in_eilenberg_moore.
    - use eq_mor_co_eilenberg_moore.
      (* A suitable accessor has to be used (might need to be created) *)
      refine (_ @ pr222 (pr2 (linear_category_bang L))).
      cbn.
      unfold comonoid_counit_data_in_linear_category.
      unfold MonoidalDialgebras.dialgebra_disp_unit.
      cbn.
      rewrite id_left.
      apply maponpaths.
      apply linear_category_counit_of_unit_coincides_with_counit_bang_comonad.
    - intros x y.
      (* the natural transformations are monoidal; page 159 *)
      use eq_mor_co_eilenberg_moore.
      Opaque SymmetricDiagonal.inner_swap.
      cbn.
      unfold comonoid_comult_data_in_linear_category.
      cbn.
      rewrite ! tensor_mor_right.
      rewrite ! tensor_mor_left.
      unfold dialgebra_disp_tensor_op.
      cbn.
      rewrite id_left.
      etrans.
      2: {
        apply maponpaths_2.
        apply tensor_split'.
      }
      etrans.
      2: {
        apply maponpaths_2.
        apply pathsinv0, tensor_comp_mor.
      }
      etrans.
      2: {
        do 2 apply maponpaths_2.
        apply pathsinv0, tensor_comp_mor.
      }

      rewrite ! assoc'.
      apply maponpaths.
      etrans.
      2: {
        apply maponpaths.
        apply naturality_inner_swap.
      }

      etrans.
      2: {
        do 2 apply maponpaths.
        etrans.
        2: {
          apply maponpaths.
          exact (pr1 (bang_counit_is_mon_nat_trans L) (pr11 x) (pr11 y) @ id_right _).
        }
        apply maponpaths_2.
        exact (pr1 (bang_counit_is_mon_nat_trans L) (pr11 x) (pr11 y) @ id_right _).
      }
      rewrite ! tensor_comp_mor.
      rewrite ! assoc.
      apply maponpaths_2.
      (* now apply (d := linear_comult L) is a monoidal natural transformation *)
      (* to clean up the goal *)
      set (m :=  fmonoidal_preservestensordata
    (lax_monoidal_from_symmetric_monoidal_comonad _ (linear_category_bang L))
    (pr11 x) (pr11 y)).

      refine (idpath (m · _) @ _).
      refine (_ @ idpath (_ · (m #⊗ m))).

      admit.
  Admitted.

End EilenbergMooreCartesian.

Section CofreeAdjunction.

  Context (L : linear_category).

  Lemma bla (x : L)
    :  # ((linear_category_bang L)) (δ (linear_category_bang L) x) =
         δ (linear_category_bang L) ((linear_category_bang L) x).
  Proof.
  Admitted.

  Lemma bla' (x : L)
    :  # (linear_category_bang L) (ε (linear_category_bang L) x) =
         ε (linear_category_bang L) (linear_category_bang L x).
  Proof.
  Admitted.

  Definition TO_BE_REPLACED
    :  pr1 L ⟶ co_eilenberg_moore_cat (linear_category_bang L).
  Proof.
    use functor_to_co_eilenberg_moore_cat.
    - apply (linear_category_bang L).
    - use nat_trans_comp.
      2: { apply nat_trans_functor_id_left. }
      exact (δ (linear_category_bang L)).
    - intro x.
      refine (_ @ Comonad_law1 (T := linear_category_bang L) x).
      refine (assoc' _ _ _ @ _).
      apply id_left.
    - intro x.
      cbn.
      rewrite id_left.
      apply maponpaths.
      apply bla.
  Defined.

  Local Definition eilenberg_moore_forget
    :  full_subcat (dialgebra (functor_identity (pr1 L)) (linear_category_bang L))
         mon_cat_co_eilenberg_moore_extra_condition ⟶ L.
  Proof.
    use functor_composite.
    2: {
      apply Total.pr1_category.
    }
    apply Total.pr1_category.
  Defined.

  Local Definition eilenberg_moore_adj_unit
    : functor_identity
        (full_subcat (dialgebra (functor_identity (pr1 L)) (linear_category_bang L))
           mon_cat_co_eilenberg_moore_extra_condition) ⟹
        eilenberg_moore_forget ∙ TO_BE_REPLACED
  .
  Proof.
    use make_nat_trans.
    -- intro x.
       use make_mor_co_eilenberg_moore.
       ++ exact (pr21 x).
       ++ refine (! pr22 x @ _).
          apply maponpaths,
            pathsinv0,
            id_left.
    -- intros x y f.
       use eq_mor_co_eilenberg_moore.
       exact (! pr21 f).
  Defined.

  Definition eilenberg_moore_cmd_adj
    : adjunction
    (full_subcat (dialgebra (functor_identity (pr1 L)) (linear_category_bang L))
       mon_cat_co_eilenberg_moore_extra_condition) L.
  Proof.
    use make_adjunction.
    - use tpair.
      + exact eilenberg_moore_forget.
      + exists TO_BE_REPLACED.
        split.
        * exact eilenberg_moore_adj_unit.
        * exact (ε (linear_category_bang L)).
    - split.
      + exact (λ x, pr12 x).
      + intro x.
        use eq_mor_co_eilenberg_moore.
        cbn.
        refine (assoc' _ _ _ @ _).
        refine (id_left _ @ _).
        refine (_ @ Comonad_law1 (T := linear_category_bang L) x).
        apply maponpaths.
        apply bla'.
  Defined.

End CofreeAdjunction.

Section LinearToLNL.

  Definition linear_to_lnl (L : linear_category)
    : linear_non_linear_model.
  Proof.
    use make_linear_non_linear_from_strong.
    - exact (linear_category_data_to_sym_mon_closed_cat L).
    - exact (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L)).
    - apply eilenberg_moore_cmd_adj.
    - apply linear_category_eilenberg_moore_cartesian.
    - use comp_fmonoidal.
      + apply mon_cat_co_eilenberg_moore_base.
      + apply TotalMonoidal.projection_fmonoidal.
      + apply TotalMonoidal.projection_fmonoidal.
    - intros x y.
      etrans. {
        apply maponpaths.
        apply id_right.
      }
      refine (id_right _ @ _).
      cbn.
      refine (_ @ id_left _).
      rewrite id_right.
      apply pathsinv0.
      refine (id_left _ @ _).
      apply id_left.
  Defined.

End LinearToLNL.
