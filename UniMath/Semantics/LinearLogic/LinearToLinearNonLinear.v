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
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.categories.Dialgebras.

Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.MonoidalCartesianBuilder.

Require Import UniMath.CategoryTheory.categories.CoEilenbergMoore.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SymmetricMonoidalCoEilenbergMoore.

Require Import UniMath.Semantics.LinearLogic.LinearCategory.
Require Import UniMath.Semantics.LinearLogic.LinearCategoryEilenbergMooreAdjunction.
Require Import UniMath.Semantics.LinearLogic.LinearNonLinear.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Import ComonoidNotations.

Section ConstructionOfComonoidsInLinearCategory.

  Context {L : linear_category}.
  Context (B : comonoid L) {a : L} (i : L⟦a,B⟧) (r : L⟦B,a⟧) (ir : is_retraction i r).
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

    rewrite tensor_mor_left.
    rewrite tensor_mor_right.
    rewrite ! tensor_comp_id_l.
    rewrite ! tensor_comp_id_r.
    rewrite ! assoc.

    etrans.
    2: {
      do 2 apply maponpaths_2.
      exact (! diagram_2).
    }

    etrans. {
      do 3 apply maponpaths_2.
      exact diagram_1.
    }

    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply tensor_swap'.
    }

    etrans.
    2: {
      rewrite assoc.
      do 2 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- tensor_mor_left.
      apply comonoid_to_law_assoc.
    }
    rewrite tensor_mor_right.
    rewrite ! assoc'.
    do 2 apply maponpaths.

    rewrite <- tensor_split'.
    etrans.
    2: {
      apply maponpaths.
      apply tensor_lassociator.
    }
    rewrite ! assoc.
    apply maponpaths_2.
    rewrite <- tensor_split.
    do 2 rewrite <- tensor_comp_mor.
    apply maponpaths.
    exact (id_right _ @ ! id_left _).
  Qed.

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

  Lemma postcomp_with_section_reflect_coalg_mor
    (L : linear_category)
    (xx aa bb : @sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L))
    (i : _⟦aa,bb⟧)
    (f : L⟦pr11 xx, pr11 aa⟧)
    (f_i_coalg : pr21 xx · #(linear_category_bang L) (f · pr11 i) = (f · pr11 i) · pr21 bb)
    (r : L⟦pr11 bb, pr11 aa⟧)
    (ir_id : is_retraction (pr11 i) r)
    : pr21 xx · #(linear_category_bang L) f = f · pr21 aa.
  Proof.
    pose (p := cancel_postcomposition _ _ (#(linear_category_bang L) r) f_i_coalg).
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

  Definition lifting_is_coalg_mor
    {L : linear_category}
    {xx aa bb : (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L))}
    {g : _⟦xx,bb⟧} {i : _⟦aa,bb⟧} {f : L⟦pr11 xx, pr11 aa⟧}
    {r : L⟦pr11 bb, pr11 aa⟧}
    (ir_id : is_retraction (pr11 i) r)
    (p : f · pr11 i = pr11 g)
    : pr21 xx · #(linear_category_bang L) f = f · pr21 aa.
  Proof.
    use (postcomp_with_section_reflect_coalg_mor L xx aa bb i f _ r ir_id).
    etrans. {
      do 2 apply maponpaths.
      exact p.
    }
    etrans.
    2: {
      apply maponpaths_2.
      exact (! p).
    }
    exact (pr21 g).
  Qed.

End LiftingPropertyCoalgebraMorSection.

Section TransportationFreeCoalgebraComonoid.

  Context (L : linear_category).
  Let bang : sym_monoidal_cmd L
      := linear_category_bang L.

  Context (xx : (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L))).
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

  Local Lemma yank (* any suggestions for the name are welcome *)
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

  Definition transport_comonoid_from_free
    : disp_cat_of_comonoids L x.
  Proof.
    use comonoid_in_linear_category.
    - exact comonoid_on_bang_x.
    - exact hx.
    - exact (ε (linear_category_bang L) x).
    - exact (pr12 xx).
    - exact yank.
  Defined.

End TransportationFreeCoalgebraComonoid.

Section MakeComonoidInEilenbergMooreFromComonoidInLinear.

  Context (L : linear_category).

  Context (m : comonoid L).

  Let bang := linear_category_bang L.

  Context
    (x_b : L⟦m, bang m⟧)
      (x_b_u : x_b · ε bang m = identity (pr1 m))
      (x_b_m : x_b · δ bang (pr1 m) = x_b · #bang x_b)
      (mx_t : x_b · #bang δ_{ m} = δ_{ m} · (x_b #⊗ x_b · mon_functor_tensor (_ ,, lax_monoidal_from_symmetric_monoidal_comonad L bang) m m))
      (mx_u :  x_b · #bang ε_{ m} = ε_{ m} · mon_functor_unit (_ ,, lax_monoidal_from_symmetric_monoidal_comonad L bang)).

  Definition make_comonoid_object_in_eilenberg_moore
    : @sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L).
  Proof.
    use make_ob_co_eilenberg_moore.
    - apply m.
    - exact x_b.
    - exact x_b_u.
    - exact x_b_m.
  Defined.

  Definition make_comonoid_struct_data_in_eilenberg_moore
    : disp_cat_of_comonoids_data sym_monoidal_cat_co_eilenberg_moore
        make_comonoid_object_in_eilenberg_moore.
  Proof.
    use tpair.
    - use make_mor_co_eilenberg_moore.
      + exact δ_{m}.
      + abstract (
            refine (mx_t @ _);
            apply maponpaths;
            apply pathsinv0;
            refine (assoc' _ _ _ @ _);
            apply id_left).
    - use make_mor_co_eilenberg_moore.
      + exact ε_{m}.
      + abstract (
            refine (mx_u @ _);
        apply maponpaths;
        apply pathsinv0;
            apply id_left).
  Defined.

  Definition make_comonoid_laws_in_eilenberg_moore
    : comonoid_laws sym_monoidal_cat_co_eilenberg_moore
        (make_comonoid_object_in_eilenberg_moore ,, make_comonoid_struct_data_in_eilenberg_moore).
  Proof.
    refine (_ ,, _ ,, _) ; use eq_mor_co_eilenberg_moore.
    - apply comonoid_to_law_unit_left.
    - apply comonoid_to_law_unit_right.
    - apply comonoid_to_law_assoc.
  Qed.

  Definition make_comonoid_in_eilenberg_moore
    : comonoid (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L)).
  Proof.
    exists make_comonoid_object_in_eilenberg_moore.
    exists make_comonoid_struct_data_in_eilenberg_moore.
    exact make_comonoid_laws_in_eilenberg_moore.
  Defined.

End MakeComonoidInEilenbergMooreFromComonoidInLinear.

Section ConstructionOfComonoidsInEilenbergMoore.

  Context (L : linear_category).

  Let EM := (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L)).

  Let bang : sym_monoidal_cmd L
      := linear_category_bang L.

  Context (xx : EM).
  Let x : L := pr11 xx.
  Let hx : L⟦x, bang x⟧ := pr21 xx.

  Lemma comonoid_in_eilenberg_moore_from_coalg_counit_alg_mor
    :  hx · #bang ε_{(x,, transport_comonoid_from_free L xx) : comonoid L}
       = ε_{(x,, transport_comonoid_from_free L xx) : comonoid L}
           · mon_functor_unit (_,, lax_monoidal_from_symmetric_monoidal_comonad L bang).
  Proof.
    cbn.
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

  Lemma comonoid_in_eilenberg_moore_from_coalg_comult_alg_mor
    :  hx · #bang δ_{(x,, transport_comonoid_from_free L xx) : comonoid L}
       = δ_{(x,, transport_comonoid_from_free L xx) : comonoid L}
           ·  (hx #⊗ hx
     · mon_functor_tensor (_,,lax_monoidal_from_symmetric_monoidal_comonad L (linear_category_bang L)) x x).
  Proof.
    assert (p : pr21 (xx ⊗ xx) = (hx #⊗ hx
     · mon_functor_tensor
     (_,,lax_monoidal_from_symmetric_monoidal_comonad L (linear_category_bang L)) x x)).
    {
      refine (assoc' _ _ _ @ _).
      apply id_left.
    }
    rewrite <- p.

    assert (retr :  is_retraction (hx #⊗ hx) (ε bang x #⊗ ε bang x)).
    {
      refine (! tensor_comp_mor _ _ _ _ @ _ @ tensor_id_id _ _).
      use two_arg_paths ; apply (pr2 xx).
    }

    use (lifting_is_coalg_mor
           (xx := xx)
           (aa :=  xx ⊗ xx)
           (bb := (eilenberg_moore_cofree L x : EM) ⊗ (eilenberg_moore_cofree L x : EM))
           (g := (hx · linear_category_comult L x ,, _) ,, tt)
           (i := (hx #⊗ hx,, _) ,, tt)
           (f := δ_{ x,, transport_comonoid_from_free L xx : comonoid L})
           (r := ε bang x #⊗ ε bang x)
           retr
        ).

    - (* (hx · linear_category_comult L x) is a coalgebra morphism, because it is the composition of coalgebra morphisms *)
      cbn.
      unfold dialgebra_disp_tensor_op.
      cbn.
      rewrite id_left.
      rewrite ! assoc'.
      rewrite ! id_left.

      rewrite functor_comp.
      rewrite assoc.
      etrans. {
        apply maponpaths_2.
        exact (! pr22 xx).
      }

      etrans.
      2: {
        apply maponpaths.
        apply pathsinv0.
        exact (assoc _ _ _ @ linear_category_comult_coalgebra_mor x).
      }
      apply assoc'.

    - cbn.
      unfold dialgebra_disp_tensor_op.
      cbn.
      rewrite ! id_left.

      etrans. {
        rewrite assoc'.
        apply maponpaths.
        apply pathsinv0.
        apply (tensor_mon_functor_tensor (_ ,, lax_monoidal_from_symmetric_monoidal_comonad _ bang) hx hx).
      }

      do 2 rewrite assoc.
      apply maponpaths_2.
      refine (! tensor_comp_mor _ _ _ _ @ _ @ tensor_comp_mor _ _ _ _).
      use two_arg_paths ; exact (! pr22 xx).
    - apply yank.
  Qed.

  Definition comonoid_in_eilenberg_moore_from_coalg
    : comonoid EM.
  Proof.
    use (make_comonoid_in_eilenberg_moore L).
    - exact (_ ,, transport_comonoid_from_free L xx).
    - exact hx.
    - exact (pr12 xx).
    - exact (pr22 xx).
    - exact comonoid_in_eilenberg_moore_from_coalg_comult_alg_mor.
    - exact comonoid_in_eilenberg_moore_from_coalg_counit_alg_mor.
  Defined.

End ConstructionOfComonoidsInEilenbergMoore.

Section EilenbergMooreCartesian.

  Context (L : linear_category).

  (* naturality of the comultiplication and counit *)
  Lemma comonoid_mor_in_eilenberg_moore
    {x y : (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L))}
    (f : _⟦x, y⟧)
    : comonoid_mor_struct
         (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L))
         (comonoid_in_eilenberg_moore_from_coalg L x)
         (comonoid_in_eilenberg_moore_from_coalg L y)
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

  (* Unfortunately, I'm unable to clean up this lemma.
     If I do this, I will have to do some manipulation in
     definition linear_category_eilenberg_moore_cartesian.
     The purpose of this lemma is to avoid having to prove this property in that definition.
   *)
  Local Lemma aux
    (x y : @sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L))
    :
    identity (pr11 x ⊗ pr11 y)
      · (pr21 x #⊗ pr21 y)
      · fmonoidal_preservestensordata
      (lax_monoidal_from_symmetric_monoidal_comonad _ (linear_category_bang L))
      (pr11 x) (pr11 y)
      · linear_category_comult L (pr11 x ⊗ pr11 y)
      · ε (linear_category_bang L) (pr11 x ⊗ pr11 y) #⊗ ε (linear_category_bang L) (pr11 x ⊗ pr11 y)
    = rightwhiskering_on_morphisms (pr1 L) (pr11 y) _ _
        (pr21 x · linear_category_comult L (pr11 x) · ε (linear_category_bang L) (pr11 x) #⊗ ε (linear_category_bang L) (pr11 x))
        · leftwhiskering_on_morphisms (pr1 L) (pr11 x ⊗ pr11 x) _ _
        (pr21 y · linear_category_comult L (pr11 y)
           · ε (linear_category_bang L) (pr11 y) #⊗ ε (linear_category_bang L) (pr11 y))
  · pr11 (inner_swap sym_monoidal_cat_co_eilenberg_moore x x y y).
  Proof.
    Opaque SymmetricDiagonal.inner_swap. (* I do not include the file SymmetricDiagonal because this is the only place I use it *)

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
        refine (_ @ id_right _).
        apply (symmetric_monoidal_comonad_extra_laws _ (linear_category_bang L)).
      }
      apply maponpaths_2.
      refine (_ @ id_right _).
      apply (symmetric_monoidal_comonad_extra_laws _ (linear_category_bang L)).
    }
    rewrite ! tensor_comp_mor.
    rewrite ! assoc.
    apply maponpaths_2.
    refine (linear_category_comult_preserves_tensor (pr11 x) (pr11 y) @ _).
    apply assoc.
  Qed.

  Definition linear_category_eilenberg_moore_cartesian
    : is_cartesian (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L)).
  Proof.
    use symm_monoidal_is_cartesian_from_comonoid.
    - intro ; apply comonoid_in_eilenberg_moore_from_coalg.
    - intro ; intros ; apply comonoid_mor_in_eilenberg_moore.
    - abstract (
          use eq_mor_co_eilenberg_moore;
          refine (assoc' _ _ _ @ _);
          refine (id_left _ @ _);
          apply linear_category_counit_preserves_unit).
    - intros x y.
      use eq_mor_co_eilenberg_moore.
      apply aux.
  Qed.

End EilenbergMooreCartesian.

Section LinearToLNL.

  Context (L : linear_category).

  Local Definition em_projection
    : fmonoidal
        sym_monoidal_cat_co_eilenberg_moore
        L
        (left_adjoint (eilenberg_moore_cmd_adj L)).
  Proof.
    use comp_fmonoidal.
    - apply mon_cat_co_eilenberg_moore_base.
    - apply projection_fmonoidal.
    - apply projection_fmonoidal.
  Defined.

  Local Lemma em_projection_is_symmetric
    : is_symmetric_monoidal_functor sym_monoidal_cat_co_eilenberg_moore L em_projection.
  Proof.
    intros x y.
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
  Qed.

  Definition linear_to_lnl
    : linear_non_linear_model.
  Proof.
    use make_linear_non_linear_from_strong.
    - exact (linear_category_data_to_sym_mon_closed_cat L).
    - exact (@sym_monoidal_cat_co_eilenberg_moore _ _ _ (linear_category_bang L)).
    - apply eilenberg_moore_cmd_adj.
    - apply linear_category_eilenberg_moore_cartesian.
    - exact em_projection.
    - exact em_projection_is_symmetric.
  Defined.

End LinearToLNL.
