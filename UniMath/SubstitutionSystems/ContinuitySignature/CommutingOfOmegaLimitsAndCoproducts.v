Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Require Import UniMath.SubstitutionSystems.ContinuitySignature.GeneralLemmas.

Local Open Scope cat.

Section OmegaLimitsCommutingWithCoproducts.

  (* We ask for the canonical morphism from canonical : ∐ ω-lim -> ω-lim ∐ to be an isomorphism. *)
  Context (C : category).

  Context (ω_lim_given : Lims_of_shape conat_graph C).
  Context {I : UU} (Iset : isaset I).
  Context (coproducts_given : Coproducts I C).

  Context (ind : I → cochain C).

  Let coproduct_n (n : nat) : Coproduct I C (λ i, dob (ind i) n) := coproducts_given (λ i, dob (ind i) n).

  Definition coproduct_n_cochain : cochain C.
  Proof.
    exists (λ n, coproduct_n n).
    intros n m f.
    use CoproductArrow.
    exact (λ j, dmor (ind j) f · CoproductIn I C (coproducts_given (λ i0 : I, dob (ind i0) m)) j).
  Defined.

  Definition limit_of_coproduct : LimCone coproduct_n_cochain
    := ω_lim_given coproduct_n_cochain.

  Definition coproduct_of_limit : Coproduct I C (λ i : I, lim (ω_lim_given (ind i)))
    := coproducts_given (λ i, lim (ω_lim_given (ind i))).

  Definition limit_of_coproduct_as_cone_of_coproduct_to_limit
    : cone coproduct_n_cochain coproduct_of_limit.
  Proof.
    use tpair.
    - intro n.
      use CoproductOfArrows.
      exact (λ i, coneOut (limCone (ω_lim_given (ind i))) n).
    - intros n m p.
      cbn.
      etrans.
      1: apply precompWithCoproductArrow.
      use CoproductArrowUnique.
      intro i.
      etrans.
      1: apply (CoproductInCommutes _ _ _ coproduct_of_limit _ (λ i0 : I, coneOut (limCone (ω_lim_given (ind i0))) n · (dmor (ind i0) p · CoproductIn I C (coproducts_given (λ i1 : I, dob (ind i1) m)) i0))).
      etrans.
      1: apply assoc.
      apply maponpaths_2.
      exact (coneOutCommutes (limCone (ω_lim_given (ind i))) n m p).
  Defined.

  Definition coproduct_of_limit_to_limit_of_coproduct
    : coproduct_of_limit --> lim limit_of_coproduct
    := pr11 (isLimCone_LimCone limit_of_coproduct _ limit_of_coproduct_as_cone_of_coproduct_to_limit).

  Definition coproduct_distribute_over_omega_limits : UU
    := is_z_isomorphism coproduct_of_limit_to_limit_of_coproduct.

End OmegaLimitsCommutingWithCoproducts.

Definition ω_limits_distribute_over_I_coproducts
           (C : category) (I : HSET)
           (ω_lim : Lims_of_shape conat_graph C)
           (coprd : Coproducts (pr1 I) C)
  : UU := ∏ ind, coproduct_distribute_over_omega_limits C ω_lim coprd ind.

(*
A coproducts of omega-continuous functors is in general not omega-continuous.
This boils down to the commutativity of ω-limits and coproducts.
*)
Section CoproductOfFunctorsContinuity.

  Context (D : category) (I : HSET) (ω_lim : Lims_of_shape conat_graph D) (CP : Coproducts (pr1 I) D).

  Definition ω_complete_functor_cat (C : category) : Lims_of_shape conat_graph [C, D].
  Proof.
    apply LimsFunctorCategory_of_shape, ω_lim.
  Defined.

  Let coproduct_functor_cat (C : category) : Coproducts (pr1 I) [C,D]
    := Coproducts_functor_precat (pr1 I) C D CP.

  Definition functor_category_ω_limits_distribute_over_I_coproducts
    : ω_limits_distribute_over_I_coproducts D I ω_lim CP
      -> ∏ C : category, ω_limits_distribute_over_I_coproducts [C,D] I (ω_complete_functor_cat C) (coproduct_functor_cat C).
  Proof.
    intros distr C ind.
    use nat_trafo_z_iso_if_pointwise_z_iso.
    intro c.

    transparent assert (ind_c : (pr1 I -> cochain D)).
    {
      intro i.
      exists (λ n, pr1 (dob (ind i) n) c).
      exact (λ n m p, pr1 (dmor (ind i) p) c).
    }

    exists (pr1 (distr ind_c)).
    split.
    - refine (_ @ pr12 (distr ind_c)).
      apply maponpaths_2.
      use limArrowUnique ; intro.
      use CoproductArrowUnique ; intro.
      etrans.
      1: {
        apply maponpaths.
        apply (limArrowCommutes (ω_lim (diagram_pointwise (coproduct_n_cochain [C, D] (coproduct_functor_cat C) ind) c))).
      }
      apply (CoproductInCommutes _ _ _ (CP (λ i0 : pr1 I, lim (ω_lim (ind_c i0))))).
    - refine (_ @ pr22 (distr ind_c)).
      apply maponpaths.
      use limArrowUnique ; intro.
      use CoproductArrowUnique ; intro.
      etrans.
      1: {
        apply maponpaths.
        apply (limArrowCommutes (ω_lim (diagram_pointwise (coproduct_n_cochain [C, D] (coproduct_functor_cat C) ind) c))).
      }
      apply (CoproductInCommutes _ _ _ (CP (λ i0 : pr1 I, lim (ω_lim (ind_c i0))))).
  Defined.


  Definition coproduct_of_functors_omega_cont
             (C : category)
             (F : (pr1 I) → C ⟶ D)
             (ω_distr : ω_limits_distribute_over_I_coproducts D I ω_lim CP)
    : (∏ i : pr1 I, is_omega_cont (F i)) -> is_omega_cont (coproduct_of_functors _ _ _ CP F).
  Proof.
    intro Fi_cont.
    intros coch l l_cone l_lim.

    use Limits.is_z_iso_isLim.
    { apply ω_lim. }

    transparent assert (ind : (pr1 I -> cochain D)).
    {
      intro i.
      exists (λ n, F i (dob coch n)).
      exact (λ n m p, #(F i) (dmor coch p)).
    }

    set (distr := ω_distr ind).
    set (distr1 := pr1 distr).
    unfold limit_of_coproduct in distr1.
    unfold coproduct_of_limit in distr1.

    use make_is_z_isomorphism.
    - refine (distr1 · _).
      use CoproductOfArrows.
      intro i.
      set (Fi_l := Fi_cont i coch l l_cone l_lim).
      apply (pr1 (isLim_is_z_iso _ _ _ _ Fi_l)).
      (* apply (Fi_l (pr11 (ω_lim (ind i))) (pr21 (ω_lim (ind i)))). *)
    - split.
      + cbn.

        transparent assert (i_iso : (is_z_isomorphism (CoproductOfArrows (pr1 I) D (CP (λ i : pr1 I, lim (ω_lim (ind i)))) (CP (λ i : pr1 I, F i l)) (λ i : pr1 I, limArrow (make_LimCone (mapdiagram (F i) coch) (F i l) (mapcone (F i) coch l_cone) (Fi_cont i coch l l_cone l_lim)) (lim (ω_lim (ind i))) (limCone (ω_lim (ind i))))))).
        {
          use CoproductOfArrowsIsos.
          intro i.
          set (Fi_l := Fi_cont i coch l l_cone l_lim).
          apply (pr2 (z_iso_inv (_ ,, isLim_is_z_iso _ _ _ _ Fi_l))).
        }

        etrans.
        1: apply assoc.
        use (z_iso_inv_to_right _ _ _ _ (_ ,, i_iso)).
        etrans.
        2: apply pathsinv0, id_left.
        use CoproductArrowUnique.
        intro i.
        cbn.
        etrans.
        1: apply assoc.
        etrans.
        1: apply maponpaths_2, postCompWithLimArrow.

        use (z_iso_inv_to_right _ _ _ _ (distr1 ,, _)).
        {
          unfold coproduct_distribute_over_omega_limits in distr.
          apply (pr2 (z_iso_inv (_,,distr))).
        }
        apply pathsinv0, limArrowUnique.
        intro n.
        cbn.

        etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          set (t := limArrowCommutes (ω_lim (mapdiagram (coproduct_of_functors (pr1 I) C D CP F) coch))).
          exact (t (pr11 (CP (λ i0 : pr1 I, lim (ω_lim (ind i0))))) (limit_of_coproduct_as_cone_of_coproduct_to_limit D ω_lim CP ind) n).
        }

        cbn.
        unfold CoproductOfArrows.
        etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply (CoproductInCommutes _ _ _  (CP (λ i0 : pr1 I, lim (ω_lim (ind i0))))).
        }

        etrans.
        2: apply pathsinv0, (CoproductInCommutes _ _ _  (CP (λ j : pr1 I, F j l))).
        etrans.
        1: apply assoc.

        apply maponpaths_2.
        exact (limArrowCommutes (ω_lim (ind i))  (F i l) (mapcone (F i) coch l_cone) n).
      + cbn.
        etrans.
        1: apply assoc'.
        apply pathsinv0.
        use (z_iso_inv_to_left _ _ _ (_,,_)).
        {
          unfold coproduct_distribute_over_omega_limits in distr.
          apply (pr2 (z_iso_inv (_,,distr))).
        }
        etrans.
        1: apply id_right.

        apply pathsinv0.
        use limArrowUnique.
        intro n.

        etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply (limArrowCommutes  (ω_lim (mapdiagram (coproduct_of_functors (pr1 I) C D CP F) coch))).
        }

        etrans.
        1: apply CoproductOfArrows_comp.
        use CoproductArrowUnique.
        intro i.

        etrans.
        1: apply (CoproductInCommutes _ _ _  (CP (λ i0 : pr1 I, lim (ω_lim (ind i0))))).
        apply maponpaths_2.

        exact (limArrowCommutes ( (make_LimCone (mapdiagram (F i) coch) (F i l) (mapcone (F i) coch l_cone) (Fi_cont i coch l l_cone l_lim))) _ (limCone (ω_lim (ind i))) n).
  Defined.


End CoproductOfFunctorsContinuity.
