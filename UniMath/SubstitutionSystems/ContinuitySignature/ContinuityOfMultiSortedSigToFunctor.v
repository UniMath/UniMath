(* - Proof that the functor obtained from a multisorted binding signature
  is omega-cocontinuous ([is_omega_cont_MultiSortedSigToFunctor]) *)

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
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require UniMath.SubstitutionSystems.SortIndexing.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Require Import UniMath.SubstitutionSystems.ContinuitySignature.GeneralLemmas.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.


Local Open Scope cat.

Section FixTheContext.

  Context (sort : UU) (Hsort : isofhlevel 3 sort) (C : category)
          (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (* (PC : forall (I : UU), Products I C) *) (eqsetPC : forall (s s' : sort), Products (s=s') C)
          (CC : forall (I : UU), isaset I → Coproducts I C).

  (** Define the discrete category of sorts *)
  Let sort_cat : category := path_pregroupoid sort Hsort.

  (** This represents "sort → C" *)
  Let sortToC : category := SortIndexing.sortToC sort Hsort C.

  Let sortToCC : category := SortIndexing.sortToCC sort Hsort C.
  Let TsortToCC : Terminal sortToCC := SortIndexing.TsortToCC sort Hsort C TC.

  Let sortToC2 : category := SortIndexing.sortToC2 sort Hsort C.

  Local Definition BPsortToC2 : BinProducts sortToC2 := SortIndexing.BPsortToC2 sort Hsort _ BP.

  Let projSortToC : sort -> sortToCC := projSortToC sort Hsort C.
  Let hat_functorC : sort -> C ⟶ sortToC := hat_functor sort Hsort C CC.

  Section DefinitionOfMultiSortedSigToFunctorPrime.

  Definition hat_exp_functor_list'_piece
             (xt : (list sort × sort) × sort)
    : functor sortToC2 sortToC2.
  Proof.
    induction xt as [[si s] t].
    set (op_f := option_list sort Hsort C TC BC CC si).
    refine (functor_composite (pre_comp_functor op_f) _).
    set (prs := projSortToC s).
    set (hatt := hat_functorC t).
    set (prshatt := functor_composite prs hatt).
    exact (post_comp_functor prshatt).
  Defined.

  Definition hat_exp_functor_list'
             (xst : list (list sort × sort) × sort)
    : functor sortToC2 sortToC2.
  Proof.
    induction xst as [a t].
    (* a := [a1,...,am]
       Each ai := ([si_1, ... si_n],si)
     *)

    set (T := constant_functor sortToC2 sortToCC TsortToCC).
    set (TT := (functor_composite T (post_comp_functor (hat_functorC t)))).

    use (list_ind _ _ _ a).
    - exact TT.
    - intros ap ap1 ap_func.
      use (BinProduct_of_functors _ ap_func (hat_exp_functor_list'_piece (ap,,t))).
      repeat (apply BinProducts_functor_precat) ; exact BP.
  Defined.

(** optimized version that does not introduce the terminal element in the singleton case: *)
  Definition hat_exp_functor_list'_optimized
             (xst : list (list sort × sort) × sort)
    : functor sortToC2 sortToC2.
  Proof.
    induction xst as [xs t].
    set (T := constant_functor sortToC2 sortToCC TsortToCC).
    set (TT := (functor_composite T (post_comp_functor (hat_functorC t)))).
    set (HH := fun ap => (hat_exp_functor_list'_piece (ap,,t))).
    exact (foldr1_map (λ F G, BinProduct_of_functors BPsortToC2 F G) TT HH xs).
  Defined.

  Definition MultiSortedSigToFunctor' (M : MultiSortedSig sort) :
    functor sortToC2 sortToC2.
  Proof.
    use (coproduct_of_functors (ops sort M)).
    + apply Coproducts_functor_precat, Coproducts_functor_precat, CC, setproperty.
    + intros op.
      exact (hat_exp_functor_list'_optimized (arity sort M op)).
  Defined.

  End DefinitionOfMultiSortedSigToFunctorPrime.

  (** * the following is a deviation from the main topic of this file *)
  Section OmegaCocontinuityOfMultiSortedSigToFunctorPrime.

    Context (EsortToC2 : Exponentials BPsortToC2) (** this requires exponentials in a higher space than before *)
      (HC : Colims_of_shape nat_graph C).

    Local Lemma is_omega_cocont_hat_exp_functor_list'_piece  (xt : (list sort × sort) × sort) :
      is_omega_cocont (hat_exp_functor_list'_piece xt).
    Proof.
      apply is_omega_cocont_functor_composite.
      - apply is_omega_cocont_pre_composition_functor.
        apply (ColimsFunctorCategory_of_shape nat_graph sort_cat _ HC).
      - use is_omega_cocont_post_composition_functor.
        apply is_left_adjoint_functor_composite.
        + apply MultiSorted_alt.is_left_adjoint_projSortToC, eqsetPC.
        + apply MultiSorted_alt.is_left_adjoint_hat.
    Defined.

    Local Lemma is_omega_cocont_hat_exp_functor_list' (xst : list (list sort × sort) × sort) :
      is_omega_cocont (hat_exp_functor_list' xst).
    Proof.
      induction xst as [xs t].
      revert t.
      use (list_ind (fun xs => ∏ t : sort, is_omega_cocont (hat_exp_functor_list' (xs,, t))) _ _ xs).
      - intro t.
        apply is_omega_cocont_functor_composite.
        + apply is_omega_cocont_constant_functor.
        + apply is_omega_cocont_post_composition_functor, MultiSorted_alt.is_left_adjoint_hat.
      - intros ap ap1 ap_func t.
        apply is_omega_cocont_BinProduct_of_functors.
        * apply BinProducts_functor_precat, BinProducts_functor_precat, BP.
        * apply is_omega_cocont_constprod_functor1.
          apply EsortToC2.
        * apply (ap_func t).
        * apply is_omega_cocont_hat_exp_functor_list'_piece.
    Defined.

    Local Lemma is_omega_cocont_hat_exp_functor_list'_optimized (xst : list (list sort × sort) × sort) :
      is_omega_cocont (hat_exp_functor_list'_optimized xst).
    Proof.
      induction xst as [xs t].
      refine (foldr1_map_ind_nodep _ _ _ is_omega_cocont _ _ _ xs).
      - apply is_omega_cocont_functor_composite.
        + apply is_omega_cocont_constant_functor.
        + apply is_omega_cocont_post_composition_functor, MultiSorted_alt.is_left_adjoint_hat.
      - intro lt. apply is_omega_cocont_hat_exp_functor_list'_piece.
      - intros lt F Hyp.
        apply is_omega_cocont_BinProduct_of_functors.
        + apply BPsortToC2.
        + apply is_omega_cocont_constprod_functor1.
          apply EsortToC2.
        + apply is_omega_cocont_hat_exp_functor_list'_piece.
        + exact Hyp.
    Defined.

    Lemma is_omega_cocont_MultiSortedSigToFunctor' (M : MultiSortedSig sort) :
      is_omega_cocont (MultiSortedSigToFunctor' M).
    Proof.
      apply is_omega_cocont_coproduct_of_functors.
      intros op; apply is_omega_cocont_hat_exp_functor_list'_optimized.
    Defined.

  End OmegaCocontinuityOfMultiSortedSigToFunctorPrime.

  Section OmegaContinuityOfMultiSortedSigToFunctorPrime.

  Context (LC : Lims_of_shape conat_graph C)
          (distr : ∏ I : HSET, ω_limits_distribute_over_I_coproducts C I LC (CC (pr1 I) (pr2 I))).

  (* Should also be split up into multiple definitions/lemmas *)
  Lemma post_comp_with_pr_and_hat_is_omega_cont (s t : sort)
    :  is_omega_cont (post_comp_functor
                        (A := sortToC)
                        (projSortToC s ∙ hat_functorC t)
                     ).
  Proof.
    intros coch L con isLimcon.

    apply Limits.pointwise_Lim_is_isLimFunctor ; intro F.
    apply Limits.pointwise_Lim_is_isLimFunctor ; intro G.

    use Limits.is_z_iso_isLim.
    { apply LC. }

    transparent assert (x : (t = G → cochain C)).
    {
      intro p.
      use tpair.
      - intro n.
        exact (pr1 (pr1 (dob coch n) F) s).
      - intros n m q.
        exact (pr1 (pr1 (dmor coch q) F) s).
    }

    use make_is_z_isomorphism.
    - refine (pr1 (distr (_,,Hsort t G) x) · _).

      assert (bla : (∏ a : sortToC, LimCone (diagram_pointwise coch a))).
      { intro ; apply ω_complete_functor_cat ; exact LC. }

      assert (bla' : (∏ a : path_pregroupoid sort Hsort, LimCone (diagram_pointwise (diagram_pointwise coch F) a))).
      { intro ; apply LC. }

      set (LF_lim := Limits.isLimFunctor_is_pointwise_Lim coch bla _ _ isLimcon F).
      set (LFs_lim := Limits.isLimFunctor_is_pointwise_Lim _ bla' _ _ LF_lim s).
      set (LFs_cone := make_LimCone _ _ _ LFs_lim).

      use CoproductOfArrows.
      intro i.

      (* The following proof "justifies" the exact statement *)
      (* assert (diagram_pointwise (diagram_pointwise coch F) s = x i).
         { apply idpath. } *)

      exact (pr1 (z_iso_inv (z_iso_from_lim_to_lim LFs_cone (LC (x i))))).
    - split.
      + etrans.
        1: apply assoc.
        use (z_iso_inv_to_right _ _ _ _ (_ ,, CoproductOfArrowsIsos  _ _ _ _ _ _ _ _: z_iso _ _)).
        { intro ; apply (pr2 (z_iso_inv _)). }
        rewrite ! id_left.

        use (z_iso_inv_to_right _ _ _ _ (z_iso_inv (make_z_iso _ _ (pr2 (distr _ _))))).
        apply pathsinv0, limArrowUnique.
        intro n.

        rewrite assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply limArrowCommutes.
        }


        etrans.
        1: { apply precompWithCoproductArrow. }

        cbn.
        unfold CoproductOfArrows.
        apply maponpaths.
        apply funextsec ; intro p.
        rewrite ! assoc.
        apply maponpaths_2.
        apply (Graphs.Limits.limArrowCommutes (LC (x p))).
      + etrans.
        1: apply assoc'.
        apply pathsinv0.

        transparent assert (d_i : (is_z_isomorphism ( pr1 (distr ((t = G),, Hsort t G) x)))).
        {
          exists (coproduct_of_limit_to_limit_of_coproduct C LC (CC (t = G) (Hsort t G)) x).
          set (q := distr ((t = G),, Hsort t G) x).
          split ; apply (pr2 q).
        }

        use (z_iso_inv_to_left _ _ _ (_,,d_i)).
        refine (id_right _ @ _).
        use (z_iso_inv_to_left _ _ _ (CoproductOfArrows _ _ _ _ _,, _ : z_iso _ _)).
        {
          use CoproductOfArrowsIsos ; intro.
          apply is_z_iso_inv_from_z_iso.
        }
        apply limArrowUnique.
        intro n.

        etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply (limArrowCommutes  (LC
         (diagram_pointwise
            (diagram_pointwise
               (mapdiagram
                  (post_comp_functor (projSortToC s ∙ hat_functorC t))
                  coch) F) G))).
        }
        etrans.
        1: { apply precompWithCoproductArrow. }

        cbn.
        unfold CoproductOfArrows.
        apply maponpaths.
        apply funextsec ; intro p.
        rewrite ! assoc.
        apply maponpaths_2.
        apply (Graphs.Limits.limArrowCommutes (LC (x p))).
  Defined.

  (* In case no constructors were given, i.e. just H := Id. *)
  Lemma pre_comp_option_list_omega_cont
        (xst : (list sort × sort) × sort)
    : is_omega_cont (pre_comp_functor (C := sortToC) (option_list sort Hsort C TC BC CC (pr11 xst))).
  Proof.
    apply is_omega_cont_pre_composition_functor'.
    intro.
    apply ω_complete_functor_cat ; exact LC.
  Defined.

  Lemma is_omega_cont_hat_exp_functor_list'_piece
  (xst : (list sort × sort) × sort)
    :  is_omega_cont (hat_exp_functor_list'_piece xst).
  Proof.
    apply is_omega_cont_functor_composite.
    - exact (pre_comp_option_list_omega_cont xst).
    - exact (post_comp_with_pr_and_hat_is_omega_cont (pr21 xst) (pr2 xst)).
  Defined.

  Lemma is_omega_cont_hat_exp_functor_list'
        (xst : list (list sort × sort) × sort) :
    is_omega_cont (hat_exp_functor_list' xst).
  Proof.
    induction xst as [a t] ; revert a.
    use list_ind.
    - use nat_z_iso_preserve_ωlimits.
      3: apply nat_z_iso_inv, constant_functor_composition_nat_z_iso.
      apply is_omega_cont_constant_functor.
    - intros x xs IHn.
      apply is_omega_cont_BinProduct_of_functors.
      + apply IHn.
      + apply is_omega_cont_hat_exp_functor_list'_piece.
  Defined.

  Lemma is_omega_cont_hat_exp_functor_list'_optimized
        (xst : list (list sort × sort) × sort) :
    is_omega_cont (hat_exp_functor_list'_optimized xst).
  Proof.
    induction xst as [xs t].
    refine (foldr1_map_ind_nodep _ _ _ is_omega_cont _ _ _ xs).
    - use nat_z_iso_preserve_ωlimits.
      3: apply nat_z_iso_inv, constant_functor_composition_nat_z_iso.
      apply is_omega_cont_constant_functor.
    - intro lt.
      apply is_omega_cont_hat_exp_functor_list'_piece.
    - intros lt F Hyp.
      apply is_omega_cont_BinProduct_of_functors.
      + apply is_omega_cont_hat_exp_functor_list'_piece.
      + exact Hyp.
  Defined.

  (** The functor obtained from a multisorted binding signature is omega-continuous *)
  Lemma is_omega_cont_MultiSortedSigToFunctor' (M : MultiSortedSig sort)
    : is_omega_cont (MultiSortedSigToFunctor' M).
  Proof.
    use coproduct_of_functors_omega_cont.
    - do 2 apply ω_complete_functor_cat ; exact LC.
    - do 2 apply functor_category_ω_limits_distribute_over_I_coproducts ; apply distr.
    - intro ; apply is_omega_cont_hat_exp_functor_list'_optimized.
  Defined.

  End OmegaContinuityOfMultiSortedSigToFunctorPrime.


End FixTheContext.
