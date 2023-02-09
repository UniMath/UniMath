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
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Require Import UniMath.SubstitutionSystems.ContinuitySignature.GeneralLemmas.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.

Local Open Scope cat.

(*
The following lemmas has to be moved accordingly,
e.g. in the file CategoryTheory.Chains.Omegacontfunctors
 *)

Lemma nat_trans_preserve_cone
      {A B : category}
      {F G : functor A B}
      (α : nat_trans F G)
      {coch : cochain A}
      {b : B} (b_con : cone (mapdiagram F coch) b)
  : cone (mapdiagram G coch) b.
Proof.
  exists (λ v, pr1 b_con v · α (dob coch v)).
  intros u v p.
  etrans.
  1: apply assoc'.
  cbn.
  etrans.
  1: apply maponpaths, pathsinv0, (pr2 α).
  etrans.
  1: apply assoc.
  apply maponpaths_2.
  exact (pr2 b_con u v p).
Defined.

Lemma nat_z_iso_preserve_ωlimits {A B : category}
      (F G : functor A B)
  : is_omega_cont F -> nat_z_iso F G -> is_omega_cont G.
Proof.
  (* This lemma should be split up in data and property and there is also a repeat of proof, need a more "general, but easy" lemma.
 *)
  intros Fc i.
  intros coch a a_con a_lim.
  intros b b_con.
  set (b'_con := nat_trans_preserve_cone (nat_z_iso_inv i) b_con).
  set (t := Fc coch a a_con a_lim b b'_con).
  use tpair.
  - exists (pr11 t · pr1 i a).
    intro v.
    etrans.
    1: apply assoc'.
    etrans.
    1: apply maponpaths, pathsinv0, (pr21 i).
    etrans.
    1: apply assoc.
    etrans.
    1: apply maponpaths_2, (pr21 t v).
    etrans.
    1: apply assoc'.
    etrans.
    1: apply maponpaths, (pr2 i (dob coch v)).
    apply id_right.
  - intro f.
    use total2_paths_f.
    + use (cancel_z_iso _ _ (_ ,, pr2 (nat_z_iso_inv i) a)).
      etrans.
      2: apply assoc.
      etrans.
      2: apply maponpaths, pathsinv0, (pr2 (pr2 i a)).
      etrans.
      2: apply pathsinv0, id_right.

      transparent assert (c' : (∑ x : B ⟦ b, F a ⟧, limits.is_cone_mor b'_con (limits.mapcone F coch a_con) x)).
      {
        exists (pr1 f · pr1 (pr2 i a)).
        intro v.
        cbn.
        etrans.
        1: apply assoc'.
        etrans.
        1: apply maponpaths, pathsinv0, (pr21 (nat_z_iso_inv i)).
        etrans.
        1: apply assoc.
        apply maponpaths_2, (pr2 f v).
      }

      exact (base_paths _ _ (pr2 t c')).
    + apply (impred_isaprop) ; intro ; apply homset_property.
Defined.

Definition LimFunctor_is_pointwise_Lim:
  ∏ (A C : category) (g : graph) (D : diagram g [A, C]),
    (∏ a : A, LimCone (diagram_pointwise D a))
    → ∏ (X : [A, C]) (R : cone D X),
    isLimCone D X R
    → ∏ a : A, LimCone (diagram_pointwise D a)
  := λ A C g D la F F_cone F_lim a, make_LimCone _ _ _ (isLimFunctor_is_pointwise_Lim D la F F_cone F_lim a).

Definition LimFunctor_is_pointwise_Lim':
  ∏ (A C : category) (g : graph) (D : diagram g [A, C]),
    (∏ a : A, LimCone (diagram_pointwise D a))
    → LimCone D → ∏ a : A, LimCone (diagram_pointwise D a)
  := λ A C g D la F_l, LimFunctor_is_pointwise_Lim _ _ _ _ la _ _ (pr2 F_l).

Section OmegaContinuityOfSignatureFunctor.

  Variables (sort : UU) (Hsort : isofhlevel 3 sort) (C : category).
  Variables (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

  (** Define the discrete category of sorts *)
  Let sort_cat : category := path_pregroupoid sort Hsort.

  (** This represents "sort → C" *)
  Let sortToC : category := [sort_cat,C].
  Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

  Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.
  Let BPC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

  Lemma sortToC_hasbinproducts
    : BinProducts [sortToC, sortToC].
  Proof.
    repeat (apply BinProducts_functor_precat) ; exact BP.
  Defined.

  Lemma sortToC_hascoproducts
    : ∏ I : UU, isaset I -> Coproducts I [sortToC, sortToC].
  Proof.
    intros I Iset.
    repeat (apply Coproducts_functor_precat) ; exact (CC I Iset).
  Defined.

  Definition hat_exp_functor_list'_piece
             (xst : (list sort × sort) × sort)
    : functor [sortToC,sortToC] [sortToC,sortToC].
  Proof.
    induction xst as [[si s] t].
    set (op_f := option_list sort Hsort C TC BC CC si).
    refine (functor_composite (pre_comp_functor op_f) _).
    set (prs := projSortToC sort Hsort C s).
    set (hatt := hat_functor sort Hsort C CC t).
    set (prshatt := functor_composite prs hatt).
    exact (post_comp_functor prshatt).
  Defined.

  Definition hat_exp_functor_list'
             (xst : list (list sort × sort) × sort)
    : functor [sortToC,sortToC] [sortToC,sortToC].
  Proof.
    induction xst as [a t].
    (* a := [a1,...,am]
       Each ai := ([si_1, ... si_n],si)
     *)

    set (T := constant_functor [sortToC,sortToC] [sortToC,C]
                               (constant_functor sortToC C TC)).
    set (TT := (functor_composite T (post_comp_functor (hat_functor sort Hsort C CC t)))).

    use (list_ind _ _ _ a).
    - exact TT.
    - intros ap ap1 ap_func.
      use (BinProduct_of_functors _ ap_func (hat_exp_functor_list'_piece (ap,,t))).
      repeat (apply BinProducts_functor_precat) ; exact BP.
  Defined.

  Definition hat_exp_functor_list'_test
             (xst : list (list sort × sort) × sort)
    : nat_z_iso (hat_exp_functor_list sort Hsort C TC BP BC CC xst)
                (hat_exp_functor_list' xst).
  Proof.
    induction xst as [a t] ; revert a.
    use list_ind.
    - use tpair.
      + apply (nat_trans_id (C := [sortToC,sortToC]) (C' := [sortToC,sortToC])).
      + intro ; apply (identity_is_z_iso (C := [sortToC,sortToC])).
    - intros x xs IHn.
      use make_nat_z_iso.
      + use make_nat_trans.
        * intro F.
          use make_nat_trans.
          -- intro G.
             use make_nat_trans.
             ++ intro H.
                assert (p :  pr1 (pr1 (hat_exp_functor_list' (cons x xs,, t) F) G) H = pr1 (pr1 (pr1 (BinProduct_of_functors sortToC_hasbinproducts (hat_exp_functor_list' (xs,, t)) (hat_exp_functor_list'_piece (x,,t))) F) G) H).
                {
                  apply idpath.
                }

                refine (_ · Univalence.idtoiso (! p)).
                clear p.

                unfold hat_exp_functor_list.
                (* pr1 (pr1 (IHn F) G) H *)
                admit.
             ++ intros H1 H2 α.
                admit.
          -- intros G1 G2 α.
             use nat_trans_eq.
             { apply homset_property. }
             intro H.
             admit.
        * intros F1 F2 α.
          use nat_trans_eq.
          { apply homset_property. }
          intro G.
          use nat_trans_eq.
          { apply homset_property. }
          admit.
      + intro F.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        intro G.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        intro H.
        use make_is_z_isomorphism.
        * admit.
        * split ; admit.
  Admitted.

  Lemma MultiSortedSigToFunctor' (M : MultiSortedSig sort) :
    functor [sortToC,sortToC] [sortToC,sortToC].
  Proof.
    use (coproduct_of_functors (ops sort M)).
    + apply Coproducts_functor_precat, Coproducts_functor_precat, CC, setproperty.
    + intros op.
      exact (hat_exp_functor_list' (arity sort M op)).
  Defined.

  Definition MultiSortedSigToFunctor_test
       (M : MultiSortedSig sort)
    : nat_z_iso (MultiSortedSigToFunctor sort Hsort C TC BP BC CC M)
                (MultiSortedSigToFunctor' M).
  Proof.
    use coproduct_of_functors_nat_z_iso.
    intro i.
    apply hat_exp_functor_list'_test.
  Defined.

  Variable (LC : ∏ coch : cochain C, LimCone coch).
  Variable (distr : ∏ I : HSET, ω_limits_distribute_over_I_coproducts C I LC (CC (pr1 I) (pr2 I))).

  (* Should also be split up into multiple definitions/lemmas *)
  Lemma post_comp_with_pr_and_hat_is_omega_cont (s t : sort)
    :  is_omega_cont (post_comp_functor
                        (A := sortToC)
                        (projSortToC sort Hsort C s ∙ hat_functor sort Hsort C CC t)
                     ).
  Proof.
    intros coch L con isLimcon.

    apply limits.pointwise_Lim_is_isLimFunctor ; intro F.
    apply limits.pointwise_Lim_is_isLimFunctor ; intro G.

    use limits.is_z_iso_isLim.
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

      set (LF_lim := limits.isLimFunctor_is_pointwise_Lim coch bla _ _ isLimcon F).
      set (LFs_lim := limits.isLimFunctor_is_pointwise_Lim _ bla' _ _ LF_lim s).
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
        apply (graphs.limits.limArrowCommutes (LC (x p))).
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
                  (post_comp_functor (projSortToC sort Hsort C s ∙ hat_functor sort Hsort C CC t))
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
        apply (graphs.limits.limArrowCommutes (LC (x p))).
  Defined.

  (* In case no constructors were given, i.e. just H := Id. *)
  Lemma pre_comp_option_list_omega_cont
        (xst : (list sort × sort) × sort)
    : is_omega_cont (pre_comp_functor (C := sortToC) (option_list sort Hsort C TC BC CC (pr11 xst))).
  Proof.
  Admitted.

  Lemma is_omega_cont_hat_exp_functor_list_piece
  (xst : (list sort × sort) × sort)
    :  is_omega_cont (hat_exp_functor_list'_piece xst).
  Proof.
    apply is_omega_cont_functor_composite.
    - exact (pre_comp_option_list_omega_cont xst).
    - exact (post_comp_with_pr_and_hat_is_omega_cont (pr21 xst) (pr2 xst)).
  Defined.

  Lemma is_omega_cont_hat_exp_functor_list
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
      + apply is_omega_cont_hat_exp_functor_list_piece.
  Defined.

  (** The functor obtained from a multisorted binding signature is omega-continuous *)
  Lemma is_omega_cont_MultiSortedSigToFunctor' (M : MultiSortedSig sort)
        (ω_distr : ω_limits_distribute_over_I_coproducts C (ops sort M) LC (CC (ops sort M) (setproperty (ops sort M))))
    : is_omega_cont (MultiSortedSigToFunctor' M).
  Proof.
    (* The following lemma/definition already existed, so
       I have done the work of commuting with limits
       in a sense for nothing ..
     *)
    (* apply is_omega_cont_coproduct_of_functors.
    - intro ; apply is_omega_cont_hat_exp_functor_list.
    - admit. *)

    use coproduct_of_functors_omega_cont.
    - do 2 apply ω_complete_functor_cat ; exact LC.
    - do 2 apply functor_category_ω_limits_distribute_over_I_coproducts ; exact ω_distr.
    - intro ; apply is_omega_cont_hat_exp_functor_list.
  Defined.

  (** The functor obtained from a multisorted binding signature is omega-continuous *)
  Lemma is_omega_cont_MultiSortedSigToFunctor (M : MultiSortedSig sort)
        (ω_distr : ω_limits_distribute_over_I_coproducts C (ops sort M) LC (CC (ops sort M) (setproperty (ops sort M))))
    : is_omega_cont (MultiSortedSigToFunctor sort Hsort C TC BP BC CC M).
  Proof.
    use nat_z_iso_preserve_ωlimits.
    3: exact (nat_z_iso_inv (MultiSortedSigToFunctor_test M)).
    apply (is_omega_cont_MultiSortedSigToFunctor' M) ; exact ω_distr.
  Defined.

End OmegaContinuityOfSignatureFunctor.
