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
(* Require Import UniMath.SubstitutionSystems.SignatureExamples. *)

Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Local Open Scope cat.

Section OmegaLimitsCommutingWithCoproducts.

  (* We ask for the canonical morphism from canonical : ∐ ω-lim -> ω-lim ∐ to be an isomorphism. *)
  Context (C : category).

  Context (ω_lim_given : ∏ (coch : cochain C), LimCone coch).
  Context {I : UU} (Iset : isaset I).
  Context (coproducts_given : Coproducts I C).

  Variable (ind : I → cochain C).

  Let coproduct_n (n : nat) := coproducts_given (λ i, pr1 (ind i) n).
  Definition coproduct_n_cochain : cochain C.
  Proof.
    exists (λ n, pr11 (coproduct_n n)).
    intros n m f.
    use CoproductArrow.
    exact (λ j, pr2 (ind j) n m f · CoproductIn I C (coproducts_given (λ i0 : I, pr1 (ind i0) m)) j).
  Defined.

  Definition limit_of_coproduct
    := ω_lim_given coproduct_n_cochain.

  Definition coproduct_of_limit
    := coproducts_given (λ i, pr11 (ω_lim_given (ind i))).

  Definition limit_of_coproduct_as_cone_of_coproduct_to_limit
    : cone coproduct_n_cochain (pr11 coproduct_of_limit).
  Proof.
    use tpair.
    - intro n.
      use CoproductOfArrows.
      exact (λ i, pr1 (pr21 (ω_lim_given (ind i))) n).
    - intros n m p.
      cbn.
      etrans.
      1: apply precompWithCoproductArrow.
      use CoproductArrowUnique.
      intro i.
      etrans.
      1: apply (CoproductInCommutes _ _ _ coproduct_of_limit _ ( (λ i0 : I, (pr121 (ω_lim_given (ind i0))) n · (pr2 (ind i0) n m p · CoproductIn I C (coproducts_given (λ i1 : I, pr1 (ind i1) m)) i0)))).
      etrans.
      1: apply assoc.
      apply maponpaths_2.
      exact (pr221 (ω_lim_given (ind i)) n m p).
  Defined.

  Definition coproduct_of_limit_to_limit_of_coproduct
    : pr11 coproduct_of_limit --> pr11 limit_of_coproduct
    := pr11 (pr2 limit_of_coproduct _ limit_of_coproduct_as_cone_of_coproduct_to_limit).

  Definition coproduct_distribute_over_omega_limits
    := is_z_isomorphism coproduct_of_limit_to_limit_of_coproduct.

End OmegaLimitsCommutingWithCoproducts.

Definition ω_limits_distribute_over_I_coproducts
           (C : category) (I : HSET)
           (ω_lim : (∏ coch : cochain C, LimCone coch))
           (coprd : Coproducts (pr1 I) C)
  : UU := ∏ ind, coproduct_distribute_over_omega_limits C ω_lim coprd ind.

Section OmegaLimitsCommutingWithCoproductsHSET.

  Definition HSET_ω_limits : ∏ coch : cochain HSET, LimCone coch.
  Proof.
    intro coch.
    apply LimConeHSET.
  Defined.

  Definition I_coproduct_distribute_over_omega_limits_HSET (I : HSET)
    : ω_limits_distribute_over_I_coproducts HSET I HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)).
  Proof.
    intro ind.
    use make_is_z_isomorphism.
    - intros [f p].
      assert (q0 : ∏ n : nat, S n = n + 1 ).
      {
        intro n ; induction n.
        - apply idpath.
        - admit.
      }

      assert (q : ∏ n : nat, pr1 (f n) = pr1 (f (n + 1))).
      { exact (λ n, ! base_paths _ _ (p (n+1) n (q0 n))). }

      assert (q' : ∏ n : nat, pr1 (f n) = pr1 (f (S n))).
      {
        intro n.
        admit.
      }

      (* From this extract the i *)
      exists (pr1 (f 0)).
      use tpair.
      + intro n.
        assert (h : pr1 (f 0) = pr1 (f n)).
        {
          induction n.
          - apply idpath.
          - exact (IHn @ q' n).
        }
        induction (! h).
        exact (pr2 (f n)).
      + intros n m h.
        cbn in p.
        cbn in f.
        admit.
    - split ; apply funextsec ; intro x ; use total2_paths_f ; admit.
  Admitted.

End OmegaLimitsCommutingWithCoproductsHSET.

Definition CoproductOfArrowsIsos
           (I : UU) (C : category) (a : I -> C) (CC : Coproduct I C a)
           (c : I -> C) (CC' : Coproduct I C c) (f : ∏ i : I, C⟦a i, c i⟧)
  : (∏ i : I, is_z_isomorphism (f i)) -> is_z_isomorphism (CoproductOfArrows I C CC CC' f).
Proof.
  intro fi_iso.
  use make_is_z_isomorphism.
  - use CoproductOfArrows.
    exact (λ i, pr1 (fi_iso i)).
  - split.
    + etrans. { apply precompWithCoproductArrow. }
      apply pathsinv0, CoproductArrowUnique.
      intro i.
      refine (id_right _ @ ! id_left _ @ _).
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      apply pathsinv0, (pr2 (fi_iso i)).
    + etrans. { apply precompWithCoproductArrow. }
      apply pathsinv0, CoproductArrowUnique.
      intro i.
      refine (id_right _ @ ! id_left _ @ _).
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      apply pathsinv0, (pr2 (fi_iso i)).
Defined.

Lemma constant_functor_composition_nat_trans
      (A B C : category) (b : B) (F : functor B C)
  : nat_trans (functor_composite (constant_functor A B b) F)
              (constant_functor A C (F b)).
Proof.
  use make_nat_trans.
  + intro ; apply identity.
  + intro ; intros.
    apply maponpaths_2.
    exact (functor_id F b).
Defined.

Lemma nat_z_iso_preserve_ωlimits {A B : category}
      (F G : functor A B)
  : is_omega_cont F -> nat_z_iso F G -> is_omega_cont G.
Proof.
  (* This lemma should be split up in data and property and there is also a repeat of proof, need a more "general, but easy" lemma. *)
  intros Fc i.
  intros coch a a_con a_lim.
  intros b b_con.

  transparent assert (b'_con : (cone (mapdiagram F coch) b)).
  {
    exists (λ v, pr1 b_con v · pr1 (pr2 i (dob coch v))).
    intros u v p.
    etrans.
    1: apply assoc'.
    cbn.
    etrans.
    1: apply maponpaths, pathsinv0, (pr21 (nat_z_iso_inv i)).
    etrans.
    1: apply assoc.
    apply maponpaths_2.
    exact (pr2 b_con u v p).
  }

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

Lemma constant_functor_composition_nat_z_iso (A B C : category) (b : B) (F : functor B C)
  : nat_z_iso (functor_composite (constant_functor A B b) F)
              (constant_functor A C (F b)).
Proof.
  exists (constant_functor_composition_nat_trans A B C b F).
  intro ; apply identity_is_z_iso.
Defined.

Lemma coproduct_of_functors_nat_trans
      {I : UU} {C D : category} (CP : Coproducts I D) {F G : I → C ⟶ D}
      (α : ∏ i : I, nat_trans (F i) (G i))
  : nat_trans (coproduct_of_functors I C D CP F) (coproduct_of_functors I C D CP G).
Proof.
  use make_nat_trans.
  - intro c.
    use CoproductOfArrows.
    exact (λ i, α i c).
  - intros c1 c2 f.
    etrans.
    1: apply precompWithCoproductArrow.
    etrans.
    2: apply pathsinv0, precompWithCoproductArrow.
    apply maponpaths.
    apply funextsec ; intro i.
    etrans.
    1: apply assoc.
    etrans.
    2: apply assoc'.
    apply maponpaths_2.
    exact (pr2 (α i) _ _ f).
Defined.

Lemma coproduct_of_functors_nat_z_iso
      {I : UU} {C D : category} (CP : Coproducts I D) {F G : I → C ⟶ D}
      (α : ∏ i : I, nat_z_iso (F i) (G i))
  : nat_z_iso (coproduct_of_functors I C D CP F) (coproduct_of_functors I C D CP G).
Proof.
  exists (coproduct_of_functors_nat_trans CP α).
  intro c.
  use tpair.
  - use CoproductOfArrows.
    exact (λ i, pr1 (pr2 (α i) c)).
  - split.
    + etrans.
      1: apply precompWithCoproductArrow.
      apply pathsinv0, CoproductArrowUnique.
      intro i.
      etrans.
      2: apply assoc'.
      etrans.
      2: apply maponpaths_2, pathsinv0, (pr2 (pr2 (α i) c)).
      exact (id_right _ @ ! id_left _).
    + etrans.
      1: apply precompWithCoproductArrow.
      apply pathsinv0, CoproductArrowUnique.
      intro i.
      etrans.
      2: apply assoc'.
      etrans.
      2: apply maponpaths_2, pathsinv0, (pr2 (pr2 (α i) c)).
      exact (id_right _ @ ! id_left _).
Defined.

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

                (* How to apply IHN? We need to do #(BinProduct_of_functors _ IHn _) *)
                unfold BinProduct_of_functors.
                unfold BinProduct_of_functors_data.
                Search BinProduct_of_functors_ob.
                unfold BinProduct_of_functors_ob.
                simpl.
                unfold BinProduct_of_functors_ob.
                simpl.
                use BinProductArrow.
                ** refine (_ · pr1 (pr1 (IHn F) G) H).
                   admit.
                ** use CoproductArrow.
                   intro q.
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

End OmegaContinuityOfSignatureFunctor.

(* This is currently in a seperate because of testing,
the two have to become merged *)
Section OmegaContinuityOfSignatureFunctor.

  (* Let C := HSET.

  Let TC := TerminalHSET.
  Let IC := InitialHSET.
  Let BP := BinProductsHSET.
  Let BC := BinCoproductsHSET.

  Let PC := ProductsHSET.
  Let CC := CoproductsHSET. *)

  Variables (sort : UU) (Hsort : isofhlevel 3 sort).
  Variables (C : category) (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

  (** Define the discrete category of sorts *)
  Let sort_cat : category := path_pregroupoid sort Hsort.

  (** This represents "sort → C" *)
  Let sortToC : category := [sort_cat,C].
  Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

  Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.
  Let BPC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

  Variable (LC : ∏ coch : cochain C, LimCone coch).
  (* Definition LC : ∏ coch : cochain C, graphs.limits.LimCone coch.
  Proof.
    intro coch.
    apply LimConeHSET.
  Defined. *)

  Variable (distr : ∏ I : HSET, ω_limits_distribute_over_I_coproducts C I LC (CC (pr1 I) (pr2 I))).

  (* Not sure why I just can't write A := sortToC *)
  Lemma post_comp_with_pr_and_hat_is_omega_cont (s t : sort)
    :  is_omega_cont (post_comp_functor
                        (A := functor_category
                    ((sort,, (λ x y : sort, x = y)),,
                     make_dirprod (λ c : sort, idpath c) (λ a b c : sort, pathscomp0)) C)
                        (projSortToC sort Hsort C s ∙ hat_functor sort Hsort C CC t)
                     ).
  Proof.
    intros coch L con isLimcon.

    apply limits.pointwise_Lim_is_isLimFunctor ; intro F.
    apply limits.pointwise_Lim_is_isLimFunctor ; intro G.

    use limits.is_z_iso_isLim.
    { apply LC. }

    use make_is_z_isomorphism.
    - transparent assert (x : (t = G → cochain C)).
      {
        intro p.
        use tpair.
        - intro n.
          exact (pr1 (pr1 (dob coch n) F) s).
        - intros n m q.
          exact (pr1 (pr1 (dmor coch q) F) s).
      }

      refine (pr1 (distr (_,,Hsort t G) x) · _).

      assert (bla : (∏ a : [(sort,, (λ x y : sort, x = y)),,make_dirprod (λ c : sort, idpath c) (λ a b c : sort, pathscomp0), C], LimCone (diagram_pointwise coch a))).
      { admit. }

      assert (bla' : (∏ a : path_pregroupoid sort Hsort, LimCone (diagram_pointwise (diagram_pointwise coch F) a))).
      { admit. }

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
        unfold coproduct_of_limit_to_limit_of_coproduct.

        rewrite assoc'.
        etrans.
        1: {
          apply maponpaths.
          apply limArrowCommutes.
        }

        cbn.
        etrans.
        1: { apply precompWithCoproductArrow. }

        unfold CoproductOfArrows.
        apply maponpaths.
        apply funextsec ; intro p.
        rewrite ! assoc.
        apply maponpaths_2.

        (* exact (graphs.limits.limArrowCommutes _ _ _ _). This is the final step, just doesn't type check, I have to define the cochain out of here that is uses the lemma whose output is cochain *)
        admit.
      + admit.
  Admitted.

  (* In case no constructors were given, i.e. just H := Id. *)
  Lemma pre_comp_option_list_omega_cont
        (xst : (list sort × sort) × sort)
    : is_omega_cont (pre_comp_functor (C := sortToC) (option_list sort Hsort C TC BC CC (pr11 xst))).
  Proof.
  Admitted.


  Lemma is_omega_cont_hat_exp_functor_list_piece
  (xst : (list sort × sort) × sort)
    :  is_omega_cont (hat_exp_functor_list'_piece _ Hsort C TC BC CC xst).
  Proof.
    (*  [sortToC, sortToC] ⟶ [sortToC, sortToC] *)
    apply is_omega_cont_functor_composite.
    - exact (pre_comp_option_list_omega_cont xst).
    - exact (post_comp_with_pr_and_hat_is_omega_cont (pr21 xst) (pr2 xst)).
  Defined.

  Lemma is_omega_cont_hat_exp_functor_list
        (xst : list (list sort × sort) × sort) :
    is_omega_cont (hat_exp_functor_list' _ Hsort C TC BP BC CC xst).
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
    : is_omega_cont (MultiSortedSigToFunctor' _ Hsort C TC BP BC CC M).
  Proof.
    (* apply is_omega_cont_product_of_functors.
    -
    - intros op; apply is_omega_cont_hat_exp_functor_list. *)
    (* Defined. *)
  Admitted.

  (** The functor obtained from a multisorted binding signature is omega-continuous *)
  Lemma is_omega_cont_MultiSortedSigToFunctor (M : MultiSortedSig sort)
    : is_omega_cont (MultiSortedSigToFunctor sort Hsort C TC BP BC CC M).
  Proof.
    use nat_z_iso_preserve_ωlimits.
    3: exact (nat_z_iso_inv (MultiSortedSigToFunctor_test _ Hsort C TC IC BP BC PC CC M)).
    exact (is_omega_cont_MultiSortedSigToFunctor' M).
  Defined.

End OmegaContinuityOfSignatureFunctor.
