(** the coinductive analogue of [MultiSortedMonadConstruction_actegorical]

author: Ralph Matthes 2023
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

(** for the additions in 2023 *)
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.Chains.CoAdamek.
Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.CoproductsInActegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegoryMorphisms.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoidsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsWhiskeredMonoidalElementary.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonadsAsMonoidsWhiskeredElementary.
Require Import UniMath.SubstitutionSystems.EquivalenceLaxLineatorsHomogeneousCase.
Require UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.ConstructionOfGHSS.
Require UniMath.SubstitutionSystems.BindingSigToMonad_actegorical.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.MultiSortedSignatureFunctorEquivalence.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section ToBeMoved.

  (* Definition limArrowOfInverses
             {C : category} {g : graph} {d : diagram g C}
             (CC : LimCone d)
             (c : C) (cc : cone d c)
    : (∏  v : vertex g, Isos.is_z_isomorphism (pr1 cc v)) -> Isos.is_z_isomorphism (limArrow CC c cc).
  Proof.
    intro iv.
    apply isLim_is_z_iso.
    intros x x_con.
    use tpair.
    - unfold LimCone in CC.
      use tpair.
      + refine (pr11 (pr2 CC x x_con) · _).
        Search lim.
        Search lim.


    use Isos.make_is_z_isomorphism.
    - unfold cone in cc.

      Check pr1 cc.
      Search lim. *)


  Lemma ω_limits_distribute_over_I_coproducts_independent_of_product
        {C : category} {I : SET}
        {l : Lims_of_shape conat_graph C}
        (p q : Coproducts (pr1 I) C)
    : ω_limits_distribute_over_I_coproducts C I l p
      -> ω_limits_distribute_over_I_coproducts C I l q.
  Proof.
    intro distr.
    intro ind.
    use Isos.make_is_z_isomorphism.
    - refine (_ · pr1 (distr ind) · _).
      + use limOfArrows.
        * intro.
          use CoproductOfArrows.
          intro ; apply identity.
        * abstract
            (intros n m e ;
             simpl ;
             refine (precompWithCoproductArrow
                       _ _ _ _ _ _
                       @ _
                       @ ! precompWithCoproductArrow _ _ _ _ _ _) ;

             use CoproductArrowUnique ; intro;
             refine (CoproductInCommutes _ _ _  (q (λ i0 : pr1 I, pr1 (ind i0) n)) _ _ _ @ _) ;
             refine (id_left _ @ _) ;
             apply maponpaths ; apply pathsinv0, id_left
            ).
      + use CoproductOfArrows.
        intro ; apply identity.
    - split.
      + set (pf := pr12 (distr ind)).

        rewrite ! assoc.

        transparent assert (ii : (Isos.is_z_isomorphism (CoproductOfArrows (pr1 I) C (coproduct_of_limit C l p ind) (coproduct_of_limit C l q ind)
                                                                           (λ i : pr1 I, identity (pr11 (l (ind i))))))).
        {
          apply GeneralLemmas.CoproductOfArrowsIsos.
          intro ; apply Isos.identity_is_z_iso.
        }

        use (Isos.z_iso_inv_to_right _ _ _ _ (_,,ii)).
        etrans.
        2: apply pathsinv0, id_left.
        etrans.
        2: { cbn. apply idpath. }

        etrans.
        1: {
          apply maponpaths_2.
          apply postCompWithLimOfArrows.
        }
        clear ii.

        apply pathsinv0.
        use (Isos.z_iso_inv_on_left _ _ _ _ (_,, (distr ind : Isos.is_z_isomorphism _))).
        simpl.

        apply pathsinv0, limArrowUnique.
        intro n.
        simpl.

        etrans.
        2: apply pathsinv0, precompWithCoproductArrow.
        cbn.

        use CoproductArrowUnique.
        intro i.
        cbn.
        etrans.
        1: apply assoc.
        etrans.
        1: {
          apply maponpaths_2.
          etrans.
          1: apply assoc.
          apply maponpaths_2.
          apply (CoproductOfArrowsIn _ _  (coproduct_of_limit C l q ind) (coproduct_of_limit C l p ind)).
        }
        cbn.
        etrans.
        1: apply maponpaths_2, maponpaths_2, id_left.
        etrans.
        2: apply maponpaths, pathsinv0, id_left.

        etrans.
        1: apply assoc'.
        etrans.
        1: {
          apply maponpaths.
          exact (limArrowCommutes  (limit_of_coproduct C l p ind) _ (limit_of_coproduct_as_cone_of_coproduct_to_limit C l p ind) n).
        }
        apply (CoproductInCommutes _ _ _  (coproduct_of_limit C l p ind)).
      + set (pf := pr22 (distr ind)).

        rewrite ! assoc'.

        transparent assert (ii : (Isos.is_z_isomorphism (limOfArrows (limit_of_coproduct C l q ind) (limit_of_coproduct C l p ind)
    (λ u : vertex conat_graph,
     CoproductOfArrows (pr1 I) C (q (λ i : pr1 I, pr1 (ind i) u)) (p (λ i : pr1 I, pr1 (ind i) u))
       (λ i : pr1 I, identity (pr1 (ind i) u)))
    (ω_limits_distribute_over_I_coproducts_independent_of_product_subproof C I p q ind)))).
        {
          apply isLim_is_z_iso.
          intros c cc.
          use tpair.
          - use tpair.
            + use limArrow.
              use make_cone.
              * intro n.
                refine (pr1 cc n · _).
                use CoproductOfArrows.
                intro ; apply identity.
              * intros n m e.
                cbn.
                etrans.
                1: apply assoc'.
                etrans.
                1: {
                  apply maponpaths.
                  apply precompWithCoproductArrow.
                }
                cbn.
                admit.
            + admit.
          - cbn.
            admit.

            (* apply GeneralLemmas.CoproductOfArrowsIsos.
          intro ; apply Isos.identity_is_z_iso. *)
        }

        apply pathsinv0.
        use (Isos.z_iso_inv_to_left _ _ _ (_,,(ii : Isos.is_z_isomorphism _))).
        cbn.
        clear ii.
        etrans.
        1: apply id_right.

        etrans.
        2: {
          apply maponpaths.
          apply pathsinv0, postcompWithCoproductArrow.
        }

        apply pathsinv0.
        apply (Isos.z_iso_inv_on_right _ _ _ (_,, (distr ind : Isos.is_z_isomorphism _))).

        etrans.
        2: {
          apply pathsinv0.
          apply postCompWithLimArrow.
        }

        use limArrowUnique.
        intro n.

        etrans.
        1: apply  postcompWithCoproductArrow.

        apply pathsinv0.
        use CoproductArrowUnique.
        intro i.

        etrans.
        2: {
          do 2 apply maponpaths_2.
          apply pathsinv0, id_left.
        }

        etrans.
        2: apply assoc.
        etrans.
        2: {
          apply maponpaths, pathsinv0.
          apply (limArrowCommutes  (limit_of_coproduct C l q ind)).
        }

        etrans.
        2: {
          apply pathsinv0.
          apply (CoproductInCommutes _ _ _  (coproduct_of_limit C l q ind)).
        }

        cbn.









  Admitted.

  Definition BinProduct_of_functors_BinProducts_of_shape
             {C D : category}
             (BC :  Colims_of_shape two_graph D)
             (F G : functor C D)
    : nat_z_iso (BinCoproduct_of_functors C D (BinCoproducts_from_Colims _ BC) F G)
                (coproduct_of_functors bool C D (Coproducts_from_Colims _ _ BC) (λ x : bool, if x then F else G)).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro c.
        use colimOfArrows.
        * intro b.
          induction b ; apply identity.
        * intros b1 b2 e.
          apply fromempty.
          exact e.
      + intros c1 c2 f.
        cbn.
        etrans.
        2: apply pathsinv0, precompWithColimOfArrows.
        etrans.
        1: apply postcompWithColimArrow.
        apply colimArrowUnique.
        intro b.
        cbn.
        etrans.
        1: apply (colimArrowCommutes (BC (bincoproduct_diagram D (F c1) (G c1)))).
        cbn.
        induction b.
        * cbn.
          etrans.
          1: apply assoc'.
          etrans.
          1: { apply maponpaths.
               apply (colimArrowCommutes  (BC (bincoproduct_diagram D (F c2) (G c2))) _ _ true).
          }
          cbn.
          etrans.
          1: apply maponpaths, id_left.
          apply pathsinv0, id_left.
        * cbn.
          etrans.
          1: apply assoc'.
          etrans.
          1: { apply maponpaths.
               apply (colimArrowCommutes  (BC (bincoproduct_diagram D (F c2) (G c2))) _ _ false).
          }
          cbn.
          etrans.
          1: apply maponpaths, id_left.
          apply pathsinv0, id_left.
    - intro c.
      use tpair.
      + use colimOfArrows.
        * intro b.
          induction b ; apply identity.
        * intros b1 b2 e.
          apply fromempty.
          exact e.
      + split ; cbn.
        * etrans.
          1: apply postcompWithColimArrow.
          apply pathsinv0.
          use colimArrowUnique.
          intro b.
          etrans.
          1: apply id_right.
          cbn.
          etrans.
          2: apply assoc.
          etrans.
          2: { apply maponpaths, pathsinv0.
               apply (colimArrowCommutes (BC (coproducts_diagram bool D (λ i : bool, (if i then F else G) c))) ).
          }
          induction b ; refine (_ @ ! id_left _) ; apply pathsinv0, id_left.
        * etrans.
          1: apply postcompWithColimArrow.
          apply pathsinv0.
          use colimArrowUnique.
          intro b.
          etrans.
          1: apply id_right.
          cbn.
          etrans.
          2: apply assoc.
          etrans.
          2: { apply maponpaths, pathsinv0.
               apply (colimArrowCommutes (BC (bincoproduct_diagram D (F c) (G c))) ).
          }
          induction b ; refine (_ @ ! id_left _) ; apply pathsinv0, id_left.
  Defined.

  Definition Colims_from_BinCoproducts
             {C : category} (CC : BinCoproducts C)
    : Colims_of_shape two_graph C.
  Proof.
    unfold Colims_of_shape.
    intro d.
    unfold diagram in d.
    cbn in d.

    set (c := CC (pr1 d true) (pr1 d false)).
    unfold BinCoproduct in c.
    use make_ColimCocone.
    - exact (pr11 c).
    - use tpair.
      + intro b.
        induction b.
        * exact (pr121 c).
        * exact (pr221 c).
      + intros b1 b2 e.
        apply fromempty.
        exact e.
    - intros co cc.
      unfold cocone in cc.

      use tpair.
      + exists (pr11 (pr2 c co (pr1 cc true) (pr1 cc false))).
        intro b.
        induction b.
        * exact (pr121 (pr2 c co (pr1 cc true) (pr1 cc false))).
        * exact (pr221 (pr2 c co (pr1 cc true) (pr1 cc false))).
      + intro t.
        transparent assert (ϕ : (∑ fg : C ⟦ pr11 c, co ⟧, pr121 c · fg = pr1 cc true × pr221 c · fg = pr1 cc false)).
        {
          use tpair.
          - exact (pr1 t).
          - split ; apply (pr2 t).
        }

        set (p := pr2 (pr2 c co (pr1 cc true) (pr1 cc false)) ϕ).
        use total2_paths_f.
        * apply (base_paths _ _ p).
        * apply isaprop_is_cocone_mor.
  Defined.

End ToBeMoved.

Section Upstream.

  Context (C : category) (BC : BinCoproducts C).
  Local Definition Id_H := LiftingInitial_alt.Id_H C BC.

  Context (L : ∏ coch : cochain [C, C], LimCone coch).
  Context (distr :  ω_limits_distribute_over_I_coproducts [C, C] (bool,, isasetbool) L
    (Coproducts_from_Colims bool [C, C]
       (Colims_from_BinCoproducts (BinCoproducts_functor_precat C C BC)))).

  Definition is_omega_cont_Id_H (H: [C, C] ⟶ [C, C]) :
    is_omega_cont H -> is_omega_cont (Id_H H).
  Proof.
    intro Hc.
    use is_omega_cont_z_iso.
    2: {
      use z_iso_from_nat_z_iso.
      use nat_z_iso_inv.

      transparent assert (BC0 : (Colims_of_shape two_graph [C,C])).
      {
        use Colims_from_BinCoproducts.
        apply BinCoproducts_functor_precat.
        exact BC.
      }

      exact (BinProduct_of_functors_BinProducts_of_shape BC0 (constant_functor [C, C] [C, C] (functor_identity C)) H).
    }

    use (coproduct_of_functors_omega_cont [C,C] (bool,,isasetbool)).
    - exact L.
    - exact distr.
    - intro b.
      induction b.
      + apply is_omega_cont_constant_functor.
      + exact Hc.
  Defined.

End Upstream.

Section MBindingSig.

Context (sort : UU) (Hsort_set : isaset sort) (C : category).

(* Assumptions on [C] used to construct the functor *)
(* Note that there is some redundancy in the assumptions *)
Context (TC : Terminal C) (IC : Initial C)
          (BP : BinProducts C) (BC : BinCoproducts C)
          (PC : forall (I : UU), Products I C) (CC : forall (I : UU), isaset I → Coproducts I C).

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject (BC a b)).

Let Hsort := hlevelntosn 2 _ Hsort_set.

(** Define the discrete category of sorts *)
Let sort_cat : category := path_pregroupoid sort Hsort.

(** This represents "sort → C" *)
Let sortToC : category := [sort_cat,C].
Let make_sortToC (f : sort → C) : sortToC := functor_path_pregroupoid Hsort f.

Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BC.

Let BPC : BinProducts [sortToC,C] := BinProducts_functor_precat sortToC C BP.

(* Assumptions needed to prove ω-continuity of the functor *)
Context (HcoC : Lims_of_shape conat_graph C)
 (HCcommuteBP : propcoproducts_commute_binproducts C BP (λ p : hProp, CC p (isasetaprop (pr2 p))))
 (HCcommuteCC : ∏ I : SET, ω_limits_distribute_over_I_coproducts C I HcoC (CC (pr1 I) (pr2 I))).



(** * Construction of a monad from a multisorted signature *)
Section monad.

  Local Definition sortToC1 := [sortToC, sortToC].
  Local Definition sortToC2 := [sortToC1, sortToC1].

  Let BCsortToC1 : BinCoproducts sortToC1 := BinCoproducts_functor_precat _ _ BCsortToC.
  (* Let ICsortToC1 : Initial sortToC1 := Initial_functor_precat _ _ (Initial_functor_precat _ _ IC).*)
  Let TCsortToC1 : Terminal sortToC1 := Terminal_functor_precat _ _ (Terminal_functor_precat _ _ TC).

  Local Definition HcoCsortToC : Lims_of_shape conat_graph sortToC.
  Proof.
    apply LimsFunctorCategory_of_shape, HcoC.
  Defined.
  Local Definition HcoCsortToC1 : Lims_of_shape conat_graph sortToC1.
  Proof.
    apply LimsFunctorCategory_of_shape, HcoCsortToC.
  Defined.

  Local Definition MultiSortedSigToFunctor : MultiSortedSig sort -> sortToC2 := MultiSortedSigToFunctor sort Hsort C TC BP BC CC.

  Local Definition is_omega_cont_MultiSortedSigToFunctor (M : MultiSortedSig sort) :
    is_omega_cont (MultiSortedSigToFunctor M) :=
    is_omega_cont_MultiSortedSigToFunctor sort Hsort_set C TC IC
                                          BP BC PC CC M HcoC HCcommuteBP HCcommuteCC.

  Context (sortToC_exp : Exponentials (BinProducts_functor_precat [path_pregroupoid sort Hsort, C] C BP)).

  Local Definition MultiSortedSigToStrengthFromSelfCAT : ∏ M : MultiSortedSig sort,
        MultiSorted_actegorical.pointedstrengthfromselfaction_CAT sort Hsort C (MultiSortedSigToFunctor M)
    := MultiSortedSigToStrengthFromSelfCAT sort Hsort C TC BP BC CC.

  Let Id_H := Id_H sortToC BCsortToC.

  (** Construction of terminal coalgebra for the omega-continuous signature functor with lax lineator *)
  Definition coindCodatatypeOfMultisortedBindingSig_CAT (sig : MultiSortedSig sort) :
    Terminal (CoAlg_category (Id_H (MultiSortedSigToFunctor sig))).
  Proof.
    use limCoAlgTerminal.
    - exact TCsortToC1.
    - use is_omega_cont_Id_H.
      + apply HcoCsortToC1.
      + set (CP' := CoproductsBool BCsortToC).

        transparent assert (CP'' : (Coproducts bool sortToC)).
        {
          use Coproducts_functor_precat.
          apply CC.
          apply isasetbool.
        }

        transparent assert (CP'_distr : (ω_limits_distribute_over_I_coproducts sortToC (bool,, isasetbool) HcoCsortToC CP'')).
        {
          use functor_category_ω_limits_distribute_over_I_coproducts.
          apply HCcommuteCC.
        }

        set (q := functor_category_ω_limits_distribute_over_I_coproducts sortToC  (bool,, isasetbool) HcoCsortToC CP'' CP'_distr sortToC).
        apply (ω_limits_distribute_over_I_coproducts_independent_of_product _ _ q).
      + exact (is_omega_cont_MultiSortedSigToFunctor sig).
    - apply HcoCsortToC1.
  Defined.

  Definition coindGHSSOfMultiSortedSig_CAT (sig : MultiSortedSig sort) :
    ghss (monendocat_monoidal sortToC) (MultiSortedSigToFunctor sig) (MultiSortedSigToStrengthFromSelfCAT sig).
  Proof.
    use (terminal_coalg_to_ghss (MultiSortedSigToStrengthFromSelfCAT sig) BCsortToC1).
    - apply BindingSigToMonad_actegorical.bincoprod_distributor_pointed_CAT.
    - exact (pr1 (coindCodatatypeOfMultisortedBindingSig_CAT sig)).
    - exact (pr2 (coindCodatatypeOfMultisortedBindingSig_CAT sig)).
  Defined.

  (** the associated Sigma-monoid *)
  Definition coindSigmaMonoidOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : SigmaMonoid (MultiSortedSigToStrengthFromSelfCAT sig).
  Proof.
    apply ghhs_to_sigma_monoid.
    exact (coindGHSSOfMultiSortedSig_CAT sig).
  Defined.

  (** the associated monad *)
  Definition coindMonadOfMultiSortedSig_CAT (sig : MultiSortedSig sort) : Monad sortToC.
  Proof.
    use monoid_to_monad_CAT.
    use SigmaMonoid_to_monoid.
    - exact (MultiSortedSigToFunctor sig).
    - exact (MultiSortedSigToStrengthFromSelfCAT sig).
    - exact (coindSigmaMonoidOfMultiSortedSig_CAT sig).
  Defined.

End monad.

End MBindingSig.

Section InstanceHSET.

  Context (sort : UU) (Hsort_set : isaset sort).

  Let Hsort := hlevelntosn 2 _ Hsort_set.

  Let sortToHSET : category := [path_pregroupoid sort Hsort, HSET].

  Definition coindMultiSortedSigToMonadHSET_viaCAT : MultiSortedSig sort → Monad (sortToHSET).
  Proof.
    intros sig; simple refine (coindMonadOfMultiSortedSig_CAT sort Hsort_set HSET _ _ _ _ _ _ _ _ _ sig).
    - apply TerminalHSET.
    - apply InitialHSET.
    - apply BinProductsHSET.
    - apply BinCoproductsHSET.
    - apply ProductsHSET.
    - apply CoproductsHSET.
    - apply LimsHSET_of_shape.
    - apply propcoproducts_commute_binproductsHSET.
    - apply I_coproduct_distribute_over_omega_limits_HSET.
  Defined.

End InstanceHSET.
