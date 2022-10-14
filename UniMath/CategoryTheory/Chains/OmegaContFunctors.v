(** * ω-cocontinuous functors

This file contains theory about (omega-) continuous functors, i.e. functors
which preserve (sequential-) limits ([is_omega_cont] and [is_cont]).

This file contains proofs that the following functors are (omega-)continuous:

- Identity functor
  [is_cont_functor_identity] [is_omega_cont_functor_identity]
- Constant functor: F_x : C -> D, c |-> x
  [is_omega_cont_constant_functor]
- Composition of omega-continuous functors
  [is_cont_functor_composite] [is_omega_cont_functor_composite]
- Iteration of omega-continuous functors: F^n : C -> C
  [is_cont_iter_functor] [is_omega_cont_iter_functor]
- Pairing of (omega-)cont functors (F,G) : A * B -> C * D, (x,y) |-> (F x,G y)
  [is_cont_pair_functor] [is_omega_cont_pair_functor]
- Indexed families of (omega-)cont functors F^I : A^I -> B^I
  [is_cont_family_functor] [is_omega_cont_family_functor]
- Binary delta functor: C -> C^2, x |-> (x,x)
  [is_cont_bindelta_functor] [is_omega_cont_bindelta_functor]
- General delta functor: C -> C^I
  [is_cont_delta_functor] [is_omega_cont_delta_functor]
- Binary coproduct functor: C^2 -> C, (x,y) |-> x + y
  [is_cont_bincoproduct_functor] [is_omega_cont_bincoproduct_functor]
- General coproduct functor: C^I -> C
  [is_cont_coproduct_functor] [is_omega_cont_coproduct_functor]
- Binary coproduct of functors: F + G : C -> D, x |-> F x + G x
  [is_cont_BinCoproduct_of_functors_alt] [is_omega_cont_BinCoproduct_of_functors_alt]
  [is_cont_BinCoproduct_of_functors_alt2] [is_omega_cont_BinCoproduct_of_functors_alt2]
  [is_cont_BinCoproduct_of_functors] [is_omega_cont_BinCoproduct_of_functors]
- Coproduct of families of functors: + F_i : C -> D  (generalization of coproduct of functors)
  [is_cont_coproduct_of_functors_alt] [is_cont_coproduct_of_functors]
  [is_omega_cont_coproduct_of_functors_alt] [is_omega_cont_coproduct_of_functors]
- Constant product functors: C -> C, x |-> a * x  and  x |-> x * a
  [is_cont_constprod_functor1] [is_cont_constprod_functor2]
  [is_omega_cont_constprod_functor1] [is_omega_cont_constprod_functor2]
- Binary product functor: C^2 -> C, (x,y) |-> x * y
  [is_omega_cont_binproduct_functor]
- Product of functors: F * G : C -> D, x |-> (x,x) |-> (F x,G x) |-> F x * G x
  [is_omega_cont_BinProduct_of_functors_alt] [is_omega_cont_BinProduct_of_functors]
- Precomposition functor: _ o K : ⟦C,A⟧ -> ⟦M,A⟧ for K : M -> C
  [preserves_limit_pre_composition_functor] [is_omega_cont_pre_composition_functor]
- Postcomposition with a left adjoint:
  [is_cont_post_composition_functor] [is_omega_cont_post_composition_functor]
- Swapping of functor category arguments:
  [is_cont_functor_cat_swap] [is_omega_cont_functor_cat_swap]
- The forgetful functor from Set/X to Set preserves limits
  ([preserves_limit_slicecat_to_cat_HSET])

Written by: Kobe Wullaert: October 2022
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Slice.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Examples.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.

Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.OppositeCategory.LimitsAsColimits.
Require Import UniMath.CategoryTheory.OppositeCategory.OppositeOfFunctorCategory.

Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.

Local Open Scope cat.

(** ** Right adjoints preserve limits *)
Lemma right_adjoint_cont {C D : category} (F : functor C D)
      (H : is_right_adjoint F) : is_cont F.
Proof.
  intros g d L ccL.
  apply right_adjoint_preserves_limit.
  exact H.
Defined.

(** ** Identity preserves limits *)

Lemma is_omega_cont_functor_identity {C : category} : is_omega_cont (functor_identity C).
Proof.
  use (is_omega_cocont_op (F := functor_op (functor_identity C))).
  apply is_omega_cocont_functor_identity.
Defined.

(** ** Constant functors *)
Lemma is_omega_cont_constant_functor {C D : category} (x : D)
  : is_omega_cont (constant_functor C D x).
Proof.
  use (is_omega_cocont_op (F := functor_op (constant_functor C D x))).
  use is_omega_cocont_constant_functor.
Defined.

(** ** Composition of omega (continuous) functors *)
Lemma is_cont_functor_composite {C D E : category}
      (F : functor C D) (G : functor D E) :
  is_cont F -> is_cont G -> is_cont (functor_composite F G).
Proof.
  intros hF hG.
  use (is_cocont_op (F := functor_op (functor_composite F G))).
  exact (is_cocont_functor_composite (functor_op F) (functor_op G) (is_cont_op hF) (is_cont_op hG)).
Defined.

Lemma is_omega_cont_functor_composite {C D E : category}
      (F : functor C D) (G : functor D E) :
  is_omega_cont F -> is_omega_cont G -> is_omega_cont (functor_composite F G).
Proof.
  intros hF hG.
  use (is_omega_cocont_op (F := functor_op (functor_composite F G))).
  exact (is_omega_cocont_functor_composite (functor_op F) (functor_op G) (is_omega_cont_op hF) (is_omega_cont_op hG)).
Defined.

(** ** Functor iteration preserves (omega)-continuity *)
Lemma is_omega_cont_iter_functor
      {C : category} {F : functor C C}
      (hF : is_omega_cont F) (n : nat)
  : is_omega_cont (iter_functor F n).
Proof.
  induction n as [|n IH]; simpl.
  - exact (is_omega_cont_functor_identity (C := C)).
  - apply (is_omega_cont_functor_composite _ _ IH hF).
Defined.

(** ** Binary product of functors: F * G : C -> D is omega continuous *)
Lemma is_omega_cont_BinProduct_of_functors
      {C D : category}
      (F G : functor C D)
      (PD : BinProducts D)
      (HF : is_omega_cont F) (HG : is_omega_cont G)
  : is_omega_cont (BinProduct_of_functors _ _ PD F G).
Proof.
  use (is_omega_cocont_op (F := functor_op  (BinProduct_of_functors C D PD F G))).
  use (is_omega_cocont_BinCoproduct_of_functors
         _
         (functor_op F)
         (functor_op G)
         (is_omega_cont_op HF)
         (is_omega_cont_op HG)
      ).
Defined.

(** Continuity is preserved by isomorphic functors *)
Section cont_iso.

  (* As this section is proving a proposition, the hypothesis can be weakened from a specified iso to
F    an   d G being isomorphic. *)

  Context {C D : category} {F G : functor C D}
          (αiso : @z_iso [C, D] F G).

  Local Definition αiso_op : @z_iso [opp_cat C, opp_cat D] (functor_op F) (functor_op G).
  Proof.
    set (αisoop := z_iso_inv αiso).
    use make_z_iso.
    - use make_nat_trans.
      + exact (λ x, pr1 (pr1 αisoop) x).
      + exact (λ  x y f, ! pr2 (pr1 αisoop) y x f).
    - use make_nat_trans.
      + exact (λ x, pr1 (pr1 αiso) x).
      + exact (λ x y f, ! pr2 (pr1 αiso) y x f).
    - use tpair.
      + use nat_trans_eq.
        { apply homset_property. }
        intro c.
        exact (toforallpaths _ _ _ (base_paths _ _ (pr1 (pr2 (pr2 αiso)))) c).
      + use nat_trans_eq.
        { apply homset_property. }
        intro c.
        exact (toforallpaths _ _ _ (base_paths _ _ (pr2 (pr2 (pr2 αiso)))) c).
  Defined.

  Lemma is_omega_cont_z_iso : is_omega_cont F -> is_omega_cont G.
  Proof.
    intro H.
    use (is_omega_cocont_op (F := functor_op G)).
    use is_omega_cocont_z_iso.
    { exact (functor_op F). }
    - exact αiso_op.
    - exact (is_omega_cont_op H).
  Defined.

End cont_iso.

(** * If a functor is part of an equivalence of categories,
      it is both continuous and cocontinuous *)
Section equivalence_of_categories.

  Require Import UniMath.CategoryTheory.Equivalences.Core.
  Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
  Lemma is_cont_equivalence_of_cats
        {C D : category} {F : functor C D} (e : adj_equivalence_of_cats F)
    : is_cont F.
  Proof.
    apply right_adjoint_cont.
    use are_adjoints_to_is_right_adjoint.
    - exact (pr1 (pr1 e)).
    - exact (pr2 (pr1 (adj_equivalence_of_cats_inv e))).
  Defined.

  Lemma is_cocont_equivalence_of_cats
        {C D : category} {F : functor C D} (e : adj_equivalence_of_cats F)
    : is_cocont F.
  Proof.
    apply left_adjoint_cocont.
    exact (pr1 e).
  Defined.

End equivalence_of_categories.

(** ** Post composition with a right adjoint is continuous *)
Section post_composition_functor.

  Context {C D E : category}.
  Context (F : functor D E) (HF : is_right_adjoint F).

  Lemma is_cont_post_composition_functor :
    is_cont (post_composition_functor C D E F).
  Proof.
    apply right_adjoint_cont.
    apply (is_right_adjoint_post_composition_functor _ HF).
  Defined.

  Lemma is_omega_cont_post_composition_functor :
    is_omega_cont (post_composition_functor C D E F).
  Proof.
    now intros c L ccL; apply is_cont_post_composition_functor.
  Defined.

End post_composition_functor.

(** ** Direct proof that the precomposition functor is continuous *)
Section pre_composition_functor.

  (* Lemma preserves_limit_pre_composition_functor
        {A B C : category} (F : functor A B)
        {g : graph}
        {d : diagram g [B, C]} {G : [B, C]}
        (cG : cone d G)
        (H : ∏ b : B, LimCone (diagram_pointwise d b))
    :
    preserves_limit (pre_composition_functor A B C F) d G cG.
  Proof.
    intros HccG.
    apply pointwise_Lim_is_isLimFunctor; intro a.
    apply (isLimFunctor_is_pointwise_Lim _ H _ _ HccG).
  Defined.*)

  Lemma is_omega_cont_pre_composition_functor' {A B C : category}
        (F : functor A B)
        (H : Lims_of_shape conat_graph C) :
    is_omega_cont (pre_composition_functor _ _ C F).
  Proof.
    use (is_omega_cocont_op (F := functor_op (pre_composition_functor _ _ C F))).
    use is_omega_cocont_z_iso.
    2: {
      set (facto := functor_op_of_precomp_functor_factorizes_through_functorcatofopp_nat_z_iso C F).
      set (t := z_iso_inv (z_iso_from_nat_z_iso (homset_property _) facto)).
      exact t.
    }
    repeat (use is_omega_cocont_functor_composite).
    2: {
      apply is_omega_cocont_pre_composition_functor.
      intro ch.
      repeat (use tpair).
      - exact (pr1 (pr1 (H (chain_op ch)))).
      - exact (λ v, pr1 (pr2 (pr1 (H (chain_op ch)))) v).
      - exact (λ u v e, pr2 (pr2 (pr1 (H (chain_op ch)))) v u e).
      - exact (λ c cc, ((pr2 (H (chain_op ch))) c (cocone_op cc))).
    }
    - use is_cocont_equivalence_of_cats.
      exact (adj_equivalence_of_cats_inv (opfunctorcat_adjequiv_functorcatofoppcats B C)).
    - use is_cocont_equivalence_of_cats.
      apply opfunctorcat_adjequiv_functorcatofoppcats.
  Defined.

End pre_composition_functor.

(** ** A pair of functors (F,G) : A * B -> C * D is omega continuous if F and G are *)
Section pair_functor.

  Context {A B C D : category} (F : functor A C) (G : functor B D).

  Lemma is_omega_cont_pair_functor (HF : is_omega_cont F) (HG : is_omega_cont G) :
    is_omega_cont (pair_functor F G).
  Proof.
    use (is_omega_cocont_op (F := functor_op (pair_functor F G))).
    use (is_omega_cocont_pair_functor _ _ (is_omega_cont_op HF) (is_omega_cont_op HG)).
  Defined.

End pair_functor.

(* Should be moved into Categorytheory/limits/graphs/limits.v *)
Lemma mapcone_functor_composite
      {A B C : category} (F : A ⟶ B) (G : B ⟶ C) (g : graph) (D : diagram g A)
      {a : A} (cc : cone D a)
  : mapcone (F ∙ G) D cc = mapcone G (mapdiagram F D) (mapcone F D cc).
Proof.
  apply subtypePath.
  - intros x. repeat (apply impred_isaprop; intro). apply C.
  - reflexivity.
Qed.

(** ** A functor F : A -> product_category I B is (omega-)continuous if each F_i : A -> B_i is *)
Section functor_into_product_category.

  Context {I : UU} {A : category} {B : I -> category}.

  Lemma isLimCone_in_product_category
        {g : graph} (c : diagram g (product_category B))
        (b : product_precategory B) (cc : cone c b)
        (M : ∏ i, isLimCone _ _ (mapcone (pr_functor I B i) _ cc))
    : isLimCone c b cc.
  Proof.
    intros b' cc'.
    apply iscontraprop1.
    - abstract (
          apply invproofirrelevance; intros f1 f2;
          apply subtypePath;
          [ intros f; apply impred_isaprop; intros v;
            apply has_homsets_product_precategory | ];
          apply funextsec; intros i;
          set (MM := M i _ (mapcone (pr_functor I B i) _ cc'));
          set (H := proofirrelevancecontr MM);
          use (maponpaths pr1 (H (pr1 f1 i,,_) (pr1 f2 i,,_)));
          clear MM H; intros v ;
          [ exact (toforallpaths _ _ _ (pr2 f1 v) i) |
            exact (toforallpaths _ _ _ (pr2 f2 v) i) ]
        ) .
    - use tpair.
      + intros i.
        use (pr1 (pr1 (M i _ (mapcone (pr_functor I B i) _ cc')))).
      + abstract (
            intros v; apply funextsec; intros i;
            use (pr2 (pr1 (M i _ (mapcone (pr_functor I B i) _ cc'))) v)
          ).
  Defined.

  Lemma is_cont_functor_into_product_category
        {F : functor A (product_category B)}
        (HF : ∏ (i : I), is_cont (functor_composite F (pr_functor I B i))) :
    is_cont F.
  Proof.
    intros gr cA a cc Hcc.
    apply isLimCone_in_product_category.
    intros i.
    rewrite <- mapcone_functor_composite.
    now apply HF, Hcc.
  Defined.

  Lemma is_omega_cont_functor_into_product_category
        {F : functor A (product_category B)}
        (HF : ∏ (i : I), is_omega_cont (functor_composite F (pr_functor I B i))) :
    is_omega_cont F.
  Proof.
    intros cA a cc Hcc.
    apply isLimCone_in_product_category.
    intros i.
    rewrite <- mapcone_functor_composite.
    now apply HF, Hcc.
  Defined.

End functor_into_product_category.

(** * *)
Section tuple_functor.

  Context {I : UU} {A : category} {B : I -> category}.

  Lemma is_cont_tuple_functor {F : ∏ i, functor A (B i)}
        (HF : ∏ i, is_cont (F i)) : is_cont (tuple_functor F).
  Proof.
    apply is_cont_functor_into_product_category.
    intro i; rewrite pr_tuple_functor; apply HF.
  Defined.

  Lemma is_omega_cont_tuple_functor {F : ∏ i, functor A (B i)}
        (HF : ∏ i, is_omega_cont (F i)) : is_omega_cont (tuple_functor F).
  Proof.
    apply is_omega_cont_functor_into_product_category.
    intro i; rewrite pr_tuple_functor; apply HF.
  Defined.

End tuple_functor.

(** ** The functor "+ : C^I -> C" is continuous is equivalently with saying that coproducts commute with limits *)
Section coprod_functor.

  Definition coproducts_commute_with_limits (C : category) : UU
    := ∏ I : UU, ∏ PC : Coproducts I C, is_cont (coproduct_functor _ PC).

  Definition omega_coproducts_commute_with_limits (C : category) : UU
    := ∏ I : UU, ∏ PC : Coproducts I C, is_omega_cont (coproduct_functor _ PC).

End coprod_functor.

(** ** Coproduct of families of functors: + F_i : C -> D is omega continuous given coproducts in D distribute over limits *)
Section coproduct_of_functors.

  Context {I : UU} {C D : category} (HD : Coproducts I D).

  Lemma is_cont_coproduct_of_functors
        {F : ∏ (i : I), functor C D}
        (HF : ∏ i, is_cont (F i))
        (com : coproducts_commute_with_limits HD)
    : is_cont (coproduct_of_functors I _ _ HD F).
  Proof.
    use (transportf _
                    (coproduct_of_functors_alt_eq_coproduct_of_functors _ _ _ _ F)
                    _).
    apply is_cont_functor_composite.
    - use is_cont_tuple_functor.
      apply HF.
    - apply com.
  Defined.

  Lemma is_omega_cont_coproduct_of_functors
        {F : ∏ (i : I), functor C D}
        (HF : ∏ i, is_omega_cont (F i))
        (com : omega_coproducts_commute_with_limits HD)
        : is_omega_cont (coproduct_of_functors I _ _ HD F).
  Proof.
    use (transportf _
                    (coproduct_of_functors_alt_eq_coproduct_of_functors _ _ _ _ F)
                    _).
    apply is_omega_cont_functor_composite.
    - apply is_omega_cont_tuple_functor.
      apply HF.
    - apply com.
  Defined.

End coproduct_of_functors.



  (* section pre_composition_functor.

    Context {C D E : category}.
    Context (F : functor D E) (HF : is_right_adjoint F).

    Lemma is_cont_pre_composition_functor :
      is_cont (pre_composition_functor _ _ E F).
    Proof.
      apply right_adjoint_cont; try apply functor_category_has_homsets.
    Admitted.

    Lemma is_omega_cont_pre_composition_functor
          (H : Lims_of_shape nat_graph C) :
      is_omega_cont (pre_composition_functor _ _ C F).
    Proof.
      now intros c L ccL; apply preserves_limit_pre_composition_functor.
    Defined.

    (* Lemma is_omega_cont_pre_composition_functor :
      is_omega_cont (pre_composition_functor _ _ E F).
    Proof.
      now intros c L ccL; apply is_cont_pre_composition_functor.
    Defined. *)

  End pre_composition_functor. *)



  (** ** Direct proof that the postcomposition functor is continuous *)
  (* Section post_composition_functor'.

    Context {A B C : category} (F : functor B C).

    Lemma preserves_limit_post_composition_functor {g : graph}
          {d : diagram g [A, B]} {G : [A, B]}
          (cG : cone d G)
          (H : ∏ a : A, LimCone (diagram_pointwise d a))
      : preserves_limit (post_composition_functor A B C F) d G cG.
    Proof.
      intros HccG.
      apply pointwise_Lim_is_isLimFunctor; intro a.
      use (isLimFunctor_is_pointwise_Lim
               (mapdiagram (post_composition_functor A B C F) d)
               _
               (functor_composite G F)
               (mapcone (post_composition_functor A B C F) d cG)
               _
               a
          ).
    Admitted.


    Lemma is_omega_cont_post_composition_functor'
          (H : Lims_of_shape nat_graph C) :
      is_omega_cont (pre_composition_functor _ _ A F).
    Proof.
      (* intros c L ccL.
      apply preserves_limit_pre_composition_functor.
      intro.
      unfold Lims_of_shape in H.
      apply H. *)

      use (is_omega_cocont_op (F := functor_op _)).

      Check  (functor_op (pre_composition_functor B C A F)).

      (* assert ( (functor_op (pre_composition_functor B C A F))
               = post_composition_functor (opp_cat A) _ _ (functor_op F)).
*)

      Admitted.
    (* Defined. *)

    End post_composition_functor'. *)





  (** ** Binary product of functors: F * G : C -> D is omega continuous *)
  (* Section BinProduct_of_functors.

    Context {C D : category}
            (*(PC : BinProducts C)*) (PD : BinProducts D).
    (* (PCo : BinProducts (opp_cat C)) (PDo : BinProducts (opp_cat D)). *)

    (* Lemma binproducts_op : BinCoproducts D.
    Proof.
      use PDo.
    Defined.

    Lemma bincoproducts_op : BinCoproducts (opp_cat D).
    Proof.
      use PD.
    Defined. *)

    (* Lemma bla :  (functor_op (bindelta_functor C))
                 = bindelta_functor (opp_cat C).
    Proof.
      use functor_eq.
      { apply homset_property. }
      use total2_paths_f.
      { apply idpath. }
      simpl.
      rewrite idpath_transportf.
      repeat (apply funextsec ; intro).
      apply idpath.
    Defined. *)

    (* Lemma test (F G : functor C D)
      :  (functor_op (binproduct_functor PD))
         = bincoproduct_functor (C := opp_cat D) bincoproducts_op.
    Proof.
      use functor_eq.
      { apply homset_property. }
      use total2_paths_f.
      { apply idpath. }
      simpl.
      rewrite idpath_transportf.
      repeat (apply funextsec ; intro).
      apply idpath.
    Defined. *)


    (* Lemma is_omega_cont_BinProduct_of_functors_alt (F G : functor C D)
          (HF : is_omega_cont F) (HG : is_omega_cont G) :
      is_omega_cont (BinProduct_of_functors_alt PD F G).
    Proof.
      apply is_omega_cont_functor_composite.
      - use (is_omega_cocont_op (F := functor_op (bindelta_functor C))).
        (* rewrite bla. *)
        use (is_omega_cocont_bindelta_functor (C := opp_cat C)).
        exact PCo.
      - apply is_omega_cont_functor_composite.
        + apply (is_omega_cont_pair_functor _ _ HF HG).
        + use (is_omega_cocont_op (F := functor_op (binproduct_functor PD))).
          (* rewrite (test F G).*)
          use (is_omega_cocont_bincoproduct_functor bincoproducts_op).
    Defined. *)



    (* Lemma is_omega_cont_BinCoproduct_of_functors (F G : functor C D)
          (HF : is_omega_cont F) (HG : is_omega_cont G) (exp :  Exponentials PDo)
      : is_omega_cont (BinCoproduct_of_functors _ _ binproducts_op F G).
    Proof.
      use (is_omega_cocont_op (F := functor_op  (BinCoproduct_of_functors C D binproducts_op F G))).
      use (is_omega_cocont_BinProduct_of_functors
             _
             _
             _
               (functor_op F)
               (functor_op G)
               (is_omega_cont_op HF)
               (is_omega_cont_op HG)
          ).
      - exact PCo.
      - intro.
        apply is_omega_cocont_constprod_functor1.
        exact exp.
    Defined. *)

  End BinProduct_of_functors.

End continuous_properties. *)




(* Section mapcone_functor_composite.
  (* This section should be put in Categories.limits.graphs.limits. *)

Context {A B C : category}
        (F : functor A B) (G : functor B C).

Lemma mapcone_functor_composite {g : graph} {D : diagram g A} {a : A} (cc : cone D a) :
  mapcone (functor_composite F G) _ cc = mapcone G _ (mapcone F _ cc).
Proof.
  Check (mapcocone_functor_composite (functor_op F) (functor_op G) (cc : cocone (C := opp_cat A) D)).

  apply subtypePath.
  - intros x. repeat (apply impred_isaprop; intro). apply C.
  - reflexivity.
Qed.

End mapcone_functor_composite.



(** ** A pair of functors (F,G) : A * B -> C * D is omega continuous if F and G are *)
Section pair_functor.

Context {A B C D : category} (F : functor A C) (G : functor B D).

Lemma is_omega_cont_pair_functor (HF : is_omega_cont F) (HG : is_omega_cont G) :
  is_omega_cont (pair_functor F G).
Proof.
now intros cAB ml ccml Hccml; apply isLimCone_pair_functor.
Defined.


Local Definition cone_pr1_functor {g : graph} (cAB : diagram g (category_binproduct A B))
  (ab : A × B) (ccab : cone cAB ab) :
  cone (mapdiagram (pr1_functor A B) cAB) (ob1 ab).
Proof.
use make_cone.
- simpl; intro n; apply (mor1 (coneOut ccab n)).
- simpl; intros m n e.
  set (X:= coneOutCommutes ccab m n e).
  etrans. 2: { apply maponpaths. apply X. }
  apply idpath.
Defined.

Local Lemma isLimCone_pr1_functor {g : graph} (cAB : diagram g (category_binproduct A B))
  (ab : A × B) (ccab : cone cAB ab) (Hccab : isLimCone cAB ab ccab) :
   isLimCone (mapdiagram (pr1_functor A B) cAB) (ob1 ab)
     (mapcone (pr1_functor A B) cAB ccab).
Proof.
intros x ccx.
transparent assert (HHH : (cone cAB (x,, ob2 ab))).
{ use make_cone.
  - simpl; intro n; split;
      [ apply (pr1 ccx n) | apply (# (pr2_functor A B) (pr1 ccab n)) ].
  - abstract(simpl; intros m n e; apply pathsdirprod;
               [ apply (pr2 ccx m n e) | apply (maponpaths dirprod_pr2 ((pr2 ccab) m n e)) ]).
}
destruct (Hccab _ HHH) as [[[x1 x2] p1] p2].
use tpair.
- apply (tpair _ x1).
  abstract (intro n; apply (maponpaths pr1 (p1 n))).
- intro t.
  transparent assert (X : (∑ x0, ∏ v, x0 · coneOut ccab v =
                                 catbinprodmor (pr1 ccx v) (pr2 (pr1 ccab v)) )).
  { use tpair.
    - split; [ apply (pr1 t) | apply (identity _) ].
    - cbn. abstract (intro n; rewrite id_left; apply pathsdirprod;
                 [ apply (pr2 t) | apply idpath ]).
  }
  abstract (apply subtypePath; simpl;
            [ intro f; apply impred; intro; apply homset_property
            | apply (maponpaths (λ x, pr1 (pr1 x)) (p2 X))]).
Defined.

Lemma is_cont_pr1_functor : is_cont (pr1_functor A B).
Proof.
now intros c L ccL M H; apply isLimCone_pr1_functor.
Defined.

Local Definition cone_pr2_functor {g : graph} (cAB : diagram g (category_binproduct A B))
  (ab : A × B) (ccab : cone cAB ab) :
  cone (mapdiagram (pr2_functor A B) cAB) (pr2 ab).
Proof.
use make_cone.
- simpl; intro n; apply (pr2 (coneOut ccab n)).
- simpl; intros m n e.
  etrans. 2: { apply maponpaths. apply (coneOutCommutes ccab m n e). }
  apply idpath.
Defined.

Local Lemma isLimCone_pr2_functor {g : graph} (cAB : diagram g (category_binproduct A B))
  (ab : A × B) (ccab : cone cAB ab) (Hccab : isLimCone cAB ab ccab) :
   isLimCone (mapdiagram (pr2_functor A B) cAB) (pr2 ab)
     (mapcone (pr2_functor A B) cAB ccab).
Proof.
intros x ccx.
transparent assert (HHH : (cone cAB (pr1 ab,, x))).
{ use make_cone.
  - simpl; intro n; split;
      [ apply (# (pr1_functor A B) (pr1 ccab n)) | apply (pr1 ccx n) ].
  - abstract (simpl; intros m n e; apply pathsdirprod;
                [ apply (maponpaths pr1 (pr2 ccab m n e)) | apply (pr2 ccx m n e) ]).
 }
destruct (Hccab _ HHH) as [[[x1 x2] p1] p2].
use tpair.
- apply (tpair _ x2).
  abstract (intro n; apply (maponpaths dirprod_pr2 (p1 n))).
- intro t.
  transparent assert (X : (∑ x0, ∏ v, x0 · coneOut ccab v =
                                 catbinprodmor (pr1 (pr1 ccab v)) (pr1 ccx v))).
  { use tpair.
    - split; [ apply (identity _) | apply (pr1 t) ].
    - cbn. abstract (intro n; rewrite id_left; apply pathsdirprod;
                 [ apply idpath | apply (pr2 t) ]).
  }
  abstract (apply subtypePath; simpl;
              [ intro f; apply impred; intro; apply homset_property
              | apply (maponpaths (λ x, dirprod_pr2 (pr1 x)) (p2 X)) ]).
Defined.

Lemma is_cont_pr2_functor : is_cont (pr2_functor A B).
Proof.
now intros c L ccL M H; apply isLimCone_pr2_functor.
Defined.

Lemma isLimCone_pair_functor {gr : graph}
  (HF : ∏ (d : diagram gr A) (c : A) (cc : cone d c) (h : isLimCone d c cc),
        isLimCone _ _ (mapcone F d cc))
  (HG : ∏ (d : diagram gr B) (c : B) (cc : cone d c) (h : isLimCone d c cc),
        isLimCone _ _ (mapcone G d cc)) :
  ∏ (d : diagram gr (category_binproduct A B)) (cd : A × B) (cc : cone d cd),
  isLimCone _ _ cc ->
  isLimCone _ _ (mapcone (pair_functor F G) d cc).
Proof.
intros cAB ml ccml Hccml xy ccxy.
transparent assert (cFAX : (cone (mapdiagram F (mapdiagram (pr1_functor A B) cAB)) (pr1 xy))).
{ use make_cone.
  - intro n; apply (pr1 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths dirprod_pr1 (pr2 ccxy m n e))).
}
transparent assert (cGBY : (cone (mapdiagram G (mapdiagram (pr2_functor A B) cAB)) (pr2 xy))).
{ use make_cone.
  - intro n; apply (pr2 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths dirprod_pr2 (pr2 ccxy m n e))).
}
destruct (HF _ _ _ (isLimCone_pr1_functor cAB ml ccml Hccml) _ cFAX) as [[f hf1] hf2].
destruct (HG _ _ _ (isLimCone_pr2_functor cAB ml ccml Hccml) _ cGBY) as [[g hg1] hg2].
unfold is_cone_mor in *. simpl in *.
use tpair.
- apply (tpair _ (f,,g)).
  abstract (intro n; unfold catbinprodmor, compose; simpl;
            now rewrite hf1, hg1).
- abstract (intro t; apply subtypePath; simpl;
             [ intro x; apply impred; intro; apply isaset_dirprod; apply homset_property
             | induction t as [[f1 f2] p]; simpl in *; apply pathsdirprod;
               [ apply (maponpaths pr1 (hf2 (f1,, (λ n, maponpaths pr1 (p n)))))
               | apply (maponpaths pr1 (hg2 (f2,, (λ n, maponpaths dirprod_pr2 (p n)))))]]).
Defined.

Lemma is_cont_pair_functor (HF : is_cont F) (HG : is_cont G) :
  is_cont (pair_functor F G).
Proof.
intros gr cAB ml ccml Hccml.
now apply isLimCone_pair_functor; [apply HF|apply HG|].
Defined.

Lemma is_omega_cont_pair_functor (HF : is_omega_cont F) (HG : is_omega_cont G) :
  is_omega_cont (pair_functor F G).
Proof.
now intros cAB ml ccml Hccml; apply isLimCone_pair_functor.
Defined.

End pair_functor.



Section tuple_functor.

Context {I : UU} {A : category} {B : I -> category}.

Lemma is_cont_tuple_functor {F : ∏ i, functor A (B i)}
  (HF : ∏ i, is_cont (F i)) : is_cont (tuple_functor F).
Proof.
  apply is_cont_functor_into_product_category.
  intro i; rewrite pr_tuple_functor; apply HF.
Defined.

Lemma is_omega_cont_tuple_functor {F : ∏ i, functor A (B i)}
  (HF : ∏ i, is_omega_cont (F i)) : is_omega_cont (tuple_functor F).
Proof.
  apply is_omega_cont_functor_into_product_category.
  intro i; rewrite pr_tuple_functor; apply HF.
Defined.

End tuple_functor.

(** ** A family of functor F^I : A^I -> B^I is omega continuous if each F_i is *)
(** TODO: split out section [pr_functor], and then factor results on [family_functor] using that
together with [tuple_functor] (maybe after redefining [family_functor] using [tuple_functor]. *)
Section family_functor.

Context {I : UU} {A B : category}.

(* The index set I needs decidable equality for pr_functor to be cont *)
Hypothesis (HI : isdeceq I).

Local Definition ifI (i j : I) (a b : A) : A :=
  coprod_rect (λ _, A) (λ _,a) (λ _,b) (HI i j).

Local Lemma ifI_eq i x y : ifI i i x y = x.
Proof.
now unfold ifI; destruct (HI i i) as [p|p]; [|destruct (p (idpath _))].
Defined.

Local Lemma isLimCone_pr_functor
  {g : graph} (c : diagram g (power_category I A))
  (L : power_category I A) (ccL : cone c L)
  (M : isLimCone c L ccL) : ∏ i,
  isLimCone _ _ (mapcone (pr_functor I (λ _, A) i) c ccL).
Proof.
intros i x ccx; simpl in *.
transparent assert (HHH : (cone c (λ j, ifI i j x (L j)))).
{ unfold ifI.
  use make_cone.
  - simpl; intros n j.
    destruct (HI i j) as [p|p].
    + apply (transportf (λ i, A ⟦ x, dob c n i ⟧) p (coneOut ccx n)).
    + apply (# (pr_functor I (λ _, A) j) (coneOut ccL n)).
  - abstract (simpl; intros m n e;
      apply funextsec; intro j; unfold compose; simpl;
      destruct (HI i j);
        [ destruct p; apply (pr2 ccx m n e)
        | apply (toforallpaths _ _ _ (pr2 ccL m n e) j)]).
}
destruct (M _ HHH) as [[x1 p1] p2].
use tpair.
- exists ((idtoiso (! ifI_eq i x (L i))) · x1 i).

  abstract (
      intro n; rewrite <- assoc ;
      eapply pathscomp0;
        [eapply cancel_precomposition, (toforallpaths _ _ _ (p1 n) i)|] ;
      unfold ifI, ifI_eq; simpl ;
      destruct (HI i i); [|destruct (n0 (idpath _))];
      rewrite idtoiso_precompose, idpath_transportf;
      assert (hp : p = idpath i); [apply (isasetifdeceq _ HI)|];
      now rewrite hp, idpath_transportf
    ).
- intro t.
  transparent assert (X : (∑ x0, ∏ n, x0 · coneOut ccL n = coneOut HHH n)).
  { use tpair.
    - simpl; intro j; unfold ifI.
      destruct (HI i j).
      + apply (transportf (λ i, A ⟦ x , L i ⟧) p (pr1 t)).
      + apply identity.
    - cbn. abstract (intro n; apply funextsec; intro j; unfold ifI; destruct (HI i j);
          [ now destruct p; rewrite <- (pr2 t), !idpath_transportf
          | apply id_left ]).
  }
  apply subtypePath; simpl; [intro f; apply impred; intro; apply homset_property|].
  set (H := toforallpaths _ _ _ (maponpaths pr1 (p2 X)) i); simpl in H.
  rewrite <- H; clear H; unfold ifI_eq, ifI.
  destruct (HI i i) as [p|p]; [|destruct (p (idpath _))].
  assert (hp : p = idpath i); [apply (isasetifdeceq _ HI)|].
  rewrite hp, idpath_transportf.
  apply (! id_left _).
Defined.

Lemma is_cont_pr_functor (i : I) : is_cont (pr_functor I (λ _, A) i).
Proof.
now intros c L ccL M H; apply isLimCone_pr_functor.
Defined.

Lemma isLimCone_family_functor {gr : graph} (F : ∏ (i : I), functor A B)
  (HF : ∏ i (d : diagram gr A) (c : A) (cc : cone d c) (h : isLimCone d c cc),
        isLimCone _ _ (mapcone (F i) d cc)) :
  ∏ (d : diagram gr (product_category (λ _, A))) (cd : I -> A) (cc : cone d cd),
  isLimCone _ _ cc ->
  isLimCone _ _ (mapcone (family_functor I F) d cc).
Proof.
intros cAB ml ccml Hccml xy ccxy; simpl in *.
transparent assert (cc : (∏ i, cone (mapdiagram (F i) (mapdiagram (pr_functor I (λ _ : I, A) i) cAB)) (xy i))).
{ intro i; use make_cone.
  - intro n; use (pr1 ccxy n).
  - abstract (intros m n e; apply (toforallpaths _ _ _ (pr2 ccxy m n e) i)).
}
set (X i := HF i _ _ _ (isLimCone_pr_functor _ _ _ Hccml i) (xy i) (cc i)).
use tpair.
- use tpair.
  + intro i; apply (pr1 (pr1 (X i))).
  + abstract (intro n; apply funextsec; intro j; apply (pr2 (pr1 (X j)) n)).
- (* abstract (intro t; apply subtypePath; simpl;
             [ intro x; apply impred; intro; apply impred_isaset; intro i; apply homset_property
             | destruct t as [f1 f2]; simpl in *;  apply funextsec; intro i;
               transparent assert (H : (∑ x : B ⟦ (F i) (ml i), xy i ⟧,
                                       ∏ n, # (F i) (coneOut ccml n i) · x =
                                       coneOut ccxy n i));
                [apply (tpair _ (f1 i)); intro n; apply (toforallpaths _ _ _ (f2 n) i)|];
               apply (maponpaths pr1 (pr2 (X i) H))]).*)
  admit.
  (*Defined.*)
Admitted.


Lemma is_cont_family_functor
  {F : ∏ (i : I), functor A B} (HF : ∏ (i : I), is_cont (F i)) :
  is_cont (family_functor I F).
Proof.
  intros gr cAB ml ccml Hccml.
  apply isLimCone_family_functor; trivial; intro i; apply HF.
Defined.

Lemma is_omega_cont_family_functor
  {F : ∏ (i : I), functor A B} (HF : ∏ (i : I), is_omega_cont (F i)) :
  is_omega_cont (family_functor I F).
Proof.
  now intros cAB ml ccml Hccml; apply isLimCone_family_functor.
Defined.

End family_functor.


(** ** The bindelta functor C -> C^2 mapping x to (x,x) is omega continuous *)
(* Section bindelta_functor.

Context {C : category} (PC : BinProducts C).

Lemma is_cont_bindelta_functor : is_cont (bindelta_functor C).
Proof.
  apply (left_adjoint_cont _ _ _ (is_left_adjoint_bindelta_functor PC)).
Defined.

Lemma is_omega_cont_bindelta_functor : is_omega_cont (bindelta_functor C).
Proof.
  now intros c L ccL; apply is_cont_bindelta_functor.
Defined.

End bindelta_functor. *)


(** ** The generalized delta functor C -> C^I is omega continuous *)
(* Section delta_functor.
(* TODO: factor this using [tuple_functor] results above, after redefining [delta_functor] in terms of [tuple_functor]. *)

Context {I : UU} {C : category} (PC : Products I C).

Lemma is_cont_delta_functor : is_cont (delta_functor I C).
Proof.
  apply (left_adjoint_cont _ _ _ (is_left_adjoint_delta_functor _ PC)).
Defined.

Lemma is_omega_cont_delta_functor :
  is_omega_cont (delta_functor I C).
Proof.
  now intros c L ccL; apply is_cont_delta_functor.
Defined.

End delta_functor. *)

(** ** The functor "+ : C^2 -> C" is continuous *)
(* Section bincoprod_functor.

Context {C : category} (PC : BinCoproducts C).

Lemma is_cont_bincoproduct_functor : is_cont (bincoproduct_functor PC).
Proof.
  apply (right_adjoint_cont _ _ _ (is_right_adjoint_bincoproduct_functor PC)).
Defined.

Lemma is_omega_cont_bincoproduct_functor :
  is_omega_cont (bincoproduct_functor PC).
Proof.
  now intros c L ccL; apply is_cont_bincoproduct_functor.
Defined.

End bincoprod_functor.*)

(** ** The functor "+ : C^I -> C" is continuous *)
(* Section coprod_functor.

Context {I : UU} {C : category} (PC : Coproducts I C).

Lemma is_cont_coproduct_functor :
  is_cont (coproduct_functor _ PC).
Proof.
  apply (left_adjoint_cont _ _ _ (is_left_adjoint_coproduct_functor _ PC)).
Defined.

Lemma is_omega_cont_coproduct_functor :
  is_omega_cont (coproduct_functor _ PC).
Proof.
  now intros c L ccL; apply is_cont_coproduct_functor.
Defined.

End coprod_functor.*)

(** ** Binary coproduct of functors: F + G : C -> D is omega continuous *)
(* Section BinCoproduct_of_functors.

Context {C D : category} (HD : BinCoproducts D).

Lemma is_cont_BinCoproduct_of_functors_alt {F G : functor C D}
  (HF : is_cont F) (HG : is_cont G) :
  is_cont (BinCoproduct_of_functors_alt HD F G).
Proof.
apply is_cont_functor_composite.
- apply is_cont_tuple_functor.
  induction i; assumption.
- apply is_cont_coproduct_functor.
Defined.

Lemma is_omega_cont_BinCoproduct_of_functors_alt {F G : functor C D}
  (HF : is_omega_cont F) (HG : is_omega_cont G) :
  is_omega_cont (BinCoproduct_of_functors_alt HD F G).
Proof.
apply is_omega_cont_functor_composite.
- apply is_omega_cont_tuple_functor.
  induction i; assumption.
- apply is_omega_cont_coproduct_functor.
Defined.

Definition omega_cont_BinCoproduct_of_functors_alt (F G : omega_cont_functor C D) :
  omega_cont_functor C D :=
    tpair _ _ (is_omega_cont_BinCoproduct_of_functors_alt (pr2 F) (pr2 G)).

Lemma is_cont_BinCoproduct_of_functors (F G : functor C D)
  (HF : is_cont F) (HG : is_cont G) :
  is_cont (BinCoproduct_of_functors _ _ HD F G).
Proof.
exact (transportf _
         (BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors _ _ _ F G)
         (is_cont_BinCoproduct_of_functors_alt HF HG)).
Defined.

Lemma is_omega_cont_BinCoproduct_of_functors (F G : functor C D)
  (HF : is_omega_cont F) (HG : is_omega_cont G) :
  is_omega_cont (BinCoproduct_of_functors _ _ HD F G).
Proof.
exact (transportf _
         (BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors _ _ _ F G)
         (is_omega_cont_BinCoproduct_of_functors_alt HF HG)).
Defined.

Definition omega_cont_BinCoproduct_of_functors
 (F G : omega_cont_functor C D) :
  omega_cont_functor C D :=
    tpair _ _ (is_omega_cont_BinCoproduct_of_functors _ _ (pr2 F) (pr2 G)).

(* Keep these as they have better computational behavior than the one for _alt above *)
Lemma is_cont_BinCoproduct_of_functors_alt2
  (PC : BinProducts C) (F G : functor C D)
  (HF : is_cont F) (HG : is_cont G) :
  is_cont (BinCoproduct_of_functors_alt2 HD F G).
Proof.
apply is_cont_functor_composite.
  apply (is_cont_bindelta_functor PC).
apply is_cont_functor_composite.
  apply (is_cont_pair_functor _ _ HF HG).
apply is_cont_bincoproduct_functor.
Defined.

Lemma is_omega_cont_BinCoproduct_of_functors_alt2
  (PC : BinProducts C) (F G : functor C D)
  (HF : is_omega_cont F) (HG : is_omega_cont G) :
  is_omega_cont (BinCoproduct_of_functors_alt2 HD F G).
Proof.
apply is_omega_cont_functor_composite.
  apply (is_omega_cont_bindelta_functor PC).
apply is_omega_cont_functor_composite.
  apply (is_omega_cont_pair_functor _ _ HF HG).
apply is_omega_cont_bincoproduct_functor.
Defined.

Definition omega_cont_BinCoproduct_of_functors_alt2
  (PC : BinProducts C) (F G : omega_cont_functor C D) :
  omega_cont_functor C D :=
    tpair _ _ (is_omega_cont_BinCoproduct_of_functors_alt2 PC _ _ (pr2 F) (pr2 G)).

End BinCoproduct_of_functors. *)

(** ** Coproduct of families of functors: + F_i : C -> D is omega continuous *)
(* Section coproduct_of_functors.

Context {I : UU} {C D : category} (HD : Coproducts I D).

Lemma is_cont_coproduct_of_functors
  {F : ∏ (i : I), functor C D} (HF : ∏ i, is_cont (F i)) :
  is_cont (coproduct_of_functors I _ _ HD F).
Proof.
  use (transportf _
        (coproduct_of_functors_alt_eq_coproduct_of_functors _ _ _ _ F)
        _).
  apply is_cont_functor_composite.
  - apply is_cont_tuple_functor.
    apply HF.
  - apply is_cont_coproduct_functor.
Defined.

Lemma is_omega_cont_coproduct_of_functors
  {F : ∏ (i : I), functor C D} (HF : ∏ i, is_omega_cont (F i)) :
  is_omega_cont (coproduct_of_functors I _ _ HD F).
Proof.
  use (transportf _
        (coproduct_of_functors_alt_eq_coproduct_of_functors _ _ _ _ F)
        _).
  apply is_omega_cont_functor_composite.
  - apply is_omega_cont_tuple_functor.
    apply HF.
  - apply is_omega_cont_coproduct_functor.
Defined.

Definition omega_cont_coproduct_of_functors
  (F : ∏ i, omega_cont_functor C D) :
  omega_cont_functor C D :=
    tpair _ _ (is_omega_cont_coproduct_of_functors (λ i, pr2 (F i))).

End coproduct_of_functors. *)

(** ** Constant product functors: C -> C, x |-> a * x  and  x |-> x * a are continuous *)
(* Section constprod_functors.

Context {C : category} (PC : BinProducts C) (hE : Exponentials PC).

Lemma is_cont_constprod_functor1 (x : C) : is_cont (constprod_functor1 PC x).
Proof.
  exact (left_adjoint_cont _ _ _ (hE _)).
Defined.

Lemma is_omega_cont_constprod_functor1 (x : C) : is_omega_cont (constprod_functor1 PC x).
Proof.
  now intros c L ccL; apply is_cont_constprod_functor1.
Defined.

Definition omega_cont_constprod_functor1 (x : C) :
  omega_cont_functor C C := tpair _ _ (is_omega_cont_constprod_functor1 x).

Lemma is_cont_constprod_functor2 (x : C) : is_cont (constprod_functor2 PC x).
Proof.
  apply left_adjoint_cont.
  apply (is_left_adjoint_constprod_functor2 PC), hE.
Defined.

Lemma is_omega_cont_constprod_functor2 (x : C) : is_omega_cont (constprod_functor2 PC x).
Proof.
  now intros c L ccL; apply is_cont_constprod_functor2.
Defined.

Definition omega_cont_constprod_functor2 (x : C) :
  omega_cont_functor C C := tpair _ _ (is_omega_cont_constprod_functor2 x).

End constprod_functors. *)

(** ** The functor "* : C^2 -> C" is omega continuous *)
(* Section binprod_functor.

Context {C : category} (PC : BinProducts C).

(* This hypothesis follow directly if C has exponentials *)
Variable omega_cont_constprod_functor1 :
  ∏ x : C, is_omega_cont (constprod_functor1 PC x).

Let omega_cont_constprod_functor2 :
  ∏ x : C, is_omega_cont (constprod_functor2 PC x).
Proof.
now intro x; apply (is_omega_cont_z_iso (flip_z_iso PC x)).
Defined.

Local Definition fun_lt (cAB : chain (category_binproduct C C)) :
  ∏ i j, i < j ->
              C ⟦ BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))),
                  BinProductObject C (PC (ob1 (dob cAB j)) (ob2 (dob cAB j))) ⟧.
Proof.
intros i j hij.
apply (BinProductOfArrows _ _ _ (mor1 (chain_mor cAB hij)) (identity _)).
Defined.

Local Definition fun_gt (cAB : chain (category_binproduct C C)) :
  ∏ i j, i > j ->
              C ⟦ BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))),
                  BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB i))) ⟧.
Proof.
intros i j hij.
apply (BinProductOfArrows _ _ _ (identity _) (mor2 (chain_mor cAB hij))).
Defined.

(* The map to K from the "grid" *)
Local Definition map_to_K (cAB : chain (category_binproduct C C)) (K : C)
  (ccK : cone (mapchain (binproduct_functor PC) cAB) K) i j :
  C⟦BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))), K⟧.
Proof.
destruct (natlthorgeh i j).
- apply (fun_lt cAB _ _ h · coneOut ccK j).
- destruct (natgehchoice _ _ h) as [H|H].
  * apply (fun_gt cAB _ _ H · coneOut ccK i).
  * destruct H; apply (coneOut ccK i).
Defined.

Local Lemma map_to_K_commutes (cAB : chain (category_binproduct C C)) (K : C)
  (ccK : cone (mapchain (binproduct_functor PC) cAB) K)
  i j k (e : edge j k) :
   BinProduct_of_functors_mor C C PC (constant_functor C C (pr1 (pr1 cAB i)))
     (functor_identity C) (pr2 (dob cAB j)) (pr2 (dob cAB k))
     (mor2 (dmor cAB e)) · map_to_K cAB K ccK i k =
   map_to_K cAB K ccK i j.
Proof.
destruct e; simpl.
unfold BinProduct_of_functors_mor, map_to_K.
destruct (natlthorgeh i j) as [h|h].
- destruct (natlthorgeh i (S j)) as [h0|h0].
  * rewrite assoc, <- (coneOutCommutes ccK j (S j) (idpath _)), assoc; simpl.
    apply cancel_postcomposition; unfold fun_lt.
    rewrite BinProductOfArrows_comp, id_left.
    eapply pathscomp0; [apply BinProductOfArrows_comp|].
    rewrite id_right.
    apply maponpaths_12; trivial; rewrite id_left; simpl.
    destruct (natlehchoice4 i j h0) as [h1|h1].
    + apply cancel_postcomposition, maponpaths, maponpaths, isasetbool.
    + destruct h1; destruct (isirreflnatlth _ h).
  * destruct (isirreflnatlth _ (natlthlehtrans _ _ _ (natlthtolths _ _ h) h0)).
- destruct (natlthorgeh i (S j)) as [h0|h0].
  * destruct (natgehchoice i j h) as [h1|h1].
    + destruct (natlthchoice2 _ _ h1) as [h2|h2].
      { destruct (isirreflnatlth _ (istransnatlth _ _ _ h0 h2)). }
      { destruct h2; destruct (isirreflnatlth _ h0). }
    + destruct h1; simpl.
      rewrite <- (coneOutCommutes ccK i (S i) (idpath _)), assoc.
      eapply pathscomp0; [apply cancel_postcomposition, BinProductOfArrows_comp|].
      rewrite id_left, id_right.
      apply cancel_postcomposition,
        (maponpaths_12 (BinProductOfArrows _ _ _)); trivial.
      simpl; destruct (natlehchoice4 i i h0) as [h1|h1]; [destruct (isirreflnatlth _ h1)|].
      apply maponpaths, maponpaths, isasetnat.
  * destruct (natgehchoice i j h) as [h1|h1].
    + destruct (natgehchoice i (S j) h0) as [h2|h2].
      { unfold fun_gt; rewrite assoc.
        eapply pathscomp0; [eapply cancel_postcomposition, BinProductOfArrows_comp|].
        rewrite id_right.
        apply cancel_postcomposition, maponpaths_12; trivial.
        now rewrite <- (chain_mor_right h1 h2). }
      { destruct h; unfold fun_gt; simpl.
        generalize h1; clear h1.
        rewrite h2; intro h1.
        apply cancel_postcomposition.
        apply maponpaths_12; trivial; simpl.
        destruct (natlehchoice4 j j h1); [destruct (isirreflnatlth _ h)|].
        apply maponpaths, maponpaths, isasetnat. }
    + destruct h1; destruct (negnatgehnsn _ h0).
Qed.

(* The cone over K from the A_i * B chain *)
Local Definition ccAiB_K (cAB : chain (category_binproduct C C)) (K : C)
  (ccK : cone (mapchain (binproduct_functor PC) cAB) K) i :
  cone (mapchain (constprod_functor1 PC (pr1 (pr1 cAB i)))
         (mapchain (pr2_functor C C) cAB)) K.
Proof.
use make_cone.
+ intro j; apply (map_to_K cAB K ccK i j).
+ simpl; intros j k e; apply map_to_K_commutes.
Defined.

Section omega_cont_binproduct.

Context {cAB : chain (category_binproduct C C)} {LM : C × C}
        {ccLM : cone cAB LM} (HccLM : isLimCone cAB LM ccLM)
        {K : C} (ccK : cone (mapchain (binproduct_functor PC) cAB) K).

Let L := pr1 LM : C.
Let M := pr2 LM : (λ _ : C, C) (pr1 LM).
Let cA := mapchain (pr1_functor C C) cAB : chain C.
Let cB := mapchain (pr2_functor C C) cAB : chain C.
Let HA := isLimCone_pr1_functor _ _ _ HccLM
  : isLimCone cA L (cone_pr1_functor cAB LM ccLM).
Let HB := isLimCone_pr2_functor _ _ _ HccLM
  : isLimCone cB M (cone_pr2_functor cAB LM ccLM).

(* Form the limiting cones of "A_i * B_0 -> A_i * B_1 -> ..." *)
Let HAiB := λ i, omega_cont_constprod_functor1 (pr1 (pr1 cAB i)) _ _ _ HB.

(* Turn HAiB into a LimCone: *)
Let CCAiB := λ i, make_LimCone _ _ _ (HAiB i).

(* Define the HAiM LimCone: *)
Let HAiM := make_LimCone _ _ _ (omega_cont_constprod_functor2 M _ _ _ HA).

Let ccAiB_K := λ i, ccAiB_K _ _ ccK i.

(* The f which is used in limOfArrows *)
Local Definition f i j : C
   ⟦ BinProduct_of_functors_ob C C PC (constant_functor C C (pr1 (dob cAB i)))
       (functor_identity C) (pr2 (dob cAB j)),
     BinProduct_of_functors_ob C C PC (constant_functor C C (pr1 (dob cAB (S i))))
       (functor_identity C) (pr2 (dob cAB j)) ⟧.
Proof.
  apply BinProductOfArrows; [apply (dmor cAB (idpath _)) | apply identity ].
Defined.

Local Lemma fNat : ∏ i u v (e : edge u v),
   dmor (mapchain (constprod_functor1 PC _) cB) e · f i v =
   f i u · dmor (mapchain (constprod_functor1 PC _) cB) e.
Proof.
  intros i j k e; destruct e; simpl.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  eapply pathscomp0; [|eapply pathsinv0; apply BinProductOfArrows_comp].
  now rewrite !id_left, !id_right.
Qed.

(* Define the chain A_i * M *)
Local Definition AiM_chain : chain C.
Proof.
  use tpair.
  - intro i; apply (lim (CCAiB i)).
  - intros i j e; destruct e.
    apply (limOfArrows (CCAiB i) (CCAiB (S i)) (f i) (fNat i)).
Defined.

Local Lemma AiM_chain_eq : ∏ i, dmor AiM_chain (idpath (S i)) =
                       dmor (mapchain (constprod_functor2 PC M) cA) (idpath _).
Proof.
  intro i; simpl; unfold limOfArrows, BinProduct_of_functors_mor; simpl.
  apply pathsinv0, limArrowUnique.
  simpl; intro j.
  unfold limIn; simpl; unfold BinProduct_of_functors_mor, f; simpl.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  apply pathsinv0.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  now rewrite !id_left, !id_right.
Qed.

(* Define a cone over K from the A_i * M chain *)
Local Lemma ccAiM_K_subproof : forms_cone (mapdiagram (constprod_functor2 PC M) cA)
                                            (fun u => limArrow (CCAiB u) K (ccAiB_K u)).
Proof.
  intros i j e; destruct e; simpl.
  generalize (AiM_chain_eq i); simpl; intro H; rewrite <- H; clear H; simpl.
  eapply pathscomp0.
  apply (precompWithLimOfArrows _ _ (CCAiB i) (CCAiB (S i)) _ _ K (ccAiB_K (S i))).
  apply (limArrowUnique (CCAiB i) K (ccAiB_K i)).
  simpl; intros j.
  eapply pathscomp0; [apply (limArrowCommutes (CCAiB i) K)|]; simpl.
  unfold map_to_K.
  destruct (natlthorgeh (S i) j).
  + destruct (natlthorgeh i j).
    * rewrite assoc; apply cancel_postcomposition.
      unfold f, fun_lt; simpl.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      now rewrite id_right, <- (chain_mor_right h0 h).
    * destruct (isasymmnatgth _ _ h h0).
  + destruct (natgehchoice (S i) j h).
    * destruct h.
      { destruct (natlthorgeh i j).
        - destruct (natlthchoice2 _ _ h) as [h2|h2].
          + destruct (isirreflnatlth _ (istransnatlth _ _ _ h0 h2)).
          + destruct h2; destruct (isirreflnatlth _ h0).
        - destruct (natgehchoice i j h).
          + destruct h.
            rewrite <- (coneOutCommutes ccK i _ (idpath _)); simpl.
            rewrite !assoc; apply cancel_postcomposition.
            unfold f, fun_gt.
            rewrite BinProductOfArrows_comp.
            eapply pathscomp0; [apply BinProductOfArrows_comp|].
            now rewrite !id_left, !id_right, <- (chain_mor_left h1 h0).
          + destruct p.
            rewrite <- (coneOutCommutes ccK i _ (idpath _)), assoc.
            apply cancel_postcomposition.
            unfold f, fun_gt.
            eapply pathscomp0; [apply BinProductOfArrows_comp|].
            rewrite id_left, id_right.
            apply (maponpaths_12 (BinProductOfArrows _ _ _)); trivial; simpl.
            destruct (natlehchoice4 i i h0); [destruct (isirreflnatlth _ h1)|].
            apply maponpaths, maponpaths, isasetnat.
       }
    * destruct p, h.
      destruct (natlthorgeh i (S i)); [|destruct (negnatgehnsn _ h)].
      apply cancel_postcomposition; unfold f, fun_lt.
      apply maponpaths_12; trivial; simpl.
      destruct (natlehchoice4 i i h); [destruct (isirreflnatlth _ h0)|].
      assert (H : idpath (S i) = maponpaths S p). apply isasetnat.
      now rewrite H.
Qed.

Local Definition ccAiM_K := make_cone _ ccAiM_K_subproof.

Local Lemma is_cone_morphism :
 ∏ v : nat,
   BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
     (pr1 (coneOut ccLM v)) (pr2 (coneOut ccLM v)) ·
   limArrow HAiM K ccAiM_K = coneOut ccK v.
Proof.
  intro i.
  generalize (limArrowCommutes HAiM K ccAiM_K i).
  assert (H : coneOut ccAiM_K i = limArrow (CCAiB i) K (ccAiB_K i)).
  { apply idpath. }
  rewrite H; intros HH.
  generalize (limArrowCommutes (CCAiB i) K (ccAiB_K i) i).
  rewrite <- HH; simpl; unfold map_to_K.
  destruct (natlthorgeh i i); [destruct (isirreflnatlth _ h)|].
  destruct (natgehchoice i i h); [destruct (isirreflnatgth _ h0)|].
  simpl; destruct h, p.
  intros HHH.
  rewrite <- HHH, assoc.
  apply cancel_postcomposition.
  unfold limIn; simpl; unfold BinProduct_of_functors_mor; simpl.
  apply pathsinv0.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  now rewrite id_left, id_right.
Qed.

Local Lemma is_unique_cone_morphism :
 ∏ t : ∑ x : C ⟦ BinProductObject C (PC L M), K ⟧,
       ∏ v : nat,
       BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
         (pr1 (coneOut ccLM v)) (pr2 (coneOut ccLM v)) · x =
       coneOut ccK v, t = limArrow HAiM K ccAiM_K,, is_cone_morphism.
Proof.
  intro t.
  apply subtypePath; simpl.
  + intro; apply impred; intros; apply homset_property.
  + apply (limArrowUnique HAiM K ccAiM_K).
    induction t as [t p]; simpl; intro i.
    apply (limArrowUnique (CCAiB i) K (ccAiB_K i)).
    simpl; intros j; unfold map_to_K.
    induction (natlthorgeh i j) as [h|h].
    * rewrite <- (p j); unfold fun_lt.
      rewrite !assoc.
      apply cancel_postcomposition.
      unfold limIn; simpl; unfold BinProduct_of_functors_mor; simpl.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      apply pathsinv0.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      rewrite !id_left, id_right.
      apply maponpaths_12; trivial.
      apply (maponpaths pr1 (chain_mor_coneOut cAB LM ccLM i j h)).
    * destruct (natgehchoice i j h).
      { unfold fun_gt; rewrite <- (p i), !assoc.
        apply cancel_postcomposition.
        unfold limIn; simpl; unfold BinProduct_of_functors_mor; simpl.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        apply pathsinv0.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        rewrite !id_left, id_right.
        set (X := (chain_mor_coneOut cAB LM ccLM _ _ h0)).
        apply maponpaths.
        etrans. 2: { apply maponpaths. apply X. }
              apply idpath.
      }
      { destruct p0.
        rewrite <- (p i), assoc.
        apply cancel_postcomposition.
        unfold limIn; simpl; unfold BinProduct_of_functors_mor; simpl.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        now rewrite id_left, id_right. }
Qed.

Local Definition isLimProductOfLims :  ∃! x : C ⟦ BinProductObject C (PC L M), K ⟧,
   ∏ v : nat,
   BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
     (pr1 (coneOut ccLM v)) (pr2 (coneOut ccLM v)) · x =
   coneOut ccK v.
Proof.
use tpair.
- use tpair.
  + apply (limArrow HAiM K ccAiM_K).
  + cbn. apply is_cone_morphism.
- cbn. apply is_unique_cone_morphism.
Defined.

End omega_cont_binproduct.

Lemma is_omega_cont_binproduct_functor : is_omega_cont (binproduct_functor PC).
Proof.
  intros cAB LM ccLM HccLM K ccK; simpl in *.
  cbn.
apply isLimProductOfLims, HccLM.
Defined.

End binprod_functor. *)

(** ** Binary product of functors: F * G : C -> D is omega continuous *)
(* Section BinProduct_of_functors.

Context {C D : category} (PC : BinProducts C) (PD : BinProducts D).

Variable omega_cont_constprod_functor1 :
  ∏ x : D, is_omega_cont (constprod_functor1 PD x).

Lemma is_omega_cont_BinProduct_of_functors_alt (F G : functor C D)
  (HF : is_omega_cont F) (HG : is_omega_cont G) :
  is_omega_cont (BinProduct_of_functors_alt PD F G).
Proof.
apply is_omega_cont_functor_composite.
- apply (is_omega_cont_bindelta_functor PC).
- apply is_omega_cont_functor_composite.
  + apply (is_omega_cont_pair_functor _ _ HF HG).
  + now apply is_omega_cont_binproduct_functor.
Defined.

Definition omega_cont_BinProduct_of_functors_alt (F G : omega_cont_functor C D) :
  omega_cont_functor C D :=
    tpair _ _ (is_omega_cont_BinProduct_of_functors_alt _ _ (pr2 F) (pr2 G)).

Lemma is_omega_cont_BinProduct_of_functors (F G : functor C D)
  (HF : is_omega_cont F) (HG : is_omega_cont G) :
  is_omega_cont (BinProduct_of_functors _ _ PD F G).
Proof.
exact (transportf _
        (BinProduct_of_functors_alt_eq_BinProduct_of_functors C D PD F G)
        (is_omega_cont_BinProduct_of_functors_alt _ _ HF HG)).
Defined.

Definition omega_cont_BinProduct_of_functors (F G : omega_cont_functor C D) :
  omega_cont_functor C D :=
    tpair _ _ (is_omega_cont_BinProduct_of_functors _ _ (pr2 F) (pr2 G)).

End BinProduct_of_functors. *)

(** ** Direct proof that the precomposition functor is continuous *)
Section pre_composition_functor.

Context {A B C : category} (F : functor A B).
(* Context (CC : Lims C). *) (* This is too strong *)

Lemma preserves_limit_pre_composition_functor {g : graph}
  (d : diagram g [B, C]) (G : [B, C])
  (ccG : cone d G) (H : ∏ b, LimCone (diagram_pointwise d b)) :
  preserves_limit (pre_composition_functor A B C F) d G ccG.
Proof.
  intros HccG.
  Search "LimFunctor".
  (* apply isLimFunctor_is_pointwise_Lim.

  Search "pointwise_Lim".

     apply   point               wise_Lim_is_isLimFunctor; intro a.
      now apply (isLimFunctor_is                          _pointwise_Lim _ H _ _ HccG).
Defined. *)


Admitted.



(* Lemma is_cont_pre_composition_functor *)
(*   (H : ∏ (g : graph) (d : diagram g [B,C,hsC]) (b : B), *)
(*        LimCone (diagram_pointwise hsC d b)) : *)
(*   is_cont (pre_composition_functor _ _ _ hsB hsC F). *)
(* Proof. *)
(* now intros g d G ccG; apply preserves_limit_pre_composition_functor. *)
(* Defined. *)


Lemma is_omega_cont_pre_composition_functor
  (H : Lims_of_shape nat_graph C) :
  is_omega_cont (pre_composition_functor _ _ C F).
Proof.
now intros c L ccL; apply preserves_limit_pre_composition_functor.
Defined.

Definition omega_cont_pre_composition_functor
  (H : Lims_of_shape nat_graph C) :
  omega_cont_functor [B, C] [A, C] :=
  tpair _ _ (is_omega_cont_pre_composition_functor H).

End pre_composition_functor.

(** ** Precomposition functor is continuous using construction of right Kan extensions *)
Section pre_composition_functor_kan.

Context {A B C : category} (F : functor A B).
Context (LC : Lims C).

Lemma is_cont_pre_composition_functor_kan :
  is_cont (pre_composition_functor _ _ C F).
Proof.
  apply right_adjoint_cont; try apply functor_category_has_homsets.
  apply (RightKanExtension_from_limits _ _ _ _ LC).
Qed.

Lemma is_omega_cont_pre_composition_functor_kan :
  is_omega_cont (pre_composition_functor _ _ C F).
Proof.
  now intros c L ccL; apply is_cont_pre_composition_functor_kan.
Defined.

Definition omega_cont_pre_composition_functor_kan :
  omega_cont_functor [B, C] [A, C] :=
  tpair _ _ is_omega_cont_pre_composition_functor_kan.

End pre_composition_functor_kan.

Section post_composition_functor.

Context {C D E : category}.
Context (F : functor D E) (HF : is_left_adjoint F).

Lemma is_cont_post_composition_functor :
  is_cont (post_composition_functor C D E F).
Proof.
  apply left_adjoint_cont; try apply functor_category_has_homsets.
  apply (is_left_adjoint_post_composition_functor _ HF).
Defined.

Lemma is_omega_cont_post_composition_functor :
  is_omega_cont (post_composition_functor C D E F).
Proof.
  now intros c L ccL; apply is_cont_post_composition_functor.
Defined.

End post_composition_functor.

(** * Swapping of functor category arguments *)
Section functor_swap.

Lemma is_cont_functor_cat_swap (C D E : category) :
  is_cont (functor_cat_swap C D E).
Proof.
  apply left_adjoint_cont.
  apply is_left_adjoint_functor_cat_swap.
Defined.

Lemma is_omega_cont_functor_cat_swap (C D E : category) :
  is_omega_cont (functor_cat_swap C D E).
Proof.
  intros d L ccL HccL.
  apply (is_cont_functor_cat_swap _ _ _ _ d L ccL HccL).
Defined.

End functor_swap.

(** * The forgetful functor from Set/X to Set preserves limits *)
Section cont_slicecat_to_cat_HSET.

Local Notation "HSET / X" := (slice_cat HSET X) (only parsing).

Lemma preserves_limit_slicecat_to_cat_HSET (X : HSET)
  (g : graph) (d : diagram g (HSET / X)) (L : HSET / X) (ccL : cone d L) :
  preserves_limit (slicecat_to_cat HSET X) d L ccL.
Proof.
  apply left_adjoint_preserves_limit.
  - apply is_left_adjoint_slicecat_to_cat_HSET.
Defined.

Lemma is_cont_slicecat_to_cat_HSET (X : HSET) :
  is_cont (slicecat_to_cat HSET X).
Proof.
  intros g d L cc.
  now apply preserves_limit_slicecat_to_cat_HSET.
Defined.

Lemma is_omega_cont_slicecat_to_cat (X : HSET) :
  is_omega_cont (slicecat_to_cat HSET X).
Proof.
  intros d L cc.
  now apply preserves_limit_slicecat_to_cat_HSET.
Defined.

(** Direct proof that the forgetful functor Set/X to Set preserves limits *)
Lemma preserves_limit_slicecat_to_cat_HSET_direct (X : HSET)
  (g : graph) (d : diagram g (HSET / X)) (L : HSET / X) (ccL : cone d L) :
  preserves_limit (slicecat_to_cat HSET X) d L ccL.
Proof.
  intros HccL y ccy.
  set (CC := make_LimCone _ _ _ HccL).
  transparent assert (c : (HSET / X)).
  { use tpair.
    - exists (∑ (x : pr1 X), pr1 y).
      abstract (apply isaset_total2; intros; apply setproperty).
    - cbn. apply pr1.
  }
  transparent assert (cc : (cone d c)).
  { use make_cone.
    - intros n.
      use tpair; simpl.
      + intros z.
        use tpair.
        * exact (pr2 L (pr1 (coneOut ccL n) z)).
        * apply (coneOut ccy n z).
      + abstract (now apply funextsec; intro z;
                  apply (toforallpaths _ _ _ (pr2 (coneOut ccL n)) z)).
    - abstract (intros m n e; apply eq_mor_slicecat, funextsec; intro z;
                use total2_paths_f;
                [ apply (maponpaths _ (toforallpaths _ _ _
                                                     (maponpaths pr1 (coneOutCommutes ccL m n e)) z))|];
                cbn in *; induction (maponpaths pr1 _);
                simpl;
                now rewrite idpath_transportf, <- (coneOutCommutes ccy m n e)).
  }
  use unique_exists.
  - intros l; apply (pr2 (pr1 (limArrow CC c cc) l)).
  - simpl; intro n.
    apply funextsec; intro x; cbn.
    now etrans; [apply maponpaths,
        (toforallpaths _ _ _ (maponpaths pr1 (limArrowCommutes CC c cc n)) x)|].
  - intros z; apply impred_isaprop; intro n; apply setproperty.
  - simpl; intros f Hf.
    apply funextsec; intro l.
    transparent assert (k : (HSET/X⟦lim CC,c⟧)).
    { use tpair.
      - intros l'.
        exists (pr2 L l').
        apply (f l').
      - abstract (now apply funextsec).
    }
    assert (Hk : (∏ n, limIn CC n · k = coneOut cc n)).
    { intros n.
      apply subtypePath; [intros x; apply setproperty|].
      apply funextsec; intro z.
      use total2_paths_f; [apply idpath|].
      now rewrite idpath_transportf; cbn; rewrite <- (toforallpaths _ _ _ (Hf n) z).
    }
    apply (maponpaths dirprod_pr2
                      (toforallpaths _ _ _ (maponpaths pr1 (limArrowUnique CC c cc k Hk)) l)).
Defined.

End cont_slicecat_to_cat_HSET.
End cont_functors.

(** Specialized notations for HSET *)
Declare Scope cont_functor_hset_scope.
Delimit Scope cont_functor_hset_scope with CS.

Notation "' x" := (omega_cont_constant_functor x)
                    (at level 10) : cont_functor_hset_scope.

Notation "'Id'" := (omega_cont_functor_identity _) :
                     cont_functor_hset_scope.

Notation "F * G" :=
  (omega_cont_BinProduct_of_functors_alt BinProductsHSET _
     (is_omega_cont_constprod_functor1 _ Exponentials_HSET)
     F G) : cont_functor_hset_scope.

Notation "F + G" :=
  (omega_cont_BinCoproduct_of_functors_alt2
     BinCoproductsHSET BinProductsHSET F G) : cont_functor_hset_scope.

Notation "1" := (unitHSET) : cont_functor_hset_scope.
Notation "0" := (emptyHSET) : cont_functor_hset_scope.


Section NotationTest.
Variable A : HSET.

Local Open Scope cont_functor_hset_scope.

(** F(X) = 1 + (A * X) *)
Definition L_A : omega_cont_functor HSET HSET := '1 + 'A * Id.

End NotationTest.
*)
