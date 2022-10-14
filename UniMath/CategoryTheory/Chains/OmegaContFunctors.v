(** * ω-cocontinuous functors

This file contains theory about (omega-) continuous functors, i.e. functors
which preserve (sequential-) limits ([is_omega_cont] and [is_cont]).

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
        (com : coproducts_commute_with_limits D)
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
        (com : omega_coproducts_commute_with_limits D)
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
