(** binary and I-indexed product of actegories w.r.t. the same acting monoidal category

author: Ralph Matthes, 2023
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
(* Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories. *)
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section FixAMonoidalCategory.

  Context {V : category} (Mon_V : monoidal V). (** given the monoidal category that acts upon categories *)

Section BinaryProduct.

Section OneProduct.

  Context {C D : category} (ActC : actegory Mon_V C) (ActD : actegory Mon_V D).

  Let CD : category := category_binproduct C D.

  Definition actegory_binprod_action_data : bifunctor_data V CD CD.
  Proof.
    use make_bifunctor_data.
    * intros v cd.
      exact (v ⊗_{ActC} (pr1 cd),, v ⊗_{ActD} (pr2 cd)).
    * intros v cd1 cd2 fg.
      exact (v ⊗^{ActC}_{l} (pr1 fg),, v ⊗^{ActD}_{l} (pr2 fg)).
    * intros cd v1 v2 h.
      exact (h ⊗^{ActC}_{r} (pr1 cd),, h ⊗^{ActD}_{r} (pr2 cd)).
  Defined.

  Lemma actegory_binprod_action_data_is_bifunctor : is_bifunctor actegory_binprod_action_data.
  Proof.
    red; repeat split.
    * intros v cd.
      apply dirprodeq; apply bifunctor_leftid.
    * intros cd v.
      apply dirprodeq; apply bifunctor_rightid.
    * intros v cd1 cd2 cd3 fg1 fg2.
      apply dirprodeq; apply bifunctor_leftcomp.
    * intros cd v1 v2 v3 h1 h2.
      apply dirprodeq; apply bifunctor_rightcomp.
    * intros v1 v2 cd1 cd2 h fg.
      apply dirprodeq; apply bifunctor_equalwhiskers.
  Qed.

  Definition actegory_binprod_action : action(V:=V) CD := _,,actegory_binprod_action_data_is_bifunctor.

  Definition actegory_binprod_data : actegory_data Mon_V CD.
  Proof.
    use make_actegory_data.
    - exact actegory_binprod_action.
    - intros cd.
      exact (catbinprodmor (au_{ActC} _) (au_{ActD} _)).
    - intros cd.
      exact (catbinprodmor (auinv^{ActC}_{_}) (auinv^{ActD}_{_})).
    - intros v w cd.
      exact (catbinprodmor (aα^{ActC}_{_,_,_}) (aα^{ActD}_{_,_,_})).
    - intros v w cd.
      exact (catbinprodmor (aαinv^{ActC}_{_,_,_}) (aαinv^{ActD}_{_,_,_})).
  Defined.

  Lemma actegory_binprod_laws : actegory_laws Mon_V actegory_binprod_data.
  Proof.
    red; repeat split; try red; intros.
    - apply dirprodeq; apply actegory_unitornat.
    - apply dirprodeq; apply actegory_unitorisolaw.
    - apply dirprodeq; apply actegory_unitorisolaw.
    - apply dirprodeq; apply actegory_actornatleft.
    - apply dirprodeq; apply actegory_actornatright.
    - apply dirprodeq; apply actegory_actornatleftright.
    - apply dirprodeq; apply actegory_actorisolaw.
    - apply dirprodeq; apply actegory_actorisolaw.
    - apply dirprodeq; apply actegory_triangleidentity.
    - apply dirprodeq; apply actegory_pentagonidentity.
  Qed.

  Definition actegory_binprod : actegory Mon_V CD := _,,actegory_binprod_laws.

  Definition actegory_binprod_pr1_lineator_data :
    lineator_data Mon_V actegory_binprod ActC (pr1_functor C D).
  Proof.
    intros v cd. apply identity.
  Defined.

  Lemma actegory_binprod_pr1_lineator_lax_laws :
    lineator_laxlaws _ _ _ _ actegory_binprod_pr1_lineator_data.
  Proof.
    red; repeat split; red; intros.
    - rewrite id_left. apply id_right.
    - rewrite id_left. apply id_right.
    - cbn. unfold actegory_binprod_pr1_lineator_data.
      rewrite id_left, id_right.
      etrans.
      2: { apply maponpaths.
           apply pathsinv0, (functor_id (leftwhiskering_functor ActC v)). }
      apply pathsinv0, id_right.
    - apply id_left.
  Qed.

  Definition actegory_binprod_pr1_lineator :
    lineator Mon_V actegory_binprod ActC (pr1_functor C D).
  Proof.
    use tpair.
    - exists actegory_binprod_pr1_lineator_data.
      exact actegory_binprod_pr1_lineator_lax_laws.
    - intros v vd.
      use tpair.
      + apply identity.
      + red; split; apply id_left.
  Defined.

  Definition actegory_binprod_pr2_lineator_data :
    lineator_data Mon_V actegory_binprod ActD (pr2_functor C D).
  Proof.
    intros v cd. apply identity.
  Defined.

  Lemma actegory_binprod_pr2_lineator_lax_laws :
    lineator_laxlaws _ _ _ _ actegory_binprod_pr2_lineator_data.
  Proof.
    red; repeat split; red; intros.
    - rewrite id_left. apply id_right.
    - rewrite id_left. apply id_right.
    - cbn. unfold actegory_binprod_pr2_lineator_data.
      rewrite id_left, id_right.
      etrans.
      2: { apply maponpaths.
           apply pathsinv0, (functor_id (leftwhiskering_functor ActD v)). }
      apply pathsinv0, id_right.
    - apply id_left.
  Qed.

  Definition actegory_binprod_pr2_lineator :
    lineator Mon_V actegory_binprod ActD (pr2_functor C D).
  Proof.
    use tpair.
    - exists actegory_binprod_pr2_lineator_data.
      exact actegory_binprod_pr2_lineator_lax_laws.
    - intros v cd.
      use tpair.
      + apply identity.
      + red; split; apply id_left.
  Defined.

End OneProduct.

Section SelfProduct.

  Context {C : category} (Act : actegory Mon_V C).

  Definition actegory_binprod_delta_lineator_data :
    lineator_data Mon_V Act (actegory_binprod Act Act) (bindelta_functor C).
  Proof.
    intros v c. apply identity.
  Defined.

  Lemma actegory_binprod_delta_lineator_lax_laws :
    lineator_laxlaws _ _ _ _ actegory_binprod_delta_lineator_data.
  Proof.
    red; repeat split; red; intros.
    - cbn. apply maponpaths_12; (rewrite id_left; apply id_right).
    - cbn. apply maponpaths_12; (rewrite id_left; apply id_right).
    - cbn.
      apply maponpaths_12; unfold actegory_binprod_pr2_lineator_data;
        (rewrite id_left, id_right);
        (etrans; [| apply maponpaths;
                   apply pathsinv0, (functor_id (leftwhiskering_functor Act v))];
        apply pathsinv0, id_right).
    - cbn. apply maponpaths_12; apply id_left.
  Qed.

  Definition actegory_binprod_delta_lineator :
    lineator Mon_V Act (actegory_binprod Act Act) (bindelta_functor C).
  Proof.
    use tpair.
    - exists actegory_binprod_delta_lineator_data.
      exact actegory_binprod_delta_lineator_lax_laws.
    - intros v c.
      use tpair.
      + apply identity.
      + red; split; apply id_left.
  Defined.

End SelfProduct.

Section TwoProducts.

  Context {C1 C2 D1 D2 : category} (ActC1 : actegory Mon_V C1) (ActC2 : actegory Mon_V C2)
    (ActD1 : actegory Mon_V D1) (ActD2 : actegory Mon_V D2)
    {F1 : functor C1 D1} {F2 : functor C2 D2 }
    (Fll1 : lineator_lax Mon_V ActC1 ActD1 F1) (Fll2 : lineator_lax Mon_V ActC2 ActD2 F2).

  Let ActC12 : actegory Mon_V (category_binproduct C1 C2) := actegory_binprod ActC1 ActC2.
  Let ActD12 : actegory Mon_V (category_binproduct D1 D2) := actegory_binprod ActD1 ActD2.

  Definition actegory_pair_functor_lineator_data :
    lineator_data Mon_V ActC12 ActD12 (pair_functor F1 F2).
  Proof.
    intros v c12. cbn. unfold precategory_binproduct_mor. cbn.
    exact (catbinprodmor (Fll1 v (pr1 c12)) (Fll2 v (pr2 c12))).
  Defined.

  Lemma actegory_pair_functor_lineator_lax_laws :
    lineator_laxlaws _ _ _ _ actegory_pair_functor_lineator_data.
  Proof.
    red; repeat split; red; intros.
    - cbn. apply maponpaths_12; apply lineator_linnatleft.
    - cbn. apply maponpaths_12; apply lineator_linnatright.
    - cbn. apply maponpaths_12; apply lineator_preservesactor.
    - cbn. apply maponpaths_12; apply lineator_preservesunitor.
  Qed.

  Definition actegory_pair_functor_lineator :
    lineator_lax Mon_V ActC12 ActD12 (pair_functor F1 F2) :=
    _,,actegory_pair_functor_lineator_lax_laws.

End TwoProducts.

End BinaryProduct.

Section Product.

  Context {I: UU} {C : I -> category} {D : category} (ActC : ∏ i: I, actegory Mon_V (C i)) (ActD : actegory Mon_V D).

  Let PC : category := product_category C.


Definition actegory_prod_action_data : bifunctor_data V PC PC.
  Proof.
    use make_bifunctor_data.
    * intros v cs.
      exact (fun (i: I) => v ⊗_{ActC i} (cs i)).
    * intros v cs1 cs2 fs.
      exact (fun (i: I) => v ⊗^{ActC i}_{l} (fs i)).
    * intros cs v1 v2 h.
      exact (fun (i: I) => h ⊗^{ActC i}_{r} (cs i)).
  Defined.

  Lemma actegory_prod_action_data_is_bifunctor : is_bifunctor actegory_prod_action_data.
  Proof.
    red; repeat split.
    * intros v cs.
      apply funextsec; intro i; apply bifunctor_leftid.
    * intros cs v.
      apply funextsec; intro i; apply bifunctor_rightid.
    * intros v cs1 cs2 cs3 fs1 fs2.
      apply funextsec; intro i; apply bifunctor_leftcomp.
    * intros cs v1 v2 v3 h1 h2.
      apply funextsec; intro i; apply bifunctor_rightcomp.
    * intros v1 v2 cs1 cs2 h fs.
      apply funextsec; intro i; apply bifunctor_equalwhiskers.
  Qed.

  Definition actegory_prod_action : action(V:=V) PC := _,,actegory_prod_action_data_is_bifunctor.

  Definition actegory_prod_data : actegory_data Mon_V PC.
  Proof.
    use make_actegory_data.
    - exact actegory_prod_action.
    - intros cs.
      intro i. apply au_{ActC i}.
    - intros cs.
      intro i. exact (auinv^{ActC i}_{_}).
    - intros v w cs.
      intro i. exact (aα^{ActC i}_{_,_,_}).
    - intros v w cs.
      intro i. exact (aαinv^{ActC i}_{_,_,_}).
  Defined.

  Lemma actegory_prod_laws : actegory_laws Mon_V actegory_prod_data.
  Proof.
    red; repeat split; try red; intros; apply funextsec; intro i.
    - apply actegory_unitornat.
    - apply actegory_unitorisolaw.
    - apply actegory_unitorisolaw.
    - apply actegory_actornatleft.
    - apply actegory_actornatright.
    - apply actegory_actornatleftright.
    - apply actegory_actorisolaw.
    - apply actegory_actorisolaw.
    - apply actegory_triangleidentity.
    - apply actegory_pentagonidentity.
  Qed.

  Definition actegory_prod : actegory Mon_V PC := _,,actegory_prod_laws.

  (* TODO: projections, delta_functor and family_functor are linear *)

End Product.

End FixAMonoidalCategory.
