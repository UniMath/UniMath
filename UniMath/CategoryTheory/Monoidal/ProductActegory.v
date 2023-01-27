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
(* Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat. *)
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.
(* Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects. *)

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section FixAMonoidalCategory.

  Context {V : category} (Mon_V : monoidal V). (** given the monoidal category that acts upon categories *)

Section BinaryProduct.

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

  (* TODO: projections are linear *)


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

  (* TODO: projections are linear *)

End Product.

End FixAMonoidalCategory.
