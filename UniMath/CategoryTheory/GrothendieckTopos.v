(** * Grothendick toposes *)
(** ** Contents
- Definition of Grothendieck topology
 - Grothendieck topologies
 - Precategory of sheaves
- Grothendieck toposes
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.graphs.equalizers.
Require Import UniMath.CategoryTheory.sub_precategories.
Require Import UniMath.CategoryTheory.equivalences.

(** HSET Pullbacks and Equalizers from limits to direct definition *)
Section HSET_Structures.

  Definition HSET_Pullbacks : @limits.pullbacks.Pullbacks HSET :=
    equiv_Pullbacks_2 HSET has_homsets_HSET PullbacksHSET_from_Lims.

  Definition HSET_Equalizers: @limits.equalizers.Equalizers HSET :=
    equiv_Equalizers2 HSET has_homsets_HSET EqualizersHSET_from_Lims.

End HSET_Structures.

(** * Definiton of Grothendieck topology
    The following definition is a formalization of the definition in Sheaves in Geometry and Logic,
    Saunders Mac Lane and Ieke Moerdijk, pages 109 and 110.

    Grothendieck topology is a collection J(c) of subobjects of the Yoneda functor, for every object
    of C, such that:
    - The Yoneda functor y(c) is in J(c).
    - Pullback of a subobject in J(c) along any morphism h : c' --> c is in J(c')
    - If S is a subobject of y(c) such that for all objects c' and all morphisms
      h : c' --> c in C the pullback of S along h is in J(c'), then S is in J(c).
  *)
Section def_grothendiecktopology.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** A sieve on c is a subobject of the yoneda functor. *)
  Definition sieve (c : C) : UU :=
    Subobjectscategory
      (functor_category_has_homsets (opp_precat C) HSET has_homsets_HSET)
      (yoneda C hs c).

  (* Coq does not automatically convert the following types *)
  Definition FunctorPrecatObToFunctor
             (c : functor_precategory (opp_precat C) HSET has_homsets_HSET) :
    functor (opp_precat C) HSET := c.

  Definition FunctorPrecatMorToNatTrans
             {c c': functor_precategory (opp_precat C) HSET has_homsets_HSET} (h : c --> c') :
    nat_trans (FunctorPrecatObToFunctor c) (FunctorPrecatObToFunctor c') := h.

  Definition sieve_functor {c : C} (S : sieve c) : functor (opp_precat C) HSET :=
    precategory_object_from_sub_precategory_object _ _ (slicecat_ob_object _ _ S).

  Definition sieve_nat_trans {c : C} (S : sieve c) :
    nat_trans (sieve_functor S) (FunctorPrecatObToFunctor (yoneda C hs c)) :=
    precategory_morphism_from_sub_precategory_morphism _ _ _ _ (slicecat_ob_morphism _ _ S).


  (** ** Grothendieck topology *)

  Definition collection_of_sieves : UU := ∏ (c : C), hsubtype (sieve c).

  Definition isGrothendieckTopology_maximal_sieve (COS : collection_of_sieves) : UU :=
    ∏ (c : C), COS c (Subobjectscategory_ob
                        (functor_category_has_homsets (opp_precat C) HSET has_homsets_HSET)
                        (identity (yoneda C hs c)) (identity_isMonic _)).

  Definition isGrothendieckTopology_stability (COS : collection_of_sieves) : UU :=
    ∏ (c c' : C) (h : c' --> c) (s : sieve c),
    COS c s ->
    COS c' (PullbackSubobject
              _
              (FunctorcategoryPullbacks (opp_precat C) HSET has_homsets_HSET HSET_Pullbacks)
              s (yoneda_morphisms C hs _ _ h)).

  Definition isGrothendieckTopology_transitivity (COS : collection_of_sieves) : UU :=
    ∏ (c : C) (s : sieve c),
    (∏ (c' : C) (h : c' --> c),
     COS c' (PullbackSubobject
               _
               (FunctorcategoryPullbacks (opp_precat C) HSET has_homsets_HSET HSET_Pullbacks)
               s (yoneda_morphisms C hs _ _ h))
     -> COS c s).

  Definition isGrothendieckTopology (COS : collection_of_sieves) : UU :=
    (isGrothendieckTopology_maximal_sieve COS)
      × (isGrothendieckTopology_stability COS)
      × (isGrothendieckTopology_transitivity COS).

  Definition GrothendieckTopology : UU :=
    ∑ COS : collection_of_sieves, isGrothendieckTopology COS.

  (** Accessor functions *)
  Definition GrothendieckTopology_COS (GT : GrothendieckTopology) : collection_of_sieves := pr1 GT.

  Definition GrothendieckTopology_isGrothendieckTopology (GT : GrothendieckTopology) :
    isGrothendieckTopology (GrothendieckTopology_COS GT) := pr2 GT.


  (** ** Sheaves *)

  (** For some reason I need the following *)
  Definition Presheaf : UU := functor (opp_precat C) HSET.

  Definition PresheafToFunctor (P : Presheaf) : functor (opp_precat C) HSET := P.

  Definition mk_Presheaf (F : functor (opp_precat C) HSET) : Presheaf := F.

  (** This is a formalization of the definition on page 122 *)
  Definition isSheaf (P : Presheaf) (GT : GrothendieckTopology) : UU :=
    ∏ (c : C) (S : sieve c) (isCOS : GrothendieckTopology_COS GT c S)
      (τ : nat_trans (sieve_functor S) (PresheafToFunctor P)),
    iscontr (∑ η : nat_trans (FunctorPrecatObToFunctor (yoneda C hs c)) (PresheafToFunctor P),
                   nat_trans_comp _ _ _ (sieve_nat_trans S) η = τ).

  Lemma isaprop_isSheaf (GT : GrothendieckTopology) (P : Presheaf) : isaprop(isSheaf P GT).
  Proof.
    apply impred_isaprop; intros t.
    apply impred_isaprop; intros S.
    apply impred_isaprop; intros isCOS.
    apply impred_isaprop; intros τ.
    apply isapropiscontr.
  Qed.

  (** The category of sheaves is the full subcategory of presheaves consisting of the presheaves
      which satisfy the isSheaf proposition. *)
  Definition hsubtype_obs_isSheaf (GT : GrothendieckTopology) :
    hsubtype (functor_precategory (opp_precat C) HSET has_homsets_HSET) :=
    (fun P : functor_precategory (opp_precat C) HSET has_homsets_HSET =>
       hProppair _ (isaprop_isSheaf GT (mk_Presheaf P))).

  Definition categoryOfSheaves (GT : GrothendieckTopology) :
    sub_precategories (functor_precategory (opp_precat C) HSET has_homsets_HSET) :=
    full_sub_precategory (hsubtype_obs_isSheaf GT).

End def_grothendiecktopology.


(** * Definition of Grothendieck topos
    Grothendieck topos is a precategory which is equivalent to the category of sheaves on some
    Grothendieck topology. *)
Section def_grothendiecktopos.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Here (pr1 D) is the precategory which is equivalent to the precategory of sheaves on the
      Grothendieck topology (pr2 D). *)
  Definition GrothendieckTopos : UU :=
    ∑ D' : (∑ D : precategory × (GrothendieckTopology C hs),
                  functor (pr1 D) (categoryOfSheaves C hs (pr2 D))),
           (adj_equivalence_of_precats (pr2 D')).

  (** Accessor functions *)
  Definition GrothendieckTopos_precategory (GT : GrothendieckTopos) : precategory :=
    pr1 (pr1 (pr1 GT)).
  Coercion GrothendieckTopos_precategory : GrothendieckTopos >-> precategory.

  Definition GrothendieckTopos_GrothendieckTopology (GT : GrothendieckTopos) :
    GrothendieckTopology C hs := pr2 (pr1 (pr1 GT)).

  Definition GrothendieckTopos_functor (GT : GrothendieckTopos) :
    functor (GrothendieckTopos_precategory GT)
            (categoryOfSheaves C hs (GrothendieckTopos_GrothendieckTopology GT)) :=
    pr2 (pr1 GT).

  Definition GrothendieckTopos_equivalence (GT : GrothendieckTopos) :
    adj_equivalence_of_precats (GrothendieckTopos_functor GT) := pr2 GT.

End def_grothendiecktopos.
