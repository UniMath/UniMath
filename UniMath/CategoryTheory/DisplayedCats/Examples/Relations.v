(* The category of relations:
   1. The objects are sets
   2. The morphisms are relations of sets
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

Section Relations.

  Definition hrel (X Y : hSet) : UU := X -> Y -> hProp.
  Identity Coercion idhrel : hrel >-> Funclass.

  Local Definition eq_set {X : hSet} (x y : X)
    : hProp.
  Proof.
    exists (x = y).
    apply (pr2 X).
  Defined.

  Definition REL_precategory_ob_mor
    : precategory_ob_mor
    := make_precategory_ob_mor hSet hrel.

  Definition REL_precategory_id_comp
    : precategory_id_comp REL_precategory_ob_mor.
  Proof.
    exists (λ _ x1 x2, eq_set x1 x2).
    exact (λ X Y Z r1 r2 x z, ∃ y : pr1 Y, r1 x y × r2 y z).
  Defined.

  Definition REL_precategory_data : precategory_data.
  Proof.
    exists REL_precategory_ob_mor.
    exact REL_precategory_id_comp.
  Defined.

  Lemma REL_is_precategory : is_precategory REL_precategory_data.
  Proof.
    repeat split ; intro ; intros ;
      repeat (apply funextsec ; intro) ;
      use hPropUnivalence.
    - intro p.
      use (factor_through_squash_hProp (f _ _) _ p).
      clear p ; intro p.
      induction (! pr12 p).
      exact (pr22 p).
    - intro p.
      apply hinhpr.
      exact (x ,, idpath _ ,, p).
    - intro p.
      use (factor_through_squash_hProp (f _ _) _ p).
      clear p ; intro p.
      induction (pr22 p).
      exact (pr12 p).
    - intro p.
      apply hinhpr.
      exact (x0 ,, p ,, idpath _).
    - intro p.
      use (factor_through_squash_hProp ((f · g · h) x x0) _ p).
      clear p ; intro p.

      use (factor_through_squash_hProp ((f · g · h) x x0) _ (pr22 p)).
      intro q.
      apply hinhpr.
      exists (pr1 q).
      use tpair.
      + apply hinhpr.
        exact (pr1 p ,, pr12 p ,, pr12 q).
      + exact (pr22 q).
    - intro p.
      use (factor_through_squash_hProp ((f · g · h) x x0) _ p).
      + clear p ; intro p.
        use (factor_through_squash_hProp ((f · g · h) x x0) _ (pr12 p)).
        intro q.
        apply hinhpr.
        exists (pr1 p).
        use tpair.
        * apply hinhpr.
          exact (pr1 q,,  pr12 q ,, pr22 q).
        * exact (pr22 p).
      + clear p ; intro p.
        use (factor_through_squash_hProp ((f · (g · h)) x x0) _ (pr12 p)).
        intro q.
        apply hinhpr.
        exists (pr1 q).
        use tpair.
        -- exact (pr12 q).
        -- use (factor_through_squash_hProp _ _ (pr12 p)).
           intro q0.
           apply hinhpr.
           exact (pr1 p ,, pr22 q ,, pr22 p).
    - intro p.
      use (factor_through_squash_hProp ((f · g · h) x x0) _ p).
      + clear p ; intro p.
        use (factor_through_squash_hProp ((f · g · h) x x0) _ (pr12 p)).
        intro q.
        apply hinhpr.
        exists (pr1 p).
        use tpair.
        * apply hinhpr.
          exact (pr1 q,,  pr12 q ,, pr22 q).
        * exact (pr22 p).
      + clear p ; intro p.
        use (factor_through_squash_hProp ((f · (g · h)) x x0) _ (pr12 p)).
        intro q.
        apply hinhpr.
        exists (pr1 q).
        use tpair.
        -- exact (pr12 q).
        -- use (factor_through_squash_hProp _ _ (pr12 p)).
           intro q0.
           apply hinhpr.
           exact (pr1 p ,, pr22 q ,, pr22 p).
    - intro p.
      use (factor_through_squash_hProp ((f · g · h) x x0) _ p).
      + clear p ; intro p.
        use (factor_through_squash_hProp _ _ (pr22 p)).
        intro q.
        apply hinhpr.
        exists (pr1 q).
        use tpair.
        * apply hinhpr.
          exact (pr1 p ,, pr12 p ,, pr12 q).
        * exact (pr22 q).
  Qed.

  Definition REL_precategory : precategory
    := _ ,, REL_is_precategory.

  Lemma REL_precategory_has_homsets
    : has_homsets REL_precategory.
  Proof.
    exact (λ _ _, isaset_set_fun_space (pr1 _) (_ ,, isaset_set_fun_space _ (_ ,, isasethProp))).
  Qed.

  Definition REL : category
    := REL_precategory ,, REL_precategory_has_homsets.

End Relations.
