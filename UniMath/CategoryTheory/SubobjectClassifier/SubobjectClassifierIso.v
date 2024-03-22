(*******************************************************************************************

 Subobject classifiers and isomorphisms

 This file is a collection of statements about isomorphisms and subobject classifiers. We
 show that
 - Any two subobject classifiers are isomorphic. This implies that the type of subobject
   classifiers in a category is a proposition.
 - If an object is isomorphic to a subobject classifier, then it is also a subobject
   classifier.
 For the second statement, we use univalent categories, because it simplifies the proof.

 Contents
 1. Isomorphisms between subobject classifiers
 2. Being isomorphic to subobject classifiers

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.

Local Open Scope cat.

(** * 1. Isomorphisms between subobject classifiers *)
Definition mor_subobject_classifier
           {C : category}
           {T : Terminal C}
           (Ω Ω' : subobject_classifier T)
  : Ω --> Ω'.
Proof.
  use characteristic_morphism.
  - exact T.
  - exact (true Ω).
Defined.

Proposition mor_subobject_classifier_inv
            {C : category}
            {T : Terminal C}
            (Ω Ω' : subobject_classifier T)
  : mor_subobject_classifier Ω Ω' · mor_subobject_classifier Ω' Ω = identity Ω.
Proof.
  use subobject_classifier_map_eq.
  - exact T.
  - exact (true Ω).
  - abstract
      (cbn ;
       unfold mor_subobject_classifier ;
       rewrite !assoc ;
       refine (maponpaths
                 (λ z, z · _)
                 (subobject_classifier_square_commutes Ω' (true Ω))
               @ _) ;
       rewrite assoc' ;
       refine (maponpaths
                 (λ z, _ · z)
                 (subobject_classifier_square_commutes Ω (true Ω'))
               @ _) ;
       unfold const_true ; cbn ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - abstract
      (unfold const_true ;
       rewrite id_right ;
       refine (!(id_left _) @ _) ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - use (isPullback_mor_paths
           _ _ _ _ _ _
           (isPullback_Pullback
              (pullback_glue_pullback
                 _
                 (subobject_classifier_pullback Ω (true Ω'))
                 (subobject_classifier_pullback Ω' (true Ω))))).
    + apply idpath.
    + apply idpath.
    + apply idpath.
    + apply TerminalArrowEq.
  - use (isPullback_mor_paths
           _ _ _ _ _ _
           (isPullback_Pullback (subobject_classifier_pullback Ω (true Ω)))).
    + apply characteristic_morphism_true.
    + apply idpath.
    + apply idpath.
    + apply idpath.
Qed.

Proposition z_iso_subobject_classifier_inverse
            {C : category}
            {T : Terminal C}
            (Ω Ω' : subobject_classifier T)
  : is_inverse_in_precat
      (mor_subobject_classifier Ω Ω')
      (mor_subobject_classifier Ω' Ω).
Proof.
  split.
  - exact (mor_subobject_classifier_inv Ω Ω').
  - exact (mor_subobject_classifier_inv Ω' Ω).
Qed.

Definition z_iso_subobject_classifier
           {C : category}
           {T : Terminal C}
           (Ω Ω' : subobject_classifier T)
  : z_iso Ω Ω'.
Proof.
  use make_z_iso.
  - exact (mor_subobject_classifier Ω Ω').
  - exact (mor_subobject_classifier Ω' Ω).
  - exact (z_iso_subobject_classifier_inverse Ω Ω').
Defined.

Definition isaprop_subobject_classifier'
           {C : category}
           (HC : is_univalent C)
           (T : Terminal C)
  : isaprop (subobject_classifier T).
Proof.
  use invproofirrelevance.
  intros Ω Ω'.
  use total2_paths_f.
  - exact (isotoid _ HC (z_iso_subobject_classifier Ω Ω')).
  - use subtypePath.
    {
      intro.
      apply isaprop_is_subobject_classifier.
    }
    rewrite pr1_transportf.
    rewrite transportf_isotoid'.
    cbn.
    unfold mor_subobject_classifier.
    etrans.
    {
      apply (subobject_classifier_square_commutes Ω' (true Ω)).
    }
    refine (_ @ id_left _) ; cbn.
    apply maponpaths_2.
    apply TerminalArrowEq.
Qed.

Definition isaprop_subobject_classifier
           {C : univalent_category}
           (T : Terminal C)
  : isaprop (subobject_classifier T).
Proof.
  use isaprop_subobject_classifier'.
  exact (univalent_category_is_univalent C).
Qed.

(** * 2. Being isomorphic to subobject classifiers *)
Definition eq_to_is_subobject_classifier
           {C : category}
           {T : Terminal C}
           (Ω : subobject_classifier T)
           (Ω' : C)
           (t : T --> Ω')
           (p : (Ω : C) = Ω')
           (q : true Ω · idtoiso p = t)
  : is_subobject_classifier T Ω' t.
Proof.
  induction p.
  cbn in q.
  rewrite id_right in q.
  induction q.
  apply (pr2 Ω).
Qed.

Proposition z_iso_to_is_subobject_classifier
           {C : univalent_category}
           {T : Terminal C}
           (Ω : subobject_classifier T)
           (Ω' : C)
           (t : T --> Ω')
           (f : z_iso Ω Ω')
           (q : true Ω · f = t)
  : is_subobject_classifier T Ω' t.
Proof.
  use eq_to_is_subobject_classifier.
  - exact Ω.
  - exact (isotoid C (univalent_category_is_univalent C) f).
  - rewrite idtoiso_isotoid.
    exact q.
Qed.
