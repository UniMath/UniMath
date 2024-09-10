Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** ** Functors into displayed categories *)

(** With sections defined, we can now define _lifts_ to a displayed category of a functor into the base. *)
Section Functor_Lifting.

  Notation "# F" := (section_disp_on_morphisms F)
                      (at level 3) : mor_disp_scope.

  Definition functor_lifting
             {C C' : category} (D : disp_cat C) (F : functor C' C)
    := section_disp (reindex_disp_cat F D).

  Identity Coercion section_from_functor_lifting
    : functor_lifting >-> section_disp.

  (** Note: perhaps it would be better to define [functor_lifting] directly?
  Reindexed displayed-cats are a bit confusing to work in, since a term like [id_disp xx] is ambiguous: it can mean both the identity in the original displayed category, or the identity in the reindexing, which is nearly but not quite the same.  This shows up already in the proofs of [lifted_functor_axioms] below. *)

  Definition lifted_functor_data {C C' : category} {D : disp_cat C}
             {F : functor C' C} (FF : functor_lifting D F)
    : functor_data C' (total_category D).
  Proof.
    exists (λ x, (F x ,, FF x)).
    intros x y f. exists (# F f)%cat. exact (# FF f).
  Defined.

  Definition lifted_functor_axioms {C C' : category} {D : disp_cat C}
             {F : functor C' C} (FF : functor_lifting D F)
    : is_functor (lifted_functor_data FF).
  Proof.
    split.
    - intros x. use total2_paths_f; simpl.
      apply functor_id.
      eapply pathscomp0. apply maponpaths, (section_disp_id FF).
      cbn. apply transportfbinv.
    - intros x y z f g. use total2_paths_f; simpl.
      apply functor_comp.
      eapply pathscomp0. apply maponpaths, (section_disp_comp FF).
      cbn. apply transportfbinv.
  Qed.

  Definition lifted_functor {C C' : category} {D : disp_cat C}
             {F : functor C' C} (FF : functor_lifting D F)
    : functor C' (total_category D)
    := (_ ,, lifted_functor_axioms FF).

  Lemma from_lifted_functor {C C' : category} {D : disp_cat C}
        {F : functor C' C} (FF : functor_lifting D F):
    functor_composite (lifted_functor FF) (pr1_category D) = F.
  Proof.
    use (functor_eq _ _ (homset_property C)). apply idpath.
  Qed.

  (** redo the development for the special case that F is the identity *)
  Definition section_functor_data {C : category} {D : disp_cat C} (sd : section_disp D)
    : functor_data C (total_category D).
  Proof.
    exists (λ x, (x ,, sd x)).
    intros x y f. exists f. exact (section_disp_on_morphisms sd f).
  Defined.

  Definition section_functor_axioms {C : category} {D : disp_cat C} (sd : section_disp D)
    : is_functor (section_functor_data sd).
  Proof.
    split.
    - intro x. use total2_paths_f; simpl.
      + apply idpath.
      + apply (section_disp_id sd).
    - intros x y z f g. use total2_paths_f; simpl.
      + apply idpath.
      + apply (section_disp_comp sd).
  Qed.

  Definition section_functor {C : category} {D : disp_cat C} (sd : section_disp D):
    functor C (total_category D) :=
    section_functor_data sd,, section_functor_axioms sd.

  Lemma from_section_functor {C : category} {D : disp_cat C} (sd : section_disp D):
    functor_composite (section_functor sd) (pr1_category D) = functor_identity C.
  Proof.
    use (functor_eq _ _ (homset_property C)). apply idpath.
  Qed.

End Functor_Lifting.

(* Natural transformations of sections  *)
Section Section_transformation.

Definition section_nat_trans_data
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
      nat_trans_data (section_functor F) (section_functor F').
Proof.
  intro x.
  exists (identity _).
  exact (nt x).
Defined.

Definition section_nat_trans_axioms
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
      is_nat_trans (section_functor F) (section_functor F') (section_nat_trans_data nt).
Proof.
  intros x x' f.
  use total2_paths_f.
  - simpl. now rewrite id_left, id_right.
  - simpl.
    rewrite <- (section_nt_disp_axioms_from_section_nt_disp nt).
    apply transportf_paths.
    apply homset_property.
Qed.

Definition section_nat_trans
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : nat_trans (section_functor F) (section_functor F') :=
  section_nat_trans_data nt,, section_nat_trans_axioms nt.

End Section_transformation.
