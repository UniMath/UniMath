(**************************************************************************************************

  Constructing a functor to a total category via a functor to its base category

  For two categories C and C' and a displayed category D over C, we can construct some functors from
  C' to the total category ∫D from just a functor F : C' ⟶ C and a "functor lifting". A functor
  lifting gives displayed objects and morphisms above F c and #F f for all c : C' and f : C'⟦c, c'⟧,
  compatible with morphism composition.
  If F is the identity functor on C, this construction gives sections to the projection functor
  π1 : ∫D ⟶ C, because composing it with the projection gives the identity functor on C.
  In that case, the construction is functorial, and gives a functor from the category
  of displayed sections to the functor category [C, ∫D].

  Contents
  1. The construction of functors via lifting [lifted_functor]
  2. The special case where F is the identity
  2.1. The construction of a section from a displayed section [section_functor]
  2.2. The construction of a natural transformation from a morphism [section_nat_trans]
  2.3. The functor from displayed sections to the functor category [section_disp_to_section]

 **************************************************************************************************)
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.

(* Exporting for backwards compatibility *)
Require Export UniMath.CategoryTheory.DisplayedCats.Constructions.DisplayedSections.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** * 1. The construction of functors via lifting *)

Section FunctorLifting.

  Notation "# F" := (section_disp_on_morphisms F)
                      (at level 3) : mor_disp_scope.

  Context {C C' : category}.
  Context {D : disp_cat C}.
  Context {F : functor C' C}.

  Definition functor_lifting
    := section_disp (reindex_disp_cat F D).

  Identity Coercion section_from_functor_lifting
    : functor_lifting >-> section_disp.

  (** Note: perhaps it would be better to define [functor_lifting] directly?
  Reindexed displayed-cats are a bit confusing to work in, since a term like [id_disp xx] is ambiguous: it can mean both the identity in the original displayed category, or the identity in the reindexing, which is nearly but not quite the same.  This shows up already in the proofs of [lifted_functor_axioms] below. *)

  Definition lifted_functor_data
             (FF : functor_lifting)
    : functor_data C' (total_category D).
  Proof.
    exists (λ x, (F x ,, FF x)).
    intros x y f. exists (# F f)%cat. exact (# FF f).
  Defined.

  Definition lifted_functor_axioms
             (FF : functor_lifting)
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

  Definition lifted_functor
             (FF : functor_lifting)
    : functor C' (total_category D)
    := (_ ,, lifted_functor_axioms FF).

  Lemma from_lifted_functor
        (FF : functor_lifting):
    functor_composite (lifted_functor FF) (pr1_category D) = F.
  Proof.
    use (functor_eq _ _ (homset_property C)). apply idpath.
  Qed.

End FunctorLifting.

Arguments functor_lifting {C C'} D F.

(** * 2. The special case where F is the identity *)

Section Sections.

  Context {C : category}.
  Context {D : disp_cat C}.

(** ** 2.1. The construction of a section from a displayed section *)

  Section Ob.

    Context (sd : section_disp D).

    Definition section_functor_data
      : functor_data C (total_category D).
    Proof.
      exists (λ x, (x ,, sd x)).
      intros x y f. exists f. exact (section_disp_on_morphisms sd f).
    Defined.

    Definition section_functor_axioms
      : is_functor section_functor_data.
    Proof.
      split.
      - intro x. use total2_paths_f; simpl.
        + apply idpath.
        + apply (section_disp_id sd).
      - intros x y z f g. use total2_paths_f; simpl.
        + apply idpath.
        + apply (section_disp_comp sd).
    Qed.

    Definition section_functor :
      functor C (total_category D) :=
      section_functor_data ,, section_functor_axioms.

    Lemma from_section_functor :
      functor_composite section_functor (pr1_category D) = functor_identity C.
    Proof.
      use (functor_eq _ _ (homset_property C)). apply idpath.
    Qed.

  End Ob.

(** ** 2.2. The construction of a natural transformation from a morphism *)

  Section Mor.

    Context {F F': section_disp D}.
    Context (nt : section_nat_trans_disp F F').

    Definition section_nat_trans_data :
          nat_trans_data (section_functor F) (section_functor F').
    Proof.
      intro x.
      exists (identity _).
      exact (nt x).
    Defined.

    Definition section_nat_trans_axioms :
          is_nat_trans (section_functor F) (section_functor F') section_nat_trans_data.
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
        : nat_trans (section_functor F) (section_functor F') :=
      section_nat_trans_data ,, section_nat_trans_axioms.

  End Mor.

(** ** 2.3. The functor from displayed sections to the functor category *)

  Lemma section_id_nat_trans
    (F : section_disp D)
    : section_nat_trans (section_nat_trans_id F) = nat_trans_id (section_functor F).
  Proof.
    now apply nat_trans_eq_alt.
  Qed.

  Lemma section_comp_nat_trans
    {F F' F'' : section_disp D}
    (nt : section_nat_trans_disp F F')
    (nt' : section_nat_trans_disp F' F'')
    : section_nat_trans (section_nat_trans_comp nt nt')
    = nat_trans_comp _ _ _ (section_nat_trans nt) (section_nat_trans nt').
  Proof.
    apply nat_trans_eq_alt.
    intro c.
    use total2_paths_b.
    - exact (!id_left _).
    - apply (maponpaths (λ x, transportf _ x _)).
      exact (!pathsinv0inv0 _).
  Qed.

  Definition section_disp_to_section
    : section_disp_cat D ⟶ [C, total_category D].
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact section_functor.
      + do 2 intro.
        exact section_nat_trans.
    - split.
      + exact section_id_nat_trans.
      + do 3 intro.
        exact section_comp_nat_trans.
  Defined.

End Sections.

Arguments section_disp_to_section {C} D.
