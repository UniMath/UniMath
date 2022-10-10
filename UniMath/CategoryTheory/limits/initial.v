(**

Direct definition of initial object together with:

- A proof that initial object is a property in a (saturated/univalent) category ([isaprop_Initial])
- Construction of initial from the empty coproduct ([initial_from_empty_coproduct])
- Initial element in a functor precategory ([Initial_functor_precat])

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.coproducts.

Local Open Scope cat.

Section def_initial.

Definition isInitial {C : precategory} (a : C) : UU := ∏ b : C, iscontr (a --> b).

Definition Initial (C : precategory) : UU := ∑ a, @isInitial C a.

Definition InitialObject {C : precategory} (O : Initial C) : C := pr1 O.
Coercion InitialObject : Initial >-> ob.

Definition InitialArrow {C : precategory} (O : Initial C) (b : C) : O --> b := pr1 (pr2 O b).

Lemma InitialArrowUnique {C : precategory} {I : Initial C} {a : C} (f : C⟦InitialObject I,a⟧) :
  f = InitialArrow I _.
Proof.
exact (pr2 (pr2 I _ ) _ ).
Defined.

Lemma InitialEndo_is_identity {C : precategory} {O : Initial C} (f : O --> O) : f = identity O.
Proof.
apply proofirrelevancecontr, (pr2 O O).
Qed.

Lemma InitialArrowEq {C : precategory} {O : Initial C} {a : C} (f g : O --> a) : f = g.
Proof.
now rewrite (InitialArrowUnique f), (InitialArrowUnique g).
Qed.

Definition make_Initial {C : precategory} (a : C) (H : isInitial a) : Initial C.
Proof.
  exists a.
  exact H.
Defined.

Definition make_isInitial {C : precategory} (a : C) (H : ∏ (b : C), iscontr (a --> b)) :
  isInitial a.
Proof.
  exact H.
Defined.

Lemma isziso_from_Initial_to_Initial {C : precategory} (O O' : Initial C) :
   is_z_isomorphism (InitialArrow O O').
Proof.
  exists (InitialArrow O' O).
  split; apply InitialEndo_is_identity.
Defined.

Definition ziso_Initials {C : precategory} (O O' : Initial C) : z_iso O O' :=
   (InitialArrow O O',,isziso_from_Initial_to_Initial O O').

Definition hasInitial {C : precategory} : UU := ishinh (Initial C).

End def_initial.

Arguments Initial : clear implicits.
Arguments isInitial : clear implicits.
Arguments InitialObject {_} _.
Arguments InitialArrow {_} _ _.
Arguments InitialArrowUnique {_} _ _ _.
Arguments make_isInitial {_} _ _ _.
Arguments make_Initial {_} _ _.


(** * Being initial is a property in a (saturated/univalent) category *)
Section Initial_Unique.

  Variable C : category.
  Hypothesis H : is_univalent C.

Lemma isaprop_Initial : isaprop (Initial C).
Proof.
  apply invproofirrelevance.
  intros O O'.
  apply (total2_paths_f (isotoid _ H (ziso_Initials O O')) ).
  apply proofirrelevance.
  unfold isInitial.
  apply impred.
  intro t ; apply isapropiscontr.
Qed.

End Initial_Unique.


Section Initial_and_EmptyCoprod.

  (** Construct Initial from empty arbitrary coproduct. *)
  Definition initial_from_empty_coproduct (C : category):
    Coproduct empty C fromempty -> Initial C.
  Proof.
    intros X.
    use (make_Initial (CoproductObject _ _ X)).
    use make_isInitial.
    intros b.
    assert (H : ∏ i : empty, C⟦fromempty i, b⟧) by
        (intros i; apply (fromempty i)).
    apply (make_iscontr (CoproductArrow _ _ X H)); intros t.
    apply CoproductArrowUnique; intros i; apply (fromempty i).
  Defined.

End Initial_and_EmptyCoprod.

(* Section Initial_from_Colims. *)

(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)

(* Variable C : precategory. *)

(* Definition empty_graph : graph. *)
(* Proof. *)
(*   exists empty. *)
(*   exact (λ _ _, empty). *)
(* Defined. *)

(* Definition initDiagram : diagram empty_graph C. *)
(* Proof. *)
(* exists fromempty. *)
(* intros u; induction u. *)
(* Defined. *)

(* Definition initCocone (b : C) : cocone initDiagram b. *)
(* Proof. *)
(* simple refine (make_cocone _ _); intros u; induction u. *)
(* Defined. *)

(* Lemma Initial_from_Colims : Colims C -> Initial C. *)
(* Proof. *)
(* intros H. *)
(* case (H _ initDiagram); intros cc iscc; destruct cc as [c cc]. *)
(* apply (make_Initial c); apply make_isInitial; intros b. *)
(* case (iscc _ (initCocone b)); intros f Hf; destruct f as [f fcomm]. *)
(* apply (tpair _ f); intro g. *)
(* transparent assert (X : (∑ x : c --> b, ∏ v, *)
(*                        coconeIn cc v · x = coconeIn (initCocone b) v)). *)
(*   { apply (tpair _ g); intro u; induction u. } *)
(* apply (maponpaths pr1 (Hf X)). *)
(* Defined. *)

(* End Initial_from_Colims. *)

(** * Construction of initial object in a functor category *)
Section InitialFunctorCat.

Variables (C D : category) (ID : Initial D).

Definition Initial_functor_precat : Initial [C, D].
Proof.
use make_Initial.
- use make_functor.
  + use tpair.
    * intros c; apply (InitialObject ID).
    * simpl; intros a b f; apply (InitialArrow ID).
  + split.
    * intro a; apply InitialEndo_is_identity.
    * intros a b c f g; apply pathsinv0, InitialArrowUnique.
- intros F.
  use tpair.
  + use make_nat_trans; simpl.
    * intro a; apply InitialArrow.
    * intros a b f; simpl.
      rewrite (InitialEndo_is_identity (InitialArrow ID ID)), id_left.
      now apply pathsinv0, InitialArrowUnique.
  + abstract (intros α; apply (nat_trans_eq D); intro a; apply InitialArrowUnique).
Defined.

End InitialFunctorCat.

(** Morphisms to the initial object are epis *)
Section epis_initial.

Context {C : precategory} (IC : Initial C).

Lemma to_initial_isEpi (a : C) (f : C⟦a,IC⟧) : isEpi f.
Proof.
apply make_isEpi; intros b g h H.
now apply InitialArrowEq.
Qed.

End epis_initial.

Definition iso_to_Initial
           {C : category}
           (I : Initial C)
           (x : C)
           (i : z_iso I x)
  : isInitial C x.
Proof.
  intros w.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       refine (!(id_left _) @ _ @ id_left _) ;
       rewrite <- !(z_iso_after_z_iso_inv i) ;
       rewrite !assoc' ;
       apply maponpaths ;
       apply InitialArrowEq).
  - exact (z_iso_inv i · InitialArrow I w).
Defined.
