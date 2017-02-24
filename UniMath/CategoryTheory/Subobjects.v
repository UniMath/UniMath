(** * Subobjects *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.sub_precategories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.limits.pullbacks.


(** * Definition of subobjects *)
Section def_subobjects.

  Context {C : precategory} (hsC : has_homsets C).

  Definition SubobjectsPrecategory (c : C) : precategory :=
    slice_precat (subprecategory_of_monics C hsC)
                 (subprecategory_of_monics_ob C hsC c)
                 (has_homsets_subprecategory_of_monics C hsC).

  (** Construction of a subobject from a monic *)
  Definition SubobjectsPrecategory_ob {c c' : C} (h : C⟦c', c⟧) (isM : isMonic h) :
    SubobjectsPrecategory c := (subprecategory_of_monics_ob C hsC c',,(h,,isM)).

  Hypothesis hpb : @Pullbacks C.

  (** Given any subobject S of c and a morphism h : c' -> c, by taking then pullback of S by h we
      obtain a subobject of c'. *)
  Definition PullbackSubobject {c : C} (S : SubobjectsPrecategory c) {c' : C} (h : C⟦c', c⟧) :
    SubobjectsPrecategory c'.
  Proof.
    set (pb := hpb _ _ _ h (pr1 (pr2 S))).
    use SubobjectsPrecategory_ob.
    - exact pb.
    - exact (PullbackPr1 pb).
    - use MonicPullbackisMonic'.
  Defined.

End def_subobjects.

Section temp.

Context (C : precategory).

(** a and b are related if there merely exists an iso between them *)
Definition iso_rel : hrel C := λ a b, hProppair (∥iso a b∥) (isapropishinh _).

Lemma iseqrel_iso_rel : iseqrel iso_rel.
Proof.
repeat split.
- intros x y z h1.
  apply hinhuniv; intros h2; generalize h1; clear h1.
  now apply hinhuniv; intros h1; apply hinhpr, (iso_comp h1 h2).
- now intros x; apply hinhpr, identity_iso.
- now intros x y; apply hinhuniv; intro h1; apply hinhpr, iso_inv_from_iso.
Qed.

Definition iso_eqrel : eqrel C := (iso_rel,,iseqrel_iso_rel).

End temp.

Section temp1.

Context {C : precategory} (hsC : has_homsets C).

(** Equivalence classes of subobjects defined by identifying monos into c with isomorphic source *)
Definition SubObj (c : C) : HSET :=
  hSetpair (setquot (iso_eqrel (SubobjectsPrecategory hsC c))) (isasetsetquot _).

Definition mono_rel c : hrel (ob (SubobjectsPrecategory hsC c)).
Proof.
intros f g.
apply (hProppair (∥ ∑ (h : C⟦_,_⟧), pr1 (pr2 f) = h ;; pr1 (pr2 g) ∥) (isapropishinh _)).
Defined.

Lemma mono_preorder c : ispreorder (mono_rel c).
Proof.
split.
- intros x y z h1.
  apply hinhuniv; intros h2; generalize h1; clear h1.
  apply hinhuniv; intros h1; apply hinhpr.
  admit.
- admit.
Admitted.

Definition SubObjPoset (c : C) : Poset.
Proof.
exists (SubObj c).
mkpair.
- intros x y.
  admit.
Admitted.

Require Import UniMath.CategoryTheory.opp_precat.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "'Psh' C" := [C^op,HSET,has_homsets_HSET] (at level 3).

Definition FunctorSub (PC : Pullbacks C) : Psh C.
Proof.
simpl.
use mk_functor.
+ mkpair.
  - apply SubObj.
  - intros c d f.
    use (setquotuniv (iso_eqrel (SubobjectsPrecategory hsC c))).
    * intros S.
      apply setquotpr.
      apply (PullbackSubobject hsC PC S f).
    * admit.
    + admit.
Admitted.

(* Definition SubObj (c : C) : UU := ∥ ∑ (af : ∑ (a : C), C⟦a,c⟧), isMonic (pr2 af) ∥. *)

(* a is a subobject of c *)
(* Definition SubObj (a c : C) : UU := ∥ ∑ (f : C⟦a,c⟧), isMonic f ∥. (* Monic C a c. *) *)

(* Definition SubObjects (c : C) : UU := ∑ (a : ob C), SubObj a c. *)

(* Definition SubObj (c : C) : hsubtype (∑ a, precategory_morphisms a c). *)
(* Proof. *)
(*   intros f. *)
(*   exists (isMonic (pr2 f)). *)
(*   apply isapropisMonic, hsC. *)
(* (* apply (hProppair (∥ Monic C a c ∥) (isapropishinh _)). *) *)
(* Defined. *)

End temp1.
