
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


Extended by: Anders Mörtberg, 2016

************************************************************)


(** **********************************************************

Contents:

- Definition of global right Kan extension as right adjoint to precomposition

- Construction of right Kan extensions when the target category has limits
    ([RightKanExtension_from_limits])

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.CommaCategories.

Local Open Scope cat.

(** * Definition of global right Kan extension as right adjoint to precomposition *)
Section RightKanExtension.

Context (C D : category) (F : functor C D) (E : category).

Let PrecompWithF : [D, E] ⟶ [C, E]
  := pre_composition_functor C D E F.

Definition GlobalRightKanExtensionExists : UU
  := is_left_adjoint PrecompWithF.

Definition GlobalRan (H : GlobalRightKanExtensionExists)
  : [C, E] ⟶ [D, E] := right_adjoint H.

End RightKanExtension.


(** * Construction of right Kan extensions when the target category has limits *)
Section RightKanExtensionFromLims.

Context (M C A : category) (K : functor M C) (LA : Lims A).

Local Notation "c ↓ K" := (cComma _ _ K c) (at level 30).

Section fix_T.

Variable (T : functor M A).

Local Definition Q (c : C) : functor (c ↓ K) M := cComma_pr1 _ _ K c.

Local Definition QT (c : C) : diagram (c ↓ K) A :=
  diagram_from_functor _ _ (functor_composite (Q c) T).

Local Definition R (c : C) : A := lim (LA _ (QT c)).

Local Definition lambda (c : C) : cone (QT c) (R c) := limCone (LA _ (QT c)).

Local Definition Rmor_cone (c c' : C) (g : C⟦c,c'⟧) : cone (QT c') (R c).
Proof.
use make_cone.
- intro m1f1.
  transparent assert (m1gf1 : (c ↓ K)).
  { use tpair.
    + apply (pr1 m1f1).
    + apply (g · pr2 m1f1). }
  exact (coneOut (lambda c) m1gf1).
- intros x y f; simpl in *.
  transparent assert (e : ((c ↓ K) ⟦ pr1 x,, g · pr2 x, pr1 y,, g · pr2 y ⟧)).
  { use tpair.
    + exact (pr1 f).
    + change (g · pr2 x · # K (pr1 f) = g · pr2 y).
      rewrite <- assoc. rewrite (pr2 f). apply idpath. }
  exact (coneOutCommutes (lambda c) _ _ e).
Defined.

Local Definition Rmor (c c' : C) (g : C⟦c,c'⟧) : A⟦R c,R c'⟧ :=
  limArrow (LA (c' ↓ K) (QT c')) (R c) (Rmor_cone c c' g).

Local Definition R_data : functor_data C A := R,,Rmor.
Local Lemma R_is_functor : is_functor R_data.
Proof.
split.
- intros c; simpl.
  apply pathsinv0, limArrowUnique.
  intro c'; simpl; rewrite !id_left.
  now destruct c'.
- intros c c' c'' f f'; simpl.
  apply pathsinv0, limArrowUnique; intros x; simpl.
  rewrite <- assoc; eapply pathscomp0.
  apply maponpaths, (limArrowCommutes _ _ (Rmor_cone c' c'' f')).
  eapply pathscomp0.
  apply (limArrowCommutes _ _ (Rmor_cone c c' f) (pr1 x,,f' · pr2 x)).
  destruct x.
  now rewrite <- assoc.
Qed.

Local Definition R_functor : functor C A := tpair _ R_data R_is_functor.

Local Definition eps_n (n : M) : A⟦R_functor (K n),T n⟧ :=
  coneOut (lambda (K n)) (n,,identity (K n)).

Local Definition Kid n : K n ↓ K := (n,, identity (K n)).

Local Lemma eps_is_nat_trans : is_nat_trans (functor_composite_data K R_data) T eps_n.
Proof.
intros n n' h; simpl.
eapply pathscomp0.
apply (limArrowCommutes (LA (K n' ↓ K) (QT (K n'))) (R (K n))
       (Rmor_cone (K n) (K n') (# K h)) (Kid n')).
unfold eps_n; simpl.
transparent assert (v : (K n ↓ K)).
{ apply (n',, # K h · identity (K n')). }
transparent assert (e : (K n ↓ K ⟦ Kid n, v ⟧)).
{ use tpair.
  + apply h.
  + abstract (cbn ; now rewrite id_left, id_right).
}
now apply pathsinv0; eapply pathscomp0; [apply (coneOutCommutes (lambda (K n)) _ _ e)|].
Qed.

Local Definition eps : [M, A]⟦functor_composite K R_functor, T⟧ :=
  tpair _ eps_n eps_is_nat_trans.

End fix_T.

(** Construction of right Kan extensions based on MacLane, CWM, X.3 (p. 233) *)
Lemma RightKanExtension_from_limits : GlobalRightKanExtensionExists _ _ K A.
Proof.
unfold GlobalRightKanExtensionExists.
apply coreflections_to_is_left_adjoint.
intro T.
use make_coreflection'.
- exact (R_functor T).
- exact (eps T).
- intro α'; simpl in *.
  pose (S := coreflection_data_object α' : _ ⟶ _).
  pose (α := (α' : _ --> _) : _ ⟹ _).

  transparent assert (cc : (∏ c, cone (QT T c) (S c))).
  { intro c.
    use make_cone.
    + intro mf; apply (# S (pr2 mf) · α (pr1 mf)).
    + abstract (intros fm fm' h; simpl; rewrite <- assoc;
                eapply pathscomp0; [apply maponpaths, (pathsinv0 (nat_trans_ax α _ _ (pr1 h)))|];
                simpl; rewrite assoc, <- functor_comp; apply cancel_postcomposition, maponpaths, (pr2 h)).
  }

  transparent assert (σ : (∏ c, A ⟦ S c, R T c ⟧)).
  { intro c; apply (limArrow _ _ (cc c)). }

  set (lambda' := λ c' mf', limOut (LA (c' ↓ K) (QT T c')) mf').

  (* this is the conclusion from the big diagram (8) in MacLane's proof *)
  assert (H : ∏ c c' (g : C ⟦ c, c' ⟧) (mf' : c' ↓ K),
                # S g · σ c' · lambda' _ mf' = σ c · Rmor T c c' g · lambda' _ mf').
  { intros c c' g mf'.
    rewrite <- !assoc.
    apply pathsinv0; eapply pathscomp0.
    apply maponpaths, (limArrowCommutes _ _ (Rmor_cone T c c' g) mf').
    apply pathsinv0; eapply pathscomp0.
    eapply maponpaths, (limArrowCommutes _ _ (cc c') mf').
    simpl; rewrite assoc, <- functor_comp.
    set (mf := tpair _ (pr1 mf') (g · pr2 mf') : c ↓ K).
    apply pathsinv0.
    exact (limArrowCommutes (LA (c ↓ K) (QT T c)) (S c) (cc c) mf).
  }

  assert (is_nat_trans_σ : is_nat_trans S (R_data T) σ).
  { intros c c' g; simpl.
    transparent assert (ccc : (cone (QT T c') (S c))).
    { use make_cone.
      - intro mf'; apply (σ c · Rmor T c c' g · limOut (LA (c' ↓ K) (QT T c')) mf').
      - abstract (intros u v e; simpl; rewrite <- !assoc;
                  apply maponpaths, maponpaths, (limOutCommutes (LA (c' ↓ K) (QT T c')) u v e)).
    }
    rewrite (limArrowUnique (LA (c' ↓ K) (QT T c')) _ ccc (# S g · σ c') (H _ _ _)).
    now apply pathsinv0, limArrowUnique.
  }

  use tpair.
  + apply (tpair _ (tpair _ σ is_nat_trans_σ)).
    apply nat_trans_eq; [apply homset_property | intro n; cbn].
    generalize (limArrowCommutes (LA (K n ↓ K) (QT T (K n))) _ (cc _) (Kid n)); simpl.
    now rewrite functor_id, id_left.
  + intro x.
    apply subtypePath; [intros xx; apply (isaset_nat_trans (homset_property A))|].
    apply subtypePath; [intros xx; apply (isaprop_is_nat_trans _ _ (homset_property A))|]; simpl.
    apply funextsec; intro c.
    apply limArrowUnique; intro u; simpl.
    destruct x as [t p]; simpl.
    assert (temp : α (pr1 u) = nat_trans_comp _ _ T (pre_whisker K t) (eps T) (pr1 u)).
      unfold α; now rewrite p.
    refine (_ @ !maponpaths _ temp).
    simpl.
    destruct u as [n g]; simpl in *.
    apply pathsinv0; eapply pathscomp0;
    [rewrite assoc; apply cancel_postcomposition, (nat_trans_ax t _ _ g)|].
    rewrite <- !assoc; apply maponpaths.
    generalize (limArrowCommutes (LA (K n ↓ K) _) _ (Rmor_cone T c (K n) g) (Kid n)).
    now simpl; rewrite id_right.
Defined.

End RightKanExtensionFromLims.
