(** * Limits in slice categories *)

(** ** Contents

  - Terminal object in slice categories ([Terminal_slice_precat])

  - Binary products in slice categories of categories with pullbacks
    ([BinProducts_slice_precat])

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import UniMath.CategoryTheory.Slice.Core.

Local Open Scope cat.

(** ** Terminal object *)

Section slicecat_terminal.

Context {C : precategory} (hsC : has_homsets C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma Terminal_slice_precat (x : C) : Terminal (C / x).
Proof.
use mk_Terminal.
- use tpair.
  + apply x.
  + apply (identity x).
- intros y.
  use unique_exists; simpl.
  * apply (pr2 y).
  * abstract (rewrite id_right; apply idpath).
  * abstract (intros f; apply hsC).
  * abstract (intros f ->; rewrite id_right; apply idpath).
Defined.

End slicecat_terminal.

(** * Moving between binary products in slice categories and pullbacks in base category *)

Section slicecat_binproducts.

Context {C : precategory} (hsC : has_homsets C).

Local Notation "C / X" := (slice_precat C X hsC).

Definition pullback_to_slice_binprod {A B Z : C} {f : A --> Z} {g : B --> Z} :
  Pullback f g -> BinProduct (C / Z) (A ,, f) (B ,, g).
Proof.
  intros P.
  use (((PullbackObject P ,, (PullbackPr1 P) · f) ,, (((PullbackPr1 P) ,, idpath _) ,, (((PullbackPr2 P) ,, (PullbackSqrCommutes P))))) ,, _).
  intros Y [j jeq] [k keq]; simpl in jeq , keq.
  use unique_exists.
  + use tpair.
    - apply (PullbackArrow P _ j k).
      abstract (rewrite <- jeq , keq; apply idpath).
    - abstract (cbn; rewrite assoc, PullbackArrow_PullbackPr1, <- jeq; apply idpath).
  + abstract (split; apply eq_mor_slicecat; simpl;
              [ apply PullbackArrow_PullbackPr1 | apply PullbackArrow_PullbackPr2 ]).
  + abstract (intros h; apply isapropdirprod; apply has_homsets_slice_precat).
  + abstract (intros h [H1 H2]; apply eq_mor_slicecat, PullbackArrowUnique;
             [ apply (maponpaths pr1 H1) | apply (maponpaths pr1 H2) ]).
Defined.

Definition BinProducts_slice_precat (PC : Pullbacks C) : ∏ x, BinProducts (C / x) :=
 λ x a b, pullback_to_slice_binprod (PC _ _ _ (pr2 a) (pr2 b)).

Definition slice_binprod_to_pullback {Z : C} {AZ BZ : C / Z} :
  BinProduct (C / Z) AZ BZ → Pullback (pr2 AZ) (pr2 BZ).
Proof.
  induction AZ as [A f].
  induction BZ as [B g].
  intros [[[P h] [[l leq] [r req]]] PisProd].
  use ((P ,, l ,, r) ,, (! leq @ req) ,, _).
  intros Y j k Yeq. simpl in *.
  use unique_exists.
  + exact (pr1 (pr1 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))).
  + abstract (exact (maponpaths pr1 (pr1 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))) ,,
                                maponpaths pr1 (pr2 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))))).
  + abstract (intros x; apply isofhleveldirprod; apply (hsC _ _)).
  + intros t teqs.
    use (maponpaths pr1 (maponpaths pr1 (pr2 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq)) ((t ,, (maponpaths (λ x, x · f) (!(pr1 teqs)) @ !(assoc _ _ _) @ maponpaths (λ x, t · x) (!leq))) ,, _)))).
    abstract (split; apply eq_mor_slicecat; [exact (pr1 teqs) | exact (pr2 teqs)]).
Defined.

Definition Pullbacks_from_slice_BinProducts (BP : ∏ x, BinProducts (C / x)) : Pullbacks C :=
  λ x a b f g, slice_binprod_to_pullback (BP x (a ,, f) (b ,, g)).

End slicecat_binproducts.