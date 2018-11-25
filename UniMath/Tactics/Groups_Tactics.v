(** Author: Michael A. Warren (maw@mawarren.net).*)
(** Date: Spring 2015.*)
(** Description: Some tactics for groups.*)

Require Import UniMath.Algebra.Monoids_and_Groups
               UniMath.Tactics.Utilities
               UniMath.Tactics.Monoids_Tactics.

Local Open Scope multmonoid.

Ltac gr_preclean G := monoid_clean (grtomonoid G).

Ltac gr_preclean_in G t := monoid_clean_in (grtomonoid G) t.

Ltac gr_preclean_all G := monoid_clean_all (grtomonoid G).

Ltac gr_prezap G := monoid_zap (grtomonoid G).

Ltac gr_group_in G x s t :=
  assocop_group_in (grtomonoid G) (@op (grtomonoid G)) x s t.

Ltac gr_group G s t := assocop_group (grtomonoid G) (@op (grtomonoid G)) s t.

Ltac gr_clean G :=
  gr_preclean G; repeat rewrite (grlinvax G); repeat rewrite (grrinvax G);
  repeat (gr_preclean G;
          match goal with
            | |- context [?y * ?x * (@grinv G ?x)] =>
              rewrite (assocax G y x (@grinv G x)), (grrinvax G);
            gr_clean G
            | |- context [?y * (@grinv G ?x) * ?x] =>
              rewrite (assocax G y (@grinv G x) x), (grlinvax G);
            gr_clean G
          end);
  gr_preclean G.

(** Tests*)
(*
Unset Ltac Debug.

Section Tests.

  Hypothesis G : gr.

  Hypothesis x y z u v w : G.

  Lemma test_gr_prezap_1 (is : w = v): x * (y * w) = x * (y * v).
  Proof.
    intros. gr_prezap G.
  Qed.

  Lemma test_gr_prezap_2 (is : w = v):  x * (y * w) = (x * y) * v.
  Proof.
    intros. gr_prezap G.
  Qed.

  Lemma test_gr_prezap_3 (t : x * (y * (z * u)) = (v * w) * u) :
    (((x * y) * z) * u) * w = v * (w * (u * w)).
  Proof.
    intros. gr_prezap G.
  Qed.

  Lemma test_gr_prezap_4 (t : x * (y * (z * u)) = (v * w) * u) :
    (((x * y) * z) * u) * w = v * (w * (u * w)).
  Proof.
    intros. gr_prezap G.
  Qed.

  Lemma test_gr_group_1 (t : x * (y * (z * u)) = (v * w) * u) :
    ((x * (y * z)) * u) * w = v * (w * (u * w)).
  Proof.
    intros. gr_group_in G t w u. gr_group G w u. gr_group G v (w * u).
    gr_prezap G.
  Qed.

  Lemma test_gr_prezap_5 (t : x * (y * (z * u)) = (v * w) * u) :
    ((x * (y * z)) * u) * w = v * (w * (u * w)).
  Proof.
    intros. gr_prezap G.
  Qed.

  Lemma test_gr_prezap_6 (t : x * y = y * x) : x * y * x = x * x * y.
  Proof.
    intros. gr_prezap G.
  Qed.

  Lemma test_gr_prezap_7 (t : x * y = y * x) (i : x * z = @unel G) :
    x * (y * z) = y * (x * z).
  Proof.
    intros. gr_prezap G.
  Qed.

  Lemma test_gr_clean_1 :
    x * (y * (@grinv G y)) * (@unel G) * ((@grinv G x) * v) = v.
  Proof.
    intros. gr_clean G. apply idpath.
  Qed.

End Tests.

Close Scope multmonoid.
 *)
