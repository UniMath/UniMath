(** * Limits in the precategory of types

  This is a partial reconstruction of the results of "Homotopy limits in type
  theory" by Jeremy Avigad, Chris Kapulkin, and Peter LeFanu Lumsdaine
  (arXiv:1304.0680v3).

  Eventually, this should probably be moved into CategoryTheory, but there is
  no proof of the universal property ([isLimCone]) as phrased in
  [CategoryTheory.limits.graphs.limits]. *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.Type.Core.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Local Open Scope cat.

Section StandardLimits.

  Context {g : graph} (d : diagram g type_precat).

  Definition standard_limit : UU :=
    ∑ (x : ∏ (v : vertex g), dob d v),
    ∏ (u v : vertex g) (e : edge u v), dmor d e (x u) = x v.

  (** The condition that [standard_limit] is a cone is basically a rephrasing of
      its definition. *)
  Lemma type_cone : cone d standard_limit.
    use mk_cone; cbn.
    - exact (λ n l, pr1 l n).
    - intros u v f.
      apply funextsec; intro l; unfold funcomp; cbn.
      apply (pr2 l).
  Defined.

End StandardLimits.

Section StandardLimitHomot.

  Context {g : graph} {d : diagram g type_precat} (x y : standard_limit d).

  (** A homotopy of cones *)
  Definition standard_limit_homot : UU :=
    ∑ h : pr1 x ~ pr1 y,
      ∏ (u v : vertex g) (ed : edge u v),
        (maponpaths (dmor d ed) (h u) @ (pr2 y _ _) ed = pr2 x _ _ ed @ (h v)).

  (** Such homotopies can be made into paths *)
  Lemma type_cone_homot_to_path (h : standard_limit_homot) : x = y.
  Proof.
    apply (total2_paths_f (funextsec _ _ _ (pr1 h))).

    (** transport_lemma in peterlefanulumsdaine/hott-limits/Limits1.v. *)
    assert (transport_lemma :
              ∏ p : pr1 x = pr1 y,
                transportf _ p (pr2 x) = λ u v (ed : edge u v),
                maponpaths (dmor d ed) (!(toforallpaths _ _ _ p u))
                @ pr2 x _ _ ed
                @ toforallpaths _ _ _ p v).
    {
      intros p; induction p; cbn; unfold idfun.
      do 3 (apply funextsec; intro).
      exact (!(pathscomp0rid _)).
    }
    refine (transport_lemma _ @ _).
    apply funextsec; intro u; apply funextsec; intro v; apply funextsec; intro ed.
    rewrite toforallpaths_funextsec.
    replace (pr2 y u v ed) with (idpath _ @ (pr2 y u v ed)) by reflexivity.
    refine (_ @ maponpaths (λ p, p @ _) (pathsinv0l (maponpaths _ (pr1 h u)))).
    refine (_ @ (path_assoc (! maponpaths _ _) (maponpaths _ _) _)).
    rewrite maponpathsinv0.
    apply maponpaths, pathsinv0.
    exact (pr2 h u v ed).
  Defined.
End StandardLimitHomot.

(** The canonical cone given by an arrow X → Y where Y has a cone *)

Definition into_cone_to_cone {X Y : UU} {g : graph} {d : diagram g _}
            (coneY : cone d (Y : ob type_precat)) (f : X → Y) : cone d X.
  use mk_cone.
  - intro ver.
    exact (pr1 coneY ver ∘ (f : type_precat ⟦ X, Y ⟧)).
  - intros ver1 ver2 ed; cbn.
    apply funextsec; intro x.
    apply (toforallpaths _ _ _ (pr2 coneY ver1 ver2 ed)).
Defined.

Section StandardLimitUP.

  Context {g : graph} {d : diagram g type_precat}.

  (** A rephrasing of the universal property: the canonical map that makes a
      cone out of a map X → L is an equivalence. *)
  Definition is_limit_cone {L} (C : cone d L) :=
    ∏ (X : UU), isweq (@into_cone_to_cone X L g d C).

  Lemma isaprop_isLimCone {L} (C : cone d L) : isaprop (is_limit_cone C).
  Proof.
    repeat (apply impred; intro).
    apply isapropiscontr.
  Qed.

  (** A weak equivalence expressing the above universal property. *)
  Definition limit_up_weq {X L} {C : cone d L} {is : is_limit_cone C} :
    (X → L) ≃ cone d X := weqpair (into_cone_to_cone C) (is X).

  (** The universal property of a limit.

      - Proposition 4.2.8 (limit_universal) in Avigad, Kapulkin, and Lumsdaine
      - Generalizes Lemma 10 in Ahrens, Capriotti, and Spadotti
      - Generalizes univ-iso in HoTT/M-types
  *)
  Lemma limit_universal : is_limit_cone (type_cone d).
    intro X.
    use isweq_iso.
    - intros xcone x.
      unfold standard_limit.
      use tpair.
      + exact (λ ver, pr1 xcone ver x).
      + intros ver1 ver2 ed.
        apply (toforallpaths _ _ _ (pr2 xcone _ _ _)).
    - intros f.
      apply funextfun; intro xcone.
      use total2_paths_f; cbn; [reflexivity|].
      cbn; unfold idfun.
      apply funextsec; intro ver1.
      apply funextsec; intro ver2.
      apply funextsec; intro ed.
      do 2 (rewrite toforallpaths_funextsec).
      reflexivity.
    - intro conex.
      unfold into_cone_to_cone; cbn.
      use total2_paths_f; cbn.
      + reflexivity.
      + apply funextsec; intro ver1.
        apply funextsec; intro ver2.
        apply funextsec; intro ed.
        unfold funcomp; cbn; unfold idfun.
        rewrite toforallpaths_funextsec; cbn.
        rewrite funextsec_toforallpaths.
        reflexivity.
  Defined.

  (** The above weak equivalence specialized to the case of [standard_limit]s *)
  Definition standard_limit_up_weq {X} : (X → standard_limit d) ≃ cone d X :=
    weqpair (into_cone_to_cone (type_cone d)) (limit_universal X).

End StandardLimitUP.
