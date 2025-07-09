(*
Definition of the arrow category given a category C
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
(* The Structure Identity Principle (HoTT book, chapter 9.8) *)
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.

Local Open Scope cat.
Local Open Scope mor_disp.

Section Arrow_Disp.

Context (C:category).

Definition arrow_base := category_binproduct C C.

Definition arrow_disp : disp_cat arrow_base.
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ xy, pr1 xy --> pr2 xy).
  - simpl.
    intros xx' yy' g h ff'.
    exact (pr1 ff' · h = g · pr2 ff').
  - abstract (
      intros;
      use homset_property
    ).
  - abstract (
      simpl;
      intros;
      now rewrite id_left, id_right
    ).
  - abstract (
      simpl;
      intros;
      rewrite assoc, <- X;
      symmetry;
      now rewrite <- assoc, <- X0, assoc
    ).
Defined.

Definition arrow : category := total_category arrow_disp.

End Arrow_Disp.

Definition arrow_dom {C : category} (f : arrow C) : C := pr11 f.
Definition arrow_cod {C : category} (f : arrow C) : C := pr21 f.
#[reversible] Coercion arrow_mor {C : category} (f : arrow C) := pr2 f.

Definition arrow_mor00 {C : category} {f g : arrow C} (F : f --> g) := pr11 F.
Definition arrow_mor11 {C : category} {f g : arrow C} (F : f --> g) := pr21 F.
Definition arrow_mor_comm {C : category} {f g : arrow C} (F : f --> g) := pr2 F.

#[reversible] Coercion mor_to_arrow_ob {C : category} {x y : C} (f : x --> y) : arrow C :=
    (make_dirprod x y,, f).

Definition mors_to_arrow_mor {C : category} {a b x y : C} (f : a --> b) (g : x --> y)
    (h : a --> x) (k : b --> y) (H : g ∘ h = k ∘ f) : (mor_to_arrow_ob f) --> (mor_to_arrow_ob g).
Proof.
  use tpair.
  - exact (make_dirprod h k).
  - exact H.
Defined.

Lemma arrow_mor_eq {C : category} {f g : arrow C}
    (γ γ' : f --> g)
    (H00 : arrow_mor00 γ = arrow_mor00 γ')
    (H11 : arrow_mor11 γ = arrow_mor11 γ') :
  γ = γ'.
Proof.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod; assumption.
Qed.

Definition opp_arrow {C : category} (g : arrow C) : arrow (op_cat C) :=
    (make_dirprod (arrow_cod g) (arrow_dom g),, arrow_mor g).

(* Lemma arrow_eq {C : category} {g g' : arrow C} {f f' : g --> g'} :
    pr1 f = pr1 f' -> f = f'.
Proof.
  intro H.
  apply subtypePath; [intro; apply homset_property|].
  exact H.
Qed. *)

(* base_paths : equality in pr1 of ∑-type (paths in base category)
    pathsdirprodweq : _ × _ = _ × _ -> equality of terms
*)
Definition arrow_mor00_eq {C : category}
    {f f' : arrow C} {mor mor' : f --> f'} (H : mor = mor') :
  arrow_mor00 mor = arrow_mor00 mor'.
Proof.
  exact (dirprod_pr1 (pathsdirprodweq (base_paths _ _ H))).
Qed.

Definition arrow_mor11_eq {C : category}
    {f f' : arrow C} {mor mor' : f --> f'} (H : mor = mor') :
  arrow_mor11 mor = arrow_mor11 mor'.
Proof.
  exact (dirprod_pr2 (pathsdirprodweq (base_paths _ _ H))).
Qed.

Section Colims.

Context {C : category}.

Definition arrow_base_colims (CC : Colims C) :
    Colims (arrow_base C).
Proof.
  intros g d.

  set (d1 := mapdiagram (pr1_functor _ _) d).
  set (d2 := mapdiagram (pr2_functor _ _) d).

  set (cc1 := CC _ d1).
  set (cc2 := CC _ d2).

  use tpair.
  - exists (make_dirprod (colim cc1) (colim cc2)).
    use tpair.
    * intro v.
      split.
      + exact (colimIn cc1 v).
      + exact (colimIn cc2 v).
    * abstract (
        intros u v e;
        use pathsdirprod; [
          exact (colimInCommutes cc1 _ _ e)|
          exact (colimInCommutes cc2 _ _ e)
        ]
      ).
  - intros c cc.
    destruct cc as [f ccf].
    use unique_exists.
    * split.
      + use colimArrow.
        exists (λ v, pr1 (f v)).
        abstract (
          intros u v e;
          exact (pr1 (pathsdirprodweq (ccf _ _ e)))
        ).
      + use colimArrow.
        exists (λ v, pr2 (f v)).
        abstract (
          intros u v e;
          exact (pr2 (pathsdirprodweq (ccf _ _ e)))
        ).
    * abstract (
        intro; apply pathsdirprod; [
          apply (colimArrowCommutes cc1)|apply (colimArrowCommutes cc2)
        ]
      ).
    * abstract (
        intro; apply impred; intro; apply homset_property
      ).
    * abstract (
        intros y H;
        apply pathsdirprod; apply colimArrowUnique; intro v; [
          exact (pr1 (pathsdirprodweq (H v)))|exact (pr2 (pathsdirprodweq (H v)))
        ]
      ).
Defined.


Local Definition arrow_colimit (CC : Colims C)
    {g : graph} (d : diagram g (arrow C)) : arrow C.
Proof.
  set (dbase := mapdiagram (pr1_category _) d).
  set (clbase := arrow_base_colims CC _ dbase).

  (* dom / cod are colims of dom / cod *)
  exists (colim clbase).

  (* arrow colim is colim of arrows *)
  use colimOfArrows.
  - exact (dob d).
  - abstract (
      intros u v e;
      exact (arrow_mor_comm (dmor d e))
    ).
Defined.

Definition arrow_colims (CC : Colims C) :
    Colims (arrow C).
Proof.
  intros g d.

  set (dbase := mapdiagram (pr1_category _) d).
  set (clbase := arrow_base_colims CC _ dbase).

  use tpair.
  - exists (arrow_colimit CC d).
    use tpair.
    * intro v.
      exists (colimIn clbase v).
      abstract (
        use (colimOfArrowsIn _ _ (CC g (mapdiagram (pr1_functor C C) dbase)))
      ).
    * abstract (
        intros u v e;
        (* cbn. *)
        apply subtypePath; [intro; apply homset_property|];
        apply (colimInCommutes clbase)
      ).
  - intros c cc.
    transparent assert (ccbase : (cocone dbase (pr1 c))).
    {
      exists (λ v, pr1 (coconeIn cc v)).
      abstract (
        intros u v e;
        exact (base_paths _ _ (coconeInCommutes cc _ _ e))
      ).
    }

    use unique_exists.
    * exists (colimArrow clbase _ ccbase).

      abstract (
        etrans; [use postcompWithColimArrow|];
        apply pathsinv0;
        etrans; [use precompWithColimOfArrows|];

        apply maponpaths;
        (apply subtypePath; [intro; do 3 (apply impred; intro); apply homset_property|]);
        apply funextsec;
        intro v;
        exact (pathsinv0 (arrow_mor_comm (coconeIn cc v)))
      ).
    * abstract (
        intro;
        apply subtypePath; [intro; apply homset_property|];
        exact (colimArrowCommutes clbase _ ccbase v)
      ).
    * abstract (
        intro; apply impred; intro; apply homset_property
      ).
    * abstract (
        intros y H;
        apply subtypePath; [intro; apply homset_property|];
        apply colimArrowUnique;
        intro v;
        exact (base_paths _ _ (H v))
      ).
Defined.

Definition project_diagram00 {g : graph} (d : diagram g (arrow C)) :=
  mapdiagram (pr1_functor _ _) (mapdiagram (pr1_category _) d).

Definition project_diagram11 {g : graph} (d : diagram g (arrow C)) :=
  mapdiagram (pr2_functor _ _) (mapdiagram (pr1_category _) d).

Definition project_cocone00
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C}
    (cc : cocone d f) :
  cocone (project_diagram00 d) (arrow_dom f) :=
    mapcocone (pr1_functor _ _) _ (mapcocone (pr1_category _) _ cc).

Definition project_cocone11
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C}
    (cc : cocone d f) :
  cocone (project_diagram11 d) (arrow_cod f) :=
    mapcocone (pr2_functor _ _) _ (mapcocone (pr1_category _) _ cc).

Definition project_colimcocone00
    (CC : Colims C)
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  isColimCocone _ _ (project_cocone00 ccf).
Proof.
  set (dbase := project_diagram00 d).
  set (base_mor := isColim_is_z_iso _ (arrow_colims CC _ d) _ _ isclCC).

  use (is_z_iso_isColim _ (CC _ dbase)).
  exists (arrow_mor00 (pr1 base_mor)).
  abstract (
    split; [
      etrans; [|exact (arrow_mor00_eq (pr12 base_mor))];
      apply cancel_postcomposition
      | etrans; [|exact (arrow_mor00_eq (pr22 base_mor))];
        apply cancel_precomposition
    ]; (
      use colimArrowUnique';
      intro v;
      etrans; [apply colimArrowCommutes|];
      apply pathsinv0;
      etrans; [apply colimArrowCommutes|];
      reflexivity
    )
  ).
Defined.

Definition project_colimcocone11
    (CC : Colims C)
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  isColimCocone _ _ (project_cocone11 ccf).
Proof.
  set (dbase := project_diagram11 d).
  set (base_mor := isColim_is_z_iso _ (arrow_colims CC _ d) _ _ isclCC).

  use (is_z_iso_isColim _ (CC _ dbase)).
  exists (arrow_mor11 (pr1 base_mor)).
  abstract (
    split; [
      etrans; [|exact (arrow_mor11_eq (pr12 base_mor))];
      apply cancel_postcomposition
      | etrans; [|exact (arrow_mor11_eq (pr22 base_mor))];
        apply cancel_precomposition
    ]; (
      use colimArrowUnique';
      intro v;
      etrans; [apply colimArrowCommutes|];
      apply pathsinv0;
      etrans; [apply colimArrowCommutes|];
      reflexivity
    )
  ).
Defined.

End Colims.
