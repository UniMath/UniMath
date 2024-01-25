Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.

Local Open Scope cat.
Local Open Scope mor_disp.

Section Three_disp.

Context (C : category).

(* Can't use SIP since morphism data is not propositional (∑-type)
   For example in SET, we could have a map in
   the arrow category sending everything to one element, factorize
   it through (self, id), we may have multiple morphisms in the middle,
   so long as the one element maps properly... 
   
   So we have to do things the long way: *)
Definition three_disp_ob_mor : disp_cat_ob_mor (arrow C).
Proof.
  use make_disp_cat_ob_mor.
  - exact ((λ xy, ∑ z (xz : (arrow_dom xy) --> z) (zy : z --> (arrow_cod xy)), xz · zy = arrow_mor xy)).
  - (* double commutative square *)
    simpl.
    intros xy ab H0 H1 fff.
    destruct H0 as [z [xz [zy]]].
    destruct H1 as [c [ac [cb]]].
    destruct fff as [[f0 f1]].
    exact (∑ (f : z --> c), (xz · f = f0 · ac) × (zy · f1 = f · cb)).
Defined.

Definition three_id_comp : disp_cat_id_comp _ three_disp_ob_mor.
Proof.
  split.
  - intros.
    (* middle morphism is also identity *)
    exists (identity _).
    abstract (split; now rewrite id_left, id_right).
  - intros.
    destruct X as [f0 [H0 H1]].
    destruct X0 as [g0 [K0 K1]].

    (* middle map of composite is composite of middle maps *)
    exists (f0 · g0).
    abstract (
      simpl;
      split; [
        rewrite assoc, H0, <- assoc;
        etrans; [apply maponpaths; exact K0|];
        now rewrite assoc
      |
        rewrite <- assoc, <- K1, assoc, assoc;
        apply cancel_postcomposition;
        exact H1
      ]
    ).
Defined.

Definition three_data : disp_cat_data _ :=
    (three_disp_ob_mor,, three_id_comp).

Definition three_axioms : disp_cat_axioms _ three_data.
Proof.
  repeat apply tpair; intros.
  (* very cool from CategoryTheory/DisplayedCats/Codomain.v: cod_disp_axioms *)
  - (* subtypePath: equality in ∑-types if pr2 is a predicate *)
    apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }

    (* left identity in base category *)
    simpl.
    etrans. apply id_left.

    destruct ff as [ff H].
    apply pathsinv0.
    
    etrans. 
    use (pr1_transportf (A := x --> y)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }
    simpl.
    etrans. apply id_right.
    destruct ff as [ff H].
    apply pathsinv0.
    etrans. use (pr1_transportf (A := x --> y)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }
    simpl.
    etrans. apply assoc.
    destruct ff as [ff H].
    apply pathsinv0.
    etrans. use (pr1_transportf (A := x --> w)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply isaset_total2.
    * apply homset_property.
    * intro.
      apply isasetdirprod; apply isasetaprop; apply homset_property.    
Qed.

Definition three_disp : disp_cat (arrow C) :=
    (three_data,, three_axioms).

Definition three : category := total_category three_disp.

End Three_disp.

Definition three_ob0 {C : category} (xyz : three C) : C := pr111 xyz.
Definition three_ob1 {C : category} (xyz : three C) : C := pr12 xyz.
Definition three_ob2 {C : category} (xyz : three C) : C := pr211 xyz.
Definition three_mor01 {C : category} (xyz : three C) := pr122 xyz.
Definition three_mor12 {C : category} (xyz : three C) := pr1 (pr222 xyz).
Definition three_mor02 {C : category} (xyz : three C) := arrow_mor (pr1 xyz).
Definition three_comp {C : category} (xyz : three C) := pr2 (pr222 xyz).
Definition three_mor00 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr111 fff.
Definition three_mor11 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr12 fff.
Definition three_mor22 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr211 fff.
Definition three_mor_comm {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr22 fff.

Definition three_mor_mor01 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) :
    (three_mor01 xxx) --> (three_mor01 yyy). 
Proof.
  use mors_to_arrow_mor.
  - exact (three_mor00 fff).
  - exact (three_mor11 fff).
  - abstract (
      exact (pathsinv0 (pr1 (three_mor_comm fff)))
    ).
Defined.

Definition three_mor_mor12 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) :
    (three_mor12 xxx) --> (three_mor12 yyy). 
Proof.
  use mors_to_arrow_mor.
  - exact (three_mor11 fff).
  - exact (three_mor22 fff).
  - abstract (
      exact (pathsinv0 (pr2 (three_mor_comm fff)))
    ).
Defined.

Definition three_mor_eq {C : category} {x y : three C} {f g : x --> y}
    (H00: three_mor00 f = three_mor00 g)
    (H11: three_mor11 f = three_mor11 g)
    (H22: three_mor22 f = three_mor22 g) : 
  f = g.
Proof.
  use pair_path2.
  - exact (pr1 g).
  - apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; assumption.
  - reflexivity.
  - apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    cbn.
    rewrite pr1_transportf.
    rewrite transportf_const.
    assumption.
Qed.

Definition three_mor_eq' {C : category} {x y : three C} {f g : x --> y}
    (Hb: pr11 f = pr11 g)
    (H11: three_mor11 f = three_mor11 g) : 
  f = g.
Proof.
  use three_mor_eq.
  - exact (pr1 (pathsdirprodweq Hb)).
  - exact H11.
  - exact (pr2 (pathsdirprodweq Hb)).
Qed.

Definition three_mor_eq'' {C : category} {x y : three C} {f g : x --> y}
    (Hb: pr1 f = pr1 g)
    (H11: three_mor11 f = three_mor11 g) : 
  f = g.
Proof.
  use three_mor_eq'.
  - exact (base_paths _ _ Hb).
  - exact H11.
Qed.

Section three_colimits.

Context {C : category}.
Context {g : graph}.
Context (d : diagram g (three C)).

Local Definition three_middle_diagram : diagram g C.
Proof.
  exists (λ v, three_ob1 (dob d v)).
  intros u v e.
  exact (three_mor11 (dmor d e)).
Defined.

Context (CC : Colims C).
Context (dbase := mapdiagram (pr1_category _) d).
Context (clbase := arrow_colims CC _ dbase).
Context (d11 := three_middle_diagram).
Context (cl11 := CC _ d11).

Local Definition three_colimit : three C.
Proof.
  (* dom / cod are colims of dom / cod *)
  exists (colim clbase).

  (* arrow colim is colim of arrows *)
  exists (colim cl11).
  use tpair.
  - use colimOfArrows.
    * intro v.
      exact (three_mor01 (dob d v)).
    * abstract (
        intros u v e;
        exact (pathsinv0 (pr1 (three_mor_comm (dmor d e))))
      ).
  - use tpair.
    * use colimOfArrows.
      + intro v.
        exact (three_mor12 (dob d v)).
      + abstract (
          intros u v e;
          exact (pathsinv0 (pr2 (three_mor_comm (dmor d e))))
        ).
    * abstract (
        use colimArrowUnique;
        intro v;
        (* cbn. *)
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                use (colimOfArrowsIn _ _ (CC g
                    (mapdiagram (pr1_functor C C)
                      (mapdiagram (pr1_category (arrow_disp C)) dbase))))
        |];
        etrans; [apply assoc'|];
        etrans; [apply cancel_precomposition;
                use (colimOfArrowsIn)|];
                
        etrans; [apply assoc|];
        apply cancel_postcomposition;
        apply three_comp
      ).
Defined.

Local Definition three_cocone : cocone d three_colimit.
Proof.
  use tpair.
  - intro v.
    exists (colimIn clbase v).
    exists (colimIn cl11 _).
    split.
    * abstract (
        apply pathsinv0;
        etrans; [apply (colimOfArrowsIn _ _ (CC g
                        (mapdiagram (pr1_functor C C)
                          (mapdiagram (pr1_category (arrow_disp C)) dbase))))|];
        reflexivity
      ).
    * abstract (
        apply pathsinv0;
        etrans; [apply (colimOfArrowsIn _ _ cl11)|];
        reflexivity
      ).
  - intros u v e.
    use three_mor_eq''.
    * exact (colimInCommutes clbase _ _ e).
    * exact (colimInCommutes cl11 _ _ e).
Defined.

Definition three_isColimCocone : isColimCocone d three_colimit three_cocone.
Proof.
  intros c cc.
  
  transparent assert (ccbase : (cocone dbase (three_mor02 c))).
  {
    exists (λ v, pr1 (coconeIn cc v)).
    abstract (
      intros u v e;
      exact (base_paths _ _ (coconeInCommutes cc _ _ e))
    ).
  }
  
  transparent assert (cc11 : (cocone d11 (three_ob1 c))).
  {
    exists (λ v, three_mor11 (coconeIn cc v)).
    intros u v e.

    set (ob1_path := base_paths _ _ (fiber_paths (coconeInCommutes cc _ _ e))).
    
    abstract (
      apply pathsinv0;
      etrans; [exact (pathsinv0 ob1_path)|];
      cbn;
      rewrite pr1_transportf;
      rewrite transportf_const;
      reflexivity
    ).
  }

  use unique_exists.
  - exists (colimArrow clbase _ ccbase).
    exists (colimArrow cl11 _ cc11).
    split.
    * (* cbn *)
      abstract (
        etrans; [use precompWithColimOfArrows|];
        apply pathsinv0;
        etrans; [use postcompWithColimArrow|];

        apply maponpaths;
        (apply subtypePath; [intro; do 3 (apply impred; intro); apply homset_property|]);
        apply funextsec;
        intro v;
        (* commutativity of top square of coconeIn cc v *)
        exact (pathsinv0 (pr1 (three_mor_comm (coconeIn cc v))))
      ).
    * (* cbn *)
      abstract (
        etrans; [use precompWithColimOfArrows|];
        apply pathsinv0;
        etrans; [use postcompWithColimArrow|];

        apply maponpaths;
        (apply subtypePath; [intro; do 3 (apply impred; intro); apply homset_property|]);
        apply funextsec;
        intro v;
        (* commutativity of bottom square of coconeIn cc v *)
        exact (pathsinv0 (pr2 (three_mor_comm (coconeIn cc v))))
      ).
  - abstract (
      intro;
      use three_mor_eq''; [
        exact (colimArrowCommutes clbase _ ccbase v)|
        exact (colimArrowCommutes cl11 _ cc11 v)
      ]
    ).
  - abstract (
      intro; apply impred; intro; apply homset_property
    ).
  - abstract (
      intros y H;
      use three_mor_eq''; apply colimArrowUnique; intro v; [
        exact (base_paths _ _ (H v))|
      ];
      apply pathsinv0;
      (* base paths because fiber_paths also contains commutativity constraints
        of a three_mor *)
      etrans; [exact (pathsinv0 (base_paths _ _ (fiber_paths (H v))))|];
      etrans; [
        cbn;
        rewrite pr1_transportf;
        rewrite transportf_const;
        reflexivity|
      ];
      reflexivity
    ).
Defined.

End three_colimits.

Definition three_colims {C : category} (CC : Colims C) :
    Colims (three C).
Proof.
  intros g d.

  use tpair.
  - exists (three_colimit d CC).
    exact (three_cocone d CC).
  - exact (three_isColimCocone d CC).
Defined.