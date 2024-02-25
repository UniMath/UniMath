Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monads.ComonadCoalgebras.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Pushouts.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.
Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.
Require Import UniMath.CategoryTheory.ModelCategories.Retract.
Require Import UniMath.CategoryTheory.ModelCategories.Lifting.
Require Import UniMath.CategoryTheory.ModelCategories.NWFS.
Require Import UniMath.CategoryTheory.ModelCategories.NWFSisWFS.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.LiftingWithClass.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonadAlgebras.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope morcls.

Arguments CoproductArrow {_} {_} {_} _ {_}.
Arguments CoproductIn {_} {_} {_} _.
Arguments CoproductInCommutes {_} {_} {_} _ {_}.


(* We have to do this special stuff, because we come across
   a lot of equalities between coproduct inclusions, where
   the indexed objects are not the same (map, lifting problem map --> f)
   only because the lifting problems are not the same, the maps are
   in fact the same.

   In fact, all the inclusions we do are based on the (co)domain of the
   map of the lifting problem, and entirely independent of the lifting
   problem itself. This means that indeed, the inclusions should just
   be equal.

   In theory though, in a general case, the inclusions would not be equal,
   and differ by some idtoiso (see CoproductIn_idtoiso), since the
   objects that the inclusions originate from theoretically do not have
   to be the same.
*)
Lemma CoproductInLiftingProblemsEq
    {C : category} {J : morphism_class C} {f : arrow C}
    {a : total_category (morcls_disp J) -> C} {CCa : Coproduct _ _ (λ lp, a (morcls_lp_map lp))}
    {g : total_category (morcls_disp J)} {S S' : (pr1 g) --> f} :
    S = S' -> CoproductIn CCa (g,, S) = CoproductIn CCa (g,, S').
Proof.
  intro H.
  induction H.
  reflexivity.
Qed.

(* specialize domain / codomain cases *)
Lemma CoproductInLiftingProblemsEqDom
    {C : category} {J : morphism_class C} {f : arrow C}
    {CCa : Coproduct _ _ (λ lp, arrow_dom (pr1 (morcls_lp_map lp)))}
    {g : total_category (morcls_disp J)} {S S' : (pr1 g) --> f} :
    S = S' -> CoproductIn CCa (g,, S) = CoproductIn CCa (g,, S').
Proof.
  apply (CoproductInLiftingProblemsEq (a := λ f, arrow_dom (pr1 f))).
Qed.

Lemma CoproductInLiftingProblemsEqCod
    {C : category} {J : morphism_class C} {f : arrow C}
    {CCa : Coproduct _ _ (λ lp, arrow_cod (pr1 (morcls_lp_map lp)))}
    {g : total_category (morcls_disp J)} {S S' : (pr1 g) --> f} :
    S = S' -> CoproductIn CCa (g,, S) = CoproductIn CCa (g,, S').
Proof.
  apply (CoproductInLiftingProblemsEq (a := λ f, arrow_cod (pr1 f))).
Qed.

(* first try basic apply / use, the more expensive match statement *)
Ltac morcls_lp_coproduct_in_eq :=
  apply (CoproductInLiftingProblemsEqCod) ||
  apply (CoproductInLiftingProblemsEqDom) ||
  use (CoproductInLiftingProblemsEqCod) ||
  use (CoproductInLiftingProblemsEqDom) ||
    match goal with
    |- CoproductIn _ ?S = CoproductIn _ ?S'
      => apply (CoproductInLiftingProblemsEqCod (S:=pr2 S)) ||
         apply (CoproductInLiftingProblemsEqCod (S':=pr2 S')) ||
         apply (CoproductInLiftingProblemsEqDom (S:=pr2 S)) ||
         apply (CoproductInLiftingProblemsEqDom (S':=pr2 S'))
    end.

Section one_step_monad.

Context {C : category} (J : morphism_class C).
Context (CC : Colims C).

(* Garner 2008, section 5.2 (functor K) *)
Definition morcls_coprod_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - (* sending f to ∑_{x ∈ S_f} g_x*)
    intro f.
    exact (morcls_lp_coprod CC J f).
  - (* map γ: f --> f' gives map of lifting problems *)
    intros f f' γ.
    use mors_to_arrow_mor.
    * use CoproductOfArrowsInclusion.
      + (* inclusion of lifting problems S_f into S_f' with γ *)
        intro lpJf.
        destruct lpJf as [g S].
        exists g.
        exact (S · γ).
      + (* map from lifting problem of S_f's left hand domain into that of S_f'
           The lifting problems have the same domain on the left, as f is the
           same. *)
        intro. exact (identity _).
    * use CoproductOfArrowsInclusion.
      + (* the same map here *)
        intro lpJf.
        destruct lpJf as [g S].
        exists g.
        exact (S · γ).
      + intro. exact (identity _).
    * (* commutativity of coproduct arrow inclusion with
         ∑_{x∈S_f} g_x and ∑_{x∈S_f'} g_x *)
      abstract (
        (* simpl; *)
        (* unfold morcls_lp_coprod; *)
        (* simpl; *)
        etrans; [use CoproductOfArrowsInclusion_comp|];
        apply pathsinv0;
        etrans; [use CoproductOfArrowsInclusion_comp|];
        (* simpl; *)
        (* equality of coproduct of arrows *)
        apply maponpaths;
        apply funextsec;
        intro;
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply id_left|];
        reflexivity
      ).
Defined.

Definition morcls_coprod_functor_is_functor : is_functor morcls_coprod_functor_data.
Proof.
  split.
  - intro f.
    use arrow_mor_eq; apply pathsinv0, Coproduct_endo_is_identity; intro.
    * etrans.
      apply (CoproductOfArrowsInclusionIn _ (morcls_lp_dom_coprod CC J f)).
      (* simpl. *)
      etrans. apply id_left.
      (* unfold morcls_lp_dom_coprod. *)
      (* apply (CoproductInLiftingProblemsEqDom (S := pr2 i · _)). *)
      morcls_lp_coproduct_in_eq.
      etrans. apply id_right.
      reflexivity.
    * etrans.
      apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J f)).
      (* simpl. *)
      etrans. apply id_left.
      morcls_lp_coproduct_in_eq.
      (* apply (CoproductInLiftingProblemsEqCod (S := pr2 i · _)). *)
      apply id_right.
  - intros g f h S T.
    use arrow_mor_eq; apply pathsinv0.
    * etrans. use CoproductOfArrowsInclusion_comp.
      (* simpl. *)
      etrans. apply maponpaths.
              apply funextsec.
              intro.
              apply id_right.

      apply CoproductArrowUnique.
      intro.
      etrans. use (CoproductOfArrowsInclusionIn _ _ _ _ i).
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply id_left.
      (* apply (CoproductInLiftingProblemsEqDom (S := pr2 i · _)). *)
      morcls_lp_coproduct_in_eq.
      etrans. apply assoc.
      reflexivity.
    * etrans. use CoproductOfArrowsInclusion_comp.
      (* simpl. *)
      etrans. apply maponpaths.
              apply funextsec.
              intro.
              apply id_right.

      apply CoproductArrowUnique.
      intro.
      etrans. use (CoproductOfArrowsInclusionIn _ _ _ _ i).
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply id_left.
      morcls_lp_coproduct_in_eq.
      (* apply (CoproductInLiftingProblemsEqCod (S := pr2 i · _)). *)
      apply assoc.
Qed.

(* K in Garner *)
Definition morcls_coprod_functor : functor (arrow C) (arrow C) :=
    (_,, morcls_coprod_functor_is_functor).

Definition morcls_coprod_nat_trans_data :
    nat_trans_data morcls_coprod_functor (functor_identity _).
Proof.
  intro f.
  exact (morcls_lp_coprod_diagram CC J f).
Defined.

Definition morcls_coprod_nat_trans_is_nat_trans :
    is_nat_trans _ _ morcls_coprod_nat_trans_data.
Proof.
  intros f f' γ.
  use arrow_mor_eq.
  - etrans. use precompWithCoproductArrowInclusion.
    apply pathsinv0.
    etrans. apply postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply pathsinv0.
    apply id_left.
  - etrans. use precompWithCoproductArrowInclusion.
    apply pathsinv0.
    etrans. apply postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply pathsinv0.
    apply id_left.
Qed.

(* φ in Garner 2007, p23 *)
Definition morcls_coprod_nat_trans :
    nat_trans morcls_coprod_functor (functor_identity _) :=
  (_,, morcls_coprod_nat_trans_is_nat_trans).

Arguments CoproductObject {_} {_} {_}.
Lemma commuting_cube_construction {f f' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod CC J _)
          --> CoproductObject (morcls_lp_dom_coprod CC J _)}
    {bb : CoproductObject (morcls_lp_cod_coprod CC J f)
          --> CoproductObject (morcls_lp_cod_coprod CC J f')}
    {cc : arrow_dom f --> arrow_dom f'}
    (leftface : (morcls_coprod_functor f) · bb = aa · (morcls_coprod_functor f'))
    (topface  : arrow_mor00 (morcls_lp_coprod_diagram CC J f) · cc =
                aa · arrow_mor00 (morcls_lp_coprod_diagram CC J f')) :
  E1 CC J f --> E1 CC J f'.
Proof.
  (* The map induced by pushouts on the front and back face
     (only the front face is drawn)
          ∑h
      ∑A ------> C
       |\ aa       \  cc
  ∑f=Kg|  \     ∑h'  \
       |    ∑A' -----> C
       v    |
      ∑B    |Kg'       |
        \   |=     PO    λ1f'
      bb  \ v∑f'       v
           ∑B' - - - > E1f'
  *)
  set (CE1f' := cc · (λ1 CC J f')).
  set (BE1f' := bb · (PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J f'))).

  use (PushoutArrow
       (morcls_lp_coprod_diagram_pushout CC J f)
       _ BE1f' CE1f').

  abstract (
    (* Left to show commutativity of (outer) pushout diagram *)
    (* Kg · (arrow_mor11 Kγ) · (PushoutIn1 f') = (PushoutIn f) · γ00 · λ1f *)
    (* unfold CE1f', BE1f'; *)
    etrans; [apply assoc|];

    (* first rewrite commutativity of left face *)
    etrans; [apply cancel_postcomposition; exact leftface|];
    etrans; [apply assoc'|];

    (* rewrite commutativity in top face *)
    apply pathsinv0;
    etrans; [apply assoc|];
    etrans; [apply cancel_postcomposition; exact topface|];

    (* cancel precomposition with aa: ∑A --> ∑A' arrow *)
    etrans; [apply assoc'|];
    apply cancel_precomposition;

    (* all that's left is commutativity in the pushout square of f' *)
    apply pathsinv0;
    exact (PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout CC J f'))
  ).
Defined.

Lemma commuting_cube_bottom_face {f f' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod CC J f)
          --> CoproductObject (morcls_lp_dom_coprod  CC J f')}
    {bb : CoproductObject (morcls_lp_cod_coprod  CC J f)
          --> CoproductObject (morcls_lp_cod_coprod  CC J f')}
    {cc : arrow_dom f --> arrow_dom f'}
    {leftface : (morcls_coprod_functor f) · bb = aa · (morcls_coprod_functor f')}
    {topface  : arrow_mor00 (morcls_lp_coprod_diagram  CC J f) · cc =
                aa · arrow_mor00 (morcls_lp_coprod_diagram  CC J f')} :
  PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J f) · commuting_cube_construction leftface topface =
  bb · PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J f').
Proof.
  etrans. apply PushoutArrow_PushoutIn1.
  reflexivity.
Qed.

Lemma commuting_cube_right_face {f f' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod CC J f)
          --> CoproductObject (morcls_lp_dom_coprod CC J f')}
    {bb : CoproductObject (morcls_lp_cod_coprod CC J f)
          --> CoproductObject (morcls_lp_cod_coprod CC J f')}
    {cc : arrow_dom f --> arrow_dom f'}
    {leftface : (morcls_coprod_functor f) · bb = aa · (morcls_coprod_functor f')}
    {topface  : arrow_mor00 (morcls_lp_coprod_diagram CC J f) · cc =
                aa · arrow_mor00 (morcls_lp_coprod_diagram CC J f')} :
  cc · λ1 CC J f' =
  λ1 CC J f · commuting_cube_construction leftface topface.
Proof.
  apply pathsinv0.
  etrans. apply PushoutArrow_PushoutIn2.
  reflexivity.
Qed.

Lemma commuting_cube_construction_eq {f f' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod CC J f)
          --> CoproductObject (morcls_lp_dom_coprod CC J f')}
    {bb : CoproductObject (morcls_lp_cod_coprod CC J f)
          --> CoproductObject (morcls_lp_cod_coprod CC J f')}
    {cc : arrow_dom f --> arrow_dom f'}
    {aa' : CoproductObject (morcls_lp_dom_coprod CC J f)
           --> CoproductObject (morcls_lp_dom_coprod CC J f')}
    {bb' : CoproductObject (morcls_lp_cod_coprod CC J f)
           --> CoproductObject (morcls_lp_cod_coprod CC J f')}
    {cc' : arrow_dom f --> arrow_dom f'}
    (leftface : (morcls_coprod_functor f) · bb = aa · (morcls_coprod_functor f'))
    (topface  : arrow_mor00 (morcls_lp_coprod_diagram CC J f) · cc =
                aa · arrow_mor00 (morcls_lp_coprod_diagram CC J f'))
    (leftface' : (morcls_coprod_functor f) · bb' = aa' · (morcls_coprod_functor f'))
    (topface'  : arrow_mor00 (morcls_lp_coprod_diagram CC J f) · cc' =
                 aa' · arrow_mor00 (morcls_lp_coprod_diagram CC J f')) :
  bb = bb' -> cc = cc' -> commuting_cube_construction leftface topface = commuting_cube_construction leftface' topface'.
Proof.
  intros Hb Hc.
  (* unfold commuting_cube_construction. *)
  use PushoutArrowUnique.
  - etrans. apply PushoutArrow_PushoutIn1.
    apply cancel_postcomposition.
    exact Hb.
  - etrans. apply PushoutArrow_PushoutIn2.
    apply cancel_postcomposition.
    exact Hc.
Qed.

(* one step comonad functor L1 sends f to λ1f *)
Definition one_step_comonad_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - intro f.
    exact (λ1 CC J f).
  - intros f f' γ.
    (* The map on morphisms becomes the right face from the cube induced by
          ∑h
      ∑A ------> C
       |\          \  γ00
  ∑f=Kg|  \     ∑h'  \
       |    ∑A' -----> C
       v Kγ |
      ∑B    |Kg'       |
        \   |=     PO    λ1f'
          \ v∑f'       v
           ∑B' - - - > E1f'
    *)
    (* the morphism E1f --> E1f' we will need arises from the pushout
         property with the following maps. *)
    set (Kγ := (#morcls_coprod_functor)%cat γ).
    set (φγ := nat_trans_ax morcls_coprod_nat_trans f f' γ).
    set (φγ00 := arrow_mor00_eq φγ).

    use mors_to_arrow_mor.
    * exact (arrow_mor00 γ).
    * use commuting_cube_construction.
      + exact (arrow_mor00 Kγ).
      + exact (arrow_mor11 Kγ).
      + exact (arrow_mor00 γ).
      + abstract (exact (pathsinv0 (arrow_mor_comm Kγ))).
      + abstract (exact (pathsinv0 φγ00)).
    * (* commutativity of right face *)
      (* γ00 · λ1f' = λ1f · ccc *)
      (* This follows simply from the properties of a pushout *)
      abstract (
        apply commuting_cube_right_face
      ).
Defined.

Definition one_step_comonad_functor_is_functor : is_functor one_step_comonad_functor_data.
Proof.
  split.
  - intro f.
    use arrow_mor_eq.
    * (* top map is identity simply because it comes from a functor *)
      reflexivity.
    * (* bottom map is identity because the pushout arrow is unique *)
      apply pathsinv0, PushoutArrowUnique.
      + etrans. apply id_right.
        apply pathsinv0.
        etrans. apply cancel_postcomposition.
                apply maponpaths.
                apply functor_id.
        apply id_left.
      + etrans. apply id_right.
        apply pathsinv0.
        apply id_left.
  - intros g f h S T.
    use arrow_mor_eq.
    * reflexivity.
    * apply pathsinv0, PushoutArrowUnique.
      (* Gotta keep in mind that (# one_step_comonad_functor_data) S
         is a PushoutArrow and we can then use pushout properties. *)
      + apply pathsinv0.
        etrans. apply cancel_postcomposition.
                apply maponpaths.
                apply functor_comp.
        apply pathsinv0.
        (* PushoutIn1 · (PushoutArrow · PushoutArrow) = arrow_mor11 · PushoutIn *)
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                use PushoutArrow_PushoutIn1.
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                use PushoutArrow_PushoutIn1.
        apply assoc.
      + (* PushoutIn2 (PushoutArrow · PushoutArrow) = arrow_mor00 (S T) · PushoutIn *)
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                use PushoutArrow_PushoutIn2.
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                use PushoutArrow_PushoutIn2.
        apply assoc.
Qed.

Definition one_step_comonad_functor : functor (arrow C) (arrow C) :=
    (_,, one_step_comonad_functor_is_functor).

Lemma one_step_comonad_ρ1_compat {f f' : arrow C} (γ : f --> f') :
    arrow_mor11 (#(one_step_comonad_functor) γ)%cat · ρ1 CC J f' =
      ρ1 CC J f · arrow_mor11 γ.
Proof.
  use (MorphismsOutofPushoutEqual
        (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J f))).
  -
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use PushoutArrow_PushoutIn1.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            use PushoutArrow_PushoutIn1.
    etrans. apply precompWithCoproductArrowInclusion.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn1.
    etrans. apply postcompWithCoproductArrow.

    apply maponpaths.
    apply funextsec.
    intro.
    apply pathsinv0.
    apply id_left.
  - etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use PushoutArrow_PushoutIn2.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            use PushoutArrow_PushoutIn2.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn2.

    apply pathsinv0.
    exact (arrow_mor_comm γ).
Qed.

Definition one_step_factorization_data : section_disp_data (three_disp C).
Proof.
  use tpair.
  - intro f.
    exists (E1 CC J f).
    exists (λ1 CC J f), (ρ1 CC J f).
    abstract (
      apply λ1_ρ1_compat
    ).
  - intros f f' γ.
    (* cbn. *)
    set (L1γ := (#(one_step_comonad_functor) γ)%cat).
    exists (arrow_mor11 L1γ).
    abstract (
      split; apply pathsinv0; [
        (* commutativity of λ1 and arrow_mor11 (#L1 γ) *)
        exact (arrow_mor_comm L1γ)
      | (* commutativity of ρ1 and arrow_mor11 (#L1 γ) = arrow_mor00 (#R1 γ) *)
        apply one_step_comonad_ρ1_compat
      ]
    ).
Defined.

Definition one_step_factorization_axioms : section_disp_axioms one_step_factorization_data.
Proof.
  (* these identities follow from the functorality of f -> λ1f (one_step_comonad_functor)
  *)

  split.
  - intro f.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    (* cbn. *)
    (* behavior of commuting cube construction on identity follows from
       identity axiom of the one_step_comonad_functor *)
    set (one_step_comonad_id := functor_id (one_step_comonad_functor) f).
    set (bottom := arrow_mor11_eq one_step_comonad_id).
    exact bottom.
  - intros g1 g2 g3 γ12 γ23.
    (* behavior of commuting cube construction on composition follows from
      identity axiom of the one_step_comonad_functor *)
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    set (one_step_comonad_comp := functor_comp (one_step_comonad_functor) γ12 γ23).
    set (bottom := arrow_mor11_eq one_step_comonad_comp).
    exact bottom.
Qed.

Definition one_step_factorization : functorial_factorization C :=
    (_,, one_step_factorization_axioms).

(* Lemma E1_compat (f : arrow C) : E1 CC J f = E1 J (opp_mor f) (CC _) POs.
Proof.
  reflexivity.
Qed.

Context (CCopp : ∏ (f : arrow (op_cat C)), Coproducts (morcls_lp (morphism_class_opp J) f) (op_cat C)) (POsopp : Pushouts (op_cat C)).

Lemma λ1_ρ1_opp_compat (f : arrow C) :
    arrow_cod (λ1 CC J f) = arrow_dom (ρ1 (morphism_class_opp J) (opp_arrow f) (CCopp _) POsopp).
Proof.
  cbn.
Defined. *)

Definition one_step_monad_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - intro f.
    exact (ρ1 CC J f).
  - intros f f' γ.

    use mors_to_arrow_mor.
    * exact (arrow_mor11 (#one_step_comonad_functor γ)%cat).
    * exact (arrow_mor11 γ).
    * abstract (
        exact (one_step_comonad_ρ1_compat _)
      ).
Defined.

Definition one_step_monad_functor_is_functor : is_functor one_step_monad_functor_data.
Proof.
  split.
  - intro f.
    use arrow_mor_eq.
    * (* bottom map is identity because the pushout arrow is unique *)
      apply pathsinv0, PushoutArrowUnique.
      + etrans. apply id_right.
        apply pathsinv0.
        etrans. apply cancel_postcomposition.
                apply maponpaths.
                apply functor_id.
        apply id_left.
      + etrans. apply id_right.
        apply pathsinv0.
        apply id_left.
    * (* bottom map is identity simply because it comes from a functor *)
      reflexivity.
  - intros g f h S T.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * etrans. apply maponpaths.
              apply (functor_comp one_step_comonad_functor).
      reflexivity.
    * reflexivity.
Qed.

Definition one_step_monad_functor : functor (arrow C) (arrow C) :=
    (_,, one_step_monad_functor_is_functor).

Definition one_step_comonad_counit_data : nat_trans_data (one_step_comonad_functor) (functor_identity _).
Proof.
  (* Send λ1 f --> f along
      C ====== C
      |        |
  λ1f |   L1   | f
      v        v
    E1f ----> D
          ρ1f
  *)
  intro f.
  use mors_to_arrow_mor.
  - exact (identity _).
  - exact (ρ1 CC J f).
  - abstract (exact (arrow_mor_comm (morcls_lp_coprod_diagram_red CC J f))).
Defined.

Definition one_step_comonad_counit_is_nat_trans : is_nat_trans _ _ one_step_comonad_counit_data.
Proof.
  intros f f' γ.
  use arrow_mor_eq.
  - etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
  - (* PushoutArrow (morcls_lp_coprod_diagram_pushout f (CC f) POs) ...
       · ρ1f' = ρ1f · γ11 *)
    (* We are trying to prove an equality of maps E1f --> arrow_cod f' *)
    use (MorphismsOutofPushoutEqual
          (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J f))).
    * (* todo: this is a really common strategy, generalize this? *)
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              use PushoutArrow_PushoutIn1.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn1.

      (* simplify left hand side *)
      (* etrans. { simpl. reflexivity. } *)
      (* k_x · γ11 = arrow_mor11 (Kγ) · k_x' *)
      (* this is just the commutativity of the bottom square of the
         commutative cube of φ *)
      set (φax := nat_trans_ax morcls_coprod_nat_trans f f' γ).
      set (bottom_square := arrow_mor11_eq φax).
      apply pathsinv0.
      exact (bottom_square).
    *
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn2.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              use PushoutArrow_PushoutIn2.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn2.

      apply pathsinv0.
      exact (arrow_mor_comm γ).
Qed.

Definition one_step_comonad_counit : nat_trans (one_step_comonad_functor) (functor_identity _) :=
    (_,, one_step_comonad_counit_is_nat_trans).

Definition one_step_monad_unit_data : nat_trans_data (functor_identity _) (one_step_monad_functor).
Proof.
  (* Send f --> ρ1 f along
         λ1f
      C ----> E1f
      |        |
  f   |   R1   | ρ1f
      v        v
      D ====== D
  *)
  intro f.
  use mors_to_arrow_mor.
  - exact (λ1 CC J f).
  - exact (identity _).
  - abstract (exact (arrow_mor_comm (morcls_lp_coprod_diagram_red_flipped CC J f))).
Defined.

Definition one_step_monad_unit_is_nat_trans : is_nat_trans _ _ one_step_monad_unit_data.
Proof.
  intros f f' γ.
  use arrow_mor_eq.
  - apply pathsinv0.
    apply PushoutArrow_PushoutIn2.
  - etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
Qed.

Definition one_step_monad_unit : nat_trans (functor_identity _) (one_step_monad_functor) :=
    (_,, one_step_monad_unit_is_nat_trans).

(* ψf in Garner *)
Definition morcls_lp_coprod_L1_inclusion (f : arrow C) :
    morcls_lp J f -> morcls_lp J (λ1 CC J f).
Proof.
  (* The inclusion of lifting problems is induced by
    S_f → S_{L1f} : x ↦ (g_x -- in_x -> Kf = ∑f -- ϵf -> L1f)
    where ϵf is morcls_lp_coprod_diagram_red:
              ∑h
    A ---> ∑A ---> X
    |      |       |
  g |    ∑g|       | λ1f
    v      v       v
    B ---> ∑B ---> E1f
    *)
  intro S.
  exists (pr1 S).
  (* right hand square *)
  transparent assert (rhs_mor : (morcls_lp_coprod CC J f --> λ1 CC J f)).
  {
    use mors_to_arrow_mor.
    - exact (arrow_mor00 (morcls_lp_coprod_diagram CC J f)).
    - exact (PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J f)).
    - abstract (
        set (rhs := PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout CC J f));
        exact (pathsinv0 rhs)
      ).
  }
  apply (postcompose rhs_mor).

  (* left hand square *)
  (* todo: generalize this *)
  use mors_to_arrow_mor.
  - exact (CoproductIn (morcls_lp_dom_coprod CC J f) S).
  - exact (CoproductIn (morcls_lp_cod_coprod CC J f) S).
  - abstract (exact (CoproductInCommutes _ _ S)).
Defined.

(* δf in Garner *)
Definition morcls_lp_coprod_L1_map (f : arrow C) :
    (morcls_lp_coprod CC J f) --> (morcls_lp_coprod CC J (λ1 CC J f)).
Proof.
  (* the inclusion of the objects are just identity on themselves *)
  use mors_to_arrow_mor;
    try exact (CoproductOfArrowsInclusion
              (morcls_lp_coprod_L1_inclusion f) _ _
              (λ _, (identity _))).

  (* commutativity *)
  abstract (
    etrans; [use precompWithCoproductArrowInclusion|];
    (* simpl; *)
    apply pathsinv0;
    etrans; [use postcompWithCoproductArrow|];
    (* simpl; *)
    apply maponpaths;
    apply funextsec;
    intro S;
    apply pathsinv0;
    etrans; [apply id_left|];
    apply pathsinv0;
    etrans; [apply assoc'|];
    etrans; [apply cancel_precomposition; exact (CoproductOfArrowsInclusionIn _ _ _ _ S)|];
    etrans; [apply cancel_precomposition; apply id_left|];
    reflexivity
  ).
Defined.

Definition one_step_comonad_mul_data :
    nat_trans_data
      (fact_L one_step_factorization)
      (functor_composite (fact_L one_step_factorization) (fact_L one_step_factorization)).
Proof.
  intro f.
  (* The map on morphisms becomes the right face from the cube induced by
          ∑h
      ∑A ------> C
       |\          =
  ∑f=Kg|  \     ∑h'  =
       |    ∑A' -----> C
       v δf |
      ∑B    |Kλf       |
        \   |=     PO    λ1f
          \ v∑λf f     v
           ∑B  - - - > E1f
    *)
  set (δf := morcls_lp_coprod_L1_map f).

  use mors_to_arrow_mor.
  - exact (identity _).
  - use commuting_cube_construction.
    * (* aa *) exact (arrow_mor00 δf).
    * (* bb *) exact (arrow_mor11 δf).
    * (* cc *) exact (identity _).
    * (* left face *)
      exact (pathsinv0 (arrow_mor_comm δf)).
    * (* top face *)
      abstract (
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply precompWithCoproductArrowInclusion|];
        (* cbn. *)
        apply (maponpaths (CoproductArrow _));
        apply funextsec;
        intro S;
        etrans; [apply id_left|];
        exact (CoproductInCommutes _ _ S)
      ).
  - (* commutativity in right face *)
    abstract (
      use commuting_cube_right_face
    ).
Defined.

Definition one_step_comonad_mul_is_nat_trans : is_nat_trans _ _ one_step_comonad_mul_data.
Proof.
  intros f f' γ.
  use arrow_mor_eq.
  - (* simpl. *)
    etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
  - (* equality of arrows E1 f --> E1 (λ1f) *)
    use (MorphismsOutofPushoutEqual
      (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J f))).
    *
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.

      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.

      apply cancel_postcomposition.
      (* cbn. *)
      etrans. use CoproductOfArrowsInclusion_comp.
      apply pathsinv0.
      etrans. use CoproductOfArrowsInclusion_comp.

      (* unfold CoproductOfArrowsInclusion. *)
      use CoproductArrowUnique.
      intro.
      (* simpl. *)
      etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod CC J f)).
      etrans. apply assoc'.
      do 2 (etrans; [apply id_left|]).
      apply pathsinv0.
      etrans. apply assoc'.
      do 2 (etrans; [apply id_left|]).

      morcls_lp_coproduct_in_eq.

      use arrow_mor_eq.
      + etrans. apply cancel_postcomposition.
                apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f)).
        apply pathsinv0.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f') _ (_,, _)).
        reflexivity.
      + etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply PushoutArrow_PushoutIn1.

        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply  (CoproductInCommutes (morcls_lp_cod_coprod CC J f)).
        etrans. apply assoc'.
        apply id_left.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn2.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn2.

      etrans. apply cancel_precomposition.
              apply id_left.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn2.
      etrans. etrans. apply assoc'.
              apply cancel_precomposition.
              apply PushoutArrow_PushoutIn2.
      apply id_left.
Qed.

Definition one_step_comonad_mul :
    nat_trans
      (fact_L one_step_factorization)
      (functor_composite (fact_L one_step_factorization) (fact_L one_step_factorization)) :=
  (_,, one_step_comonad_mul_is_nat_trans).

(* Definition one_step_comonad_functor_with_μ : functor_with_μ (op_cat (arrow C)) :=
    (functor_opp one_step_comonad_functor,, op_nt one_step_comonad_mul). *)

Definition one_step_comonad_data : disp_Comonad_data _ :=
    L_monad_data one_step_factorization one_step_comonad_mul.

Local Lemma one_step_comonad_assoc_law11 (f : arrow C) :
  arrow_mor11 (
    disp_δ one_step_comonad_data f
    · (# (fact_L one_step_factorization))%cat (disp_δ one_step_comonad_data f)
  ) =
  arrow_mor11 (
    disp_δ one_step_comonad_data f
    · disp_δ one_step_comonad_data (fact_L one_step_factorization f)
  ).
Proof.
  use (MorphismsOutofPushoutEqual (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J f))).
  - etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use PushoutArrow_PushoutIn1.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply PushoutArrow_PushoutIn1.
    etrans. apply assoc.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn1.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply PushoutArrow_PushoutIn1.
    etrans. apply assoc.
    apply cancel_postcomposition.

    (* show_id_type. *)
    use CoproductArrow_eq.
    intro S.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J f)).
    etrans. apply cancel_postcomposition.
            apply id_left.
    etrans. use (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (fact_L one_step_factorization f)) _ _ (morcls_lp_coprod_L1_inclusion f S)).
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J f)).
    etrans. apply assoc'.
    etrans. apply id_left.
    etrans. use (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (fact_L one_step_factorization f)) _ _ (morcls_lp_coprod_L1_inclusion f S)).
    etrans. apply id_left.
    morcls_lp_coproduct_in_eq.
    use arrow_mor_eq.
    * etrans. apply id_right.
      etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f)).
      apply pathsinv0.
      etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (λ1 CC J f)) _ (morcls_lp_coprod_L1_inclusion f S)).
      etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f)).
      reflexivity.
    * etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.
      apply cancel_postcomposition.
      etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J f)).
      apply id_left.
  - etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn2.
    etrans. apply assoc'.
    etrans. apply id_left.
    etrans. apply PushoutArrow_PushoutIn2.
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn2.
    etrans. apply assoc'.
    etrans. apply id_left.
    etrans. apply PushoutArrow_PushoutIn2.
    apply id_left.
Qed.

Definition one_step_comonad_laws :
    disp_Comonad_laws one_step_comonad_data.
Proof.
  repeat split; intro f; use arrow_mor_eq.
  - apply id_left.
  - apply pathsinv0.
    use PushoutEndo_is_identity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply precompWithCoproductArrowInclusion.
      apply pathsinv0.

      use CoproductArrowUnique.
      intro.
      (* cbn. *)
      apply pathsinv0.
      apply id_left.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn2.
      apply id_left.
  - apply id_left.
  - apply pathsinv0.
    use PushoutEndo_is_identity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.

      apply pathsinv0.
      etrans. exact (pathsinv0 (id_left _)).
      apply cancel_postcomposition.

      apply pathsinv0.
      etrans. use CoproductOfArrowsInclusion_comp.
      apply pathsinv0.

      use Coproduct_endo_is_identity.
      intro S.
      etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J f)).
      (* simpl. *)
      etrans. apply cancel_postcomposition.
              apply id_left.
      etrans. apply id_left.
      morcls_lp_coproduct_in_eq.

      use arrow_mor_eq.
      + etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply id_right.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f) _ S).
        reflexivity.
      + etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply PushoutArrow_PushoutIn1.

        etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod CC J f) _ S).
        reflexivity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc.

      etrans. apply assoc'.
      etrans. apply id_left.
      apply id_left.
  - reflexivity.
  - exact (one_step_comonad_assoc_law11 f).
Qed.

Definition one_step_comonad :
    lnwfs_over one_step_factorization :=
  (one_step_comonad_mul,, one_step_comonad_laws).

End one_step_monad.
