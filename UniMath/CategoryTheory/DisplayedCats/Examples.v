
(** * Examples

A typical use for displayed categories is for constructing categories of structured objects, over a given (specific or general) category. We give a few examples here:

- category of topological space as total category
- arrow precategories
- objects with N-actions
- elements, over hSet

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.

Local Open Scope mor_disp_scope.


(** * Displayed category of groups *)

Module group.

Definition grp_structure_data (X : hSet) : UU
  := (X -> X -> X) × X × (X -> X).
Definition mult {X : hSet} (G : grp_structure_data X)
           : X -> X -> X := pr1 G.
Definition e {X : hSet} (G : grp_structure_data X)
           : X := pr1 (pr2 G).
Definition inv {X : hSet} (G : grp_structure_data X)
           : X -> X := pr2 (pr2 G).

Definition grp_structure_axioms {X : hSet}
           (G : grp_structure_data X) : UU
  := (∏ x y z : X, mult G x (mult G y z) = mult G (mult G x y) z)
       ×
     (∏ x : X, mult G x (e G) = x)
       ×
     (∏ x : X, mult G (e G) x = x)
       ×
     (∏ x : X, mult G x (inv G x) = e G)
       ×
     (∏ x : X, mult G (inv G x) x = e G).

Definition grp_assoc {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x y z : X, mult G x (mult G y z) = mult G (mult G x y) z := pr1 GH.
Definition grp_e_r {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x : X, mult G x (e G) = x := pr1 (pr2 GH).
Definition grp_e_l {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x : X, mult G (e G) x = x := pr1 (pr2 (pr2 GH)).
Definition grp_inv_r {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x : X, mult G x (inv G x) = e G := pr1 (pr2 (pr2 (pr2 GH))).
Definition grp_inv_l {X : hSet} {G : grp_structure_data X}
           (GH : grp_structure_axioms G)
  : ∏ x : X, mult G (inv G x) x = e G := pr2 (pr2 (pr2 (pr2 GH))).

Definition grp_structure (X : hSet) : UU
  := ∑ G : grp_structure_data X, grp_structure_axioms G.
Coercion grp_data {X} (G : grp_structure X) : grp_structure_data X := pr1 G.
Coercion grp_axioms {X} (G : grp_structure X) : grp_structure_axioms _ := pr2 G.

Definition is_grp_hom {X Y : hSet} (f : X -> Y)
           (GX : grp_structure X) (GY : grp_structure Y) : UU
           := (∏ x x', f (mult GX x x') = mult GY (f x) (f x'))
                ×
              (f (e GX) = e GY).
Definition grp_hom_mult {X Y : hSet} {f : X -> Y}
           {GX : grp_structure X} {GY : grp_structure Y}
           (is : is_grp_hom f GX GY)
           : ∏ x x', f (mult GX x x') = mult GY (f x) (f x') := pr1 is.
Definition grp_hom_e {X Y : hSet} {f : X -> Y}
           {GX : grp_structure X} {GY : grp_structure Y}
           (is : is_grp_hom f GX GY)
           : f (e GX) = e GY := pr2 is.

Definition isaprop_is_grp_hom {X Y : hSet} (f : X -> Y)
           (GX : grp_structure X) (GY : grp_structure Y)
  : isaprop (is_grp_hom f GX GY).
Proof.
  repeat apply (isofhleveldirprod);
  repeat (apply impred; intro);
  apply setproperty.
Qed.

Definition disp_grp : disp_cat hset_category.
Proof.
  use disp_struct.
  - exact grp_structure.
  - intros X Y GX GY f. exact (is_grp_hom f GX GY).
  - intros.  apply isaprop_is_grp_hom.
  - intros. simpl.
    repeat split; intros; apply idpath.
  - intros ? ? ? ? ? ? ? ? Gf Gg  ; simpl in *;
    repeat split; intros; simpl; cbn.
    + rewrite (grp_hom_mult Gf).
      apply (grp_hom_mult Gg).
    + rewrite (grp_hom_e Gf).
      apply (grp_hom_e Gg).
Defined.


End group.



(** ** The displayed arrow category

A very fertile example: many others can be obtained from it by reindexing. *)
Section Arrow_Disp.

Context (C:category).

Definition arrow_disp_ob_mor : disp_cat_ob_mor (prod_category C C).
Proof.
  exists (λ xy : (C × C), (pr1 xy) --> (pr2 xy)).
  simpl; intros xx' yy' g h ff'.
    exact (pr1 ff' · h = g · pr2 ff').
Defined.

Definition arrow_id_comp : disp_cat_id_comp _ arrow_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition arrow_data : disp_cat_data _
  := (arrow_disp_ob_mor ,, arrow_id_comp).

Lemma arrow_axioms : disp_cat_axioms (prod_category C C) arrow_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property.
Qed.

Definition arrow_disp : disp_cat (prod_category C C)
  := (arrow_data ,, arrow_axioms).

End Arrow_Disp.

(** ** Objects with N-action

For any category C, “C-objects equipped with an N-action” (or more elementarily, with an endomorphism) form a displayed category over C
Section ZAct.

Once we have pullbacks of displayed precategories, this can be obtained as a pullback of the previous example. *)

Section NAction.

Context (C:category).

Definition NAction_disp_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ c, c --> c).
  intros x y xx yy f. exact (f · yy = xx · f).
Defined.

Definition NAction_id_comp : disp_cat_id_comp C NAction_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition NAction_data : disp_cat_data C
  := (NAction_disp_ob_mor ,, NAction_id_comp).

Lemma NAction_axioms : disp_cat_axioms C NAction_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property.
Qed.

Definition NAction_disp : disp_cat C
  := (NAction_data ,, NAction_axioms).

End NAction.

(** ** Elements of sets

A presheaf on a (pre)category can be viewed as a fiberwise discrete displayed (pre)category. In fact, the universal example of this is the case corresponding to the identity functor on [SET].  So, having given the displayed category for this case, one obtains it for arbitrary presheaves by reindexing. *)

(* TODO: move? ponder? *)



Section Elements_Disp.

Definition elements_ob_mor : disp_cat_ob_mor SET.
Proof.
  use tpair.
  - simpl. exact (λ X, X).
  - simpl. intros X Y x y f. exact (f x = y).
Defined.

Lemma elements_id_comp : disp_cat_id_comp SET elements_ob_mor.
Proof.
  apply tpair; simpl.
  - intros X x. apply idpath.
  - intros X Y Z f g x y z e_fx_y e_gy_z. cbn.
    eapply pathscomp0. apply maponpaths, e_fx_y. apply e_gy_z.
Qed.

Definition elements_data : disp_cat_data SET
  := (_ ,, elements_id_comp).

Lemma elements_axioms : disp_cat_axioms SET elements_data.
Proof.
  repeat split; intros; try apply setproperty.
  apply isasetaprop; apply setproperty.
Qed.

Definition elements_universal : disp_cat SET
  := (_ ,, elements_axioms).

Definition disp_cat_of_elements {C : category} (P : functor C SET)
  := reindex_disp_cat P elements_universal.

(* TODO: compare to other definitions of this in the library! *)
Definition precat_of_elements {C : category} (P : functor C SET)
  := total_category (disp_cat_of_elements P).

End Elements_Disp.



Section functor_algebras.

Context {C : category} (F : functor C C).

Definition functor_alg_ob : C -> UU := λ c, F c --> c.

Definition functor_alg_mor
  : ∏ (x y : C), functor_alg_ob x → functor_alg_ob y → C⟦x,y⟧ → UU.
Proof.
  intros c d a a' r. exact ( (#F r)%cat · a' = a · r).
Defined.

Definition isaprop_functor_alg_mor
  :  ∏ (x y : C) a a' r,
     isaprop (functor_alg_mor x y a a' r).
Proof.
  intros. simpl. apply homset_property.
Qed.

Definition functor_alg_id
: ∏ (x : C) (a : functor_alg_ob x), functor_alg_mor _ _ a a (identity x ).
Proof.
  intros; unfold functor_alg_mor.
  rewrite functor_id;
  rewrite id_left;
  apply pathsinv0; apply id_right .
Qed.

Definition functor_alg_comp
  : ∏ (x y z : C) a b c (f : C⟦x,y⟧) (g : C⟦y,z⟧),
                 functor_alg_mor _ _  a b f
                 → functor_alg_mor _ _  b c g
                 → functor_alg_mor _ _  a c (f · g).
Proof.
  cbn; intros ? ? ? ? ? ? ? ? X X0;
  unfold functor_alg_mor in *;
  rewrite functor_comp;
  rewrite <-assoc; rewrite X0;
  rewrite assoc; rewrite X;
  apply (!assoc _ _ _ ) .
Qed.

Definition disp_cat_functor_alg : disp_cat C
  := disp_struct _ _
                 functor_alg_mor
                 isaprop_functor_alg_mor
                 functor_alg_id
                 functor_alg_comp.

Definition total_functor_alg : category := total_category disp_cat_functor_alg.

Lemma isaset_functor_alg_ob : ∏ x : C, isaset (functor_alg_ob x).
Proof.
  intro c.
  apply homset_property.
Qed.

Lemma is_univalent_disp_functor_alg : is_univalent_disp disp_cat_functor_alg.
Proof.
  use is_univalent_disp_from_SIP_data.
  - apply isaset_functor_alg_ob.
  - unfold functor_alg_mor.
    intros x a a' H H'.
    rewrite functor_id in H'.
    rewrite id_left in H'.
    rewrite id_right in H'.
    apply H'.
Defined.

Definition iso_cleaving_functor_alg : iso_cleaving disp_cat_functor_alg.
Proof.
  intros c c' i d.
  cbn in *.
  mkpair.
  - exact (compose (compose (functor_on_iso F i) d) (iso_inv_from_iso i)).
  - cbn. unfold iso_disp. cbn.
    mkpair.
    + abstract (
          etrans; [eapply pathsinv0; apply id_right |];
          repeat rewrite <- assoc;
          do 2 apply maponpaths;
          apply pathsinv0; apply iso_after_iso_inv
        ).
    + mkpair.
      * unfold functor_alg_mor.
        cbn. repeat rewrite assoc.
        unfold functor_alg_mor. cbn.
        rewrite <- functor_comp.
        rewrite iso_after_iso_inv.
        rewrite functor_id.
        rewrite id_left. apply idpath.
      * split; apply homset_property.
Defined.


Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Local Notation "'π'" := (pr1_category disp_cat_functor_alg).

Definition creates_limits_functor_alg
  : creates_limits disp_cat_functor_alg.
Proof.
  intros J D x L isL.
  unfold creates_limit. cbn.
  transparent assert (FC : (cone (mapdiagram π D) (F x))).
  { use mk_cone.
    - intro j.
      eapply compose.
      apply ((#F)%cat (coneOut L j )).
      cbn. exact (pr2 (dob D j)).
    - abstract (
      intros; cbn;
      assert (XR := pr2 (dmor D e)); cbn in XR;
      etrans; [eapply pathsinv0; apply assoc |];
      etrans; [apply maponpaths, (!XR) |];
      etrans; [apply assoc |];
      apply maponpaths_2;
      rewrite <- functor_comp;
      apply maponpaths;
      apply (coneOutCommutes L)
      ).
  }
  transparent assert (LL : (LimCone (mapdiagram π D))).
  { use mk_LimCone. apply x. apply L. apply isL. }
  mkpair.
  - mkpair.
    + mkpair.
      * use (limArrow LL). apply FC.
      * abstract (
          mkpair ;
          [
            intro j; cbn;
            set (XR := limArrowCommutes LL _ FC); cbn in XR;
            apply pathsinv0; apply XR
          | cbn; intros i j e;
            apply subtypeEquality;
            [ intro; apply homset_property |];
            cbn; apply (coneOutCommutes L)
          ]).
    + abstract (
      intro t; cbn;
      use total2_paths_f;
      [ cbn;
        apply (limArrowUnique LL);
        induction t as [t [H1 H2]]; cbn in *;
        intro j;
        apply pathsinv0, H1 |];
      apply proofirrelevance;
      apply isofhleveltotal2;
      [ apply impred_isaprop; intro; apply homset_property |];
      intros; do 3 (apply impred_isaprop; intro);
        apply (homset_property (total_category _ ))
        ).
  - cbn.
    intros x' CC.
    set (πCC := mapcone π D CC).
    use unique_exists.
    + mkpair.
      * cbn.
        use (limArrow LL _ πCC).
      * set (XR := limArrowCommutes LL).
        cbn in XR.
        set (H1:= coneOutCommutes CC). simpl in H1.
        destruct x' as [c a]. cbn.
        unfold disp_cat_functor_alg in a. cbn in a.
        cbn in πCC.
        transparent assert (X : (cone (mapdiagram π D) (F c))).
        { use mk_cone.
          - intro j.
            apply (λ f, a · f). cbn.
            apply (coneOut CC j).
          - abstract (
            intros u v e; cbn;
            rewrite <- assoc;
            apply maponpaths;
            apply (maponpaths pr1 (coneOutCommutes CC _ _ _ ))
                  ).
        }

        {
          unfold functor_alg_mor.
          pathvia (limArrow LL _ X).
          - apply (limArrowUnique LL).
            intro j. rewrite <- assoc.
            rewrite (limArrowCommutes LL).
            cbn.
            rewrite assoc.
            rewrite <- functor_comp.
            etrans. apply maponpaths_2. apply maponpaths.
            apply (limArrowCommutes LL). cbn.
            set (H := pr2 (coneOut CC j)).  cbn in H. apply H.
          - apply pathsinv0.
            use (limArrowUnique LL).
            intro j.
            rewrite <- assoc.
            rewrite (limArrowCommutes LL).
            cbn.
            apply idpath.
        }
    + simpl.
      intro j.
      apply subtypeEquality.
      { intro. apply homset_property. }
      cbn. apply (limArrowCommutes LL).
    + intros.
      apply impred_isaprop. intro t. (apply (homset_property (total_category _ ))).
    + simpl.
      intros.
      apply subtypeEquality.
      { intro. apply homset_property. }
      apply (limArrowUnique LL).
      intro u.
      specialize (X u).
      apply (maponpaths pr1 X).
Defined.

End functor_algebras.


Section monad_algebras.

Context {C : category} (T : Monad C).

Let T' : C ⟶ C := T.
Let FAlg : category := total_functor_alg T'.

Definition isMonadAlg (Xa : FAlg) : UU
  := η T (pr1 Xa) · pr2 Xa = identity _
     ×
     (#T')%cat (pr2 Xa) · pr2 Xa = μ T _ · pr2 Xa.

Definition disp_cat_monad_alg_over_functor_alg : disp_cat FAlg
  := disp_full_sub _ isMonadAlg.

Definition disp_cat_monad_alg : disp_cat C
  := sigma_disp_cat disp_cat_monad_alg_over_functor_alg.

End monad_algebras.

(** * Any category is a displayed category over unit *)

Require Import UniMath.CategoryTheory.categories.StandardCategories.

Section over_terminal_category.

Variable C : category.

Definition disp_over_unit_data : disp_cat_data unit_category.
Proof.
  mkpair.
  - mkpair.
    + intro. apply (ob C).
    + simpl. intros x y c c' e. apply (C ⟦c, c'⟧).
  - mkpair.
    + simpl. intros. apply identity.
    + intros ? ? ? ? ? a b c f g.
      apply (compose (C:=C) f g ).
Defined.

Definition disp_over_unit_axioms : disp_cat_axioms _ disp_over_unit_data.
Proof.
  repeat split; cbn; intros.
  - apply id_left.
  - etrans. apply id_right.
    apply pathsinv0. unfold mor_disp. cbn.
    apply transportf_const.
  - etrans. apply assoc.
    apply pathsinv0. unfold mor_disp. cbn.
    apply transportf_const.
  - apply homset_property.
Qed.

Definition disp_over_unit : disp_cat _ := _ ,, disp_over_unit_axioms.

End over_terminal_category.

Section cartesian_product_pb.

Variable C C' : category.

(* TODO: use a better name here (this one is baffling out of context) *)
Definition disp_cartesian : disp_cat C
  := reindex_disp_cat (functor_to_unit C) (disp_over_unit C').

Definition cartesian : category := total_category disp_cartesian.

End cartesian_product_pb.

Section arrow.

Variable C : category.

Definition disp_arrow_data : disp_cat_data (cartesian C C).
Proof.
  mkpair.
  - mkpair.
    + intro H.
      exact (pr1 H --> pr2 H).
    + cbn. intros xy ab f g h.
      exact (compose f (pr2 h) = compose (pr1 h) g ).
  - split; intros.
    + cbn.
      apply pathsinv0.
      etrans. apply id_left.
      cbn in xx.
      unfold mor_disp. cbn.
      etrans. eapply pathsinv0. apply id_right.
      apply maponpaths. apply pathsinv0.
      apply transportf_const.
    + cbn in *.
      unfold mor_disp. cbn.
      etrans. apply maponpaths. apply transportf_const.
      etrans. apply assoc.
      etrans. apply maponpaths_2. apply X.
      etrans. eapply pathsinv0, assoc.
      etrans. apply maponpaths. apply X0.
      apply assoc.
Defined.

Definition disp_arrow_axioms : disp_cat_axioms _ disp_arrow_data.
Proof.
  repeat split; intros; cbn;
    try apply homset_property.
  apply isasetaprop.
  apply homset_property.
Qed.

Definition disp_arrow : disp_cat (cartesian C C) := _ ,, disp_arrow_axioms.

Definition arrow : category := total_category disp_arrow.

Definition disp_domain : disp_cat C := sigma_disp_cat disp_arrow.

Definition total_domain := total_category disp_domain.

End arrow.

Section cartesian_product.

Variables C C' : category.

Definition disp_cartesian_ob_mor : disp_cat_ob_mor C.
Proof.
  mkpair.
  - exact (λ c, C').
  - cbn. intros x y x' y' f. exact (C'⟦x', y'⟧).
Defined.

Definition disp_cartesian_data : disp_cat_data C.
Proof.
  exists disp_cartesian_ob_mor.
  mkpair; cbn.
  - intros; apply identity.
  - intros ? ? ? ? ? ? ? ? f g. apply (f · g).
Defined.

Definition disp_cartesian_axioms : disp_cat_axioms _ disp_cartesian_data.
Proof.
  repeat split; intros; cbn.
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. unfold mor_disp. cbn. apply transportf_const.
    apply idpath.
  - etrans. apply id_right.
    apply pathsinv0.
    etrans. unfold mor_disp. cbn. apply transportf_const.
    apply idpath.
  - etrans. apply assoc.
    apply pathsinv0.
    etrans. unfold mor_disp. cbn. apply transportf_const.
    apply idpath.
  - apply homset_property.
Qed.

Definition disp_cartesian' : disp_cat C := _ ,, disp_cartesian_axioms.

End cartesian_product.





(* *)