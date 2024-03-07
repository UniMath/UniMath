
(** * Examples

A typical use for displayed categories is for constructing categories of structured objects, over a given (specific or general) category. We give a few examples here:

- category of topological space as total category
- arrow precategories
- objects with N-actions
- elements, over hSet

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.

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
#[reversible=no] Coercion grp_data {X} (G : grp_structure X) : grp_structure_data X := pr1 G.
#[reversible=no] Coercion grp_axioms {X} (G : grp_structure X) : grp_structure_axioms _ := pr2 G.

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

Definition arrow_disp_ob_mor : disp_cat_ob_mor (category_binproduct C C).
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

Lemma arrow_axioms : disp_cat_axioms (category_binproduct C C) arrow_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property.
Qed.

Definition arrow_disp : disp_cat (category_binproduct C C)
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

Definition elements_ob_mor : disp_cat_ob_mor HSET.
Proof.
  use tpair.
  - simpl. exact (λ X, X).
  - simpl. intros X Y x y f. exact (f x = y).
Defined.

Lemma elements_id_comp : disp_cat_id_comp HSET elements_ob_mor.
Proof.
  apply tpair; simpl.
  - intros X x. apply idpath.
  - intros X Y Z f g x y z e_fx_y e_gy_z. cbn.
    eapply pathscomp0. apply maponpaths, e_fx_y. apply e_gy_z.
Qed.

Definition elements_data : disp_cat_data HSET
  := (_ ,, elements_id_comp).

Lemma elements_axioms : disp_cat_axioms HSET elements_data.
Proof.
  repeat split; intros; try apply setproperty.
  apply isasetaprop; apply setproperty.
Qed.

Definition elements_universal : disp_cat HSET
  := (_ ,, elements_axioms).

Definition disp_cat_of_elements {C : category} (P : functor C HSET)
  := reindex_disp_cat P elements_universal.

Definition elements_universal_mor_eq
           {X Y : HSET}
           {f : X --> Y}
           {x : elements_universal X}
           {y : elements_universal Y}
           (ff₁ ff₂ : x -->[ f ] y)
  : ff₁ = ff₂.
Proof.
  apply Y.
Qed.

Definition is_z_iso_disp_elements_universal
           {X Y : HSET}
           {f : X --> Y}
           (Hf : is_z_isomorphism f)
           {x : elements_universal X}
           {y : elements_universal Y}
           (ff : x -->[ f ] y)
  : is_z_iso_disp (make_z_iso' _ Hf) ff.
Proof.
  simple refine (_ ,, _ ,, _).
  - pose (eqtohomot (z_iso_inv_after_z_iso (make_z_iso' f Hf)) x) as p.
    cbn in *.
    refine (_ @ p).
    apply maponpaths.
    exact (!ff).
  - apply elements_universal_mor_eq.
  - apply elements_universal_mor_eq.
Qed.

Definition is_opcartesian_disp_elements_universal
           {X Y : HSET}
           {f : X --> Y}
           {x : elements_universal X}
           {y : elements_universal Y}
           (p : x -->[ f ] y)
  : is_opcartesian p.
Proof.
  intros Z z g q.
  use iscontraprop1.
  - use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply elements_universal.
    }
    apply elements_universal_mor_eq.
  - simple refine (_ ,, _).
    + exact (maponpaths g (!p) @ q).
    + apply elements_universal_mor_eq.
Qed.

Definition opcleaving_elements_universal
  : opcleaving elements_universal.
Proof.
  intros X Y x f.
  simple refine (_ ,, _).
  - exact (f x).
  - refine (idpath _ ,, _) ; cbn.
    apply is_opcartesian_disp_elements_universal.
Defined.

(* TODO: compare to other definitions of this in the library! *)
Definition precat_of_elements {C : category} (P : functor C HSET)
  := total_category (disp_cat_of_elements P).

End Elements_Disp.


Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.


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
  use tpair.
  - exact (compose (compose (functor_on_z_iso F i) d) (z_iso_inv_from_z_iso i)).
  - cbn. unfold z_iso_disp. cbn.
    use tpair.
    + abstract (
          etrans; [eapply pathsinv0; apply id_right |];
          repeat rewrite <- assoc;
          do 2 apply maponpaths;
          apply pathsinv0; apply z_iso_after_z_iso_inv
        ).
    + use tpair.
      * unfold functor_alg_mor.
        cbn. repeat rewrite assoc.
        unfold functor_alg_mor. cbn.
        rewrite <- functor_comp.
        rewrite z_iso_after_z_iso_inv.
        rewrite functor_id.
        rewrite id_left. apply idpath.
      * split; apply homset_property.
Defined.


Local Notation "'π'" := (pr1_category disp_cat_functor_alg).

Definition creates_limits_functor_alg
  : creates_limits_unique disp_cat_functor_alg.
Proof.
  unfold creates_limits_unique.
  intros J D L.
  induction L as [tmp isL].
  induction tmp as [x L].
  unfold creates_limit. cbn.
  transparent assert (FC : (cone (mapdiagram π D) (F x))).
  { use make_cone.
    - intro j.
      eapply compose.
      apply ((#F)%cat (coneOut L j )).
      cbn. exact (pr2 (dob D j)).
    - abstract (
      red; intros; cbn;
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
  { use make_LimCone. apply x. apply L. apply isL. }
  use tpair.
  - use tpair.
    + use tpair.
      * use (limArrow LL). apply FC.
      * abstract (
          use tpair ;
          [
            intro j; cbn;
            set (XR := limArrowCommutes LL _ FC); cbn in XR;
            apply pathsinv0; apply XR
          | cbn; intros i j e;
            apply subtypePath;
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
    + use tpair.
      * cbn.
        use (limArrow LL _ πCC).
      * set (XR := limArrowCommutes LL).
        cbn in XR.
        set (H1:= coneOutCommutes CC). simpl in H1.
        destruct x' as [c a]. cbn.
        unfold disp_cat_functor_alg in a. cbn in a.
        cbn in πCC.
        transparent assert (X : (cone (mapdiagram π D) (F c))).
        { use make_cone.
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
          intermediate_path (limArrow LL _ X).
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
      apply subtypePath.
      { intro. apply homset_property. }
      cbn. apply (limArrowCommutes LL).
    + intros.
      apply impred_isaprop. intro t. (apply (homset_property (total_category _ ))).
    + simpl.
      intros.
      apply subtypePath.
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

(* *)
