(* ******************************************************************************* *)
(** * Strict bicategories
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.TransportLaws.

Local Open Scope bicategory_scope.
Local Open Scope cat.

(** Data of strictness structure *)
Definition strictness_structure_data
           (B : bicat)
  : UU
  := (∏ (a b : B) (f : a --> b), id₁ a · f = f)
     × (∏ (a b : B) (f : a --> b), f · id₁ b = f)
     × (∏ (a b c d : B) (f : a --> b) (g : b --> c) (h : c --> d),
        f · (g · h) = f · g · h).

(** Projections *)
Definition plunitor
           {B : bicat}
           (S : strictness_structure_data B)
           {a b : B}
           (f : a --> b)
  : id₁ a · f = f
  := pr1 S _ _ f.

Definition plinvunitor
           {B : bicat}
           (S : strictness_structure_data B)
           {a b : B}
           (f : a --> b)
  : f = id₁ a · f
  := !(pr1 S _ _ f).

Definition prunitor
           {B : bicat}
           (S : strictness_structure_data B)
           {a b : B}
           (f : a --> b)
  : f · id₁ b = f
  := pr12 S _ _ f.

Definition prinvunitor
           {B : bicat}
           (S : strictness_structure_data B)
           {a b : B}
           (f : a --> b)
  : f = f · id₁ b
  := !(pr12 S _ _ f).

Definition plassociator
           {B : bicat}
           (S : strictness_structure_data B)
           {a b c d : B}
           (f : a --> b)
           (g : b --> c)
           (h : c --> d)
  : f · (g · h) = f · g · h
  := pr22 S _ _ _ _ f g h.

Definition prassociator
           {B : bicat}
           (S : strictness_structure_data B)
           {a b c d : B}
           (f : a --> b)
           (g : b --> c)
           (h : c --> d)
  : f · g · h = f · (g · h)
  := !(pr22 S _ _ _ _ f g h).

(** The requirements for the data *)
Definition strictness_structure_laws
           {B : bicat}
           (S : strictness_structure_data B)
  : UU
  := (∏ (a b : B) (f : a --> b), pr1 (idtoiso_2_1 _ _ (plunitor S f)) = lunitor f)
     × (∏ (a b : B) (f : a --> b), pr1 (idtoiso_2_1 _ _ (prunitor S f)) = runitor f)
     × (∏ (a b c d : B) (f : a --> b) (g : b --> c) (h : c --> d),
        pr1 (idtoiso_2_1 _ _ (plassociator S f g h)) = lassociator f g h).

Definition strictness_structure
           (B : bicat)
  : UU
  := ∑ (S : strictness_structure_data B), strictness_structure_laws S.

(** The laws form a proposition *)
Definition isPredicate_strictness_structure_laws
           (B : bicat)
  : isPredicate (@strictness_structure_laws B).
Proof.
  intro S.
  repeat use isapropdirprod.
  - do 3 (use impred ; intro).
    apply B.
  - do 3 (use impred ; intro).
    apply B.
  - do 7 (use impred ; intro).
    apply B.
Qed.

(** Projections *)
Coercion strictness_structure_to_data
         {B : bicat}
         (S : strictness_structure B)
  : strictness_structure_data B
  := pr1 S.

Definition idtoiso_plunitor
           {B : bicat}
           (S : strictness_structure B)
           {a b : B}
           (f : a --> b)
  : pr1 (idtoiso_2_1 _ _ (plunitor S f)) = lunitor f
  := pr12 S _ _ f.

Definition idtoiso_prunitor
           {B : bicat}
           (S : strictness_structure B)
           {a b : B}
           (f : a --> b)
  : pr1 (idtoiso_2_1 _ _ (prunitor S f)) = runitor f
  := pr122 S _ _ f.

Definition idtoiso_plassociator
           {B : bicat}
           (S : strictness_structure B)
           {a b c d : B}
           (f : a --> b)
           (g : b --> c)
           (h : c --> d)
  : pr1 (idtoiso_2_1 _ _ (plassociator S f g h)) = lassociator f g h
  := pr222 S _ _ _ _ f g h.

(** Coherent strictness structure. For these, one also needs the triangle and pentagon. *)
Definition is_coh_strictness_structure
           {B : bicat}
           (S : strictness_structure B)
  : UU
  := (∏ (a b c : B) (f : a --> b) (g : b --> c),
      maponpaths (λ z, f · z) (plunitor S g)
      =
      plassociator S _ _ _ @ maponpaths (λ z, z · g) (prunitor S f))
      ×
      ∏ (v w x y z : B)
      (f : v --> w) (g : w --> x)
      (h : x --> y) (k : y --> z),
     maponpaths (λ z, f · z) (plassociator S g h k)
     @ plassociator S f (g · h) k
     @ maponpaths (λ z, z · k) (plassociator S f g h)
     =
     plassociator S f g (h · k)
     @ plassociator S (f · g) h k.

Definition coh_strictness_structure
           (B : bicat)
  := ∑ (S : strictness_structure B), is_coh_strictness_structure S.

Coercion pr_strictness_structure
         {B : bicat}
         (S : coh_strictness_structure B)
  : strictness_structure B
  := pr1 S.

(** Being coherent is a proposition *)
Definition isPredicate_is_coh_strictness_structure
           {B : bicat}
           (HB : is_univalent_2_1 B)
  : isPredicate (@is_coh_strictness_structure B).
Proof.
  intro S.
  use isapropdirprod.
  - do 5 (use impred ; intro).
    exact (univalent_bicategory_1_cell_hlevel_3 _ HB _ _ _ _ _ _).
  - do 9 (use impred ; intro).
    exact (univalent_bicategory_1_cell_hlevel_3 _ HB _ _ _ _ _ _).
Qed.

(** Definition of 2-category *)
Definition locally_strict
           (B : bicat)
  : UU
  := ∏ (a b : B), isaset (a --> b).

Definition is_strict_bicat
           (B : bicat)
  : UU
  := locally_strict B
     ×
     coh_strictness_structure B.

Definition make_is_strict_bicat
           {B : bicat}
           (HB : locally_strict B)
           (S : strictness_structure B)
  : is_strict_bicat B.
Proof.
  use tpair.
  - exact HB.
  - repeat use tpair.
    + exact (@plunitor _ S).
    + exact (@prunitor _ S).
    + exact (@plassociator _ S).
    + exact (@idtoiso_plunitor _ S).
    + exact (@idtoiso_prunitor _ S).
    + exact (@idtoiso_plassociator _ S).
    + abstract (simpl ; intros ; apply HB).
    + abstract (simpl ; intros ; apply HB).
Defined.

Definition isPredicate_is_coh_strictness_structure_from_locally_strict
           {B : bicat}
           (HB : locally_strict B)
  : isPredicate (@is_coh_strictness_structure B).
Proof.
  intro z.
  apply invproofirrelevance.
  intros c₁ c₂.
  use pathsdirprod.
  - do 5 (use funextsec ; intro).
    apply (isasetaprop (HB _ _ _ _)).
  - do 9 (use funextsec ; intro).
    apply (isasetaprop (HB _ _ _ _)).
Qed.

Definition isaprop_is_strict_bicat
           (B : bicat)
  : isaprop (is_strict_bicat B).
Proof.
  apply invproofirrelevance.
  intros x y.
  induction x as [LSx CSx].
  induction y as [LSY CSy].
  use pathsdirprod.
  - do 2 (use funextsec ; intro).
    apply isapropisaset.
  - use subtypePath.
    { exact (isPredicate_is_coh_strictness_structure_from_locally_strict LSx). }
    use subtypePath.
    { exact (isPredicate_strictness_structure_laws B). }
    repeat use pathsdirprod.
    + repeat (use funextsec ; intro).
      apply LSx.
    + repeat (use funextsec ; intro).
      apply LSx.
    + repeat (use funextsec ; intro).
      apply LSx.
Qed.

Definition strict_bicat
  := ∑ (B : bicat), is_strict_bicat B.

Coercion bicat_of_strict_bicat
         (B : strict_bicat)
  : bicat
  := pr1 B.

(** Strict bicat to 2-cat *)
Definition strict_bicat_to_category
           (B : strict_bicat)
  : category.
Proof.
  use make_category.
  - use make_precategory.
    + use make_precategory_data.
      * use make_precategory_ob_mor.
        ** exact (ob B).
        ** exact (λ b₁ b₂, b₁ --> b₂).
      * exact (λ z, id₁ z).
      * exact (λ _ _ _ f g, f · g).
    + repeat split ; cbn.
      * exact (λ _ _ f, plunitor (pr22 B) f).
      * exact (λ _ _ f, prunitor (pr22 B) f).
      * exact (λ _ _ _ _ f g h, plassociator (pr22 B) f g h).
      * exact (λ _ _ _ _ f g h, prassociator (pr22 B) f g h).
  - exact (pr12 B).
Defined.

Definition strict_bicat_to_two_cat_data
           (B : strict_bicat)
  : two_cat_data.
Proof.
  use tpair.
  - exact (strict_bicat_to_category B).
  - use tpair.
    + exact (λ _ _ f g, f ==> g).
    + repeat split.
      * exact (λ _ _ f, id₂ f).
      * exact (λ _ _ _ _ _ α β, α • β).
      * exact (λ _ _ _ f _ _ α, f ◃ α).
      * exact (λ _ _ _ _ _ g α, α ▹ g).
Defined.

Definition strict_bicat_to_two_cat_laws
           (B : strict_bicat)
  : two_cat_laws (strict_bicat_to_two_cat_data B).
Proof.
  repeat split.
  - intros ; apply id2_left.
  - intros ; apply id2_right.
  - intros ; apply vassocr.
  - intros ; apply lwhisker_id2.
  - intros ; apply id2_rwhisker.
  - intros ; apply lwhisker_vcomp.
  - intros ; apply rwhisker_vcomp.
  - intros ; apply vcomp_whisker.
Qed.

Definition strict_bicat_to_two_cat
           (B : strict_bicat)
  : two_cat.
Proof.
  use tpair.
  - use tpair.
    + exact (strict_bicat_to_two_cat_data B).
    + exact (strict_bicat_to_two_cat_laws B).
  - intros x y f g ; simpl.
    apply (pr1 B).
Defined.

(** Univalent 2-categories *)
Definition univalent_two_cat_2cells_are_prop
           (B : strict_bicat)
           (HB : is_univalent_2_1 B)
           {a b : B}
           (f g : a --> b)
  : isaprop (invertible_2cell f g).
Proof.
  refine (isofhlevelweqf 1 (make_weq _ (HB _ _ f g)) _).
  exact (pr12 B _ _ f g).
Defined.

(** Univalent categories do not form a 2-category *)
Definition diag_set
  : HSET_univalent_category ⟶ HSET_univalent_category.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (λ X, setdirprod X X).
    + exact (λ _ _ f x, f (pr1 x) ,, f (pr2 x)).
  - split.
    + intro X.
      apply idpath.
    + intros X Y Z f g.
      apply idpath.
Defined.

Definition swap
  : nat_iso diag_set diag_set.
Proof.
  use make_nat_iso.
  - use make_nat_trans.
    + intros X x.
      exact (pr2 x ,, pr1 x).
    + intros X Y f.
      apply idpath.
  - intros X.
    use is_iso_qinv.
    + exact (λ z, pr2 z ,, pr1 z).
    + split.
      * apply idpath.
      * apply idpath.
Defined.

Definition cat_not_a_two_cat
  : ¬ (is_strict_bicat bicat_of_cats).
Proof.
  intro H.
  pose (maponpaths
          pr1
          (eqtohomot
             (nat_trans_eq_pointwise
                (maponpaths
                   (λ z, pr1 z)
                   (proofirrelevance
                      _
                      (@univalent_two_cat_2cells_are_prop
                         (bicat_of_cats ,, H)
                         univalent_cat_is_univalent_2_1
                         HSET_univalent_category
                         HSET_univalent_category
                         diag_set
                         diag_set)
                      (id2_invertible_2cell _)
                      (nat_iso_to_invertible_2cell _ _ swap)))
                boolset)
             (true ,, false)))
    as C.
  exact (nopathstruetofalse C).
Qed.

(** Local univalence gives rise to a unique strictness structure *)
Definition strictness_from_univalent_2_1
           {B : bicat}
           (HB : is_univalent_2_1 B)
  : strictness_structure B.
Proof.
  repeat use tpair.
  - refine (λ _ _ f, isotoid_2_1 HB (lunitor f ,, _)).
    is_iso.
  - refine (λ _ _ f, isotoid_2_1 HB (runitor f ,, _)).
    is_iso.
  - refine (λ _ _ _ _ f g h, isotoid_2_1 HB (lassociator f g h ,, _)).
    is_iso.
  - abstract
      (cbn ; intros ;
       rewrite idtoiso_2_1_isotoid_2_1 ;
       apply idpath).
  - abstract
      (cbn ; intros ;
       rewrite idtoiso_2_1_isotoid_2_1 ;
       apply idpath).
  - abstract
      (cbn ; intros ;
       rewrite idtoiso_2_1_isotoid_2_1 ;
       apply idpath).
Defined.

Definition is_coh_strictness_from_univalent_2_1
           {B : bicat}
           (HB : is_univalent_2_1 B)
  : is_coh_strictness_structure (strictness_from_univalent_2_1 HB).
Proof.
  split.
  - intros a b c f g ; cbn.
    rewrite isotoid_2_1_lwhisker.
    rewrite isotoid_2_1_rwhisker.
    rewrite isotoid_2_1_vcomp.
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_invertible_2cell. }
    simpl.
    refine (!_).
    apply runitor_rwhisker.
  - intros v w x y z f g h k ; cbn.
    rewrite isotoid_2_1_lwhisker.
    rewrite isotoid_2_1_rwhisker.
    rewrite !isotoid_2_1_vcomp.
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_invertible_2cell. }
    simpl.
    rewrite vassocr.
    apply lassociator_lassociator.
Qed.

Definition coh_strictness_from_univalent_2_1
           (B : bicat)
           (HB : is_univalent_2_1 B)
  : coh_strictness_structure B.
Proof.
  use tpair.
  - exact (strictness_from_univalent_2_1 HB).
  - exact (is_coh_strictness_from_univalent_2_1 HB).
Defined.

Definition isaprop_coh_strictness_from_univalence_2_1
           (B : bicat)
           (HB : is_univalent_2_1 B)
  : isaprop (coh_strictness_structure B).
Proof.
  apply invproofirrelevance.
  intros S₁ S₂.
  use subtypePath.
  { exact (isPredicate_is_coh_strictness_structure HB). }
  use subtypePath.
  { exact (isPredicate_strictness_structure_laws B). }
  repeat use pathsdirprod.
  - use funextsec ; intro a.
    use funextsec ; intro b.
    use funextsec ; intro f.
    refine (_ @ isotoid_2_1_idtoiso_2_1 HB (plunitor S₂ f)).
    refine (!(isotoid_2_1_idtoiso_2_1 HB (plunitor S₁ f)) @ _).
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_invertible_2cell. }
    rewrite !idtoiso_plunitor.
    apply idpath.
  - use funextsec ; intro a.
    use funextsec ; intro b.
    use funextsec ; intro f.
    refine (_ @ isotoid_2_1_idtoiso_2_1 HB (prunitor S₂ f)).
    refine (!(isotoid_2_1_idtoiso_2_1 HB (prunitor S₁ f)) @ _).
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_invertible_2cell. }
    rewrite !idtoiso_prunitor.
    apply idpath.
  - use funextsec ; intro a.
    use funextsec ; intro b.
    use funextsec ; intro c.
    use funextsec ; intro d.
    use funextsec ; intro f.
    use funextsec ; intro g.
    use funextsec ; intro h.
    refine (_ @ isotoid_2_1_idtoiso_2_1 HB (plassociator S₂ f g h)).
    refine (!(isotoid_2_1_idtoiso_2_1 HB (plassociator S₁ f g h)) @ _).
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_invertible_2cell. }
    rewrite !idtoiso_plassociator.
    apply idpath.
Qed.

Definition unique_strictness_structure_is_univalent_2_1
           (B : bicat)
           (HB : is_univalent_2_1 B)
  : iscontr (coh_strictness_structure B).
Proof.
  use tpair.
  - exact (coh_strictness_from_univalent_2_1 B HB).
  - intro.
    apply isaprop_coh_strictness_from_univalence_2_1.
    exact HB.
Qed.
