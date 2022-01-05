(********************************************************

 Internal Street fibrations

 In this file, we define the notion of Street fibration
 internal to a bicategory.

 1. Definition of an internal Street fibration
 2. Lemmas on cartesians
 3. Street fibrations in locally groupoidal bicategories
 4. The identity Street fibration
 5. Projection Street fibration
 6. Composition of Street fibrations
 7. Pullbacks of Street fibrations
 8. Internal Street fibrations of categories
 9. Morphisms of internal Street fibrations
 10. Cells of internal Street fibrations
 11. Equivalences preserve cartesian cells

 ********************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Colimits.Products.
Import Products.Notations.

Local Open Scope cat.

(**
1. Definition of an internal Street fibration

We define internal Street fibrations using an unfolded definition.
We also show that it is equivalent to the usual definition of internal Street
fibrations, which is formulated using hom-categories.
 *)
Section InternalStreetFibration.
  Context {B : bicat}
          {e b : B}
          (p : e --> b).

  Definition is_cartesian_2cell_sfib
             {x : B}
             {f g : x --> e}
             (γ : f ==> g)
    : UU
    := ∏ (h : x --> e)
         (α : h ==> g)
         (δp : h · p ==> f · p)
         (q : α ▹ p = δp • (γ ▹ p)),
       ∃! (δ : h ==> f),
       δ ▹ p = δp
       ×
       δ • γ = α.

  Definition is_cartesian_2cell_sfib_factor
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_cartesian_2cell_sfib γ)
             {h : x --> e}
             (α : h ==> g)
             (δp : h · p ==> f · p)
             (q : α ▹ p = δp • (γ ▹ p))
    : h ==> f
    := pr11 (Hγ h α δp q).

  Definition is_cartesian_2cell_sfib_factor_over
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_cartesian_2cell_sfib γ)
             {h : x --> e}
             {α : h ==> g}
             {δp : h · p ==> f · p}
             (q : α ▹ p = δp • (γ ▹ p))
    : (is_cartesian_2cell_sfib_factor Hγ _ _ q) ▹ p = δp
    := pr121 (Hγ h α δp q).

  Definition is_cartesian_2cell_sfib_factor_comm
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_cartesian_2cell_sfib γ)
             {h : x --> e}
             {α : h ==> g}
             {δp : h · p ==> f · p}
             (q : α ▹ p = δp • (γ ▹ p))
    : is_cartesian_2cell_sfib_factor Hγ _ _ q • γ = α
    := pr221 (Hγ h α δp q).

  Definition is_cartesian_2cell_sfib_factor_unique
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_cartesian_2cell_sfib γ)
             (h : x --> e)
             (α : h ==> g)
             (δp : h · p ==> f · p)
             (q : α ▹ p = δp • (γ ▹ p))
             (δ₁ δ₂ : h ==> f)
             (pδ₁ : δ₁ ▹ p = δp)
             (pδ₂ : δ₂ ▹ p = δp)
             (δγ₁ : δ₁ • γ = α)
             (δγ₂ : δ₂ • γ = α)
    : δ₁ = δ₂.
  Proof.
    pose (proofirrelevance
            _
            (isapropifcontr (Hγ h α δp q))
            (δ₁ ,, pδ₁ ,, δγ₁)
            (δ₂ ,, pδ₂ ,, δγ₂))
      as H.
    exact (maponpaths pr1 H).
  Qed.

  Definition isaprop_is_cartesian_2cell_sfib
             {x : B}
             {f : x --> e}
             {g : x --> e}
             (γ : f ==> g)
    : isaprop (is_cartesian_2cell_sfib γ).
  Proof.
    do 4 (use impred ; intro).
    apply isapropiscontr.
  Qed.

  Definition internal_sfib_cleaving
    : UU
    := ∏ (x : B)
         (f : x --> b)
         (g : x --> e)
         (α : f ==> g · p),
       ∑ (h : x --> e)
         (γ : h ==> g)
         (β : invertible_2cell (h · p) f),
       is_cartesian_2cell_sfib γ
       ×
       γ ▹ p = β • α.

  Definition internal_sfib_cleaving_lift_mor
             (H : internal_sfib_cleaving)
             {x : B}
             {f : x --> b}
             {g : x --> e}
             (α : f ==> g · p)
    : x --> e
    := pr1 (H _ _ _ α).

  Definition internal_sfib_cleaving_lift_cell
             (H : internal_sfib_cleaving)
             {x : B}
             {f : x --> b}
             {g : x --> e}
             (α : f ==> g · p)
    : internal_sfib_cleaving_lift_mor H α ==> g
    := pr12 (H _ _ _ α).

  Definition internal_sfib_cleaving_com
             (H : internal_sfib_cleaving)
             {x : B}
             {f : x --> b}
             {g : x --> e}
             (α : f ==> g · p)
    : invertible_2cell (internal_sfib_cleaving_lift_mor H α · p) f
    := pr122 (H _ _ _ α).

  Definition internal_sfib_cleaving_is_cartesian
             (H : internal_sfib_cleaving)
             {x : B}
             {f : x --> b}
             {g : x --> e}
             (α : f ==> g · p)
    : is_cartesian_2cell_sfib (internal_sfib_cleaving_lift_cell H α)
    := pr1 (pr222 (H _ _ _ α)).

  Definition internal_sfib_cleaving_over
             (H : internal_sfib_cleaving)
             {x : B}
             {f : x --> b}
             {g : x --> e}
             (α : f ==> g · p)
    : internal_sfib_cleaving_lift_cell H α ▹ p
      =
      internal_sfib_cleaving_com H α • α
    := pr2 (pr222 (H _ _ _ α)).

  Definition lwhisker_is_cartesian
    : UU
    := ∏ (x y : B)
         (h : y --> x)
         (f g : x --> e)
         (γ : f ==> g)
         (Hγ : is_cartesian_2cell_sfib γ),
       is_cartesian_2cell_sfib (h ◃ γ).

  Definition internal_sfib
    : UU
    := internal_sfib_cleaving × lwhisker_is_cartesian.

  Coercion internal_sfib_to_cleaving
           (H : internal_sfib)
    : internal_sfib_cleaving
    := pr1 H.

  Definition rep_internal_sfib
    : UU
    := (∏ (x : B),
        street_fib (post_comp x p))
       ×
       (∏ (x y : B)
          (h : y --> x),
        preserves_cartesian
          (post_comp x p)
          (post_comp y p)
          (pre_comp e h)).

  Definition rep_internal_sfib_to_internal_sfib
             (H : rep_internal_sfib)
    : internal_sfib.
  Proof.
    split.
    - intros x f g α.
      pose (lift := pr1 H x g f α).
      exact (pr1 lift
             ,, pr112 lift
             ,, iso_to_inv2cell _ _ (pr212 lift)
             ,, pr222 lift
             ,, pr122 lift).
    - exact (pr2 H).
  Defined.

  Definition internal_sfib_to_rep_internal_sfib
             (H : internal_sfib)
    : rep_internal_sfib.
  Proof.
    split.
    - intros x f g α.
      pose (lift := pr1 H x g f α).
      exact (pr1 lift
             ,, (pr12 lift ,, inv2cell_to_iso _ _ (pr122 lift))
             ,, pr2 (pr222 lift)
             ,, pr1 (pr222 lift)).
    - exact (pr2 H).
  Defined.

  Definition internal_sfib_to_rep_to_sfib
             (H : rep_internal_sfib)
    : internal_sfib_to_rep_internal_sfib
        (rep_internal_sfib_to_internal_sfib H)
      =
      H.
  Proof.
    use pathsdirprod ; [ | apply idpath ].
    use funextsec ; intro x.
    use funextsec ; intro f.
    use funextsec ; intro g.
    use funextsec ; intro α.
    simpl.
    refine (maponpaths (λ z, _ ,, z) _).
    use subtypePath.
    {
      intro.
      use isapropdirprod.
      - apply cellset_property.
      - apply isaprop_is_cartesian_2cell_sfib.
    }
    simpl.
    refine (maponpaths (λ z, _ ,, z) _).
    use subtypePath.
    {
      intro ; apply isaprop_is_iso.
    }
    cbn.
    apply idpath.
  Qed.

  Definition rep_sfib_to_internal_to_rep
             (H : internal_sfib)
    : rep_internal_sfib_to_internal_sfib
        (internal_sfib_to_rep_internal_sfib H)
      =
      H.
  Proof.
    use pathsdirprod ; [ | apply idpath ].
    use funextsec ; intro x.
    use funextsec ; intro f.
    use funextsec ; intro g.
    use funextsec ; intro α.
    simpl.
    refine (maponpaths (λ z, _ ,, _ ,, z) _).
    use subtypePath.
    {
      intro.
      apply isapropdirprod.
      - apply isaprop_is_cartesian_2cell_sfib.
      - apply cellset_property.
    }
    use subtypePath.
    {
      intro ; apply isaprop_is_invertible_2cell.
    }
    cbn.
    apply idpath.
  Qed.

  Definition rep_internal_sfib_weq_internal_sfib
    : rep_internal_sfib ≃ internal_sfib.
  Proof.
    use make_weq.
    - exact rep_internal_sfib_to_internal_sfib.
    - use gradth.
      + exact internal_sfib_to_rep_internal_sfib.
      + exact internal_sfib_to_rep_to_sfib.
      + exact rep_sfib_to_internal_to_rep.
  Defined.

  Definition isaprop_rep_internal_sfib
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop rep_internal_sfib.
  Proof.
    use isapropdirprod.
    - use impred ; intro.
      apply isaprop_street_fib.
      apply is_univ_hom.
      exact HB_2_1.
    - do 7 (use impred ; intro).
      apply isaprop_is_cartesian_sfib.
  Qed.

  Definition isaprop_internal_sfib
             (HB_2_1 : is_univalent_2_1 B)
    : isaprop internal_sfib.
  Proof.
    use (isofhlevelweqf _ rep_internal_sfib_weq_internal_sfib).
    exact (isaprop_rep_internal_sfib HB_2_1).
  Qed.
End InternalStreetFibration.

(**
2. Lemmas on cartesians
 *)
Definition id_is_cartesian_2cell_sfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           (f : x --> e)
  : is_cartesian_2cell_sfib p (id2 f).
Proof.
  intros g α δp q.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ;
       [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
       exact (!(id2_right _) @ pr22 φ₁ @ !(pr22 φ₂) @ id2_right _)).
  - refine (α ,, _ ,, _).
    + abstract
        (rewrite q ;
         rewrite id2_rwhisker ;
         apply id2_right).
    + abstract
        (apply id2_right).
Defined.

Section VcompIsCartesian.
  Context {B : bicat}
          {e b : B}
          (p : e --> b)
          {x : B}
          {f g h : x --> e}
          {α : f ==> g}
          {β : g ==> h}
          (Hα : is_cartesian_2cell_sfib p α)
          (Hβ : is_cartesian_2cell_sfib p β).

  Definition vcomp_is_cartesian_2cell_sfib_unique
             {k : x --> e}
             {ζ : k ==> h}
             {δp : k · p ==> f · p}
             (q : ζ ▹ p = δp • ((α • β) ▹ p))
    : isaprop (∑ δ : k ==> f, δ ▹ p = δp × δ • (α • β) = ζ).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
    rewrite <- rwhisker_vcomp in q.
    rewrite !vassocr in q.
    use (is_cartesian_2cell_sfib_factor_unique
           _
           Hα
           _
           (is_cartesian_2cell_sfib_factor _ Hβ ζ (δp • (α ▹ _)) q)
           δp
           (is_cartesian_2cell_sfib_factor_over _ _ _)
           _ _
           (pr12 φ₁)
           (pr12 φ₂)) ;
    use (is_cartesian_2cell_sfib_factor_unique
           _
           Hβ
           _
           ζ
           (δp • (α ▹ _))
           q
           _
           _
           _
           (is_cartesian_2cell_sfib_factor_over _ _ _)
           _
           (is_cartesian_2cell_sfib_factor_comm _ _ _)).
    - rewrite <- rwhisker_vcomp.
      rewrite (pr12 φ₁).
      apply idpath.
    - rewrite !vassocl.
      apply (pr22 φ₁).
    - rewrite <- rwhisker_vcomp.
      rewrite (pr12 φ₂).
      apply idpath.
    - rewrite !vassocl.
      apply (pr22 φ₂).
  Qed.

  Definition vcomp_is_cartesian_2cell_sfib
    : is_cartesian_2cell_sfib p (α • β).
  Proof.
    intros k ζ δp q.
    use iscontraprop1.
    - apply vcomp_is_cartesian_2cell_sfib_unique.
      exact q.
    - simple refine (_ ,, _ ,, _).
      + simple refine (is_cartesian_2cell_sfib_factor _ Hα _ δp _).
        * simple refine (is_cartesian_2cell_sfib_factor _ Hβ ζ (δp • (α ▹ p)) _).
          abstract
            (rewrite !vassocl ;
             rewrite q ;
             rewrite <- rwhisker_vcomp ;
             apply idpath).
        * apply is_cartesian_2cell_sfib_factor_over.
      + apply is_cartesian_2cell_sfib_factor_over.
      + abstract
          (simpl ;
           rewrite !vassocr ;
           rewrite !is_cartesian_2cell_sfib_factor_comm ;
           apply idpath).
  Defined.
End VcompIsCartesian.

Definition invertible_is_cartesian_2cell_sfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g : x --> e}
           (α : f ==> g)
           (Hα : is_invertible_2cell α)
  : is_cartesian_2cell_sfib p α.
Proof.
  intros h ζ δp q.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ;
         [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
       refine (!(id2_right _) @ _ @ id2_right _) ;
       rewrite <- (vcomp_rinv Hα) ;
       rewrite !vassocr ;
       rewrite (pr22 φ₁), (pr22 φ₂) ;
       apply idpath).
  - refine (ζ • Hα^-1 ,, _ ,, _).
    + abstract
        (rewrite <- rwhisker_vcomp ;
         use vcomp_move_R_Mp ; [ is_iso | ] ;
         cbn ;
         exact q).
    + abstract
        (rewrite !vassocl ;
         rewrite vcomp_linv ;
         apply id2_right).
Defined.

(**
3. Street fibrations in locally groupoidal bicategories
 *)
Definition locally_grpd_cartesian
           {B : bicat}
           (HB : locally_groupoid B)
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g : x --> e}
           (γ : f ==> g)
  : is_cartesian_2cell_sfib p γ.
Proof.
  intros h α δp q.
  pose (α_iso := make_invertible_2cell (HB _ _ _ _ α)).
  pose (γ_iso := make_invertible_2cell (HB _ _ _ _ γ)).
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ;
       [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
       use (vcomp_rcancel _ γ_iso) ;
       cbn ;
       exact (pr22 φ₁ @ !(pr22 φ₂))).
  - refine (α • γ_iso^-1 ,, _ ,, _).
    + abstract
        (rewrite <- rwhisker_vcomp ;
         use vcomp_move_R_Mp ; [ is_iso | ] ;
         cbn ;
         rewrite q ;
         apply idpath).
    + abstract
        (rewrite !vassocl ;
         rewrite vcomp_linv ;
         apply id2_right).
Defined.

Definition locally_grpd_internal_sfib
           {B : bicat}
           (HB : locally_groupoid B)
           {e b : B}
           (p : e --> b)
  : internal_sfib p.
Proof.
  split.
  - intros x f g α.
    refine (g
            ,,
            id2 _
            ,,
            inv_of_invertible_2cell (make_invertible_2cell (HB _ _ _ _ α))
            ,,
            locally_grpd_cartesian HB _ _
            ,,
            _).
    abstract
      (cbn ;
       rewrite id2_rwhisker ;
       rewrite vcomp_linv ;
       apply idpath).
  - intro ; intros.
    apply (locally_grpd_cartesian HB).
Defined.

(**
4. The identity Street fibration
 *)
Section IdentityInternalSFib.
  Context {B : bicat}
          (b : B).

  Local Lemma identity_help
        {x : B}
        {f h : x --> b}
        (δp : h · id₁ b ==> f · id₁ b)
    : ((rinvunitor h • δp) • runitor f) ▹ id₁ b = δp.
  Proof.
    rewrite !vassocl.
    rewrite <- rwhisker_vcomp.
    use vcomp_move_R_pM ; [ is_iso | ].
    cbn.
    use (vcomp_rcancel (runitor _)) ; [ is_iso | ].
    rewrite !vassocl.
    rewrite !vcomp_runitor.
    rewrite !vassocr.
    do 2 apply maponpaths_2.
    rewrite <- runitor_triangle.
    use vcomp_move_R_pM ; [ is_iso | ].
    cbn.
    rewrite runitor_rwhisker.
    rewrite runitor_lunitor_identity.
    apply idpath.
  Qed.

  Definition identity_lift
             {x : B}
             {f g : x --> b}
             (α : f ==> g · id₁ b)
    : is_cartesian_2cell_sfib (id₁ b) (α • runitor g).
  Proof.
    intros h β δp q.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use id1_faithful ;
         exact (pr12 φ₁ @ !(pr12 φ₂))).
    - refine (rinvunitor _ • δp • runitor _ ,, _ ,, _).
      + apply identity_help.
      + abstract
          (rewrite !vassocl ;
           etrans ;
           [ do 2 apply maponpaths ;
             rewrite !vassocr ;
             rewrite <- vcomp_runitor ;
             rewrite !vassocl ;
             rewrite <- vcomp_runitor ;
             rewrite !vassocr ;
             rewrite rwhisker_vcomp ;
             apply idpath
           | ] ;
           etrans ;
           [ apply maponpaths ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             exact (!q)
           | ] ;
           rewrite vcomp_runitor ;
           rewrite !vassocr ;
           rewrite rinvunitor_runitor ;
           apply id2_left).
  Defined.

  Definition identity_internal_cleaving
    : internal_sfib_cleaving (id₁ b).
  Proof.
    intros x f g α.
    refine (f
            ,,
            α • runitor _
            ,,
            runitor_invertible_2cell _
            ,,
            _
            ,,
            _) ; cbn.
    - apply identity_lift.
    - abstract
        (rewrite <- vcomp_runitor ;
         rewrite <- rwhisker_vcomp ;
         apply maponpaths ;
         rewrite <- runitor_triangle ;
         use vcomp_move_L_pM ; [ is_iso | ] ;
         cbn ;
         rewrite runitor_rwhisker ;
         rewrite lunitor_runitor_identity ;
         apply idpath).
  Defined.

  Definition identity_lwhisker_cartesian
    : lwhisker_is_cartesian (id₁ b).
  Proof.
    intros x y h f g γ Hγ k α δp q.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use id1_faithful ;
         exact (pr12 φ₁ @ !(pr12 φ₂))).
    - refine (rinvunitor _ • δp • runitor _ ,, _ ,, _).
      + apply identity_help.
      + abstract
          (rewrite !vassocl ;
           rewrite <- vcomp_runitor ;
           etrans ;
           [ apply maponpaths ;
             rewrite !vassocr ;
             rewrite <- q ;
             apply vcomp_runitor
           | ] ;
           rewrite !vassocr ;
           rewrite rinvunitor_runitor ;
           apply id2_left).
  Defined.

  Definition identity_internal_sfib
    : internal_sfib (id₁ b).
  Proof.
    split.
    - exact identity_internal_cleaving.
    - exact identity_lwhisker_cartesian.
  Defined.
End IdentityInternalSFib.

(**
5. Projection Street fibration
 *)
Section ProjectionSFib.
  Context {B : bicat_with_binprod}
          (b₁ b₂ : B).

  Section InvertibleToCartesian.
    Context {a : B}
            {f g : a --> b₁ ⊗ b₂}
            (α : f ==> g)
            (Hα : is_invertible_2cell (α ▹ π₂)).

    Definition invertible_to_cartesian_unique
               (h : a --> b₁ ⊗ b₂)
               (β : h ==> g)
               (δp : h · π₁ ==> f · π₁)
               (q : β ▹ π₁ = δp • (α ▹ π₁))
      : isaprop (∑ (δ : h ==> f), δ ▹ π₁ = δp × δ • α = β).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
      use binprod_ump_2cell_unique_alt.
      - apply (pr2 B).
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - use (vcomp_rcancel _ Hα).
        rewrite !rwhisker_vcomp.
        apply maponpaths.
        exact (pr22 φ₁ @ !(pr22 φ₂)).
    Qed.

    Definition invertible_to_cartesian
      : is_cartesian_2cell_sfib π₁ α.
    Proof.
      intros h β δp q.
      use iscontraprop1.
      - exact (invertible_to_cartesian_unique h β δp q).
      - simple refine (_ ,, _ ,, _).
        + use binprod_ump_2cell.
          * apply (pr2 B).
          * exact δp.
          * exact (β ▹ _ • Hα^-1).
        + apply binprod_ump_2cell_pr1.
        + use binprod_ump_2cell_unique_alt.
          * apply (pr2 B).
          * abstract
              (rewrite <- !rwhisker_vcomp ;
               rewrite binprod_ump_2cell_pr1 ;
               exact (!q)).
          * abstract
              (rewrite <- !rwhisker_vcomp ;
               rewrite binprod_ump_2cell_pr2 ;
               rewrite !vassocl ;
               refine (_ @ id2_right _) ;
               rewrite vcomp_linv ;
               apply idpath).
    Defined.
  End InvertibleToCartesian.

  Section CartesianToInvertible.
    Context {a : B}
            {f g : a --> b₁ ⊗ b₂}
            (α : f ==> g)
            (Hα : is_cartesian_2cell_sfib π₁ α).

    Let h : a --> b₁ ⊗ b₂ := ⟨ f · π₁, g · π₂ ⟩.
    Let δ : h ==> g
      := binprod_ump_2cell
           (pr2 (pr2 B _ _))
           (binprod_ump_1cell_pr1 _ _ _ _ • (α ▹ _))
           (binprod_ump_1cell_pr2 _ _ _ _).
    Let hπ₁ : h · π₁ ==> f · π₁ := binprod_ump_1cell_pr1 _ _ _ _.

    Local Lemma cartesian_to_invertible_eq
      : δ ▹ π₁ = hπ₁ • (α ▹ π₁).
    Proof.
      apply binprod_ump_2cell_pr1.
    Qed.

    Let lift : ∃! δ0 : h ==> f, δ0 ▹ π₁ = hπ₁ × δ0 • α = δ
      := Hα h δ hπ₁ cartesian_to_invertible_eq.
    Let lift_map : h ==> f := pr11 lift.
    Let inv : g · π₂ ==> f · π₂
      := (binprod_ump_1cell_pr2 _ _ _ _)^-1 • (lift_map ▹ π₂).

    Let ζ : f ==> f
      := binprod_ump_2cell
           (pr2 (pr2 B _ _))
           (id2 _)
           ((α ▹ π₂) • inv).

    Local Lemma cartesian_to_invertible_map_inv_help
      : ζ = id₂ f.
    Proof.
      refine (maponpaths
                (λ z, pr1 z)
                (proofirrelevance
                   _
                   (isapropifcontr (Hα f α (id2 _) (!(id2_left _))))
                   (ζ ,, _ ,, _)
                   (id₂ _ ,, _ ,, _))).
      - apply binprod_ump_2cell_pr1.
      - use binprod_ump_2cell_unique_alt.
        + apply (pr2 B).
        + rewrite <- rwhisker_vcomp.
          unfold ζ.
          rewrite binprod_ump_2cell_pr1.
          apply id2_left.
        + unfold ζ, inv.
          rewrite <- rwhisker_vcomp.
          rewrite binprod_ump_2cell_pr2.
          rewrite !vassocl.
          rewrite rwhisker_vcomp.
          etrans.
          {
            do 3 apply maponpaths.
            apply (pr221 lift).
          }
          unfold δ.
          rewrite binprod_ump_2cell_pr2.
          rewrite vcomp_linv.
          apply id2_right.
      - apply id2_rwhisker.
      - apply id2_left.
    Qed.

    Local Lemma cartesian_to_invertible_map_inv
      : (α ▹ π₂) • inv = id₂ (f · π₂).
    Proof.
      refine (_ @ maponpaths (λ z, z ▹ π₂) cartesian_to_invertible_map_inv_help @ _).
      - unfold ζ.
        refine (!_).
        apply binprod_ump_2cell_pr2.
      - apply id2_rwhisker.
    Qed.

    Local Lemma cartesian_to_invertible_inv_map
      : inv • (α ▹ π₂) = id₂ (g · π₂).
    Proof.
      unfold inv.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      etrans.
      {
        do 2 apply maponpaths.
        exact (pr221 lift).
      }
      unfold δ.
      etrans.
      {
        apply maponpaths.
        apply binprod_ump_2cell_pr2.
      }
      apply vcomp_linv.
    Qed.

    Definition cartesian_to_invertible
      : is_invertible_2cell (α ▹ π₂).
    Proof.
      unfold is_cartesian_2cell_sfib in Hα.
      use make_is_invertible_2cell.
      - exact inv.
      - exact cartesian_to_invertible_map_inv.
      - exact cartesian_to_invertible_inv_map.
    Defined.
  End CartesianToInvertible.

  Definition pr1_internal_cleaving
    : internal_sfib_cleaving (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    intros a f g α.
    simple refine (⟨ f , g · π₂ ⟩
                     ,, ⟪ α , id2 _ ⟫ • prod_1cell_eta _ g
                     ,, prod_1cell_pr1 _ f _
                     ,, _
                     ,, _) ; simpl.
    - apply invertible_to_cartesian.
      rewrite <- rwhisker_vcomp.
      use is_invertible_2cell_vcomp.
      + rewrite prod_2cell_pr2.
        is_iso.
        apply prod_1cell_pr2.
      + is_iso.
        apply prod_1cell_eta.
    - abstract
        (unfold prod_1cell_eta_map ;
         rewrite <- !rwhisker_vcomp ;
         etrans ;
         [ apply maponpaths ;
           apply binprod_ump_2cell_pr1
         | ] ;
         rewrite prod_2cell_pr1 ;
         rewrite !vassocl ;
         rewrite vcomp_linv ;
         rewrite id2_right ;
         apply idpath).
  Defined.

  Definition pr1_lwhisker_is_cartesian
    : lwhisker_is_cartesian (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    intros x y h f g γ Hγ.
    apply invertible_to_cartesian.
    pose (cartesian_to_invertible _ Hγ) as i.
    use make_is_invertible_2cell.
    - exact (rassociator _ _ _ • (h ◃ i^-1) • lassociator _ _ _).
    - rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      refine (_ @ rassociator_lassociator _ _ _).
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_left.
    - rewrite !vassocl.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      refine (_ @ rassociator_lassociator _ _ _).
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      apply id2_right.
  Qed.

  Definition pr1_internal_sfib
    : internal_sfib (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    split.
    - exact pr1_internal_cleaving.
    - exact pr1_lwhisker_is_cartesian.
  Defined.
End ProjectionSFib.

(**
 9. Morphisms of internal Street fibrations
 *)
Definition mor_preserves_cartesian
           {B : bicat}
           {e₁ b₁ : B}
           (p₁ : e₁ --> b₁)
           {e₂ b₂ : B}
           (p₂ : e₂ --> b₂)
           (fe : e₁ --> e₂)
  : UU
  := ∏ (x : B)
       (f g : x --> e₁)
       (γ : f ==> g)
       (Hγ : is_cartesian_2cell_sfib p₁ γ),
     is_cartesian_2cell_sfib p₂ (γ ▹ fe).

Definition id_mor_preserves_cartesian
           {B : bicat}
           {e b : B}
           (p : e --> b)
  : mor_preserves_cartesian p p (id₁ e).
Proof.
  intros ? ? ? ? H.
  assert (γ ▹ id₁ e = runitor _ • γ • rinvunitor _) as q.
  {
    use vcomp_move_L_Mp ; [ is_iso | ].
    cbn.
    rewrite !vcomp_runitor.
    apply idpath.
  }
  rewrite q.
  use vcomp_is_cartesian_2cell_sfib.
  - use vcomp_is_cartesian_2cell_sfib.
    + use invertible_is_cartesian_2cell_sfib.
      is_iso.
    + exact H.
  - use invertible_is_cartesian_2cell_sfib.
    is_iso.
Qed.

Definition comp_preserves_cartesian
           {B : bicat}
           {e₁ b₁ e₂ b₂ e₃ b₃ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {p₃ : e₃ --> b₃}
           {fe₁ : e₁ --> e₂}
           {fe₂ : e₂ --> e₃}
           (H₁ : mor_preserves_cartesian p₁ p₂ fe₁)
           (H₂ : mor_preserves_cartesian p₂ p₃ fe₂)
  : mor_preserves_cartesian p₁ p₃ (fe₁ · fe₂).
Proof.
  intros x f g γ Hγ.
  specialize (H₁ x _ _ γ Hγ).
  specialize (H₂ x _ _ _ H₁).
  assert (γ ▹ fe₁ · fe₂
          =
          lassociator _ _ _
          • ((γ ▹ fe₁) ▹ fe₂)
          • rassociator _ _ _)
    as q.
  {
    use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
    rewrite rwhisker_rwhisker.
    apply idpath.
  }
  rewrite q.
  use vcomp_is_cartesian_2cell_sfib.
  - use vcomp_is_cartesian_2cell_sfib.
    + use invertible_is_cartesian_2cell_sfib.
      is_iso.
    + exact H₂.
  - use invertible_is_cartesian_2cell_sfib.
    is_iso.
Qed.

Definition locally_grpd_preserves_cartesian
           {B : bicat}
           (HB : locally_groupoid B)
           {e₁ b₁ e₂ b₂ : B}
           (p₁ : e₁ --> b₁)
           (p₂ : e₂ --> b₂)
           (fe : e₁ --> e₂)
  : mor_preserves_cartesian p₁ p₂ fe.
Proof.
  intro ; intros.
  apply (locally_grpd_cartesian HB).
Defined.

Definition isaprop_mor_preserves_cartesian
           {B : bicat}
           {e₁ b₁ : B}
           (p₁ : e₁ --> b₁)
           {e₂ b₂ : B}
           (p₂ : e₂ --> b₂)
           (fe : e₁ --> e₂)
  : isaprop (mor_preserves_cartesian p₁ p₂ fe).
Proof.
  do 5 (use impred ; intro).
  exact (isaprop_is_cartesian_2cell_sfib _ _).
Qed.

Definition mor_of_internal_sfib_over
           {B : bicat}
           {e₁ b₁ : B}
           (p₁ : e₁ --> b₁)
           {e₂ b₂ : B}
           (p₂ : e₂ --> b₂)
           (fb : b₁ --> b₂)
  : UU
  := ∑ (fe : e₁ --> e₂),
     mor_preserves_cartesian p₁ p₂ fe
     ×
     invertible_2cell (p₁ · fb) (fe · p₂).

Definition make_mor_of_internal_sfib_over
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : e₁ --> e₂)
           (fc : mor_preserves_cartesian p₁ p₂ fe)
           (f_com : invertible_2cell (p₁ · fb) (fe · p₂))
  : mor_of_internal_sfib_over p₁ p₂ fb
  := (fe ,, fc ,, f_com).

Coercion mor_of_internal_sfib_over_to_mor
         {B : bicat}
         {e₁ b₁ : B}
         {p₁ : e₁ --> b₁}
         {e₂ b₂ : B}
         {p₂ : e₂ --> b₂}
         {fb : b₁ --> b₂}
         (fe : mor_of_internal_sfib_over p₁ p₂ fb)
  : e₁ --> e₂
  := pr1 fe.

Definition mor_of_internal_sfib_over_preserves
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : mor_of_internal_sfib_over p₁ p₂ fb)
  : mor_preserves_cartesian p₁ p₂ fe
  := pr12 fe.

Definition mor_of_internal_sfib_over_com
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : mor_of_internal_sfib_over p₁ p₂ fb)
  : invertible_2cell (p₁ · fb) (fe · p₂)
  := pr22 fe.

Definition id_mor_of_internal_sfib_over
           {B : bicat}
           {e b : B}
           (p : e --> b)
  : mor_of_internal_sfib_over p p (id₁ _).
Proof.
  use make_mor_of_internal_sfib_over.
  - exact (id₁ e).
  - apply id_mor_preserves_cartesian.
  - use make_invertible_2cell.
    + refine (runitor _ • linvunitor _).
    + is_iso.
Defined.

Definition comp_mor_of_internal_sfib_over
           {B : bicat}
           {e₁ e₂ e₃ b₁ b₂ b₃ : B}
           {fb₁ : b₁ --> b₂}
           {fb₂ : b₂ --> b₃}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {p₃ : e₃ --> b₃}
           (fe₁ : mor_of_internal_sfib_over p₁ p₂ fb₁)
           (fe₂ : mor_of_internal_sfib_over p₂ p₃ fb₂)
  : mor_of_internal_sfib_over p₁ p₃ (fb₁ · fb₂).
Proof.
  use make_mor_of_internal_sfib_over.
  - exact (fe₁ · fe₂).
  - exact (comp_preserves_cartesian
             (mor_of_internal_sfib_over_preserves fe₁)
             (mor_of_internal_sfib_over_preserves fe₂)).
  - use make_invertible_2cell.
    + exact (lassociator _ _ _
             • (mor_of_internal_sfib_over_com fe₁ ▹ _)
             • rassociator _ _ _
             • (_ ◃ mor_of_internal_sfib_over_com fe₂)
             • lassociator _ _ _).
    + is_iso.
      * apply property_from_invertible_2cell.
      * apply property_from_invertible_2cell.
Defined.

(**
 10. Cells of internal Street fibrations
 *)
Definition cell_of_internal_sfib_over_homot
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           (γ : fb ==> gb)
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sfib_over p₁ p₂ gb}
           (γe : fe ==> ge)
  : UU
  := mor_of_internal_sfib_over_com fe • (γe ▹ _)
     =
     (_ ◃ γ) • mor_of_internal_sfib_over_com ge.


Definition cell_of_internal_sfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           (γ : fb ==> gb)
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           (fe : mor_of_internal_sfib_over p₁ p₂ fb)
           (ge : mor_of_internal_sfib_over p₁ p₂ gb)
  : UU
  := ∑ (γe : fe ==> ge), cell_of_internal_sfib_over_homot γ γe.

Definition make_cell_of_internal_sfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sfib_over p₁ p₂ gb}
           (γe : fe ==> ge)
           (p : cell_of_internal_sfib_over_homot γ γe)
  : cell_of_internal_sfib_over γ fe ge
  := (γe ,, p).

Coercion cell_of_cell_of_internal_sfib_over
         {B : bicat}
         {b₁ b₂ e₁ e₂ : B}
         {fb gb : b₁ --> b₂}
         {γ : fb ==> gb}
         {p₁ : e₁ --> b₁}
         {p₂ : e₂ --> b₂}
         {fe : mor_of_internal_sfib_over p₁ p₂ fb}
         {ge : mor_of_internal_sfib_over p₁ p₂ gb}
         (γe : cell_of_internal_sfib_over γ fe ge)
  : fe ==> ge
  := pr1 γe.

Definition cell_of_internal_sfib_over_eq
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sfib_over p₁ p₂ gb}
           (γe : cell_of_internal_sfib_over γ fe ge)
  : mor_of_internal_sfib_over_com fe • (γe ▹ _)
     =
     (_ ◃ γ) • mor_of_internal_sfib_over_com ge
  := pr2 γe.

Definition eq_cell_of_internal_sfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sfib_over p₁ p₂ gb}
           (γe₁ γe₂ : cell_of_internal_sfib_over γ fe ge)
           (p : pr1 γe₁ = γe₂)
  : γe₁ = γe₂.
Proof.
  use subtypePath.
  {
    intro.
    apply cellset_property.
  }
  exact p.
Qed.

(**
 11. Equivalences preserve cartesian cells
 *)
Definition equivalence_preserves_cartesian
           {B : bicat}
           {b e₁ e₂ : B}
           (p₁ : e₁ --> b)
           (p₂ : e₂ --> b)
           (L : e₁ --> e₂)
           (com : invertible_2cell p₁ (L · p₂))
           (HL : left_adjoint_equivalence L)
           (HB_2_0 : is_univalent_2_0 B)
           (HB_2_1 : is_univalent_2_1 B)
  : mor_preserves_cartesian p₁ p₂ L.
Proof.
  refine (J_2_0
            HB_2_0
            (λ (x₁ x₂ : B) (L : adjoint_equivalence x₁ x₂),
             ∏ (p₁ : x₁ --> b)
               (p₂ : x₂ --> b)
               (c : invertible_2cell p₁ (L · p₂)),
             mor_preserves_cartesian p₁ p₂ L)
            _
            (L ,, HL)
            p₁
            p₂
            com).
  clear e₁ e₂ L HL p₁ p₂ com HB_2_0.
  cbn ; intros e p₁ p₂ com.
  pose (c := comp_of_invertible_2cell com (lunitor_invertible_2cell _)).
  refine (J_2_1
            HB_2_1
            (λ (x₁ x₂ : B)
               (f g : x₁ --> x₂)
               _,
             mor_preserves_cartesian f g (id₁ _))
            _
            c).
  intros.
  apply id_mor_preserves_cartesian.
Defined.
