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
Require Import UniMath.Bicategories.Colimits.Pullback.

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

Definition is_cartesian_eq
           {B : bicat}
           {e b : B}
           {p : e --> b}
           {x : B}
           {f g : x --> e}
           (α : f ==> g)
           {β : f ==> g}
           (q : α = β)
           (Hα : is_cartesian_2cell_sfib p α)
  : is_cartesian_2cell_sfib p β.
Proof.
  intros h ζ δp r.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
       induction q ;
       exact (is_cartesian_2cell_sfib_factor_unique
                _
                Hα h ζ δp
                r _ _
                (pr12 φ₁)
                (pr12 φ₂)
                (pr22 φ₁)
                (pr22 φ₂))).
  - simple refine (_ ,, _).
    + refine (is_cartesian_2cell_sfib_factor _ Hα ζ δp _).
      abstract
        (rewrite q, r ;
         apply idpath).
    + split.
      * apply is_cartesian_2cell_sfib_factor_over.
      * abstract
          (refine (maponpaths (λ z, _ • z) (!q) @ _) ;
           apply is_cartesian_2cell_sfib_factor_comm).
Defined.

Definition is_cartesian_from_factor
           {B : bicat}
           {e b : B}
           {p : e --> b}
           {x : B}
           {f₁ f₂ g : x --> e}
           (α : f₁ ==> f₂)
           (Hα : is_invertible_2cell α)
           (β : f₁ ==> g)
           (γ : f₂ ==> g)
           (Hγ : is_cartesian_2cell_sfib p γ)
           (q : β = α • γ)
  : is_cartesian_2cell_sfib p β.
Proof.
  use (is_cartesian_eq _ (!q)).
  use vcomp_is_cartesian_2cell_sfib.
  - apply invertible_is_cartesian_2cell_sfib.
    exact Hα.
  - exact Hγ.
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
Definition prod_1cell_eta_map
           {B : bicat_with_binprod}
           {a b₁ b₂ : B}
           (g : a --> b₁ ⊗ b₂)
  : ⟨ g · π₁ , g · π₂ ⟩ ==> g.
Proof.
  use binprod_ump_2cell.
  - apply (pr2 B).
  - exact (prod_1cell_pr1 _ _ _).
  - exact (prod_1cell_pr2 _ _ _).
Defined.

Definition prod_1cell_eta_inv
           {B : bicat_with_binprod}
           {a b₁ b₂ : B}
           (g : a --> b₁ ⊗ b₂)
  : g ==> ⟨ g · π₁ , g · π₂ ⟩.
Proof.
  use binprod_ump_2cell.
  - apply (pr2 B).
  - exact ((prod_1cell_pr1 _ _ _)^-1).
  - exact ((prod_1cell_pr2 _ _ _)^-1).
Defined.

Definition prod_1cell_eta_map_inv
           {B : bicat_with_binprod}
           {a b₁ b₂ : B}
           (g : a --> b₁ ⊗ b₂)
  : prod_1cell_eta_map g • prod_1cell_eta_inv g = id₂ _.
Proof.
  use binprod_ump_2cell_unique_alt.
  - apply (pr2 B).
  - rewrite <- rwhisker_vcomp.
    unfold prod_1cell_eta_map, prod_1cell_eta_inv.
    rewrite !binprod_ump_2cell_pr1.
    rewrite vcomp_rinv.
    rewrite id2_rwhisker.
    apply idpath.
  - rewrite <- rwhisker_vcomp.
    unfold prod_1cell_eta_map, prod_1cell_eta_inv.
    rewrite !binprod_ump_2cell_pr2.
    rewrite vcomp_rinv.
    rewrite id2_rwhisker.
    apply idpath.
Qed.

Definition prod_1cell_eta_inv_map
           {B : bicat_with_binprod}
           {a b₁ b₂ : B}
           (g : a --> b₁ ⊗ b₂)
  : prod_1cell_eta_inv g • prod_1cell_eta_map g = id₂ _.
Proof.
  use binprod_ump_2cell_unique_alt.
  - apply (pr2 B).
  - rewrite <- rwhisker_vcomp.
    unfold prod_1cell_eta_map, prod_1cell_eta_inv.
    rewrite !binprod_ump_2cell_pr1.
    rewrite vcomp_linv.
    rewrite id2_rwhisker.
    apply idpath.
  - rewrite <- rwhisker_vcomp.
    unfold prod_1cell_eta_map, prod_1cell_eta_inv.
    rewrite !binprod_ump_2cell_pr2.
    rewrite vcomp_linv.
    rewrite id2_rwhisker.
    apply idpath.
Qed.

Definition prod_1cell_eta
           {B : bicat_with_binprod}
           {a b₁ b₂ : B}
           (g : a --> b₁ ⊗ b₂)
  : invertible_2cell ⟨ g · π₁ , g · π₂ ⟩ g.
Proof.
  use make_invertible_2cell.
  - exact (prod_1cell_eta_map g).
  - use make_is_invertible_2cell.
    + exact (prod_1cell_eta_inv g).
    + exact (prod_1cell_eta_map_inv g).
    + exact (prod_1cell_eta_inv_map g).
Defined.

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
                     ,, ⟪ α , id2 _ ⟫ • prod_1cell_eta g
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
 6. Composition of Street fibrations
 *)
Section CompositionSFib.
  Context {B : bicat}
          {x y z : B}
          {f : x --> y}
          {g : y --> z}
          (Hf : internal_sfib f)
          (Hg : internal_sfib g).

  Section ToCartesianCellComp.
    Context {w : B}
            {h₁ h₂ : w --> x}
            {δ : h₁ ==> h₂}
            (H₁ : is_cartesian_2cell_sfib f δ)
            (H₂ : is_cartesian_2cell_sfib g (δ ▹ f)).

    Section TheLift.
      Context {k : w --> x}
              {β : k ==> h₂}
              {δp : k · (f · g) ==> h₁ · (f · g)}
              (q : β ▹ f · g = δp • (δ ▹ f · g)).

      Local Lemma lift_f_eq
        : (β ▹ f) ▹ g
          =
          ((rassociator k f g • δp) • lassociator h₁ f g) • ((δ ▹ f) ▹ g).
      Proof.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite rwhisker_rwhisker.
        rewrite q.
        rewrite !vassocl.
        apply maponpaths.
        rewrite <- rwhisker_rwhisker.
        apply idpath.
      Qed.

      Let f_lift : k · f ==> h₁ · f
        := is_cartesian_2cell_sfib_factor
             _
             H₂
             (β ▹ f)
             (rassociator _ _ _ • δp • lassociator _ _ _)
             lift_f_eq.

      Local Lemma lift_g_eq
        : β ▹ f = f_lift • (δ ▹ f).
      Proof.
        unfold f_lift.
        rewrite is_cartesian_2cell_sfib_factor_comm.
        apply idpath.
      Qed.

      Definition to_cartesian_2cell_comp_lift
        : k ==> h₁
        := is_cartesian_2cell_sfib_factor
             _
             H₁
             β
             f_lift
             lift_g_eq.

      Definition to_cartesian_2cell_comp_over
        : to_cartesian_2cell_comp_lift ▹ f · g = δp.
      Proof.
        use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
        rewrite <- rwhisker_rwhisker.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply is_cartesian_2cell_sfib_factor_over.
          }
          apply is_cartesian_2cell_sfib_factor_over.
        }
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      Qed.

      Definition to_cartesian_2cell_unique_lift
        : isaprop (∑ (ζ : k ==> h₁), ζ ▹ f · g = δp × ζ • δ = β).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
        use (is_cartesian_2cell_sfib_factor_unique _ H₁ k β f_lift lift_g_eq).
        - use (is_cartesian_2cell_sfib_factor_unique
                 g H₂ _ (β ▹ f) ((rassociator k f g • δp) • lassociator h₁ f g) lift_f_eq).
          + rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ].
            cbn.
            rewrite rwhisker_rwhisker.
            apply maponpaths_2.
            exact (pr12 φ₁).
          + apply is_cartesian_2cell_sfib_factor_over.
          + rewrite !rwhisker_vcomp.
            rewrite (pr22 φ₁).
            apply idpath.
          + apply is_cartesian_2cell_sfib_factor_comm.
        - use (is_cartesian_2cell_sfib_factor_unique
                 g H₂ _ (β ▹ f) ((rassociator k f g • δp) • lassociator h₁ f g) lift_f_eq).
          + rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ].
            cbn.
            rewrite rwhisker_rwhisker.
            apply maponpaths_2.
            exact (pr12 φ₂).
          + apply is_cartesian_2cell_sfib_factor_over.
          + rewrite !rwhisker_vcomp.
            rewrite (pr22 φ₂).
            apply idpath.
          + apply is_cartesian_2cell_sfib_factor_comm.
        - exact (pr22 φ₁).
        - exact (pr22 φ₂).
      Qed.
    End TheLift.

    Definition to_cartesian_2cell_comp
      : is_cartesian_2cell_sfib (f · g) δ.
    Proof.
      intros k β δp q.
      use iscontraprop1.
      - exact (to_cartesian_2cell_unique_lift q).
      - refine (to_cartesian_2cell_comp_lift q ,, _ ,, _).
        + apply to_cartesian_2cell_comp_over.
        + apply is_cartesian_2cell_sfib_factor_comm.
    Defined.
  End ToCartesianCellComp.

  Section FromCartesianCellComp.
    Context {w : B}
            {h₁ h₂ : w --> x}
            {δ : h₁ ==> h₂}
            (H : is_cartesian_2cell_sfib (f · g) δ).

    Section TheLiftSnd.
      Context {k : w --> y}
              {β : k ==> h₂ · f}
              {δp : k · g ==> h₁ · f · g}
              (q : β ▹ g = δp • ((δ ▹ f) ▹ g)).

      Definition snd_lift_unique
        : isaprop (∑ ζ, ζ ▹ g = δp × ζ • (δ ▹ f) = β).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
      Admitted.

      Let ℓ : w --> x := internal_sfib_cleaving_lift_mor _ Hf β.
      Let γ : ℓ ==> h₂ := internal_sfib_cleaving_lift_cell _ Hf β.
      Let χ : invertible_2cell (ℓ · f) k
        := internal_sfib_cleaving_com _ Hf β.
      Let χq : ℓ · (f · g) ==> h₁ · (f · g)
        := lassociator _ _ _
           • (χ ▹ g)
           • δp
           • rassociator _ _ _.

      Lemma snd_lift_eq
        : γ ▹ f · g = χq • (δ ▹ f · g).
      Proof.
        unfold γ, χq.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite <- rwhisker_rwhisker_alt.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (internal_sfib_cleaving_over _ Hf β).
        }
        rewrite <- rwhisker_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        rewrite q.
        rewrite !vassocl.
        rewrite rwhisker_rwhisker_alt.
        apply idpath.
      Qed.

      Definition from_cartesian_2cell_comp_snd_lift
        : k ==> h₁ · f
        := χ^-1 • (is_cartesian_2cell_sfib_factor _ H γ χq snd_lift_eq ▹ f).

      Definition from_cartesian_2cell_comp_snd_lift_over
        : from_cartesian_2cell_comp_snd_lift ▹ g = δp.
      Proof.
        unfold from_cartesian_2cell_comp_snd_lift.
        rewrite <- rwhisker_vcomp.
        use vcomp_move_R_pM ; [ is_iso | ].
        cbn.
        use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
        rewrite rwhisker_rwhisker.
        rewrite is_cartesian_2cell_sfib_factor_over.
        unfold χq.
        rewrite !vassocl.
        rewrite rassociator_lassociator.
        rewrite id2_right.
        apply idpath.
      Qed.

      Definition from_cartesian_2cell_comp_snd_lift_com
        : from_cartesian_2cell_comp_snd_lift • (δ ▹ f) = β.
      Proof.
        unfold from_cartesian_2cell_comp_snd_lift.
        rewrite !vassocl.
        use vcomp_move_R_pM ; [ is_iso | ].
        cbn.
        rewrite rwhisker_vcomp.
        rewrite is_cartesian_2cell_sfib_factor_comm.
        apply internal_sfib_cleaving_over.
      Qed.
    End TheLiftSnd.

    Definition from_cartesian_2cell_comp_snd
      : is_cartesian_2cell_sfib g (δ ▹ f).
    Proof.
      intros k β δp q.
      use iscontraprop1.
      - exact (snd_lift_unique q).
      - refine (from_cartesian_2cell_comp_snd_lift q ,, _ ,, _).
        + exact (from_cartesian_2cell_comp_snd_lift_over q).
        + exact (from_cartesian_2cell_comp_snd_lift_com q).
    Defined.

    Section TheLiftFst.
      Context {k : w --> x}
              {β : k ==> h₂}
              {δp : k · f ==> h₁ · f}
              (q : β ▹ f = δp • (δ ▹ f)).

      Local Lemma fst_lift_eq
        : β ▹ f · g
          =
          ((lassociator k f g • (δp ▹ g)) • rassociator h₁ f g) • (δ ▹ f · g).
      Proof.
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite <- rwhisker_rwhisker_alt.
        rewrite q.
        rewrite <- rwhisker_vcomp.
        rewrite !vassocl.
        rewrite rwhisker_rwhisker_alt.
        apply idpath.
      Qed.

      Definition from_cartesian_2cell_comp_fst_lift
        : k ==> h₁
        := is_cartesian_2cell_sfib_factor
             _
             H β
             (lassociator _ _ _ • (δp ▹ g) • rassociator _ _ _)
             fst_lift_eq.

      Definition from_cartesian_2cell_comp_fst_over
        : from_cartesian_2cell_comp_fst_lift ▹ f = δp.
      Proof.
        use (is_cartesian_2cell_sfib_factor_unique
               _
               from_cartesian_2cell_comp_snd
               _
               (β ▹ f)
               (δp ▹ g)).
        - rewrite q.
          rewrite rwhisker_vcomp.
          apply idpath.
        - use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
          rewrite rwhisker_rwhisker.
          unfold from_cartesian_2cell_comp_fst_lift.
          rewrite is_cartesian_2cell_sfib_factor_over.
          rewrite !vassocl.
          rewrite rassociator_lassociator.
          rewrite id2_right.
          apply idpath.
        - apply idpath.
        - rewrite rwhisker_vcomp.
          unfold from_cartesian_2cell_comp_fst_lift.
          rewrite is_cartesian_2cell_sfib_factor_comm.
          apply idpath.
        - exact (!q).
      Qed.

      Definition from_cartesian_2cell_comp_fst_comm
        : from_cartesian_2cell_comp_fst_lift • δ = β.
      Proof.
        apply is_cartesian_2cell_sfib_factor_comm.
      Qed.

      Definition from_cartesian_2cell_comp_fst_unique
        : isaprop (∑ ζ, ζ ▹ f = δp × ζ • δ = β).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
        use (is_cartesian_2cell_sfib_factor_unique _ H _ _ _ fst_lift_eq).
        - use vcomp_move_L_Mp ; [ is_iso | ].
          cbn.
          rewrite <- rwhisker_rwhisker.
          rewrite (pr12 φ₁).
          apply idpath.
        - use vcomp_move_L_Mp ; [ is_iso | ].
          cbn.
          rewrite <- rwhisker_rwhisker.
          rewrite (pr12 φ₂).
          apply idpath.
        - exact (pr22 φ₁).
        - exact (pr22 φ₂).
      Qed.
    End TheLiftFst.

    Definition from_cartesian_2cell_comp_fst
      : is_cartesian_2cell_sfib f δ.
    Proof.
      intros k β δp q.
      use iscontraprop1.
      - exact (from_cartesian_2cell_comp_fst_unique q).
      - refine (from_cartesian_2cell_comp_fst_lift q ,, _ ,, _).
        + apply from_cartesian_2cell_comp_fst_over.
        + apply from_cartesian_2cell_comp_fst_comm.
    Defined.
  End FromCartesianCellComp.

  Definition comp_internal_sfib_cleaving
    : internal_sfib_cleaving (f · g).
  Proof.
    intros w h₁ h₂ α.
    refine (internal_sfib_cleaving_lift_mor
              _
              Hf
              (internal_sfib_cleaving_lift_cell _ Hg (α • lassociator _ _ _))
            ,,
            internal_sfib_cleaving_lift_cell
              _
              Hf
              (internal_sfib_cleaving_lift_cell _ Hg (α • lassociator _ _ _))
            ,,
            comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (lassociator_invertible_2cell _ _ _)
                 (rwhisker_of_invertible_2cell
                    g
                    (internal_sfib_cleaving_com
                       _
                       Hf
                       (internal_sfib_cleaving_lift_cell _ Hg (α • lassociator _ _ _)))))
              (internal_sfib_cleaving_com
                 _
                 Hg
                 (α • lassociator _ _ _))
            ,,
            _
            ,,
            _).
    - use to_cartesian_2cell_comp.
      + apply internal_sfib_cleaving_is_cartesian.
      + refine (transportb
                  (is_cartesian_2cell_sfib g)
                  (internal_sfib_cleaving_over _ _ _)
                  _).
        use vcomp_is_cartesian_2cell_sfib.
        * use invertible_is_cartesian_2cell_sfib.
          apply property_from_invertible_2cell.
        * apply internal_sfib_cleaving_is_cartesian.
    - abstract
        (cbn ;
         use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ] ;
         rewrite !vassocr ;
         rewrite rassociator_lassociator ;
         rewrite id2_left ;
         rewrite <- rwhisker_rwhisker_alt ;
         rewrite internal_sfib_cleaving_over ;
         rewrite <- rwhisker_vcomp ;
         rewrite internal_sfib_cleaving_over ;
         rewrite !vassocl ;
         do 2 apply maponpaths ;
         rewrite lassociator_rassociator ;
         apply id2_right).
  Defined.

  Definition comp_lwhisker_is_cartesian
    : lwhisker_is_cartesian (f · g).
  Proof.
    intros w₁ w₂ h k₁ k₂ α Hα.
    use to_cartesian_2cell_comp.
    - apply (pr2 Hf).
      apply from_cartesian_2cell_comp_fst.
      exact Hα.
    - pose (pr2 Hg _ _ h _ _ _ (from_cartesian_2cell_comp_snd Hα)) as cart_g.
      use (is_cartesian_eq
             (rassociator _ _ _ • (h ◃ (α ▹ f)) • lassociator _ _ _)
             _
             _).
      + abstract
          (rewrite rwhisker_lwhisker_rassociator ;
           rewrite !vassocl ;
           rewrite rassociator_lassociator ;
           apply id2_right).
      + use vcomp_is_cartesian_2cell_sfib.
        * use vcomp_is_cartesian_2cell_sfib.
          ** apply invertible_is_cartesian_2cell_sfib.
             is_iso.
          ** exact cart_g.
        * apply invertible_is_cartesian_2cell_sfib.
          is_iso.
  Defined.

  Definition comp_internal_sfib
    : internal_sfib (f · g).
  Proof.
    split.
    - exact comp_internal_sfib_cleaving.
    - exact comp_lwhisker_is_cartesian.
  Defined.
End CompositionSFib.

(**
 7. Pullback of Street fibrations
 *)
Section PullbackOfSFib.
  Context {B : bicat}
          {e₁ e₂ b₁ b₂ : B}
          {p₁ : e₁ --> b₁}
          {p₂ : e₂ --> b₂}
          {fe : e₁ --> e₂}
          {fb : b₁ --> b₂}
          {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
          (pb := make_pb_cone e₁ fe p₁ γ)
          (H : has_pb_ump pb)
          (Hf : internal_sfib p₂).

  Section Cartesian.
    Context {x : B}
            {g₁ g₂ : x --> e₁}
            (α : g₁ ==> g₂).

    Section ToPBCartesian.
      Context (Hα : is_cartesian_2cell_sfib p₂ (α ▹ fe))
              {h : x --> e₁}
              {β : h ==> g₂}
              {δp : h · p₁ ==> g₁ · p₁}
              (q : β ▹ p₁ = δp • (α ▹ p₁)).

      Definition to_pb_cartesian_unique
        : isaprop (∑ δ, δ ▹ p₁ = δp × δ • α = β).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
        use (pb_ump_eq H).
        - exact (pr1 φ₁ ▹ fe).
        - exact δp.
        - cbn.
          rewrite !vassocl.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite rwhisker_rwhisker_alt.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite lassociator_rassociator.
          rewrite id2_left.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          use vcomp_move_L_Mp ; [ is_iso | ].
          cbn.
          rewrite <- rwhisker_rwhisker.
          apply maponpaths.
          rewrite (pr12 φ₁).
          apply idpath.
        - apply idpath.
        - exact (pr12 φ₁).
        - cbn.
          use (is_cartesian_2cell_sfib_factor_unique _ Hα).
          + exact (β ▹ fe).
          + exact (rassociator _ _ _
                   • (h ◃ γ)
                   • lassociator _ _ _
                   • (δp ▹ _)
                   • rassociator _ _ _
                   • (g₁ ◃ γ^-1)
                   • lassociator _ _ _).
          + rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
            rewrite !rwhisker_rwhisker.
            rewrite !vassocr.
            apply maponpaths_2.
            rewrite !vassocl.
            rewrite <- vcomp_whisker.
            rewrite !vassocr.
            use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
            rewrite vcomp_whisker.
            rewrite !vassocl.
            apply maponpaths.
            rewrite <- rwhisker_rwhisker_alt.
            rewrite !vassocr.
            use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
            rewrite <- rwhisker_rwhisker.
            rewrite !vassocl.
            apply maponpaths.
            rewrite rwhisker_vcomp.
            rewrite q.
            apply idpath.
          + rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
            rewrite !rwhisker_rwhisker.
            rewrite !vassocr.
            apply maponpaths_2.
            use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
            rewrite vcomp_whisker.
            rewrite !vassocl.
            apply maponpaths.
            use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
            rewrite <- rwhisker_rwhisker_alt.
            apply maponpaths_2.
            apply maponpaths.
            exact (pr12 φ₂).
          + rewrite !vassocl.
            use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
            rewrite !rwhisker_rwhisker.
            rewrite !vassocr.
            apply maponpaths_2.
            use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
            rewrite vcomp_whisker.
            rewrite !vassocl.
            apply maponpaths.
            use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
            rewrite <- rwhisker_rwhisker_alt.
            apply maponpaths_2.
            apply maponpaths.
            exact (pr12 φ₁).
          + rewrite rwhisker_vcomp.
            rewrite (pr22 φ₂).
            apply idpath.
          + rewrite rwhisker_vcomp.
            rewrite (pr22 φ₁).
            apply idpath.
        - exact (pr12 φ₂).
      Qed.

      Let φ : h · fe · p₂ ==> g₁ · fe · p₂
        := rassociator _ _ _
           • (h ◃ γ)
           • lassociator _ _ _
           • (δp ▹ fb)
           • rassociator _ _ _
           • (g₁ ◃ γ^-1)
           • lassociator _ _ _.

      Local Proposition φ_eq
        : (β ▹ fe) ▹ p₂ = φ • ((α ▹ fe) ▹ p₂).
      Proof.
        unfold φ ; clear φ.
        rewrite !vassocl.
        rewrite rwhisker_rwhisker.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite rwhisker_rwhisker.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite <- vcomp_whisker.
        rewrite !vassocr.
        use vcomp_move_L_Mp ; [ is_iso | ].
        cbn.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite <- rwhisker_rwhisker_alt.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite <- rwhisker_rwhisker_alt.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite rwhisker_vcomp.
        apply maponpaths.
        exact q.
      Qed.

      Let to_pb_cartesian_cell_on_pr1
        : h · fe ==> g₁ · fe
        := is_cartesian_2cell_sfib_factor _ Hα _ _ φ_eq.

      Local Definition to_pb_cartesian_cell_eq
        : (h ◃ γ)
          • lassociator h p₁ fb
          • (δp ▹ fb)
          • rassociator g₁ p₁ fb
          =
          lassociator h fe p₂
          • (to_pb_cartesian_cell_on_pr1 ▹ p₂)
          • rassociator g₁ fe p₂
          • (g₁ ◃ γ).
      Proof.
        unfold to_pb_cartesian_cell_on_pr1, φ.
        rewrite is_cartesian_2cell_sfib_factor_over.
        rewrite !vassocr.
        rewrite lassociator_rassociator, id2_left.
        rewrite !vassocl.
        do 3 apply maponpaths.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
        rewrite lassociator_rassociator, id2_left.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        rewrite id2_right.
        apply idpath.
      Qed.

      Definition to_pb_cartesian_cell
        : h ==> g₁.
      Proof.
        use (pb_ump_cell H).
        - exact to_pb_cartesian_cell_on_pr1.
        - exact δp.
        - exact to_pb_cartesian_cell_eq.
      Defined.

      Definition to_pb_cartesian_comm
        : to_pb_cartesian_cell • α = β.
      Proof.
        unfold to_pb_cartesian_cell.
        use (pb_ump_eq H).
        - exact (to_pb_cartesian_cell_on_pr1 • (α ▹ fe)).
        - exact (δp • (α ▹ p₁)).
        - cbn ; unfold to_pb_cartesian_cell_on_pr1.
          rewrite <- q.
          rewrite <- !rwhisker_vcomp.
          rewrite !vassocl.
          rewrite is_cartesian_2cell_sfib_factor_over.
          rewrite rwhisker_rwhisker_alt.
          rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
          rewrite lassociator_rassociator, id2_left.
          rewrite <- vcomp_whisker.
          rewrite !vassocr.
          apply maponpaths_2.
          unfold φ.
          rewrite !vassocr.
          rewrite lassociator_rassociator, id2_left.
          rewrite !vassocl.
          refine (!_).
          etrans.
          {
            do 5 apply maponpaths.
            rewrite rwhisker_rwhisker_alt.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            apply id2_left.
          }
          rewrite <- vcomp_whisker.
          etrans.
          {
            do 3 apply maponpaths.
            rewrite !vassocr.
            rewrite <- rwhisker_rwhisker_alt.
            apply idpath.
          }
          etrans.
          {
            do 2 apply maponpaths.
            rewrite !vassocr.
            rewrite rwhisker_vcomp.
            rewrite <- q.
            rewrite rwhisker_rwhisker_alt.
            rewrite !vassocl.
            rewrite vcomp_whisker.
            apply idpath.
          }
          etrans.
          {
            apply maponpaths.
            rewrite !vassocr.
            rewrite lassociator_rassociator.
            rewrite id2_left.
            apply idpath.
          }
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite vcomp_rinv.
          rewrite lwhisker_id2.
          apply id2_left.
        - cbn ; unfold to_pb_cartesian_cell_on_pr1.
          rewrite <- rwhisker_vcomp.
          apply maponpaths_2.
          apply (pb_ump_cell_pr1 H).
        - cbn ; unfold to_pb_cartesian_cell_on_pr1.
          rewrite <- rwhisker_vcomp.
          apply maponpaths_2.
          apply (pb_ump_cell_pr2 H).
        - cbn ; unfold to_pb_cartesian_cell_on_pr1.
          refine (!_).
          apply is_cartesian_2cell_sfib_factor_comm.
        - exact q.
      Qed.
    End ToPBCartesian.

    Definition to_pb_cartesian
               (Hα : is_cartesian_2cell_sfib p₂ (α ▹ fe))
      : is_cartesian_2cell_sfib p₁ α.
    Proof.
      intros h β δp q.
      use iscontraprop1.
      - exact (to_pb_cartesian_unique Hα q).
      - simple refine (_ ,, _ ,, _).
        + exact (to_pb_cartesian_cell Hα q).
        + apply (pb_ump_cell_pr2 H).
        + exact (to_pb_cartesian_comm Hα q).
    Defined.

    Definition from_pb_cartesian
               (Hα : is_cartesian_2cell_sfib p₁ α)
      : is_cartesian_2cell_sfib p₂ (α ▹ fe).
    Proof.
      use is_cartesian_from_factor.
      - exact (internal_sfib_cleaving_lift_mor p₂ Hf ((α ▹ fe) ▹ p₂)).
      - use (is_cartesian_2cell_sfib_factor
               _
               (internal_sfib_cleaving_is_cartesian p₂ Hf ((α ▹ fe) ▹ p₂))).
        + exact (α ▹ fe).
        + exact ((internal_sfib_cleaving_com p₂ Hf ((α ▹ fe) ▹ p₂))^-1).
        + abstract
            (rewrite internal_sfib_cleaving_over ;
             rewrite !vassocr ;
             rewrite vcomp_linv ;
             rewrite id2_left ;
             apply idpath).
      - use make_is_invertible_2cell.
        + admit.
        + admit.
        + admit.
      - exact (internal_sfib_cleaving_lift_cell p₂ Hf ((α ▹ fe) ▹ p₂)).
      - exact (internal_sfib_cleaving_is_cartesian p₂ Hf ((α ▹ fe) ▹ p₂)).
      - refine (!_).
        apply is_cartesian_2cell_sfib_factor_comm.
    Admitted.
  End Cartesian.

  Section Cleaving.
    Context {x : B}
            {h₁ : x --> b₁}
            {h₂ : x --> e₁}
            (α : h₁ ==> h₂ · p₁).

    Let x_to_e₂ : x --> e₂.
    Proof.
      use (internal_sfib_cleaving_lift_mor
             _ Hf).
      - exact (h₁ · fb).
      - exact (h₂ · fe).
      - exact ((α ▹ _)
               • rassociator _ _ _
               • (h₂ ◃ γ^-1)
               • lassociator _ _ _).
    Defined.

    Definition pb_of_sfib_cleaving_cone
      : pb_cone p₂ fb.
    Proof.
      use make_pb_cone.
      - exact x.
      - exact x_to_e₂.
      - exact h₁.
      - apply internal_sfib_cleaving_com.
    Defined.

    Definition pb_of_sfib_cleaving_mor
      : x --> e₁
      := pb_ump_mor H pb_of_sfib_cleaving_cone.

    Definition pb_of_sfib_cleaving_cell
      : pb_of_sfib_cleaving_mor ==> h₂.
    Proof.
      use (pb_ump_cell H).
      - exact (pb_ump_mor_pr1 H pb_of_sfib_cleaving_cone
               •
               internal_sfib_cleaving_lift_cell _ _ _).
      - exact (pb_ump_mor_pr2 H pb_of_sfib_cleaving_cone • α).
      - abstract
          (simpl ;
           rewrite !vassocl ;
           etrans ;
           [ apply maponpaths_2 ;
             exact (pb_ump_mor_cell H pb_of_sfib_cleaving_cone)
           | ] ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           apply maponpaths ;
           cbn ;
           rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
           rewrite rassociator_lassociator ;
           rewrite id2_left ;
           etrans ;
           [ apply maponpaths ;
             rewrite !vassocr ;
             rewrite rwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite id2_rwhisker ;
             rewrite id2_left ;
             apply idpath
           | ] ;
           refine (!_) ;
           etrans ;
           [ apply maponpaths_2 ;
             apply internal_sfib_cleaving_over
           | ] ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)) ;
           rewrite lassociator_rassociator ;
           rewrite id2_left ;
           rewrite lwhisker_vcomp ;
           rewrite vcomp_linv ;
           rewrite lwhisker_id2 ;
           apply id2_right).
    Defined.

    Definition pb_of_sfib_cleaving_over
      : invertible_2cell (pb_of_sfib_cleaving_mor · p₁) h₁
      := pb_ump_mor_pr2 H pb_of_sfib_cleaving_cone.

    Definition pb_of_sfib_cleaving_commute
      : pb_of_sfib_cleaving_cell ▹ p₁ = pb_of_sfib_cleaving_over • α.
    Proof.
      apply (pb_ump_cell_pr2 H).
    Defined.
  End Cleaving.

  Definition pb_of_sfib_cleaving
    : internal_sfib_cleaving p₁.
  Proof.
    intros x h₁ h₂ α.
    refine (pb_of_sfib_cleaving_mor α
            ,,
            pb_of_sfib_cleaving_cell α
            ,,
            pb_of_sfib_cleaving_over α
            ,,
            _
            ,,
            pb_of_sfib_cleaving_commute α).
    apply to_pb_cartesian.
    refine (is_cartesian_eq _ (!(pb_ump_cell_pr1 H _ _ _ _ _)) _).
    use vcomp_is_cartesian_2cell_sfib.
    - apply invertible_is_cartesian_2cell_sfib.
      apply property_from_invertible_2cell.
    - apply internal_sfib_cleaving_is_cartesian.
  Defined.

  Definition pb_lwhisker_is_cartesian
    : lwhisker_is_cartesian p₁.
  Proof.
    intros x y h f g α Hα.
    apply to_pb_cartesian.
    use is_cartesian_eq.
    - exact (rassociator _ _ _ • (h ◃ (α ▹ fe)) • lassociator _ _ _).
    - abstract
        (rewrite rwhisker_lwhisker_rassociator ;
         rewrite !vassocl ;
         rewrite rassociator_lassociator ;
         apply id2_right).
    - use vcomp_is_cartesian_2cell_sfib.
      + use vcomp_is_cartesian_2cell_sfib.
        * apply invertible_is_cartesian_2cell_sfib.
          is_iso.
        * apply (pr2 Hf).
          apply from_pb_cartesian.
          exact Hα.
      + apply invertible_is_cartesian_2cell_sfib.
        is_iso.
  Defined.

  Definition pb_of_sfib
    : internal_sfib p₁.
  Proof.
    split.
    - exact pb_of_sfib_cleaving.
    - exact pb_lwhisker_is_cartesian.
  Defined.
End PullbackOfSFib.

(**
 8. Internal Street fibrations of categories
 *)
Section Cartesians.
  Context {E B : univalent_category}
          (P : bicat_of_univ_cats ⟦ E , B ⟧)
          {X : univalent_category}
          {F G : bicat_of_univ_cats ⟦ X , E ⟧}
          (α : F ==> G).

  Section PointwiseCartesianIsCartesian.
    Context {H : bicat_of_univ_cats ⟦ X, E ⟧}
            {γ : H ==> G}
            (δp : H · P ==> F · P)
            (q : γ ▹ P = δp • (α ▹ P))
            (Hα : ∏ (x : X), is_cartesian_sfib P (pr1 α x)).

    Definition cartesian_sfib_unique_pointwise_lift
      : isaprop (∑ δ, δ ▹ P = δp × δ • α = γ).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        use isapropdirprod ; apply cellset_property.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use (cartesian_factorization_sfib_unique
             _
             (Hα x)
             (pr1 γ x)
             (pr1 δp x)).
      - exact (nat_trans_eq_pointwise q x).
      - exact (nat_trans_eq_pointwise (pr12 φ₁) x).
      - exact (nat_trans_eq_pointwise (pr12 φ₂) x).
      - exact (nat_trans_eq_pointwise (pr22 φ₁) x).
      - exact (nat_trans_eq_pointwise (pr22 φ₂) x).
    Qed.

    Definition cartesian_sfib_pointwise_lift_data
      : nat_trans_data (pr1 H) (pr1 F)
      := λ x, cartesian_factorization_sfib
                _
                (Hα x)
                (pr1 γ x)
                (pr1 δp x)
                (nat_trans_eq_pointwise q x).

    Definition cartesian_sfib_pointwise_lift_is_nat_trans
      : is_nat_trans _ _ cartesian_sfib_pointwise_lift_data.
    Proof.
      intros x y f ; cbn ; unfold cartesian_sfib_pointwise_lift_data.
      use (cartesian_factorization_sfib_unique
             _
             (Hα y)
             (# (pr1 H) f · pr1 γ y)
             (# (pr1 P) (# (pr1 H) f) · pr1 δp y)).
      - rewrite functor_comp.
        rewrite !assoc'.
        apply maponpaths.
        exact (nat_trans_eq_pointwise q y).
      - rewrite functor_comp.
        apply maponpaths.
        apply cartesian_factorization_sfib_over.
      - rewrite functor_comp.
        refine (_ @ !(nat_trans_ax δp _ _ f)).
        apply maponpaths_2.
        apply cartesian_factorization_sfib_over.
      - rewrite !assoc'.
        rewrite cartesian_factorization_sfib_commute.
        apply idpath.
      - rewrite !assoc'.
        rewrite (nat_trans_ax α).
        rewrite !assoc.
        rewrite cartesian_factorization_sfib_commute.
        rewrite (nat_trans_ax γ).
        apply idpath.
    Qed.

    Definition cartesian_sfib_pointwise_lift
      : H ==> F.
    Proof.
      use make_nat_trans.
      - exact cartesian_sfib_pointwise_lift_data.
      - exact cartesian_sfib_pointwise_lift_is_nat_trans.
    Defined.

    Definition cartesian_sfib_pointwise_lift_over
      : cartesian_sfib_pointwise_lift ▹ P = δp.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn ; unfold cartesian_sfib_pointwise_lift_data.
      apply cartesian_factorization_sfib_over.
    Qed.

    Definition cartesian_sfib_pointwise_lift_commute
      : cartesian_sfib_pointwise_lift • α = γ.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn ; unfold cartesian_sfib_pointwise_lift_data.
      apply cartesian_factorization_sfib_commute.
    Qed.
  End PointwiseCartesianIsCartesian.

  Definition is_cartesian_sfib_to_cartesian_2cell_sfib
             (Hα : ∏ (x : X), is_cartesian_sfib P (pr1 α x))
    : is_cartesian_2cell_sfib P α.
  Proof.
    intros H γ δp q.
    use iscontraprop1.
    - exact (cartesian_sfib_unique_pointwise_lift δp q Hα).
    - simple refine (_ ,, _).
      + exact (cartesian_sfib_pointwise_lift δp q Hα).
      + split.
        * exact (cartesian_sfib_pointwise_lift_over δp q Hα).
        * exact (cartesian_sfib_pointwise_lift_commute δp q Hα).
  Defined.

  Definition cartesian_2cell_sfib_to_is_cartesian_sfib
             (Hα : is_cartesian_2cell_sfib P α)
             (x : X)
    : is_cartesian_sfib P (pr1 α x).
  Proof.
  Admitted.
End Cartesians.

Section StreetFibIsInternalStreetFib.
  Context {E B : univalent_category}
          (P : bicat_of_univ_cats ⟦ E , B ⟧)
          (HP : street_fib P).

  Section InternalCleaving.
    Context {C : bicat_of_univ_cats}
            {F : C --> B}
            {G : C --> E}
            (α : F ==> G · P).

    Definition street_fib_is_internal_lift_data
      : functor_data (pr1 C) (pr1 E).
    Proof.
      use make_functor_data.
      - exact (λ x, street_fib_lift _ HP (pr1 α x)).
      - intros x y f ; cbn.
        use (cartesian_factorization_sfib
               _
               (street_fib_mor_is_cartesian _ HP (pr1 α y))
               (street_fib_mor _ HP (pr1 α x) · # (pr1 G) f)).
        + exact (street_fib_iso P HP (pr1 α x)
                 · # (pr1 F) f
                 · inv_from_iso (street_fib_iso P HP (pr1 α y))).
        + abstract
            (rewrite functor_comp ;
             rewrite !street_fib_over ;
             rewrite !assoc' ;
             refine (maponpaths (λ z, _ · z) (!(nat_trans_ax α _ _ f)) @ _) ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             rewrite !assoc' ;
             apply maponpaths ;
             rewrite iso_after_iso_inv ;
             rewrite id_right ;
             apply idpath).
    Defined.

    Definition street_fib_is_internal_lift_is_functor
      : is_functor street_fib_is_internal_lift_data.
    Proof.
      split.
      - intros x.
        use (cartesian_factorization_sfib_unique
               _
               (street_fib_mor_is_cartesian P HP (pr1 α x))
               (street_fib_mor P HP (pr1 α x) · # (pr1 G) (id₁ x))
               (street_fib_iso P HP (pr1 α x)
                · # (pr1 F) (id₁ x)
                · inv_from_iso (street_fib_iso P HP (pr1 α x)))).
        + rewrite (functor_id G), id_right.
          rewrite (functor_id F), id_right.
          rewrite iso_inv_after_iso.
          rewrite id_left.
          apply idpath.
        + apply cartesian_factorization_sfib_over.
        + rewrite functor_id, (functor_id F).
          rewrite id_right.
          rewrite iso_inv_after_iso.
          apply idpath.
        + apply cartesian_factorization_sfib_commute.
        + rewrite id_left.
          rewrite (functor_id G).
          rewrite id_right.
          apply idpath.
      - intros x y z f g.
        cbn.
        use (cartesian_factorization_sfib_unique
               _
               (street_fib_mor_is_cartesian P HP (pr1 α z))
               (street_fib_mor P HP (pr1 α x) · # (pr1 G) (f · g))
               (street_fib_iso P HP (pr1 α x)
                · # (pr1 F) (f · g)
                · inv_from_iso (street_fib_iso P HP (pr1 α z)))).
        + rewrite !functor_comp.
          rewrite !street_fib_over.
          rewrite !assoc'.
          apply maponpaths.
          refine (!nat_trans_ax α _ _ (f · g) @ _).
          apply maponpaths.
          rewrite assoc.
          rewrite iso_after_iso_inv.
          rewrite id_left.
          apply idpath.
        + apply cartesian_factorization_sfib_over.
        + rewrite functor_comp.
          rewrite !cartesian_factorization_sfib_over.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite (functor_comp F).
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite iso_after_iso_inv.
          apply id_left.
        + apply cartesian_factorization_sfib_commute.
        + rewrite !assoc'.
          rewrite !cartesian_factorization_sfib_commute.
          rewrite !assoc.
          rewrite cartesian_factorization_sfib_commute.
          rewrite (functor_comp G).
          rewrite !assoc'.
          apply idpath.
    Qed.

    Definition street_fib_is_internal_lift
      : C --> E.
    Proof.
      use make_functor.
      - exact street_fib_is_internal_lift_data.
      - exact street_fib_is_internal_lift_is_functor.
    Defined.

    Definition street_fib_is_internal_mor_data
      : nat_trans_data street_fib_is_internal_lift_data (pr1 G)
      := λ x, street_fib_mor _ HP (pr1 α x).

    Definition street_fib_is_internal_mor_is_nat_trans
      : is_nat_trans _ _ street_fib_is_internal_mor_data.
    Proof.
      intros x y f.
      apply cartesian_factorization_sfib_commute.
    Qed.

    Definition street_fib_is_internal_mor
      : street_fib_is_internal_lift ==> G.
    Proof.
      use make_nat_trans.
      - exact street_fib_is_internal_mor_data.
      - exact street_fib_is_internal_mor_is_nat_trans.
    Defined.

    Definition street_fib_is_internal_over_data
      : nat_trans_data (pr1 (street_fib_is_internal_lift · P)) (pr1 F)
      := λ x, street_fib_iso _ HP (pr1 α x).

    Definition street_fib_is_internal_over_is_nat_trans
      : is_nat_trans _ _ street_fib_is_internal_over_data.
    Proof.
      intros x y f.
      cbn ; unfold street_fib_is_internal_over_data.
      rewrite cartesian_factorization_sfib_over.
      rewrite !assoc'.
      apply maponpaths.
      rewrite iso_after_iso_inv.
      apply id_right.
    Qed.

    Definition street_fib_is_internal_over
      : (street_fib_is_internal_lift · P) ==> F.
    Proof.
      use make_nat_trans.
      - exact street_fib_is_internal_over_data.
      - exact street_fib_is_internal_over_is_nat_trans.
    Defined.

    Definition street_fib_is_internal_over_iso
      : nat_iso (street_fib_is_internal_lift · P) F.
    Proof.
      use make_nat_iso.
      - exact street_fib_is_internal_over.
      - intro.
        apply iso_is_iso.
    Defined.

    Definition street_fib_is_internal_over_inv_2cell
      : invertible_2cell (street_fib_is_internal_lift · P) F
      := nat_iso_to_invertible_2cell _ _ street_fib_is_internal_over_iso.

    Definition street_fib_is_internal_over_eq
      : street_fib_is_internal_mor ▹ P
        =
        street_fib_is_internal_over_inv_2cell • α.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply street_fib_over.
    Qed.
  End InternalCleaving.

  Definition  street_fib_is_internal_cleaving
    : internal_sfib_cleaving P.
  Proof.
    intros C F G α.
    refine (street_fib_is_internal_lift α
            ,,
            street_fib_is_internal_mor α
            ,,
            street_fib_is_internal_over_inv_2cell α
            ,,
            _
            ,,
            street_fib_is_internal_over_eq α).
    apply is_cartesian_sfib_to_cartesian_2cell_sfib.
    intro x ; cbn.
    apply street_fib_mor_is_cartesian.
  Defined.

  Definition street_fib_lwhisker_is_cartesian
    : lwhisker_is_cartesian P.
  Proof.
    intros X Y H F G γ Hγ.
    apply is_cartesian_sfib_to_cartesian_2cell_sfib.
    intros x.
    exact (cartesian_2cell_sfib_to_is_cartesian_sfib _ _ Hγ (pr1 H x)).
  Defined.

  Definition street_fib_is_internal_sfib
    : internal_sfib P.
  Proof.
    split.
    - exact street_fib_is_internal_cleaving.
    - exact street_fib_lwhisker_is_cartesian.
  Defined.
End StreetFibIsInternalStreetFib.

Section InternalSFibIsStreetFib.
  Context {E B : univalent_category}
          (F : bicat_of_univ_cats ⟦ E , B ⟧)
          (HF : internal_sfib F).

  Local Definition help_trans
        {x : E}
        {b : B}
        (f : b --> pr1 F x)
    : constant_functor unit_category _ b ⟹ constant_functor unit_category _ x ∙ F.
  Proof.
    use make_nat_trans.
    - exact (λ _, f).
    - abstract
        (intros ? ? ? ; cbn ;
         rewrite functor_id ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition internal_sfib_is_street_fib
    : street_fib F.
  Proof.
    intros x b f.
    pose (n := help_trans f).
    refine (pr1 (internal_sfib_cleaving_lift_mor _ HF n) tt
            ,,
            (pr1 (internal_sfib_cleaving_lift_cell _ HF n) tt
             ,,
             nat_iso_pointwise_iso
               (invertible_2cell_to_nat_iso
                  _ _
                  (internal_sfib_cleaving_com _ HF n))
               tt)
            ,,
            nat_trans_eq_pointwise
              (internal_sfib_cleaving_over _ HF n)
              tt
            ,,
            _) ; simpl.
    refine (cartesian_2cell_sfib_to_is_cartesian_sfib
              F
              (internal_sfib_cleaving_lift_cell F HF n)
              _
              tt).
    apply internal_sfib_cleaving_is_cartesian.
  Defined.
End InternalSFibIsStreetFib.

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
