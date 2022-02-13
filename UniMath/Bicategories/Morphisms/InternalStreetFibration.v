(********************************************************

 Internal Street fibrations

 In this file, we define the notion of Street fibration
 internal to a bicategory.

 1. Definition of an internal Street fibration
 2. Lemmas on cartesians
 3. Street fibrations in locally groupoidal bicategories
 4. Morphisms of internal Street fibrations
 5. Cells of internal Street fibrations

 ********************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.

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
             ,, iso_to_inv2cell (pr212 lift)
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
             ,, (pr12 lift ,, inv2cell_to_iso (pr122 lift))
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

Section PostComposition.
  Context {B : bicat}
          {e b : B}
          (p : e --> b)
          {x : B}
          {f g h : x --> e}
          (α : f ==> g) {β : g ==> h}
          {γ : f ==> h}
          (Hβ : is_cartesian_2cell_sfib p β)
          (Hγ : is_cartesian_2cell_sfib p γ)
          (q : α • β = γ).

  Section PostCompositionFactor.
    Context {k : x --> e}
            {δ : k ==> g}
            (δp : k · p ==> f · p)
            (r : δ ▹ p = δp • (α ▹ p)).

    Definition is_cartesian_2cell_sfib_postcomp_factor
      : k ==> f.
    Proof.
      use (is_cartesian_2cell_sfib_factor _ Hγ (δ • β) δp).
      abstract
        (rewrite <- rwhisker_vcomp ;
         rewrite r ;
         rewrite !vassocl ;
         rewrite rwhisker_vcomp ;
         rewrite q ;
         apply idpath).
    Defined.

    Definition is_cartesian_2cell_sfib_postcomp_comm
      : is_cartesian_2cell_sfib_postcomp_factor • α = δ.
    Proof.
      use (is_cartesian_2cell_sfib_factor_unique
             _
             Hβ
             k
             (δ • β)
             (δ ▹ p)).
      - rewrite rwhisker_vcomp.
        apply idpath.
      - rewrite <- rwhisker_vcomp.
        etrans.
        {
          apply maponpaths_2.
          apply is_cartesian_2cell_sfib_factor_over.
        }
        rewrite r.
        apply idpath.
      - apply idpath.
      - rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          exact q.
        }
        apply is_cartesian_2cell_sfib_factor_comm.
      - apply idpath.
    Qed.

    Definition is_cartesian_2cell_sfib_postcomp_unique
      : isaprop (∑ φ, φ ▹ p = δp × φ • α = δ).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      use (is_cartesian_2cell_sfib_factor_unique
             _
             Hγ
             _
             (δ • β)
             δp).
      - rewrite <- rwhisker_vcomp.
        rewrite r.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite q.
        apply idpath.
      - exact (pr12 φ₁).
      - exact (pr12 φ₂).
      - rewrite <- q.
        rewrite !vassocr.
        apply maponpaths_2.
        exact (pr22 φ₁).
      - rewrite <- q.
        rewrite !vassocr.
        apply maponpaths_2.
        exact (pr22 φ₂).
    Qed.
  End PostCompositionFactor.

  Definition is_cartesian_2cell_sfib_postcomp
    : is_cartesian_2cell_sfib p α.
  Proof.
    intros k δ δp r.
    use iscontraprop1.
    - exact (is_cartesian_2cell_sfib_postcomp_unique δp r).
    - simple refine (_ ,, _ ,, _).
      + exact (is_cartesian_2cell_sfib_postcomp_factor δp r).
      + apply is_cartesian_2cell_sfib_factor_over.
      + exact (is_cartesian_2cell_sfib_postcomp_comm δp r).
  Defined.
End PostComposition.

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

Definition map_between_cartesians
           {B : bicat}
           {x e b : B}
           {p : e --> b}
           {g₀ g₁ g₂ : x --> e}
           {α : g₀ ==> g₂}
           (Hα : is_cartesian_2cell_sfib p α)
           {β : g₁ ==> g₂}
           (Hβ : is_cartesian_2cell_sfib p β)
           (δ : invertible_2cell (g₀ · p) (g₁ · p))
           (r : α ▹ p = δ • (β ▹ p))
  : g₀ ==> g₁
  := is_cartesian_2cell_sfib_factor _ Hβ α δ r.

Section InvertibleBetweenCartesians.
  Context {B : bicat}
          {x e b : B}
          {p : e --> b}
          {g₀ g₁ g₂ : x --> e}
          {α : g₀ ==> g₂}
          (Hα : is_cartesian_2cell_sfib p α)
          {β : g₁ ==> g₂}
          (Hβ : is_cartesian_2cell_sfib p β)
          (δ : invertible_2cell (g₀ · p) (g₁ · p))
          (r : α ▹ p = δ • (β ▹ p)).

  Let φ : g₀ ==> g₁ := map_between_cartesians Hα Hβ δ r.

  Local Lemma invertible_between_cartesians_help
    : β ▹ p = δ^-1 • (α ▹ p).
  Proof.
    cbn.
    use vcomp_move_L_pM ; is_iso ; cbn.
    exact (!r).
  Qed.

  Let ψ : g₁ ==> g₀
    := map_between_cartesians
         Hβ Hα
         (inv_of_invertible_2cell δ)
         invertible_between_cartesians_help.

  Local Lemma invertible_between_cartesians_inv₁
    : φ • ψ = id₂ _.
  Proof.
    use (is_cartesian_2cell_sfib_factor_unique _ Hα _ α (id2 _)).
    - rewrite id2_left.
      apply idpath.
    - unfold φ, ψ, map_between_cartesians.
      rewrite <- rwhisker_vcomp.
      rewrite !is_cartesian_2cell_sfib_factor_over.
      apply (vcomp_rinv δ).
    - apply id2_rwhisker.
    - unfold φ, ψ, map_between_cartesians.
      rewrite !vassocl.
      rewrite !is_cartesian_2cell_sfib_factor_comm.
      apply idpath.
    - apply id2_left.
  Qed.

  Local Lemma invertible_between_cartesians_inv₂
    : ψ • φ = id₂ _.
  Proof.
    use (is_cartesian_2cell_sfib_factor_unique _ Hβ _ β (id2 _)).
    - rewrite id2_left.
      apply idpath.
    - unfold φ, ψ, map_between_cartesians.
      rewrite <- rwhisker_vcomp.
      rewrite !is_cartesian_2cell_sfib_factor_over.
      apply (vcomp_linv δ).
    - apply id2_rwhisker.
    - unfold φ, ψ, map_between_cartesians.
      rewrite !vassocl.
      rewrite !is_cartesian_2cell_sfib_factor_comm.
      apply idpath.
    - apply id2_left.
  Qed.

  Definition invertible_between_cartesians
    : invertible_2cell g₀ g₁.
  Proof.
    use make_invertible_2cell.
    - exact φ.
    - use make_is_invertible_2cell.
      + exact ψ.
      + exact invertible_between_cartesians_inv₁.
      + exact invertible_between_cartesians_inv₂.
  Defined.
End InvertibleBetweenCartesians.

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
 4. Morphisms of internal Street fibrations
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

Definition invertible_2cell_between_preserves_cartesian
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe₁ fe₂ : e₁ --> e₂}
           (α : invertible_2cell fe₁ fe₂)
           (H : mor_preserves_cartesian p₁ p₂ fe₁)
  : mor_preserves_cartesian p₁ p₂ fe₂.
Proof.
  intros x f g γ Hγ.
  assert (γ ▹ fe₂ • (_ ◃ α^-1) = (f ◃ α^-1) • (γ ▹ fe₁)) as p.
  {
    rewrite vcomp_whisker.
    apply idpath.
  }
  use (is_cartesian_2cell_sfib_postcomp _ _ _ _ p).
  - use invertible_is_cartesian_2cell_sfib.
    is_iso.
  - use vcomp_is_cartesian_2cell_sfib.
    + use invertible_is_cartesian_2cell_sfib.
      is_iso.
    + exact (H x f g γ Hγ).
Defined.

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
 5. Cells of internal Street fibrations
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




(*
(**
 11. Pullbacks of Street fibrations
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

  Section ToPBCartesian.
    Context {x : B}
            {g₁ g₂ : x --> e₁}
            (α : g₁ ==> g₂)
            (Hα : is_cartesian_2cell_sfib p₂ (α ▹ fe))
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
             {x : B}
             {g₁ g₂ : x --> e₁}
             (α : g₁ ==> g₂)
             (Hα : is_cartesian_2cell_sfib p₂ (α ▹ fe))
    : is_cartesian_2cell_sfib p₁ α.
  Proof.
    intros h β δp q.
    use iscontraprop1.
    - exact (to_pb_cartesian_unique α Hα q).
    - simple refine (_ ,, _ ,, _).
      + exact (to_pb_cartesian_cell α Hα q).
      + apply (pb_ump_cell_pr2 H).
      + exact (to_pb_cartesian_comm α Hα q).
  Defined.

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

    Definition pb_of_sfib_cleaving_cell_is_cartesian_2cell_sfib
      : is_cartesian_2cell_sfib p₁ pb_of_sfib_cleaving_cell.
    Proof.
      apply to_pb_cartesian.
      refine (is_cartesian_eq _ (!(pb_ump_cell_pr1 H _ _ _ _ _)) _).
      use vcomp_is_cartesian_2cell_sfib.
      - apply invertible_is_cartesian_2cell_sfib.
        apply property_from_invertible_2cell.
      - apply internal_sfib_cleaving_is_cartesian.
    Defined.
  End Cleaving.

  Definition pb_of_sfib_cleaving
    : internal_sfib_cleaving p₁
    := λ x h₁ h₂ α,
       pb_of_sfib_cleaving_mor α
       ,,
       pb_of_sfib_cleaving_cell α
       ,,
       pb_of_sfib_cleaving_over α
       ,,
       pb_of_sfib_cleaving_cell_is_cartesian_2cell_sfib α
       ,,
       pb_of_sfib_cleaving_commute α.

  Section FromPBCartesian.
    Context {x : B}
            {g₁ g₂ : x --> e₁}
            (α : g₁ ==> g₂)
            (Hα : is_cartesian_2cell_sfib p₁ α).

    Let g₀ : x --> e₁
      := pb_of_sfib_cleaving_mor (α ▹ p₁).

    Let β : g₀ ==> g₂
      := pb_of_sfib_cleaving_cell (α ▹ p₁).

    Let Hβ : is_cartesian_2cell_sfib p₁ β.
    Proof.
      apply pb_of_sfib_cleaving_cell_is_cartesian_2cell_sfib.
    Defined.

    Local Lemma path_for_invertible_between_cartesians
      : α ▹ p₁ = (pb_of_sfib_cleaving_over (α ▹ p₁))^-1 • (β ▹ p₁).
    Proof.
      unfold β.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply pb_of_sfib_cleaving_commute.
      }
      rewrite !vassocr.
      rewrite vcomp_linv.
      apply id2_left.
    Qed.

    Let δ : invertible_2cell g₁ g₀
      := invertible_between_cartesians
           Hα
           Hβ
           (inv_of_invertible_2cell (pb_of_sfib_cleaving_over (α ▹ p₁)))
           path_for_invertible_between_cartesians.

    Definition from_pb_cartesian
      : is_cartesian_2cell_sfib p₂ (α ▹ fe).
    Proof.
      assert (p : δ • β = α).
      {
        apply is_cartesian_2cell_sfib_factor_comm.
      }
      use (is_cartesian_eq _ (maponpaths (λ z, z ▹ fe) p)).
      use (is_cartesian_eq _ (rwhisker_vcomp _ _ _)).
      use vcomp_is_cartesian_2cell_sfib.
      - apply invertible_is_cartesian_2cell_sfib.
        is_iso.
        apply property_from_invertible_2cell.
      - unfold β, pb_of_sfib_cleaving_cell.
        rewrite (pb_ump_cell_pr1 H).
        use vcomp_is_cartesian_2cell_sfib.
        + apply invertible_is_cartesian_2cell_sfib.
          apply property_from_invertible_2cell.
        + apply internal_sfib_cleaving_is_cartesian.
    Defined.
  End FromPBCartesian.

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

  Definition mor_preserves_cartesian_pb_pr1
    : mor_preserves_cartesian p₁ p₂ fe.
  Proof.
    intros x f g δ Hδ.
    apply from_pb_cartesian.
    exact Hδ.
  Defined.

  Definition mor_preserves_cartesian_pb_ump_mor
             {e₀ b₀ : B}
             (p₀ : e₀ --> b₀)
             (h₁ : e₀ --> e₂)
             (h₂ : b₀ --> b₁)
             (δ : invertible_2cell (h₁ · p₂) (p₀ · h₂ · fb))
             (cone := make_pb_cone e₀ h₁ (p₀ · h₂) δ)
             (Hh₁ : mor_preserves_cartesian p₀ p₂ h₁)
    : mor_preserves_cartesian
        p₀
        p₁
        (pb_ump_mor H cone).
  Proof.
    intros x f g ζ Hζ.
    apply to_pb_cartesian.
    assert (H₁ : is_cartesian_2cell_sfib p₂ (rassociator g (pb_ump_mor H cone) fe)) .
    {
      apply invertible_is_cartesian_2cell_sfib.
      is_iso.
    }
    assert (H₂ : is_cartesian_2cell_sfib p₂ ((g ◃ pb_ump_mor_pr1 H cone))).
    {
      apply invertible_is_cartesian_2cell_sfib.
      is_iso.
      apply property_from_invertible_2cell.
    }
    assert (H₃ : is_cartesian_2cell_sfib
                   p₂
                   (rassociator f (pb_ump_mor H cone) fe
                    • ((f ◃ pb_ump_mor_pr1 H cone)
                    • (ζ ▹ pb_cone_pr1 cone)))).
    {
      use vcomp_is_cartesian_2cell_sfib.
      - apply invertible_is_cartesian_2cell_sfib.
        is_iso.
      - use vcomp_is_cartesian_2cell_sfib.
        + apply invertible_is_cartesian_2cell_sfib.
          is_iso.
          apply property_from_invertible_2cell.
        + apply Hh₁.
          exact Hζ.
    }
    use (is_cartesian_2cell_sfib_postcomp
           p₂
           _
           (vcomp_is_cartesian_2cell_sfib _ H₁ H₂)
           H₃).
    abstract
      (rewrite vassocr ;
       rewrite rwhisker_rwhisker_alt ;
       rewrite vassocl ;
       rewrite vcomp_whisker ;
       apply idpath).
  Defined.
End PullbackOfSFib.
 *)
