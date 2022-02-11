(********************************************************

 Internal Street opfibrations

 In this file, we define the notion of Street opfibration
 internal to a bicategory.

 1. Definition of an internal Street opfibration
 2. Street opfibrations in [B] are the same as Street fibrations in [op2_bicat B]
 3. Properties of opcartesian cells
 4. Identity opfibration
 5. Projection is an opfibration
 6. Composition of Street opfibrations
 7. Internal Street opfibrations of categories
 8. Morphisms of internal Street opfibrations
 9. Cells of internal Street opfibrations
 10. Equivalences preserve cartesian cells
 11. Pullbacks of Street opfibrations

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
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.

Local Open Scope cat.

(**
 1. Definition of an internal Street opfibration
 *)
Section InternalStreetOpFibration.
  Context {B : bicat}
          {e b : B}
          (p : e --> b).

  Definition is_opcartesian_2cell_sopfib
             {x : B}
             {f g : x --> e}
             (γ : f ==> g)
    : UU
    := ∏ (h : x --> e)
         (α : f ==> h)
         (δp : g · p ==> h · p)
         (q : α ▹ p = (γ ▹ p) • δp),
       ∃! (δ : g ==> h),
       δ ▹ p = δp
       ×
       γ • δ = α.

  Definition is_opcartesian_2cell_sopfib_factor
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_opcartesian_2cell_sopfib γ)
             {h : x --> e}
             (α : f ==> h)
             (δp : g · p ==> h · p)
             (q : α ▹ p = (γ ▹ p) • δp)
    : g ==> h
    := pr11 (Hγ h α δp q).

  Definition is_opcartesian_2cell_sopfib_factor_over
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_opcartesian_2cell_sopfib γ)
             {h : x --> e}
             (α : f ==> h)
             (δp : g · p ==> h · p)
             (q : α ▹ p = (γ ▹ p) • δp)
    : (is_opcartesian_2cell_sopfib_factor Hγ _ _ q) ▹ p = δp
    := pr121 (Hγ h α δp q).

  Definition is_opcartesian_2cell_sopfib_factor_comm
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_opcartesian_2cell_sopfib γ)
             {h : x --> e}
             (α : f ==> h)
             (δp : g · p ==> h · p)
             (q : α ▹ p = (γ ▹ p) • δp)
    : γ • is_opcartesian_2cell_sopfib_factor Hγ _ _ q = α
    := pr221 (Hγ h α δp q).

  Definition is_opcartesian_2cell_sopfib_factor_unique
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_opcartesian_2cell_sopfib γ)
             (h : x --> e)
             (α : f ==> h)
             (δp : g · p ==> h · p)
             (q : α ▹ p = (γ ▹ p) • δp)
             (δ₁ δ₂ : g ==> h)
             (pδ₁ : δ₁ ▹ p = δp)
             (pδ₂ : δ₂ ▹ p = δp)
             (δγ₁ : γ • δ₁ = α)
             (δγ₂ : γ • δ₂ = α)
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

  Definition isaprop_is_opcartesian_2cell_sopfib
             {x : B}
             {f : x --> e}
             {g : x --> e}
             (γ : f ==> g)
    : isaprop (is_opcartesian_2cell_sopfib γ).
  Proof.
    do 4 (use impred ; intro).
    apply isapropiscontr.
  Qed.

  Definition internal_sopfib_opcleaving
    : UU
    := ∏ (x : B)
         (f : x --> e)
         (g : x --> b)
         (α : f · p ==> g),
       ∑ (h : x --> e)
         (γ : f ==> h)
         (β : invertible_2cell g (h · p)),
       is_opcartesian_2cell_sopfib γ
       ×
       γ ▹ p = α • β.

  Definition internal_sopfib_opcleaving_lift_mor
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : x --> e
    := pr1 (H _ _ _ α).

  Definition internal_sopfib_opcleaving_lift_cell
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : f ==> internal_sopfib_opcleaving_lift_mor H α
    := pr12 (H _ _ _ α).

  Definition internal_sopfib_opcleaving_com
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : invertible_2cell g (internal_sopfib_opcleaving_lift_mor H α · p)
    := pr122 (H _ _ _ α).

  Definition internal_sopfib_opcleaving_is_opcartesian
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : is_opcartesian_2cell_sopfib (internal_sopfib_opcleaving_lift_cell H α)
    := pr1 (pr222 (H _ _ _ α)).

  Definition internal_sopfib_opcleaving_over
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : internal_sopfib_opcleaving_lift_cell H α ▹ p
      =
      α • internal_sopfib_opcleaving_com H α
    := pr2 (pr222 (H _ _ _ α)).

  Definition lwhisker_is_opcartesian
    : UU
    := ∏ (x y : B)
         (h : y --> x)
         (f g : x --> e)
         (γ : f ==> g)
         (Hγ : is_opcartesian_2cell_sopfib γ),
       is_opcartesian_2cell_sopfib (h ◃ γ).

  Definition internal_sopfib
    : UU
    := internal_sopfib_opcleaving × lwhisker_is_opcartesian.

  Coercion internal_sopfib_to_opcleaving
           (H : internal_sopfib)
    : internal_sopfib_opcleaving
    := pr1 H.
End InternalStreetOpFibration.

(**
 2. Street opfibrations in [B] are the same as Street fibrations in [op2_bicat B]
 *)
Definition is_cartesian_to_is_opcartesian_sfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           {x : B}
           {f g : x --> e}
           {α : f ==> g}
           (Hα : @is_cartesian_2cell_sfib (op2_bicat B) e b p x g f α)
  : is_opcartesian_2cell_sopfib p α.
Proof.
  intros h γ δp q.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros δ₁ δ₂ ;
       use subtypePath ;
       [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
       exact (is_cartesian_2cell_sfib_factor_unique
                _
                Hα
                _
                γ
                δp
                q
                _ _
                (pr12 δ₁)
                (pr12 δ₂)
                (pr22 δ₁)
                (pr22 δ₂))).
  - exact (is_cartesian_2cell_sfib_factor _ Hα γ δp q
           ,,
           is_cartesian_2cell_sfib_factor_over _ Hα q
           ,,
           is_cartesian_2cell_sfib_factor_comm _ Hα q).
Defined.

Definition is_opcartesian_to_is_cartesian_sfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           {x : B}
           {f g : x --> e}
           {α : f ==> g}
           (Hα : is_opcartesian_2cell_sopfib p α)
  : @is_cartesian_2cell_sfib (op2_bicat B) e b p x g f α.
Proof.
  intros h γ δp q.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros δ₁ δ₂ ;
       use subtypePath ;
       [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
       exact (is_opcartesian_2cell_sopfib_factor_unique
                _
                Hα
                _
                γ
                δp
                q
                _ _
                (pr12 δ₁)
                (pr12 δ₂)
                (pr22 δ₁)
                (pr22 δ₂))).
  - exact (is_opcartesian_2cell_sopfib_factor _ Hα γ δp q
           ,,
           is_opcartesian_2cell_sopfib_factor_over _ Hα _ _ q
           ,,
           is_opcartesian_2cell_sopfib_factor_comm _ Hα _ _ q).
Defined.

Definition is_cartesian_weq_is_opcartesian_sfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           {x : B}
           {f g : x --> e}
           (α : f ==> g)
  : @is_cartesian_2cell_sfib (op2_bicat B) e b p x g f α
    ≃
    is_opcartesian_2cell_sopfib p α.
Proof.
  use weqimplimpl.
  - exact is_cartesian_to_is_opcartesian_sfib.
  - exact is_opcartesian_to_is_cartesian_sfib.
  - apply isaprop_is_cartesian_2cell_sfib.
  - apply isaprop_is_opcartesian_2cell_sopfib.
Defined.

Definition internal_sfib_is_internal_sopfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           (Hp : @internal_sfib (op2_bicat B) e b p)
  : internal_sopfib p.
Proof.
  split.
  - intros x f g α.
    refine (internal_sfib_cleaving_lift_mor _ Hp α
            ,,
            internal_sfib_cleaving_lift_cell _ Hp α
            ,,
            bicat_invertible_2cell_is_op2_bicat_invertible_2cell
              _
              _
              (internal_sfib_cleaving_com _ Hp α)
            ,,
            _
            ,,
            internal_sfib_cleaving_over _ Hp α).
    apply is_cartesian_to_is_opcartesian_sfib.
    exact (internal_sfib_cleaving_is_cartesian _ Hp α).
  - intros x y h f g γ Hγ.
    apply is_cartesian_to_is_opcartesian_sfib.
    apply (pr2 Hp).
    apply is_opcartesian_to_is_cartesian_sfib.
    exact Hγ.
Defined.

Definition internal_sopfib_is_internal_sfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           (Hp : internal_sopfib p)
  : @internal_sfib (op2_bicat B) e b p.
Proof.
  split.
  - intros x f g α.
    refine (internal_sopfib_opcleaving_lift_mor _ Hp α
            ,,
            internal_sopfib_opcleaving_lift_cell _ Hp α
            ,,
            bicat_invertible_2cell_is_op2_bicat_invertible_2cell
              _ _
              (internal_sopfib_opcleaving_com _  Hp α)
            ,,
            _
            ,,
            internal_sopfib_opcleaving_over _ Hp α).
    apply is_opcartesian_to_is_cartesian_sfib.
    exact (internal_sopfib_opcleaving_is_opcartesian _ Hp α).
  - intros x y h f g γ Hγ.
    apply is_opcartesian_to_is_cartesian_sfib.
    apply (pr2 Hp).
    apply is_cartesian_to_is_opcartesian_sfib.
    exact Hγ.
Defined.

Definition internal_sopfib_weq_internal_sfib_inv_left
           {B : bicat}
           {e b : B}
           {p : e --> b}
           (Hp : @internal_sfib (op2_bicat B) e b p)
  : internal_sopfib_is_internal_sfib
      (internal_sfib_is_internal_sopfib Hp)
    =
    Hp.
Proof.
  use pathsdirprod ;
    repeat (use funextsec ; intro) ;
    repeat (refine (maponpaths (λ z, _ ,, z) _)).
  - use pathsdirprod.
    + apply isaprop_is_cartesian_2cell_sfib.
    + apply idpath.
  - apply isapropiscontr.
Qed.

Definition internal_sopfib_weq_internal_sfib_inv_right
           {B : bicat}
           {e b : B}
           {p : e --> b}
           (Hp : internal_sopfib p)
  : internal_sfib_is_internal_sopfib
      (internal_sopfib_is_internal_sfib Hp)
    =
    Hp.
Proof.
  use pathsdirprod ;
    repeat (use funextsec ; intro) ;
    repeat (refine (maponpaths (λ z, _ ,, z) _)).
  - use pathsdirprod.
    + apply isaprop_is_opcartesian_2cell_sopfib.
    + apply idpath.
  - apply isapropiscontr.
Qed.

Definition internal_sopfib_weq_internal_sfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
  : @internal_sfib (op2_bicat B) e b p ≃ internal_sopfib p.
Proof.
  use make_weq.
  - exact internal_sfib_is_internal_sopfib.
  - use gradth.
    + exact internal_sopfib_is_internal_sfib.
    + exact internal_sopfib_weq_internal_sfib_inv_left.
    + exact internal_sopfib_weq_internal_sfib_inv_right.
Defined.

Definition isaprop_internal_sopfib
           {B : bicat}
           (HB_2_1 : is_univalent_2_1 B)
           {e b : B}
           (p : e --> b)
  : isaprop (internal_sopfib p).
Proof.
  use (isofhlevelweqf _ (internal_sopfib_weq_internal_sfib p)).
  apply isaprop_internal_sfib.
  apply op2_bicat_is_univalent_2_1.
  exact HB_2_1.
Qed.

(**
 3. Properties of opcartesian cells
 *)
Definition id_is_opcartesian_2cell_sopfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           (f : x --> e)
  : is_opcartesian_2cell_sopfib p (id2 f).
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  apply (@id_is_cartesian_2cell_sfib (op2_bicat B)).
Defined.

Definition vcomp_is_opcartesian_2cell_sopfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g h : x --> e}
           {α : f ==> g}
           {β : g ==> h}
           (Hα : is_opcartesian_2cell_sopfib p α)
           (Hβ : is_opcartesian_2cell_sopfib p β)
  : is_opcartesian_2cell_sopfib p (α • β).
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  use vcomp_is_cartesian_2cell_sfib.
  - apply is_opcartesian_to_is_cartesian_sfib.
    exact Hβ.
  - apply is_opcartesian_to_is_cartesian_sfib.
    exact Hα.
Defined.

Definition invertible_is_opcartesian_2cell_sopfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g : x --> e}
           (α : f ==> g)
           (Hα : is_invertible_2cell α)
  : is_opcartesian_2cell_sopfib p α.
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  apply invertible_is_cartesian_2cell_sfib.
  apply bicat_is_invertible_2cell_to_op2_bicat_is_invertible_2cell.
  exact Hα.
Defined.

Definition locally_grpd_opcartesian
           {B : bicat}
           (HB : locally_groupoid B)
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g : x --> e}
           (γ : f ==> g)
  : is_opcartesian_2cell_sopfib p γ.
Proof.
  apply invertible_is_opcartesian_2cell_sopfib.
  apply HB.
Defined.

Definition is_opcartesian_2cell_sopfib_precomp
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g h : x --> e}
           (α : f ==> g) {β : g ==> h}
           {γ : f ==> h}
           (Hα : is_opcartesian_2cell_sopfib p α)
           (Hγ : is_opcartesian_2cell_sopfib p γ)
           (q : α • β = γ)
  : is_opcartesian_2cell_sopfib p β.
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  refine (@is_cartesian_2cell_sfib_postcomp
           (op2_bicat B)
           _ _ _ _ _ _ _
           β α γ
           _ _ _).
  - apply is_opcartesian_to_is_cartesian_sfib.
    exact Hα.
  - apply is_opcartesian_to_is_cartesian_sfib.
    exact Hγ.
  - exact q.
Defined.

(**
 4. Identity opfibration
 *)
Definition identity_internal_sopfib
           {B : bicat}
           (b : B)
  : internal_sopfib (id₁ b).
Proof.
  apply internal_sfib_is_internal_sopfib.
  exact (@identity_internal_sfib (op2_bicat B) b).
Defined.

(**
 5. Projection is an opfibration
 *)
Section ProjectionSOpFib.
  Context {B : bicat_with_binprod}
          (b₁ b₂ : B).

  Section InvertibleToOpCartesian.
    Context {a : B}
            {f g : a --> b₁ ⊗ b₂}
            (α : f ==> g)
            (Hα : is_invertible_2cell (α ▹ π₂)).

    Definition invertible_to_opcartesian_unique
               (h : a --> b₁ ⊗ b₂)
               (β : f ==> h)
               (δp : g · π₁ ==> h · π₁)
               (q : β ▹ π₁ = (α ▹ π₁) • δp)
      : isaprop (∑ (δ : g ==> h), δ ▹ π₁ = δp × α • δ = β).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
      use binprod_ump_2cell_unique_alt.
      - apply (pr2 B).
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - use (vcomp_lcancel _ Hα).
        rewrite !rwhisker_vcomp.
        apply maponpaths.
        exact (pr22 φ₁ @ !(pr22 φ₂)).
    Qed.

    Definition invertible_to_opcartesian
      : is_opcartesian_2cell_sopfib π₁ α.
    Proof.
      intros h β δp q.
      use iscontraprop1.
      - exact (invertible_to_opcartesian_unique h β δp q).
      - simple refine (_ ,, _ ,, _).
        + use binprod_ump_2cell.
          * apply (pr2 B).
          * exact δp.
          * exact (Hα^-1 • (β ▹ _)).
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
               rewrite !vassocr ;
               rewrite vcomp_rinv ;
               apply id2_left).
    Defined.
  End InvertibleToOpCartesian.
  (*
  Section OpCartesianToInvertible.
    Context {a : B}
            {f g : a --> b₁ ⊗ b₂}
            (α : f ==> g)
            (Hα : is_opcartesian_2cell_sopfib π₁ α).

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
   *)
End ProjectionSOpFib.

(**
 8. Morphisms of internal Street opfibrations
 *)
Definition mor_preserves_opcartesian
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
       (Hγ : is_opcartesian_2cell_sopfib p₁ γ),
     is_opcartesian_2cell_sopfib p₂ (γ ▹ fe).

Definition mor_preserves_cartesian_to_mor_preserves_opcartesian
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           (H : @mor_preserves_cartesian
                  (op2_bicat B)
                  e₁ b₁ p₁
                  e₂ b₂ p₂
                  fe)
  : mor_preserves_opcartesian p₁ p₂ fe.
Proof.
  intros x f g γ Hγ.
  apply is_cartesian_to_is_opcartesian_sfib.
  apply H.
  apply is_opcartesian_to_is_cartesian_sfib.
  exact Hγ.
Defined.

Definition mor_preserves_opcartesian_to_mor_preserves_cartesian
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           (H : mor_preserves_opcartesian p₁ p₂ fe)
  : @mor_preserves_cartesian
      (op2_bicat B)
      e₁ b₁ p₁
      e₂ b₂ p₂
      fe.
Proof.
  intros x f g γ Hγ.
  apply is_opcartesian_to_is_cartesian_sfib.
  apply H.
  apply is_cartesian_to_is_opcartesian_sfib.
  exact Hγ.
Defined.

Definition id_mor_preserves_opcartesian
           {B : bicat}
           {e b : B}
           (p : e --> b)
  : mor_preserves_opcartesian p p (id₁ e).
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
  use vcomp_is_opcartesian_2cell_sopfib.
  - use vcomp_is_opcartesian_2cell_sopfib.
    + use invertible_is_opcartesian_2cell_sopfib.
      is_iso.
    + exact H.
  - use invertible_is_opcartesian_2cell_sopfib.
    is_iso.
Qed.

Definition comp_preserves_opcartesian
           {B : bicat}
           {e₁ b₁ e₂ b₂ e₃ b₃ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {p₃ : e₃ --> b₃}
           {fe₁ : e₁ --> e₂}
           {fe₂ : e₂ --> e₃}
           (H₁ : mor_preserves_opcartesian p₁ p₂ fe₁)
           (H₂ : mor_preserves_opcartesian p₂ p₃ fe₂)
  : mor_preserves_opcartesian p₁ p₃ (fe₁ · fe₂).
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
  use vcomp_is_opcartesian_2cell_sopfib.
  - use vcomp_is_opcartesian_2cell_sopfib.
    + use invertible_is_opcartesian_2cell_sopfib.
      is_iso.
    + exact H₂.
  - use invertible_is_opcartesian_2cell_sopfib.
    is_iso.
Qed.

Definition invertible_2cell_between_preserves_opcartesian
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe₁ fe₂ : e₁ --> e₂}
           (α : invertible_2cell fe₁ fe₂)
           (H : mor_preserves_opcartesian p₁ p₂ fe₁)
  : mor_preserves_opcartesian p₁ p₂ fe₂.
Proof.
  intros x f g γ Hγ.
  assert ((_ ◃ α) • (γ ▹ fe₂) = (γ ▹ fe₁) • (_ ◃ α)) as p.
  {
    rewrite vcomp_whisker.
    apply idpath.
  }
  use (is_opcartesian_2cell_sopfib_precomp _ _ _ _ p).
  - use invertible_is_opcartesian_2cell_sopfib.
    is_iso.
    apply property_from_invertible_2cell.
  - use vcomp_is_opcartesian_2cell_sopfib.
    + exact (H x f g γ Hγ).
    + use invertible_is_opcartesian_2cell_sopfib.
      is_iso.
      apply property_from_invertible_2cell.
Defined.

Definition locally_grpd_preserves_opcartesian
           {B : bicat}
           (HB : locally_groupoid B)
           {e₁ b₁ e₂ b₂ : B}
           (p₁ : e₁ --> b₁)
           (p₂ : e₂ --> b₂)
           (fe : e₁ --> e₂)
  : mor_preserves_opcartesian p₁ p₂ fe.
Proof.
  intro ; intros.
  apply (locally_grpd_opcartesian HB).
Defined.

Definition isaprop_mor_preserves_opcartesian
           {B : bicat}
           {e₁ b₁ : B}
           (p₁ : e₁ --> b₁)
           {e₂ b₂ : B}
           (p₂ : e₂ --> b₂)
           (fe : e₁ --> e₂)
  : isaprop (mor_preserves_opcartesian p₁ p₂ fe).
Proof.
  do 5 (use impred ; intro).
  exact (isaprop_is_opcartesian_2cell_sopfib _ _).
Qed.

Definition mor_of_internal_sopfib_over
           {B : bicat}
           {e₁ b₁ : B}
           (p₁ : e₁ --> b₁)
           {e₂ b₂ : B}
           (p₂ : e₂ --> b₂)
           (fb : b₁ --> b₂)
  : UU
  := ∑ (fe : e₁ --> e₂),
     mor_preserves_opcartesian p₁ p₂ fe
     ×
     invertible_2cell (p₁ · fb) (fe · p₂).

Definition make_mor_of_internal_sopfib_over
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : e₁ --> e₂)
           (fc : mor_preserves_opcartesian p₁ p₂ fe)
           (f_com : invertible_2cell (p₁ · fb) (fe · p₂))
  : mor_of_internal_sopfib_over p₁ p₂ fb
  := (fe ,, fc ,, f_com).

Coercion mor_of_internal_sopfib_over_to_mor
         {B : bicat}
         {e₁ b₁ : B}
         {p₁ : e₁ --> b₁}
         {e₂ b₂ : B}
         {p₂ : e₂ --> b₂}
         {fb : b₁ --> b₂}
         (fe : mor_of_internal_sopfib_over p₁ p₂ fb)
  : e₁ --> e₂
  := pr1 fe.

Definition mor_of_internal_sopfib_over_preserves
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : mor_of_internal_sopfib_over p₁ p₂ fb)
  : mor_preserves_opcartesian p₁ p₂ fe
  := pr12 fe.

Definition mor_of_internal_sopfib_over_com
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : mor_of_internal_sopfib_over p₁ p₂ fb)
  : invertible_2cell (p₁ · fb) (fe · p₂)
  := pr22 fe.

Definition id_mor_of_internal_sopfib_over
           {B : bicat}
           {e b : B}
           (p : e --> b)
  : mor_of_internal_sopfib_over p p (id₁ _).
Proof.
  use make_mor_of_internal_sopfib_over.
  - exact (id₁ e).
  - apply id_mor_preserves_opcartesian.
  - use make_invertible_2cell.
    + refine (runitor _ • linvunitor _).
    + is_iso.
Defined.

Definition comp_mor_of_internal_sopfib_over
           {B : bicat}
           {e₁ e₂ e₃ b₁ b₂ b₃ : B}
           {fb₁ : b₁ --> b₂}
           {fb₂ : b₂ --> b₃}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {p₃ : e₃ --> b₃}
           (fe₁ : mor_of_internal_sopfib_over p₁ p₂ fb₁)
           (fe₂ : mor_of_internal_sopfib_over p₂ p₃ fb₂)
  : mor_of_internal_sopfib_over p₁ p₃ (fb₁ · fb₂).
Proof.
  use make_mor_of_internal_sopfib_over.
  - exact (fe₁ · fe₂).
  - exact (comp_preserves_opcartesian
             (mor_of_internal_sopfib_over_preserves fe₁)
             (mor_of_internal_sopfib_over_preserves fe₂)).
  - use make_invertible_2cell.
    + exact (lassociator _ _ _
             • (mor_of_internal_sopfib_over_com fe₁ ▹ _)
             • rassociator _ _ _
             • (_ ◃ mor_of_internal_sopfib_over_com fe₂)
             • lassociator _ _ _).
    + is_iso.
      * apply property_from_invertible_2cell.
      * apply property_from_invertible_2cell.
Defined.

(**
 9. Cells of internal Street opfibrations
 *)
Definition cell_of_internal_sopfib_over_homot
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           (γ : fb ==> gb)
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
           (γe : fe ==> ge)
  : UU
  := mor_of_internal_sopfib_over_com fe • (γe ▹ _)
     =
     (_ ◃ γ) • mor_of_internal_sopfib_over_com ge.


Definition cell_of_internal_sopfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           (γ : fb ==> gb)
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           (fe : mor_of_internal_sopfib_over p₁ p₂ fb)
           (ge : mor_of_internal_sopfib_over p₁ p₂ gb)
  : UU
  := ∑ (γe : fe ==> ge), cell_of_internal_sopfib_over_homot γ γe.

Definition make_cell_of_internal_sopfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
           (γe : fe ==> ge)
           (p : cell_of_internal_sopfib_over_homot γ γe)
  : cell_of_internal_sopfib_over γ fe ge
  := (γe ,, p).

Coercion cell_of_cell_of_internal_sopfib_over
         {B : bicat}
         {b₁ b₂ e₁ e₂ : B}
         {fb gb : b₁ --> b₂}
         {γ : fb ==> gb}
         {p₁ : e₁ --> b₁}
         {p₂ : e₂ --> b₂}
         {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
         {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
         (γe : cell_of_internal_sopfib_over γ fe ge)
  : fe ==> ge
  := pr1 γe.

Definition cell_of_internal_sopfib_over_eq
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
           (γe : cell_of_internal_sopfib_over γ fe ge)
  : mor_of_internal_sopfib_over_com fe • (γe ▹ _)
     =
     (_ ◃ γ) • mor_of_internal_sopfib_over_com ge
  := pr2 γe.

Definition eq_cell_of_internal_sopfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
           (γe₁ γe₂ : cell_of_internal_sopfib_over γ fe ge)
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
 10. Equivalences preserve cartesian cells
 *)
Definition equivalence_preserves_opcartesian
           {B : bicat}
           {b e₁ e₂ : B}
           (p₁ : e₁ --> b)
           (p₂ : e₂ --> b)
           (L : e₁ --> e₂)
           (com : invertible_2cell p₁ (L · p₂))
           (HL : left_adjoint_equivalence L)
           (HB_2_0 : is_univalent_2_0 B)
           (HB_2_1 : is_univalent_2_1 B)
  : mor_preserves_opcartesian p₁ p₂ L.
Proof.
  refine (J_2_0
            HB_2_0
            (λ (x₁ x₂ : B) (L : adjoint_equivalence x₁ x₂),
             ∏ (p₁ : x₁ --> b)
               (p₂ : x₂ --> b)
               (c : invertible_2cell p₁ (L · p₂)),
             mor_preserves_opcartesian p₁ p₂ L)
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
             mor_preserves_opcartesian f g (id₁ _))
            _
            c).
  intros.
  apply id_mor_preserves_opcartesian.
Defined.

(**
 11. Pullbacks of Street opfibrations
 *)
Definition pb_of_sopfib
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (pb := make_pb_cone e₁ fe p₁ γ)
           (H : has_pb_ump pb)
           (Hf : internal_sopfib p₂)
  : internal_sopfib p₁.
Proof.
  apply internal_sfib_is_internal_sopfib.
  use (@pb_of_sfib
         (op2_bicat B)
         e₁ e₂ b₁ b₂
         p₁ p₂ fe fb).
  - apply bicat_invertible_2cell_is_op2_bicat_invertible_2cell.
    exact (inv_of_invertible_2cell γ).
  - apply to_op2_has_pb_ump.
    exact H.
  - apply internal_sopfib_is_internal_sfib.
    exact Hf.
Defined.

Definition mor_preserves_opcartesian_pb_pr1
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (pb := make_pb_cone e₁ fe p₁ γ)
           (H : has_pb_ump pb)
           (Hf : internal_sopfib p₂)
  : mor_preserves_opcartesian p₁ p₂ fe.
Proof.
  apply mor_preserves_cartesian_to_mor_preserves_opcartesian.
  use (@mor_preserves_cartesian_pb_pr1
         (op2_bicat B)
         e₁ e₂ b₁ b₂
         p₁ p₂ fe fb).
  - apply bicat_invertible_2cell_is_op2_bicat_invertible_2cell.
    exact (inv_of_invertible_2cell γ).
  - apply to_op2_has_pb_ump.
    exact H.
  - apply internal_sopfib_is_internal_sfib.
    exact Hf.
Defined.

Definition mor_preserves_opcartesian_pb_ump_mor
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (pb := make_pb_cone e₁ fe p₁ γ)
           (H : has_pb_ump pb)
           {e₀ b₀ : B}
           (p₀ : e₀ --> b₀)
           (h₁ : e₀ --> e₂)
           (h₂ : b₀ --> b₁)
           (δ : invertible_2cell (h₁ · p₂) (p₀ · h₂ · fb))
           (cone := make_pb_cone e₀ h₁ (p₀ · h₂) δ)
           (Hh₁ : mor_preserves_opcartesian p₀ p₂ h₁)
  : mor_preserves_opcartesian
      p₀
      p₁
      (pb_ump_mor H cone).
Proof.
  apply mor_preserves_cartesian_to_mor_preserves_opcartesian.
  exact (@mor_preserves_cartesian_pb_ump_mor
           (op2_bicat B)
           e₁ e₂ b₁ b₂
           p₁ p₂ fe fb
           _
           (to_op2_has_pb_ump _ H)
           e₀ b₀ p₀
           h₁ h₂
           (inv_of_invertible_2cell
              (bicat_invertible_2cell_is_op2_bicat_invertible_2cell
                 _ _
                 δ))
           (mor_preserves_opcartesian_to_mor_preserves_cartesian
              Hh₁)).
Defined.
