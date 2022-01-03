(********************************************************

 Internal Street opfibrations

 In this file, we define the notion of Street opfibration
 internal to a bicategory.

 1. Definition of an internal Street opfibration
 2. Street opfibrations in [B] are the same as Street fibrations in [op2_bicat B]
 3. Properties of opcartesian cells
 4. Projection is an opfibration

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
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Colimits.Products.
Import Products.Notations.

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

(**
 4. Projection is an opfibration
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
