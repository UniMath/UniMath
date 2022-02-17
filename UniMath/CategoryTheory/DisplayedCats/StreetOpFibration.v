Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Open Scope cat.

Lemma idtoiso_functor_precompose'
      {C₁ C₂ : category}
      (F : C₁ ⟶ C₂)
      {y : C₂}
      {x₁ x₂ : C₁}
      (p : x₁ = x₂)
      (f : y --> F x₁)
  : f · idtoiso (maponpaths (λ z, F z) p)
    =
    transportf (λ z, y --> F z) p f.
Proof.
  induction p.
  cbn.
  apply id_right.
Qed.

Definition transportf_functor_isotoid'
           {C₁ C₂ : category}
           (HC₁ : is_univalent C₁)
           (F : C₁ ⟶ C₂)
           {y : C₂}
           {x₁ x₂ : C₁}
           (i : iso x₁ x₂)
           (f : y --> F x₁)
  : transportf
      (λ z, y --> F z)
      (isotoid _ HC₁ i)
      f
    =
    f · #F i.
Proof.
  rewrite <- idtoiso_functor_precompose'.
  rewrite maponpaths_idtoiso.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.


(**
The definition of a Street opfibration of categories
 *)
Section StreetOpFibration.
  Context {E B : category}
          (F : E ⟶ B).

  Definition is_opcartesian_sopfib
             {e₁ e₂ : E}
             (f : e₁--> e₂)
    : UU
    := ∏ (e₃ : E)
         (g : e₁ --> e₃)
         (h : F e₂ --> F e₃)
         (p : #F g = #F f · h),
       ∃! (φ : e₂ --> e₃),
       #F φ = h
       ×
       f · φ = g.

  Definition isaprop_is_opcartesian_sopfib
             {e₁ e₂ : E}
             (f : e₁--> e₂)
    : isaprop (is_opcartesian_sopfib f).
  Proof.
    do 4 (apply impred ; intro).
    apply isapropiscontr.
  Qed.

  Definition opcartesian_factorization_sopfib
             {e₁ e₂ : E}
             {f : e₁--> e₂}
             (Hf : is_opcartesian_sopfib f)
             {e₃ : E}
             (g : e₁ --> e₃)
             (h : F e₂ --> F e₃)
             (p : #F g = #F f · h)
    : e₂ --> e₃
    := pr11 (Hf e₃ g h p).

  Definition opcartesian_factorization_sopfib_over
             {e₁ e₂ : E}
             {f : e₁--> e₂}
             (Hf : is_opcartesian_sopfib f)
             {e₃ : E}
             (g : e₁ --> e₃)
             (h : F e₂ --> F e₃)
             (p : #F g = #F f · h)
    : #F (opcartesian_factorization_sopfib Hf g h p) = h
    := pr121 (Hf e₃ g h p).

  Definition opcartesian_factorization_sopfib_commute
             {e₁ e₂ : E}
             {f : e₁--> e₂}
             (Hf : is_opcartesian_sopfib f)
             {e₃ : E}
             (g : e₁ --> e₃)
             (h : F e₂ --> F e₃)
             (p : #F g = #F f · h)
    : f · opcartesian_factorization_sopfib Hf g h p = g
    := pr221 (Hf e₃ g h p).

  Definition opcartesian_factorization_sopfib_unique
             {e₁ e₂ : E}
             {f : e₁--> e₂}
             (Hf : is_opcartesian_sopfib f)
             {e₃ : E}
             (g : e₁ --> e₃)
             (h : F e₂ --> F e₃)
             (p : #F g = #F f · h)
             (φ₁ φ₂ : e₂ --> e₃)
             (p₁ : #F φ₁ = h)
             (p₂ : #F φ₂ = h)
             (q₁ : f · φ₁ = g)
             (q₂ : f · φ₂ = g)
    : φ₁ = φ₂.
  Proof.
    exact (maponpaths
             pr1
             (proofirrelevance
                _
                (isapropifcontr (Hf e₃ g h p))
                (φ₁ ,, p₁ ,, q₁)
                (φ₂ ,, p₂ ,, q₂))).
  Defined.

  Definition street_opfib
    : UU
    := ∏ (e : E)
         (b : B)
         (f : F e --> b),
       ∑ (bb : E)
         (ff_i : e --> bb × iso b (F bb)),
       # F (pr1 ff_i) = f · pr2 ff_i
       ×
       is_opcartesian_sopfib (pr1 ff_i).
End StreetOpFibration.

(**
 *)
Definition lift_unique_sopfib_map
           {E B : category}
           (F : E ⟶ B)
           {e : E}
           {b : B}
           (f : F e --> b)
           (bb₁ bb₂ : E)
           (ff₁ : e --> bb₁)
           (β₁ : iso b (F bb₁))
           (ff₂ :  e --> bb₂)
           (β₂ : iso b (F bb₂))
           (over₁ : # F (ff₁) = f · β₁)
           (over₂ : # F (ff₂) = f · β₂)
           (cart₁ : is_opcartesian_sopfib F ff₁)
           (cart₂ : is_opcartesian_sopfib F ff₂)
  : bb₁ --> bb₂.
Proof.
  use (opcartesian_factorization_sopfib F cart₁ ff₂ (inv_from_iso β₁ · β₂) _).
  abstract
    (rewrite over₁, over₂ ;
     rewrite !assoc' ;
     apply maponpaths ;
     rewrite !assoc ;
     rewrite iso_inv_after_iso ;
     rewrite id_left ;
     apply idpath).
Defined.

Section UniqueLifts.
  Context {E B : category}
          (F : E ⟶ B)
          {e : E}
          {b : B}
          (f : F e --> b)
          (bb₁ bb₂ : E)
          (ff₁ : e --> bb₁)
          (β₁ : iso b (F bb₁))
          (ff₂ :  e --> bb₂)
          (β₂ : iso b (F bb₂))
          (over₁ : # F (ff₁) = f · β₁)
          (over₂ : # F (ff₂) = f · β₂)
          (cart₁ : is_opcartesian_sopfib F ff₁)
          (cart₂ : is_opcartesian_sopfib F ff₂).

  Let ζ : bb₁ --> bb₂
    := lift_unique_sopfib_map F f bb₁ bb₂ ff₁ β₁ ff₂ β₂ over₁ over₂ cart₁ cart₂.
  Let ζinv : bb₂ --> bb₁
    := lift_unique_sopfib_map F f bb₂ bb₁ ff₂ β₂ ff₁ β₁ over₂ over₁ cart₂ cart₁.

  Local Lemma lift_unique_sopfib_inv₁
    : ζ · ζinv = identity bb₁.
  Proof.
    unfold ζ, ζinv, lift_unique_sopfib_map.
    use (opcartesian_factorization_sopfib_unique
           F
           cart₁
           ff₁
           (identity _)).
    - rewrite id_right.
      apply idpath.
    - rewrite functor_comp.
      rewrite !opcartesian_factorization_sopfib_over.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite iso_inv_after_iso.
      rewrite id_left.
      rewrite iso_after_iso_inv.
      apply idpath.
    - apply functor_id.
    - rewrite !assoc.
      rewrite !opcartesian_factorization_sopfib_commute.
      apply idpath.
    - apply id_right.
  Qed.

  Local Lemma lift_unique_sopfib_inv₂
    : ζinv · ζ = identity bb₂.
  Proof.
    unfold ζ, ζinv, lift_unique_sopfib_map.
    use (opcartesian_factorization_sopfib_unique
           F
           cart₂
           ff₂
           (identity _)).
    - rewrite id_right.
      apply idpath.
    - rewrite functor_comp.
      rewrite !opcartesian_factorization_sopfib_over.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite iso_inv_after_iso.
      rewrite id_left.
      rewrite iso_after_iso_inv.
      apply idpath.
    - apply functor_id.
    - rewrite !assoc.
      rewrite !opcartesian_factorization_sopfib_commute.
      apply idpath.
    - apply id_right.
  Qed.

  Definition lift_unique_sopfib
    : iso bb₁ bb₂.
  Proof.
    use make_iso.
    - exact ζ.
    - use is_iso_qinv.
      + exact ζinv.
      + split.
        * exact lift_unique_sopfib_inv₁.
        * exact lift_unique_sopfib_inv₂.
  Defined.
End UniqueLifts.

(** The type of Street opfibrations is a proposition *)
Definition isaprop_street_opfib
           {B E : category}
           (HE : is_univalent E)
           (F : E ⟶ B)
  : isaprop (street_opfib F).
Proof.
  use impred ; intro e.
  use impred ; intro b.
  use impred ; intro f.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use total2_paths_f.
  - apply (isotoid _ HE).
    exact (lift_unique_sopfib
             F f
             (pr1 φ₁) (pr1 φ₂)
             (pr112 φ₁) (pr212 φ₁)
             (pr112 φ₂) (pr212 φ₂)
             (pr122 φ₁) (pr122 φ₂)
             (pr222 φ₁) (pr222 φ₂)).
  - use subtypePath.
    {
      intro.
      apply isapropdirprod ;
        [ apply homset_property
        | apply isaprop_is_opcartesian_sopfib ].
    }
    rewrite pr1_transportf.
    use dirprod_paths.
    + etrans.
      {
        apply (@pr1_transportf E (λ x, e --> x) (λ x _, iso _ (F x))).
      }
      rewrite transportf_isotoid'.
      apply opcartesian_factorization_sopfib_commute.
    + rewrite pr2_transportf.
      use subtypePath.
      {
        intro.
        apply isaprop_is_iso.
      }
      unfold iso.
      rewrite pr1_transportf.
      rewrite transportf_functor_isotoid'.
      etrans.
      {
        apply maponpaths.
        apply opcartesian_factorization_sopfib_over.
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply iso_inv_after_iso.
      }
      apply id_left.
Qed.

(**
 Lemmas on opcartesian cells for Street fibrations
 *)
Definition is_opcartesian_sopfib_eq
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           {x₁ x₂ : C₁}
           {f₁ f₂ : x₁ --> x₂}
           (p : f₁ = f₂)
           (Hf₁ : is_opcartesian_sopfib F f₁)
  : is_opcartesian_sopfib F f₂.
Proof.
  induction p.
  exact Hf₁.
Defined.

Definition iso_is_opcartesian_sopfib
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           {x₁ x₂ : C₁}
           (i : x₁ --> x₂)
           (Hi : is_iso i)
  : is_opcartesian_sopfib F i.
Proof.
  pose (i_iso := make_iso _ Hi).
  intros w g h p.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
       refine (!(id_left _) @ _ @ id_left _) ;
       rewrite <- (iso_after_iso_inv i_iso) ;
       cbn ;
       rewrite !assoc' ;
       rewrite (pr22 φ₁), (pr22 φ₂) ;
       apply idpath).
  - simple refine (_ ,, _ ,, _).
    + exact (inv_from_iso i_iso · g).
    + abstract
        (rewrite functor_comp ;
         rewrite p ;
         rewrite !assoc ;
         rewrite <- functor_comp ;
         etrans ;
           [ apply maponpaths_2 ;
             apply maponpaths ;
             exact (iso_after_iso_inv i_iso)
           | ] ;
         rewrite functor_id ;
         apply id_left).
    + abstract
        (cbn ;
         rewrite !assoc ;
         refine (_ @ id_left _) ;
         apply maponpaths_2 ;
         exact (iso_inv_after_iso i_iso)).
Defined.

Section CompositionOpCartesian.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          {x₁ x₂ x₃ : C₁}
          {f : x₁ --> x₂}
          (Hf : is_opcartesian_sopfib F f)
          {g : x₂ --> x₃}
          (Hg : is_opcartesian_sopfib F g).

  Section Factorization.
    Context {w : C₁}
            {h₁ : x₁ --> w}
            {h₂ : F x₃ --> F w}
            (p : # F h₁ = # F (f · g) · h₂).

    Definition comp_is_opcartesian_sopfib_factor_help
      : x₂ --> w.
    Proof.
      use (opcartesian_factorization_sopfib _ Hf h₁ (#F g · h₂)).
      abstract
        (refine (p @ _) ;
         rewrite functor_comp ;
         rewrite !assoc ;
         apply idpath).
    Defined.

    Definition comp_is_opcartesian_sopfib_factor
      : x₃ --> w.
    Proof.
      use (opcartesian_factorization_sopfib _ Hg).
      - exact comp_is_opcartesian_sopfib_factor_help.
      - exact h₂.
      - apply opcartesian_factorization_sopfib_over.
    Defined.

    Definition comp_is_opcartesian_sopfib_factor_over
      : # F comp_is_opcartesian_sopfib_factor = h₂.
    Proof.
      apply opcartesian_factorization_sopfib_over.
    Qed.

    Definition comp_is_opcartesian_sopfib_factor_comm
      : f · g · comp_is_opcartesian_sopfib_factor = h₁.
    Proof.
      unfold comp_is_opcartesian_sopfib_factor, comp_is_opcartesian_sopfib_factor_help.
      rewrite !assoc'.
      rewrite !opcartesian_factorization_sopfib_commute.
      apply idpath.
    Qed.

    Definition comp_is_opcartesian_sopfib_factor_unique
      : isaprop (∑ φ, # F φ = h₂ × f · g · φ = h₁).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use (opcartesian_factorization_sopfib_unique
             _ Hg
             comp_is_opcartesian_sopfib_factor_help h₂).
      - apply opcartesian_factorization_sopfib_over.
      - exact (pr12 φ₁).
      - exact (pr12 φ₂).
      - use (opcartesian_factorization_sopfib_unique _ Hf h₁ (#F g · h₂)).
        + rewrite p.
          rewrite functor_comp.
          rewrite !assoc.
          apply idpath.
        + rewrite functor_comp.
          rewrite (pr12 φ₁).
          apply idpath.
        + apply opcartesian_factorization_sopfib_over.
        + rewrite assoc.
          apply (pr22 φ₁).
        + apply opcartesian_factorization_sopfib_commute.
      - use (opcartesian_factorization_sopfib_unique _ Hf h₁ (#F g · h₂)).
        + rewrite p.
          rewrite functor_comp.
          rewrite !assoc.
          apply idpath.
        + rewrite functor_comp.
          rewrite (pr12 φ₂).
          apply idpath.
        + apply opcartesian_factorization_sopfib_over.
        + rewrite assoc.
          apply (pr22 φ₂).
        + apply opcartesian_factorization_sopfib_commute.
    Qed.
  End Factorization.

  Definition comp_is_opcartesian_sopfib
    : is_opcartesian_sopfib F (f · g).
  Proof.
    intros w h₁ h₂ p.
    use iscontraprop1.
    - exact (comp_is_opcartesian_sopfib_factor_unique p).
    - simple refine (_ ,, _ ,, _).
      + exact (comp_is_opcartesian_sopfib_factor p).
      + exact (comp_is_opcartesian_sopfib_factor_over p).
      + exact (comp_is_opcartesian_sopfib_factor_comm p).
  Defined.
End CompositionOpCartesian.
