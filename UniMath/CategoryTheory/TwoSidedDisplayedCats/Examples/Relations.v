(**********************************************************************************

 The two-sided displayed category of relations

 We define two two-sided displayed categories of relations of sets. The first one
 has as displayed objects relations that are valued in `hProp`, while the second
 one, is about relations that are valued in `hSet`. Relations valued in `hSet` are
 also known as pseudo relations.

 Contents
 1. Relations in `hProp`
 1.1. The definition
 1.2. Isomorphisms
 1.3. Univalence
 2. Relations in `hSet`
 2.1. The definition
 2.2. Isomorphisms
 2.3. Univalence

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedFibration.

Local Open Scope cat.

Definition to_rel_weq
           {X Y : UU}
           {R₁ R₂ : X → Y → hProp}
           (p : R₁ = R₂)
  : ((∏ (x : X) (y : Y), R₁ x y → R₂ x y)
    ×
    ∏ (x : X) (y : Y), R₂ x y → R₁ x y).
Proof.
  induction p.
  split.
  - exact (λ _ _ r, r).
  - exact (λ _ _ r, r).
Defined.

Definition hProp_weq
           (X Y : hProp)
  : (X ≃ Y) ≃ ((X → Y) × (Y → X)).
Proof.
  use weq_iso.
  - exact (λ w, pr1 w ,, invmap w).
  - exact (λ f, weqimplimpl (pr1 f) (pr2 f) (pr2 X) (pr2 Y)).
  - abstract
      (intro w ; cbn ;
       use subtypePath ; [ intro ; apply isapropisweq | ] ; cbn ;
       apply idpath).
  - abstract
      (intro w ; apply idpath).
Defined.

Definition rel_weq
           {X Y : UU}
           (R₁ R₂ : X → Y → hProp)
  : (R₁ = R₂)
    ≃
    ∏ (x : X) (y : Y),
    (R₁ x y → R₂ x y)
    ×
    (R₂ x y → R₁ x y)
  := (weqonsecfibers
        _ _
        (λ x,
         weqonsecfibers
           _ _
           (λ y,
            hProp_weq _ _ ∘ UA_for_HLevels _ _ _))
      ∘ weqonsecfibers
          _ _
          (λ x, invweq (weqfunextsec (λ _, hProp) (R₁ x) (R₂ x)))
      ∘ invweq (weqfunextsec (λ _, Y → hProp) R₁ R₂))%weq.

Definition set_rel_weq
           {X Y : UU}
           (R₁ R₂ : X → Y → hSet)
  : (R₁ = R₂)
    ≃
    ∏ (x : X) (y : Y), R₁ x y ≃ R₂ x y
  := (weqonsecfibers
        _ _
        (λ x,
         weqonsecfibers
           _ _
           (λ y, UA_for_HLevels 2 _ _)
         ∘ invweq (weqfunextsec (λ _, hSet) (R₁ x) (R₂ x)))
      ∘ invweq (weqfunextsec (λ _, Y → hSet) R₁ R₂))%weq.

(**
 1. Relations in `hProp`
 *)

(**
 1.1. The definition
 *)
Definition rel_disp_cat_ob_mor
  : twosided_disp_cat_ob_mor SET SET.
Proof.
  simple refine (_ ,, _).
  - exact (λ (X : hSet) (Y : hSet), X → Y → hProp).
  - exact (λ (X₁ : hSet) X₂ (Y₁ : hSet) Y₂ R₁ R₂ f g,
           ∏ (x : X₁) (y : Y₁),
           R₁ x y → R₂ (f x) (g y)).
Defined.

Definition rel_disp_cat_id_comp
  : twosided_disp_cat_id_comp rel_disp_cat_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact (λ X Y R x y r, r).
  - exact (λ X₁ X₂ X₃ Y₁ Y₂ Y₃ R₁ R₂ R₃ f₁ f₂ g₁ g₂ α β x y r, β _ _ (α _ _ r)).
Defined.

Definition rel_disp_cat_data
  : twosided_disp_cat_data SET SET.
Proof.
  simple refine (_ ,, _).
  - exact rel_disp_cat_ob_mor.
  - exact rel_disp_cat_id_comp.
Defined.

Definition rel_disp_cat_axioms
  : twosided_disp_cat_axioms rel_disp_cat_data.
Proof.
  repeat split.
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g α.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    apply R₂.
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g α.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    apply R₂.
  - intros X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ R₁ R₂ R₃ R₄ f₁ f₂ f₃ g₁ g₂ g α β γ.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    apply R₄.
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g ; cbn.
    use impred_isaset ; intro x.
    use impred_isaset ; intro y.
    use impred_isaset ; intro r.
    apply isasetaprop.
    apply R₂.
Qed.

Definition rel_disp_cat
  : twosided_disp_cat SET SET.
Proof.
  simple refine (_ ,, _).
  - exact rel_disp_cat_data.
  - exact rel_disp_cat_axioms.
Defined.

(**
 1.2. Isomoprhisms
 *)
Definition to_iso_rel_disp_cat
           {X Y : SET}
           (R₁ R₂ : rel_disp_cat X Y)
           (f : ∏ (x : pr1 X) (y : pr1 Y),
                (R₁ x y → R₂ x y)
                ×
                (R₂ x y → R₁ x y))
  : iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) R₁ R₂.
Proof.
  simple refine ((λ x y, pr1 (f x y)) ,, (λ x y, pr2 (f x y)) ,, _ ,, _).
  - abstract
      (cbn ;
       use funextsec ; intro x ;
       use funextsec ; intro y ;
       use funextsec ; intro r ;
       apply R₁).
  - abstract
      (cbn ;
       use funextsec ; intro x ;
       use funextsec ; intro y ;
       use funextsec ; intro r ;
       apply R₂).
Defined.

Definition from_iso_rel_disp_cat
           {X Y : SET}
           (R₁ R₂ : rel_disp_cat X Y)
           (f : iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) R₁ R₂)
  : ∏ (x : pr1 X) (y : pr1 Y),
    (R₁ x y → R₂ x y)
    ×
    (R₂ x y → R₁ x y)
  := λ x y, pr1 f x y ,, pr12 f x y.

Definition iso_rel_disp_cat
           {X Y : SET}
           (R₁ R₂ : rel_disp_cat X Y)
  : (∏ (x : pr1 X) (y : pr1 Y),
     (R₁ x y → R₂ x y)
     ×
     (R₂ x y → R₁ x y))
    ≃
    iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) R₁ R₂.
Proof.
  use make_weq.
  - exact (to_iso_rel_disp_cat R₁ R₂).
  - use isweq_iso.
    + exact (from_iso_rel_disp_cat R₁ R₂).
    + abstract
        (intros f ;
         apply idpath).
    + abstract
        (intros f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
Defined.

(**
 1.3. Univalence
 *)
Definition is_univalent_rel_twosided_disp_cat
  : is_univalent_twosided_disp_cat rel_disp_cat.
Proof.
  intros X₁ X₂ Y₁ Y₂ p₁ p₂ R₁ R₂.
  induction p₁, p₂ ; cbn.
  use weqhomot.
  - exact (iso_rel_disp_cat R₁ R₂
           ∘ rel_weq R₁ R₂)%weq.
  - abstract
      (intros p ;
       induction p ; cbn ;
       use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ; cbn ;
       apply idpath).
Defined.

(**
 2. Relations in `hSet`
 *)

(**
 2.1. The definition
 *)
Definition set_rel_disp_cat_ob_mor
  : twosided_disp_cat_ob_mor SET SET.
Proof.
  simple refine (_ ,, _).
  - exact (λ (X : hSet) (Y : hSet), X → Y → hSet).
  - exact (λ (X₁ : hSet) X₂ (Y₁ : hSet) Y₂ R₁ R₂ f g,
           ∏ (x : X₁) (y : Y₁),
           R₁ x y → R₂ (f x) (g y)).
Defined.

Definition set_rel_disp_cat_id_comp
  : twosided_disp_cat_id_comp set_rel_disp_cat_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact (λ X Y R x y r, r).
  - exact (λ X₁ X₂ X₃ Y₁ Y₂ Y₃ R₁ R₂ R₃ f₁ f₂ g₁ g₂ α β x y r, β _ _ (α _ _ r)).
Defined.

Definition set_rel_disp_cat_data
  : twosided_disp_cat_data SET SET.
Proof.
  simple refine (_ ,, _).
  - exact set_rel_disp_cat_ob_mor.
  - exact set_rel_disp_cat_id_comp.
Defined.

Definition transportf_set_rel
           {X₁ X₂ Y₁ Y₂ : UU}
           (R₁ : X₁ → Y₁ → hSet)
           (R₂ : X₂ → Y₂ → hSet)
           {f₁ f₂ : X₁ → X₂}
           (p : f₂ = f₁)
           {g₁ g₂ : Y₁ → Y₂}
           (q : g₂ = g₁)
           (α : ∏ (x : X₁) (y : Y₁), R₁ x y → R₂ (f₂ x) (g₂ y))
           {a : X₁}
           {b : Y₁}
           (r : R₁ a b)
  : transportf
      (λ (h : X₁ → X₂), ∏ (x : X₁) (y : Y₁), R₁ x y → R₂ (h x) (g₁ y))
      p
      (transportf
         (λ (h : Y₁ → Y₂), ∏ (x : X₁) (y : Y₁), R₁ x y → R₂ (f₂ x) (h y))
         q
         α)
      a
      b
      r
    =
    transportf
      (λ z, R₂ z _)
      (eqtohomot p _)
      (transportf
         (λ z, R₂ _ z)
         (eqtohomot q _)
         (α a b r)).
Proof.
  induction p, q.
  cbn.
  apply idpath.
Qed.

Definition transportf_id_left
           {X Y : hSet}
           (f : SET ⟦ X , Y ⟧)
           (P : Y → UU)
           (x : X)
           (p : P (f x))
  : transportf
      P
      (eqtohomot (!(id_left f)) x)
      p
    =
    p.
Proof.
  refine (_ @ idpath_transportf _ _).
  apply maponpaths_2.
  apply Y.
Qed.

Definition transportf_id_right
           {X Y : hSet}
           (f : SET ⟦ X , Y ⟧)
           (P : Y → UU)
           (x : X)
           (p : P (f x))
  : transportf
      P
      (eqtohomot (!(id_right f)) x)
      p
    =
    p.
Proof.
  refine (_ @ idpath_transportf _ _).
  apply maponpaths_2.
  apply Y.
Qed.

Definition transportf_assoc
           {W X Y Z : hSet}
           (f : SET ⟦ W , X ⟧)
           (g : SET ⟦ X , Y ⟧)
           (h : SET ⟦ Y , Z ⟧)
           (P : Z → UU)
           (w : W)
           (p : P (h(g(f w))))
  : transportf
      P
      (eqtohomot (!(assoc f g h)) w)
      p
    =
    p.
Proof.
  refine (_ @ idpath_transportf _ _).
  apply maponpaths_2.
  apply Z.
Qed.

Definition set_rel_disp_cat_axioms
  : twosided_disp_cat_axioms set_rel_disp_cat_data.
Proof.
  repeat split.
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g α.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    cbn.
    unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn.
    rewrite transportf_set_rel.
    rewrite (transportf_id_left f).
    rewrite (transportf_id_left g).
    apply idpath.
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g α.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    cbn.
    unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn.
    rewrite transportf_set_rel.
    rewrite (transportf_id_right f).
    rewrite (transportf_id_right g).
    apply idpath.
  - intros X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ R₁ R₂ R₃ R₄ f₁ f₂ f₃ g₁ g₂ g₃ α β γ.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro r.
    cbn.
    unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn.
    rewrite transportf_set_rel.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (transportf_assoc g₁ g₂ g₃ (λ z, R₄ (f₃ (f₂ (f₁ x))) z)).
    }
    apply (transportf_assoc f₁ f₂ f₃ (λ z, R₄ z (g₃ (g₂ (g₁ y))))).
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g ; cbn.
    use impred_isaset ; intro x.
    use impred_isaset ; intro y.
    use impred_isaset ; intro r.
    apply R₂.
Qed.

Definition set_rel_disp_cat
  : twosided_disp_cat SET SET.
Proof.
  simple refine (_ ,, _).
  - exact set_rel_disp_cat_data.
  - exact set_rel_disp_cat_axioms.
Defined.

(**
 2.2. Isomorphisms
 *)
Definition to_iso_set_rel_disp_cat
           {X Y : SET}
           (R₁ R₂ : set_rel_disp_cat X Y)
           (f : ∏ (x : pr1 X) (y : pr1 Y), R₁ x y ≃ R₂ x y)
  : iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) R₁ R₂.
Proof.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (λ x y, f x y).
  - exact (λ x y, invmap (f x y)).
  - abstract
      (cbn ;
       use funextsec ; intro x ;
       use funextsec ; intro y ;
       use funextsec ; intro r ;
       unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
       rewrite transportf_set_rel ;
       refine (!_) ;
       do 2 (refine (transportf_id_left _ _ _ _ @ _)) ;
       exact (!(homotinvweqweq (f x y) r))).
  - abstract
      (cbn ;
       use funextsec ; intro x ;
       use funextsec ; intro y ;
       use funextsec ; intro r ;
       unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
       rewrite transportf_set_rel ;
       refine (!_) ;
       do 2 (refine (transportf_id_left _ _ _ _ @ _)) ;
       exact (!(homotweqinvweq (f x y) r))).
Defined.

Definition from_iso_set_rel_disp_cat
           {X Y : SET}
           (R₁ R₂ : set_rel_disp_cat X Y)
           (f : iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) R₁ R₂)
           (x : pr1 X)
           (y : pr1 Y)
  : R₁ x y ≃ R₂ x y.
Proof.
  use weq_iso.
  - exact (pr1 f x y).
  - exact (pr12 f x y).
  - abstract
      (intros r ;
       pose (p := eqtohomot
                    (eqtohomot
                       (eqtohomot
                          (pr122 f)
                          x)
                       y)
                    r) ;
       refine (p @ _) ; cbn ; clear p ;
       unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
       rewrite transportf_set_rel ;
       do 2 (refine (transportf_id_left _ _ _ _ @ _)) ;
       apply idpath).
  - abstract
      (intros r ;
       pose (p := eqtohomot
                    (eqtohomot
                       (eqtohomot
                          (pr222 f)
                          x)
                       y)
                    r) ;
       refine (p @ _) ; cbn ; clear p ;
       unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
       rewrite transportf_set_rel ;
       do 2 (refine (transportf_id_left _ _ _ _ @ _)) ;
       apply idpath).
Defined.

Definition iso_set_rel_disp_cat
           {X Y : SET}
           (R₁ R₂ : set_rel_disp_cat X Y)
  : (∏ (x : pr1 X) (y : pr1 Y), R₁ x y ≃ R₂ x y)
    ≃
    iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) R₁ R₂.
Proof.
  use weq_iso.
  - exact (to_iso_set_rel_disp_cat R₁ R₂).
  - exact (from_iso_set_rel_disp_cat R₁ R₂).
  - abstract
      (intros f ;
       use funextsec ; intro x ;
       use funextsec ; intro y ;
       use subtypePath ; [ intro ; apply isapropisweq | ] ;
       apply idpath).
  - abstract
        (intros f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
Defined.

(**
 2.3. Univalence
 *)
Definition is_univalent_set_rel_twosided_disp_cat
  : is_univalent_twosided_disp_cat set_rel_disp_cat.
Proof.
  intros X₁ X₂ Y₁ Y₂ p₁ p₂ R₁ R₂.
  induction p₁, p₂ ; cbn.
  use weqhomot.
  - exact (iso_set_rel_disp_cat R₁ R₂
           ∘ set_rel_weq R₁ R₂)%weq.
  - abstract
      (intros p ;
       induction p ; cbn ;
       use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ; cbn ;
       apply idpath).
Defined.
