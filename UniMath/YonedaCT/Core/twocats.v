Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Bicat.

Section TwoCatDefinition.

  Definition twocatₛ : UU
    := ∑ (ob : UU)
         (hom : ob → ob → UU)
         (cell : ∏ x y : ob, hom x y → hom x y → UU)
         (id : ∏ x : ob, hom x x)
         (cmp : ∏ x y z : ob, hom x y → hom y z → hom x z)
         (uni : ∏ (x y : ob) (f : hom x y),
             cmp _ _ _ (id x) f = f × cmp _ _ _ f (id y) = f)
         (ass : ∏ (x y z w : ob) (f : hom x y) (g : hom y z) (h : hom z w),
             cmp _ _ _ (cmp _ _ _ f g) h = cmp _ _ _ f (cmp _ _ _ g h))
         (mtc : ∏ (x y : ob) (f : hom x y), cell _ _ f f)
         (cmp_v : ∏ (x y : ob) (f g h : hom x y), cell _ _ f g → cell _ _ g h → cell _ _ f h)
         (cmp_h : ∏ (x y z : ob) (f₁ f₂ : hom x y) (g₁ g₂ : hom y z),
             cell _ _ f₁ f₂ → cell _ _ g₁ g₂ → cell _ _ (cmp _ _ _ f₁ g₁) (cmp _ _ _ f₂ g₂)),
      (∏ (x y : ob) (f g : hom x y) (α : cell x y f g),
        cmp_v x y f f g (mtc x y f) α = α)
        × (∏ (x y : ob) (f g : hom x y) (x : cell x y f g), cmp_v _ _ f g g x (mtc _ _ g) = x)
        × (∏ (x y : ob) (f g h w : hom x y) (α : cell x y f g) (β : cell x y g h) (γ : cell x y h w),
          cmp_v _ _ f g w α (cmp_v _ _ g h w β γ) = cmp_v _ _ f h w (cmp_v _ _ f g h α β) γ)
        × ( ∏ (x y z : ob) (f : hom x y) (g : hom y z),
          cmp_h _ _ _ f f g g (mtc _ _ f) (mtc _ _ g) = mtc _ _ (cmp _ _ _ f g)).

  Definition ob (K : twocatₛ) : UU
    := pr1 K.
  Coercion ob : twocatₛ >-> UU.

  Definition hom (K : twocatₛ)
    : ob K → ob K → UU
    := pr12 K.

  Definition cell (K : twocatₛ)
    : ∏ (x y : K), hom K x y → hom K x y → UU
    := pr122 K.

  Definition id₁ (K : twocatₛ)
    : ∏ (x : K), hom K x x
    := pr1 (pr222 K).

  Definition cmp₁ (K : twocatₛ)
    : ∏ x y z : ob K, hom K x y → hom K y z → hom K x z
    := pr12 (pr222 K).

  Definition uniₗ (K : twocatₛ)
    : ∏ (x y : ob K) (f : hom K x y), cmp₁ _ _ _ _ (id₁ _ x) f = f
    := λ x y f, pr1 (pr122 (pr222 K) x y f).

  Definition uniᵣ (K : twocatₛ)
    : ∏ (x y : ob K) (f : hom K x y), cmp₁ _ _ _ _ f (id₁ _ y) = f
    := λ x y f, pr2 (pr122 (pr222 K) x y f).

  Definition ass (K : twocatₛ)
    : ∏ (x y z w : ob K) (f : hom K x y) (g : hom K y z) (h : hom K z w),
      cmp₁ _ _ _ _ (cmp₁ _ _ _ _ f g) h = cmp₁ _ _ _ _ f (cmp₁ _ _ _ _ g h)
    := pr1 (pr222 (pr222 K)).

  (* morphism to cell *)
  Definition mtc (K : twocatₛ)
    : ∏ (x y : K) (f : hom K x y), cell K x y f f
    := pr12 (pr222 (pr222 K)).

  (* path to cell *)
  Lemma ptc (K : twocatₛ)
    : ∏ (x y : K) (f g : hom K x y), f = g → cell K x y f g.
  Proof.
    intros x y f g p.
    induction p.
    exact (mtc K _ _ f).
  Defined.

  Definition cmp_v (K : twocatₛ)
    : ∏ (x y : ob K) (f g h : hom K x y), cell _ _ _ f g → cell _ _ _ g h → cell _ _ _ f h
    := pr122 (pr222 (pr222 K)).

  Definition cmp_h (K : twocatₛ)
    : ∏ (x y z : ob K) (f₁ f₂ : hom K x y) (g₁ g₂ : hom K y z),
      cell _ _ _ f₁ f₂ → cell _ _ _ g₁ g₂ → cell _ _ _ (cmp₁ _ _ _ _ f₁ g₁) (cmp₁ _ _ _ _ f₂ g₂)
    := pr1 (pr222 (pr222 (pr222 K))).

  Lemma lwh (K : twocatₛ)
    : ∏ (x y z : K) (f : hom K x y) (g₁ g₂ : hom K y z),
      cell _ _ _ g₁ g₂ → cell K _ _ (cmp₁ _ _ _ _ f g₁) (cmp₁ _ _ _ _ f g₂).
  Proof.
    intros x y z f g₁ g₂ α.
    exact (cmp_h K x y z f f g₁ g₂ (mtc _ _ _ f) α).
  Defined.

  Lemma rwh (K : twocatₛ)
    : ∏ (x y z : K) (f₁ f₂ : hom K x y) (g : hom K y z),
      cell _ _ _ f₁ f₂ → cell _ _ _ (cmp₁ _ _ _ _ f₁ g) (cmp₁ _ _ _ _ f₂ g).
  Proof.
    intros x y z f₁ f₂ g α.
    exact (cmp_h K x y z f₁ f₂ g g α (mtc _ _ _ g)).
  Defined.

  Definition uni₂l (K : twocatₛ)
    : ∏ (x y : ob K) (f g : hom K x y) (α : cell K x y f g),
      cmp_v _ _ _ f f g (mtc _ x y f) α = α
    := pr12 (pr222 (pr222 (pr222 K))).

  Definition uni₂r (K : twocatₛ)
    : ∏ (x y : ob K) (f g : hom K x y) (α : cell K x y f g),
      cmp_v _ _ _ f g g α (mtc _ _ _ g) = α
    := pr122 (pr222 (pr222 (pr222 K))).

  Definition cmp_v3 (K : twocatₛ)
    : ∏ (x y : ob K) (f g h w : hom K x y) (α : cell K x y f g) (β : cell K x y g h) (γ : cell K x y h w),
      cmp_v _ _ _ f g w α (cmp_v _ _ _ g h w β γ) = cmp_v _ _ _ f h w (cmp_v _ _ _ f g h α β) γ
    := pr1 (pr222 (pr222 (pr222 (pr222 K)))).

  Definition tst (K : twocatₛ)
    : ∏ (x y z : K) (f : hom K x y) (g : hom K y z),
      cmp_h _ _ _ _ f f g g (mtc _ _ _ f) (mtc _ _ _ g) = mtc K _ _ (cmp₁ _ _ _ _ f g)
    := pr2 (pr222 (pr222 (pr222 (pr222 K)))).

  Definition prebicat_data_from_twocat (K : twocatₛ) : prebicat_data.
  Proof.
    simple refine (((_ ,, _) ,, _) ,, _).
    - exact (ob K ,, hom K).
    - exact (id₁ K ,, cmp₁ K).
    - exact (cell K).
    - cbn; unfold prebicat_2_id_comp_struct.
      repeat (use tpair) ; cbn.
      + exact (mtc K).
      + intros x y f.
        apply ptc, uniₗ.
      + intros x y f.
        apply ptc, uniᵣ.
      + intros x y f.
        apply ptc, pathsinv0, uniₗ.
      + intros x y f.
        apply ptc, pathsinv0, uniᵣ.
      + intros x y z w f g h.
        apply ptc, ass.
      + intros x y z w f g h.
        apply ptc, pathsinv0, ass.
      + exact (cmp_v K).
      + exact (lwh K).
      + exact (rwh K).
  Defined.

  Definition prebicat_laws_from_twocat (K : twocatₛ)
    : prebicat_laws (prebicat_data_from_twocat K).
  Proof.
    repeat (use tpair) ; cbn.
    - apply uni₂l.
    - apply uni₂r.
    - apply cmp_v3.
    - apply tst.
    - apply tst.
    - unfold lwh.
      intros x y z f g₁ g₂ g₃ α β.
      admit.
    - unfold rwh.
      intros x y z f₁ f₂ f₃ g α β.
      admit.
    - intros x y f g α.
      admit.
    - intros x y f g α.
      admit.
    - intros x y z w f g h₁ h₂ α.













  Definition prebicat_from_twocat (K : twocatₛ) : prebicat.
  Proof.
    unfold prebicat.
    exists (prebicat_data_from_twocat K).

    - cbn.
      Check prebicat_laws.


















  Definition precatₛ_laws (K : precatₛ_data) : UU.
  Proof.
    use (_ × _).
    -

  Definition Cat₂ : UU
    := bicat.



End TwoCatDefinition.
