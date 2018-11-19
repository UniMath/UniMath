Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.BicatAliases.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws_2.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws.

Section Equivalence.
  Context {C : bicat}.

  Definition is_equivalence
             {X Y : C}
             (f : C⟦X,Y⟧)
    : Type
    := ∑ (g : C⟦Y,X⟧),
       ∑ (η : f ∘ g ==> identity Y),
       ∑ (ε : identity X ==> g ∘ f),
       is_invertible_2cell η × is_invertible_2cell ε.

  Definition equiv_inv
             {X Y : C}
             {f : C⟦X,Y⟧}
             (H : is_equivalence f)
    : C⟦Y,X⟧
    := pr1 H.

  Definition equiv_unit
             {X Y : C}
             {f : C⟦X,Y⟧}
             (H : is_equivalence f)
    : f ∘ equiv_inv H ==> identity Y
    := pr1(pr2 H).

  Definition equiv_counit
             {X Y : C}
             {f : C⟦X,Y⟧}
             (H : is_equivalence f)
    : identity X ==> equiv_inv H ∘ f
    := pr1(pr2(pr2 H)).

  Definition equiv_unit_iso
             {X Y : C}
             {f : C⟦X,Y⟧}
             (H : is_equivalence f)
    : is_invertible_2cell (equiv_unit H)
    := pr1(pr2(pr2(pr2 H))).

  Definition equiv_counit_iso
             {X Y : C}
             {f : C⟦X,Y⟧}
             (H : is_equivalence f)
    : is_invertible_2cell (equiv_counit H)
    := pr2 (pr2 (pr2 (pr2 H))).

  Definition build_equiv
             {X Y : C}
             (f : C⟦X,Y⟧)
             (g : C⟦Y,X⟧)
             (η : f ∘ g ==> identity Y)
             (ε : identity X ==> g ∘ f)
             (η_iso : is_invertible_2cell η)
             (ε_iso : is_invertible_2cell ε)
    : is_equivalence f.
  Proof.
    repeat (use tpair).
    - exact g.
    - exact η.
    - exact ε.
    - apply η_iso.
    - apply η_iso.
    - apply η_iso.
    - apply ε_iso.
    - apply ε_iso.
    - apply ε_iso.
  Defined.

  Definition equivalence (X Y : C)
    := ∑ (f : C⟦X,Y⟧), is_equivalence f.

  Definition Build_equivalence
             {X Y : C}
             (f : C⟦X,Y⟧)
             (Hf : is_equivalence f)
    : equivalence X Y
    := tpair _ f Hf.

  Coercion equiv_morph
           {X Y : C}
    : equivalence X Y -> C⟦X,Y⟧
    := pr1.

  Coercion equiv_is_equiv
           {X Y : C}
           (f : equivalence X Y)
    : is_equivalence f
    := pr2 f.

  Definition equivalence_inv
             {X Y : C}
             (f : equivalence X Y)
    : equivalence Y X.
  Proof.
    use Build_equivalence.
    - exact (equiv_inv f).
    - use build_equiv.
      + apply f.
      + cbn.
        exact ((equiv_counit_iso f)^-1).
      + cbn.
        exact ((equiv_unit_iso f)^-1).
      + is_iso.
      + is_iso.
  Defined.

  Definition id_equiv
             (X : C)
    : equivalence X X.
  Proof.
    use Build_equivalence.
    - exact (identity X).
    - use build_equiv.
      + exact (identity X).
      + exact (runitor (identity X)).
      + exact (rinvunitor (identity X)).
      + is_iso.
      + is_iso.
  Defined.

  Definition comp_counit
             {X Y Z : C}
             (g : equivalence Y Z) (f : equivalence X Y)
    : id₁ X ==> (equiv_inv f ∘ equiv_inv g) ∘ (g ∘ f).
  Proof.
    refine (assoc_inv _ _ (g ∘ f) o _).
    refine ((_ ◅ _) o (equiv_counit f)).
    refine (assoc _ g f o _).
    exact (((equiv_counit g) ▻ f) o rinvunitor f).
  Defined.

  Definition comp_counit_isiso
             {X Y Z : C}
             (g : equivalence Y Z) (f : equivalence X Y)
    : is_invertible_2cell (comp_counit g f).
  Proof.
    unfold comp_counit.
    is_iso.
    - exact (equiv_counit_iso f).
    - exact (equiv_counit_iso g).
  Defined.

  Definition comp_unit
             {X Y Z : C}
             (g : equivalence Y Z) (f : equivalence X Y)
    : (g ∘ f) ∘ (equivalence_inv f ∘ equivalence_inv g) ==> (id₁ Z).
  Proof.
    refine (_ o assoc g f _).
    refine (equiv_unit g o (g ◅ _)).
    refine (_ o assoc_inv f _ _).
    refine (runitor _ o _).
    exact (equiv_unit f ▻ _).
  Defined.

  Definition comp_unit_isiso
        {X Y Z : C}
        (g : equivalence Y Z) (f : equivalence X Y)
    : is_invertible_2cell (comp_unit g f).
  Proof.
    unfold comp_unit.
    is_iso.
    - exact (equiv_unit_iso f).
    - exact (equiv_unit_iso g).
  Defined.

  Definition comp_isequiv
             {X Y Z : C}
             (g : equivalence Y Z) (f : equivalence X Y)
    : is_equivalence (g ∘ f).
  Proof.
    use build_equiv.
    - exact (equivalence_inv f ∘ equivalence_inv g).
    - exact (comp_unit g f).
    - exact (comp_counit g f).
    - exact (comp_unit_isiso g f).
    - exact (comp_counit_isiso g f).
  Defined.

  Definition comp_equiv
             {X Y Z : C}
             (g : equivalence Y Z) (f : equivalence X Y)
    : equivalence X Z
    := Build_equivalence (g ∘ f) (comp_isequiv g f).

  Definition iso_equiv
             {X Y : C}
             {f g : C⟦X,Y⟧}
             (Hf : is_equivalence f)
             (α : f ==> g)
             (Hα : is_invertible_2cell α)
    : is_equivalence g.
  Proof.
    pose (ginv := equiv_inv Hf).
    use build_equiv.
    - exact ginv.
    - exact (equiv_unit Hf o Hα ^-1 ▻ ginv).
    - exact (ginv ◅ α o equiv_counit Hf).
    - is_iso.
      exact (equiv_unit_iso Hf).
    - is_iso.
      exact (equiv_counit_iso Hf).
  Defined.
End Equivalence.