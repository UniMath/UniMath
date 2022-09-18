Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Local Open Scope cat.

Section BraidedSymmetricMonoidalCategories.

  Import BifunctorNotations.
  Import MonoidalNotations.

  Definition braiding_data {C : category} (M : monoidal C) : UU
    := ∏ x y : C, C⟦x ⊗_{M} y, y ⊗_{M} x⟧.

  Definition braiding_law_naturality_left
             {C : category} {M : monoidal C} (B : braiding_data M)
    : UU := ∏ x y1 y2 : C, ∏ g : C⟦y1, y2⟧,
          (B x y1) · (g ⊗^{M}_{r} x) = (x ⊗^{M}_{l} g) · (B x y2).

  Definition braiding_law_naturality_right
             {C : category} {M : monoidal C} (B : braiding_data M)
    : UU := ∏ x1 x2 y : C, ∏ f : C⟦x1, x2⟧,
          (B x1 y) · (y ⊗^{M}_{l} f) = (f ⊗^{M}_{r} y) · (B x2 y).

  Definition braiding_law_naturality
             {C : category} {M : monoidal C} (B : braiding_data M)
    : UU := braiding_law_naturality_left B × braiding_law_naturality_right B.

  Definition braiding_iso
             {C : category} {M : monoidal C} (B1 B2 : braiding_data M)
    : UU := ∏ x y : C, is_inverse_in_precat (B1 x y) (B2 y x).

  Definition braiding_law_hexagon1
             {C : category} {M : monoidal C} (B : braiding_data M)
    : UU := ∏ x y z : C,
        α^{M}_{x,y,z} · (B x (y⊗_{M} z)) · α^{M}_{y,z,x}
        = ((B x y) ⊗^{M}_{r} z) · α^{M}_{y,x,z} · (y ⊗^{M}_{l} (B x z)).

  Definition braiding_law_hexagon2
             {C : category} {M : monoidal C} (B : braiding_data M)
    : UU := ∏ x y z : C,
        αinv^{M}_{x,y,z} · (B (x⊗_{M} y) z) · αinv^{M}_{z,x,y}
        = (x ⊗^{M}_{l} (B y z)) · αinv^{M}_{x,z,y} · ((B x z) ⊗^{M}_{r} y).

  Definition braiding_law_hexagon
             {C : category} {M : monoidal C} (B : braiding_data M)
    : UU := braiding_law_hexagon1 B × braiding_law_hexagon2 B.

  Definition braiding_laws {C : category} {M : monoidal C} (B Binv : braiding_data M)
    : UU := braiding_law_naturality B × braiding_iso B Binv × braiding_law_hexagon B.

  Lemma isaprop_braiding_laws {C : category} {M : monoidal C} (B Binv : braiding_data M)
    : isaprop (braiding_laws B Binv).
  Proof.
    repeat (apply isapropdirprod) ; repeat (apply impred_isaprop ; intro) ; try (apply homset_property).
    apply isapropdirprod ; apply homset_property.
  Qed.

  Definition braiding {C : category} (M : monoidal C) : UU
    := ∑ B Binv : braiding_data M, braiding_laws B Binv.

  Definition monoidal_braiding_data {C : category} {M : monoidal C} (B : braiding M)
    : braiding_data M := pr1 B.
  Coercion monoidal_braiding_data : braiding >-> braiding_data.

  Definition monoidal_braiding_data_inv {C : category} {M : monoidal C} (B : braiding M)
    : braiding_data M := pr12 B.

  Definition monoidal_braiding_laws {C : category} {M : monoidal C} (B : braiding M)
    : braiding_laws (monoidal_braiding_data B) (monoidal_braiding_data_inv B) := pr22 B.

  Definition monoidal_braiding_inverses {C : category} {M : monoidal C} (B : braiding M)
    : braiding_iso (monoidal_braiding_data B) (monoidal_braiding_data_inv B)
    := pr12 (monoidal_braiding_laws B) .

  Definition monoidal_braiding_naturality {C : category} {M : monoidal C} (B : braiding M)
    : braiding_law_naturality (monoidal_braiding_data B)
    := pr1 (monoidal_braiding_laws B) .

  Definition monoidal_braiding_naturality_right {C : category} {M : monoidal C} (B : braiding M)
    : braiding_law_naturality_right (monoidal_braiding_data B)
    := pr2 (monoidal_braiding_naturality B) .

  Definition monoidal_braiding_naturality_left {C : category} {M : monoidal C} (B : braiding M)
    : braiding_law_naturality_left (monoidal_braiding_data B)
    := pr1 (monoidal_braiding_naturality B) .

  Definition symmetric {C : category} (M : monoidal C) : UU
    := ∑ B : braiding_data M, braiding_laws B B.

  Definition symmetric_to_braiding {C : category} {M : monoidal C} (B : symmetric M)
    : braiding M. (* := (pr1 B,, (pr1 B ,, pr2 B)). *)
  Proof.
    exists (pr1 B).
    exists (pr1 B).
    exact (pr2 B).
  Defined.
  Coercion symmetric_to_braiding : symmetric >-> braiding.

  Definition symmetric_whiskers_swap_nat_trans_data
        {C : category} {M : monoidal C} (B : symmetric M) (x : C)
    : nat_trans_data
        (leftwhiskering_functor M (bifunctor_leftid M) (bifunctor_leftcomp M) x)
        (rightwhiskering_functor M (bifunctor_rightid M) (bifunctor_rightcomp M) x)
    := λ y, (monoidal_braiding_data B) x y.

  Lemma symmetric_whiskers_swap_is_nat_trans
        {C : category} {M : monoidal C} (B : symmetric M) (x : C)
    : is_nat_trans _ _ (symmetric_whiskers_swap_nat_trans_data B x).
  Proof.
    intros y1 y2 g.
    exact (! monoidal_braiding_naturality_left B x y1 y2 g).
  Qed.

  Definition symmetric_whiskers_swap_nat_trans
        {C : category} {M : monoidal C} (B : symmetric M) (x : C)
    : nat_trans
        (leftwhiskering_functor M (bifunctor_leftid M) (bifunctor_leftcomp M) x)
        (rightwhiskering_functor M (bifunctor_rightid M) (bifunctor_rightcomp M) x)
    := symmetric_whiskers_swap_nat_trans_data B x ,, symmetric_whiskers_swap_is_nat_trans B x.

  Lemma symmetric_whiskers_swap_is_nat_iso
        {C : category} {M : monoidal C} (B : symmetric M) (x : C)
    : is_nat_z_iso (symmetric_whiskers_swap_nat_trans B x).
  Proof.
    intro y.
    exists ((monoidal_braiding_data B) y x).
    split ; apply monoidal_braiding_inverses.
  Defined.

  Definition symmetric_whiskers_swap_nat_z_iso
        {C : category} {M : monoidal C} (B : symmetric M) (x : C)
    : nat_z_iso _ _ := symmetric_whiskers_swap_nat_trans B x,, symmetric_whiskers_swap_is_nat_iso B x.

End BraidedSymmetricMonoidalCategories.
