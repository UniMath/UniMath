(*********************************************************************************

 Braided and symmetric monoidal categories

 Braided and symmetric monoidal categories are classes of monoidal categories in
 which tensoring is commutative in a coherent way.

 Contents
 1. Braided monoidal categories
 2. Symmetric monoidal categories
 3. Accessors for symmetric monoidal categories

Note: after refactoring on March 10, 2023, the prior Git history of this development is found via
git log -- UniMath/CategoryTheory/Monoidal/BraidedMonoidalCategoriesWhiskered.v

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Local Open Scope cat.
Local Open Scope moncat.

Import BifunctorNotations.
Import MonoidalNotations.

Section BraidedSymmetricMonoidalCategories.

  (**
   1. Braided monoidal categories
   *)
  Definition braiding_data {C : category} (M : monoidal C) : UU
    := ∏ x y : C, C⟦x ⊗_{M} y, y ⊗_{M} x⟧.

  Definition braiding_law_naturality_left
             {C : category} {M : monoidal C}
             (B : braiding_data M)
    : UU
    := ∏ (x y1 y2 : C) (g : C⟦y1, y2⟧),
       (B x y1) · (g ⊗^{M}_{r} x)
       =
       (x ⊗^{M}_{l} g) · (B x y2).

  Definition braiding_law_naturality_right
             {C : category} {M : monoidal C}
             (B : braiding_data M)
    : UU
    := ∏ (x1 x2 y : C) (f : C⟦x1, x2⟧),
       (B x1 y) · (y ⊗^{M}_{l} f)
       =
       (f ⊗^{M}_{r} y) · (B x2 y).

  Definition braiding_law_naturality
             {C : category} {M : monoidal C}
             (B : braiding_data M)
    : UU
    := braiding_law_naturality_left B × braiding_law_naturality_right B.

  Definition braiding_iso
             {C : category} {M : monoidal C}
             (B1 B2 : braiding_data M)
    : UU
    := ∏ (x y : C), is_inverse_in_precat (B1 x y) (B2 y x).

  Definition braiding_law_hexagon1
             {C : category} {M : monoidal C}
             (B : braiding_data M)
    : UU
    := ∏ (x y z : C),
       α^{M}_{x,y,z} · (B x (y⊗_{M} z)) · α^{M}_{y,z,x}
       =
       ((B x y) ⊗^{M}_{r} z) · α^{M}_{y,x,z} · (y ⊗^{M}_{l} (B x z)).

  Definition braiding_law_hexagon2
             {C : category} {M : monoidal C}
             (B : braiding_data M)
    : UU
    := ∏ (x y z : C),
       αinv^{M}_{x,y,z} · (B (x⊗_{M} y) z) · αinv^{M}_{z,x,y}
       =
       (x ⊗^{M}_{l} (B y z)) · αinv^{M}_{x,z,y} · ((B x z) ⊗^{M}_{r} y).

  Definition braiding_law_hexagon
             {C : category} {M : monoidal C}
             (B : braiding_data M)
    : UU
    := braiding_law_hexagon1 B × braiding_law_hexagon2 B.

  Definition braiding_laws
             {C : category} {M : monoidal C}
             (B Binv : braiding_data M)
    : UU
    := braiding_law_naturality B × braiding_iso B Binv × braiding_law_hexagon B.

  (** the following is done for the situation of symmetric monoidal categories only *)
  Definition braiding_laws_one_hexagon
             {C : category}
             {M : monoidal C}
             (B : braiding_data M)
    : UU
    := braiding_law_naturality B × braiding_iso B B × braiding_law_hexagon1 B.

  (*
  Definition braiding_laws_to_braiding_laws_one_hexagon
             {C : category}
             {M : monoidal C}
             (B : braiding_data M) :
    braiding_laws B B -> braiding_laws_one_hexagon B.
  Proof.
    intro Hyp.
    split3.
    - exact (pr1 Hyp).
    - exact (pr12 Hyp).
    - exact (pr122 Hyp).
  Defined.

  Coercion braiding_laws_to_braiding_laws_one_hexagon : braiding_laws >-> braiding_laws_one_hexagon.
   *)

  Definition braiding_laws_one_hexagon_braiding_z_iso
             {C : category}
             {M : monoidal C}
             {B : braiding_data M}
             (H : braiding_laws_one_hexagon B)
             (x y : C)
    : z_iso (x ⊗_{M} y) (y ⊗_{M} x).
  Proof.
    use make_z_iso.
    - exact (B x y).
    - exact (B y x).
    - abstract (split ; apply H).
  Defined.

  Proposition braiding_laws_one_hexagon_to_braiding_laws
              {C : category}
              {M : monoidal C}
              {B : braiding_data M}
              (H : braiding_laws_one_hexagon B)
    : braiding_laws B B.
  Proof.
    split4.
    - split.
      + exact (pr11 H).
      + exact (pr21 H).
    - exact (pr12 H).
    - exact (pr22 H).
    - intros x y z.
      pose (pr22 H z x y).
      rewrite !assoc'.
      use (z_iso_inv_on_right _ _ _ (z_iso_from_associator_iso M _ _ _)).
      cbn.
      use (z_iso_inv_on_right _ _ _ (braiding_laws_one_hexagon_braiding_z_iso H _ _)).
      cbn.
      refine (!(id_right _) @ _).
      use (z_iso_inv_on_right _ _ _ (z_iso_from_associator_iso M _ _ _)).
      cbn.
      rewrite !assoc.
      rewrite p.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        refine (!(bifunctor_leftcomp M _ _ _ _ (B z y) (B y z)) @ _).
        etrans.
        {
          apply maponpaths.
          apply H.
        }
        apply (bifunctor_leftid M).
      }
      rewrite id_left.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply (monoidal_associatorisolaw M).
      }
      rewrite id_left.
      refine (!(bifunctor_rightcomp M _ _ _ _ (B z x) (B x z)) @ _).
      etrans.
      {
        apply maponpaths.
        apply H.
      }
      apply (bifunctor_rightid M).
  Qed.

  Lemma isaprop_braiding_laws
        {C : category} {M : monoidal C}
        (B Binv : braiding_data M)
    : isaprop (braiding_laws B Binv).
  Proof.
    repeat (apply isapropdirprod) ; repeat (apply impred_isaprop ; intro) ; try (apply homset_property).
    apply isapropdirprod ; apply homset_property.
  Qed.

  Definition braiding {C : category} (M : monoidal C) : UU
    := ∑ B Binv : braiding_data M, braiding_laws B Binv.

  Definition monoidal_braiding_data
             {C : category} {M : monoidal C}
             (B : braiding M)
    : braiding_data M
    := pr1 B.

  Coercion monoidal_braiding_data : braiding >-> braiding_data.

  Definition monoidal_braiding_data_inv
             {C : category} {M : monoidal C}
             (B : braiding M)
    : braiding_data M
    := pr12 B.

  Definition monoidal_braiding_laws
             {C : category} {M : monoidal C}
             (B : braiding M)
    : braiding_laws (monoidal_braiding_data B) (monoidal_braiding_data_inv B)
    := pr22 B.

  Definition monoidal_braiding_inverses
             {C : category} {M : monoidal C}
             (B : braiding M)
    : braiding_iso (monoidal_braiding_data B) (monoidal_braiding_data_inv B)
    := pr12 (monoidal_braiding_laws B).

  Definition monoidal_braiding_naturality
             {C : category} {M : monoidal C}
             (B : braiding M)
    : braiding_law_naturality (monoidal_braiding_data B)
    := pr1 (monoidal_braiding_laws B).

  Definition monoidal_braiding_naturality_right
             {C : category} {M : monoidal C}
             (B : braiding M)
    : braiding_law_naturality_right (monoidal_braiding_data B)
    := pr2 (monoidal_braiding_naturality B) .

  Definition monoidal_braiding_naturality_left
             {C : category} {M : monoidal C}
             (B : braiding M)
    : braiding_law_naturality_left (monoidal_braiding_data B)
    := pr1 (monoidal_braiding_naturality B) .

  (**
   2. Symmetric monoidal categories
   *)
  Definition symmetric {C : category} (M : monoidal C) : UU
    := ∑ (B : braiding_data M), braiding_laws B B.

  Definition symmetric_to_braiding
             {C : category} {M : monoidal C}
             (B : symmetric M)
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
        (leftwhiskering_functor M x)
        (rightwhiskering_functor M x)
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
        (leftwhiskering_functor M x)
        (rightwhiskering_functor M x)
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
    : nat_z_iso _ _
    := symmetric_whiskers_swap_nat_trans B x,, symmetric_whiskers_swap_is_nat_iso B x.
End BraidedSymmetricMonoidalCategories.

(**
 3. Accessors for symmetric monoidal categories
 *)
Definition sym_monoidal_cat
  : UU
  := ∑ (V : monoidal_cat), symmetric V.

#[reversible=no] Coercion sym_monoidal_cat_to_monoidal_cat
         (V : sym_monoidal_cat)
  : monoidal_cat
  := pr1 V.

#[reversible=no] Coercion sym_monoidal_cat_to_symmetric
         (V : sym_monoidal_cat)
  : symmetric V
  := pr2 V.

Definition sym_mon_cat_laws_tensored
           (V : monoidal_cat)
           (c : ∏ (x y : V), x ⊗ y --> y ⊗ x)
  : UU
  := (∏ (x y : V), c x y · c y x = identity _)
     ×
     (∏ (x₁ x₂ y₁ y₂ : V)
        (f : x₁ --> x₂)
        (g : y₁ --> y₂),
      f #⊗ g · c x₂ y₂
      =
      c x₁ y₁ · g #⊗ f)
     ×
     (∏ (x y z : V),
      mon_lassociator x y z
      · c x (y ⊗ z)
      · mon_lassociator y z x
      =
      c x y #⊗ identity z
      · mon_lassociator y x z
      · identity y #⊗ c x z).

Section BuilderTensored.
  Context (V : monoidal_cat)
          (c : ∏ (x y : V), x ⊗ y --> y ⊗ x)
          (Hc : sym_mon_cat_laws_tensored V c).

  Definition make_braiding_laws
    : braiding_laws c c.
  Proof.
    use braiding_laws_one_hexagon_to_braiding_laws.
    repeat split.
    - intros x y₁ y₂ g.
      pose (pr12 Hc x x y₁ y₂ (identity x) g).
      unfold monoidal_cat_tensor_mor in p.
      unfold functoronmorphisms1 in p.
      rewrite (bifunctor_leftid V) in p.
      rewrite (bifunctor_rightid V) in p.
      rewrite id_left, id_right in p.
      exact (!p).
    - intros x₁ x₂ y f.
      pose (pr12 Hc x₁ x₂ y y f (identity y)).
      unfold monoidal_cat_tensor_mor in p.
      unfold functoronmorphisms1 in p.
      rewrite (bifunctor_leftid V) in p.
      rewrite (bifunctor_rightid V) in p.
      rewrite id_left, id_right in p.
      exact (!p).
    - exact (pr1 Hc x y).
    - exact (pr1 Hc y x).
    - intros x y z.
      pose (pr22 Hc x y z).
      refine (p @ _).
      rewrite !assoc'.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite (bifunctor_leftid V).
      rewrite (bifunctor_rightid V).
      rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition make_symmetric
    : symmetric V.
  Proof.
    refine (c ,, _).
    exact make_braiding_laws.
  Defined.
End BuilderTensored.

Section Accessors.
  Context (V : sym_monoidal_cat).

  Definition sym_mon_braiding
             (x y : V)
    : x ⊗ y --> y ⊗ x
    := monoidal_braiding_data (pr2 V) x y.

  Proposition sym_mon_braiding_inv
              (x y : V)
    : sym_mon_braiding x y · sym_mon_braiding y x = identity _.
  Proof.
    exact (pr1 (pr1 (pr222 V) x y)).
  Qed.

  Definition is_z_isomorphism_sym_mon_braiding
             (x y : V)
    : is_z_isomorphism (sym_mon_braiding x y).
  Proof.
    use make_is_z_isomorphism.
    - exact (sym_mon_braiding y x).
    - abstract
        (split ; apply sym_mon_braiding_inv).
  Defined.

  Definition sym_mon_braiding_z_iso
             (x y : V)
    : z_iso (x ⊗ y) (y ⊗ x)
    := sym_mon_braiding x y ,, is_z_isomorphism_sym_mon_braiding x y.

  Proposition tensor_sym_mon_braiding
              {x₁ x₂ y₁ y₂ : V}
              (f : x₁ --> x₂)
              (g : y₁ --> y₂)
    : f #⊗ g · sym_mon_braiding x₂ y₂
      =
      sym_mon_braiding x₁ y₁ · g #⊗ f.
  Proof.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (pr1 (pr122 V) x₂ y₁ y₂ g).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (pr2 (pr122 V) x₁ x₂ y₁ f).
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    use (bifunctor_equalwhiskers V).
  Qed.

  Proposition sym_mon_hexagon_lassociator
              (x y z : V)
    : mon_lassociator x y z
      · sym_mon_braiding x (y ⊗ z)
      · mon_lassociator y z x
      =
      sym_mon_braiding x y #⊗ identity z
      · mon_lassociator y x z
      · identity y #⊗ sym_mon_braiding x z.
  Proof.
    pose (pr12 (pr222 V) x y z) as p.
    refine (p @ _).
    rewrite !assoc'.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite (bifunctor_leftid V).
    rewrite (bifunctor_rightid V).
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Proposition sym_mon_hexagon_lassociator1
              (x y1 y2 z : V)
    : mon_lassociator x (y1 ⊗ y2) z
        · x ⊗^{ V}_{l} (mon_lassociator y1 y2 z · y1 ⊗^{ V}_{l} sym_mon_braiding y2 z)
        · mon_rassociator x y1 (z ⊗ y2)
      = mon_rassociator x y1 y2 ⊗^{ V}_{r} z
          · mon_lassociator (x ⊗ y1) y2 z
          · (x ⊗ y1) ⊗^{ V}_{l} sym_mon_braiding y2 z.
  Proof.

    apply pathsinv0.
    use (z_iso_inv_on_left _ _ _ _ (mon_lassociator _ _ _ ,, mon_rassociator _ _ _ ,, _)).
    { apply monoidal_associatorisolaw. }
    cbn.

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      apply monoidal_associatornatleft.
    }

    rewrite (bifunctor_leftcomp V).
    rewrite ! assoc.
    apply maponpaths_2.

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, mon_lassociator_lassociator.
    }

    rewrite ! assoc.
    rewrite <- (when_bifunctor_becomes_leftwhiskering V).
    apply maponpaths_2.
    rewrite <- (when_bifunctor_becomes_rightwhiskering V).
    etrans.
    2: {
      apply maponpaths_2.
      apply tensor_comp_id_r.
    }
    rewrite mon_rassociator_lassociator.
    rewrite tensor_id_id.
    exact (! id_left _).
  Qed.

  (** a sanity check *)
  Lemma sym_mon_cat_laws_tensored_from_sym_mon :
    sym_mon_cat_laws_tensored V sym_mon_braiding.
  Proof.
    repeat split.
    - apply sym_mon_braiding_inv.
    - intros; apply tensor_sym_mon_braiding.
    - apply sym_mon_hexagon_lassociator.
  Qed.

  Proposition sym_mon_tensor_lassociator
              (x y z : V)
    : sym_mon_braiding x (y ⊗ z)
      =
      mon_rassociator x y z
      · sym_mon_braiding x y #⊗ identity z
      · mon_lassociator y x z
      · identity y #⊗ sym_mon_braiding x z
      · mon_rassociator y z x.
  Proof.
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- sym_mon_hexagon_lassociator.
      rewrite !assoc'.
      rewrite mon_lassociator_rassociator.
      rewrite id_right.
      apply idpath.
    }
    rewrite !assoc.
    rewrite mon_rassociator_lassociator.
    apply id_left.
  Qed.

  Proposition sym_mon_tensor_lassociator0
              (x y z : V)
    : sym_mon_braiding x (y ⊗ z)
        · mon_lassociator y z x
      =
      mon_rassociator x y z
      · sym_mon_braiding x y #⊗ identity z
      · mon_lassociator y x z
      · identity y #⊗ sym_mon_braiding x z.
  Proof.
    rewrite sym_mon_tensor_lassociator.
    rewrite ! assoc'.
    rewrite mon_rassociator_lassociator.
    now rewrite id_right.
  Qed.

  Proposition sym_mon_tensor_lassociator'
              (x y z : V)
    : sym_mon_braiding x y #⊗ identity z
      =
      mon_lassociator x y z
      · sym_mon_braiding x (y ⊗ z)
      · mon_lassociator y z x
      · identity y #⊗ sym_mon_braiding z x
      · mon_rassociator y x z.
  Proof.
    rewrite (sym_mon_hexagon_lassociator x y z).
    rewrite !assoc'.
    refine (!(id_right _) @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite sym_mon_braiding_inv.
      rewrite tensor_id_id.
      apply id_left.
    }
    apply mon_lassociator_rassociator.
  Qed.

  Lemma sym_mon_tensor_lassociator1 (x y z : V)
    : mon_lassociator y x z · y ⊗^{V}_{l} sym_mon_braiding x z
      = sym_mon_braiding y x ⊗^{V}_{r} z
          · mon_lassociator x y z
          · sym_mon_braiding x (y ⊗ z)
          · mon_lassociator y z x.
  Proof.
    apply pathsinv0.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      exact (sym_mon_tensor_lassociator0 x y z).
    }
    etrans. {
      rewrite ! assoc.
      do 3 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply mon_lassociator_rassociator.
    }
    rewrite id_right.
    rewrite <- (when_bifunctor_becomes_leftwhiskering V).
    rewrite <- (when_bifunctor_becomes_rightwhiskering V).

    etrans. {
      do 2 apply maponpaths_2.
      rewrite (when_bifunctor_becomes_rightwhiskering V).
      apply maponpaths.
      apply (when_bifunctor_becomes_rightwhiskering V).
    }
    etrans. {
      do 2 apply maponpaths_2.
      apply pathsinv0, (bifunctor_rightcomp V).
    }
    rewrite sym_mon_braiding_inv.
    rewrite bifunctor_rightid.
    now rewrite id_left.
  Qed.

  Proposition sym_mon_hexagon_rassociator
              (x y z : V)
    : mon_rassociator x y z
      · sym_mon_braiding (x ⊗ y) z
      · mon_rassociator z x y
      =
      identity x #⊗ sym_mon_braiding y z
      · mon_rassociator x z y
      · sym_mon_braiding x z #⊗ identity y.
  Proof.
    pose (pr22 (pr222 V) x y z) as p.
    refine (p @ _).
    rewrite !assoc'.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    rewrite (bifunctor_leftid V).
    rewrite (bifunctor_rightid V).
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Proposition sym_mon_tensor_rassociator
              (x y z : V)
    : sym_mon_braiding (x ⊗ y) z
      =
      mon_lassociator x y z
      · identity x #⊗ sym_mon_braiding y z
      · mon_rassociator x z y
      · sym_mon_braiding x z #⊗ identity y
      · mon_lassociator z x y.
  Proof.
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- sym_mon_hexagon_rassociator.
      rewrite !assoc'.
      rewrite mon_rassociator_lassociator.
      rewrite id_right.
      apply idpath.
    }
    rewrite !assoc.
    rewrite mon_lassociator_rassociator.
    apply id_left.
  Qed.

  Proposition sym_mon_hexagon_rassociator0
              (x y z : V)
    : sym_mon_braiding (x ⊗ y) z
        · mon_rassociator z x y
        · sym_mon_braiding _ _ ⊗^{V}_{r} y
        · mon_lassociator _ _ _
      =
        mon_lassociator x y z
          · x ⊗^{V}_{l} sym_mon_braiding y z.
  Proof.
    rewrite sym_mon_tensor_rassociator.
    rewrite ! assoc'.
    etrans. {
      do 4 apply maponpaths.
      rewrite assoc.
      now rewrite mon_lassociator_rassociator.
    }
    rewrite id_left.
    apply maponpaths.
    etrans. {
      do 2 apply maponpaths.
      rewrite assoc.
      do 2 apply maponpaths_2.
      apply (when_bifunctor_becomes_rightwhiskering V).
    }

    etrans. {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply pathsinv0, (bifunctor_rightcomp V).
    }
    rewrite sym_mon_braiding_inv.
    rewrite (bifunctor_rightid V).
    rewrite id_left.
    rewrite mon_rassociator_lassociator.
    rewrite id_right.
    apply (when_bifunctor_becomes_leftwhiskering V).
  Qed.

  Proposition sym_mon_hexagon_rassociator1
              (x y z : V)
    :  sym_mon_braiding (x ⊗ y) z · mon_rassociator z x y · sym_mon_braiding z x ⊗^{ V}_{r} y
       = mon_lassociator x y z · x ⊗^{ V}_{l} sym_mon_braiding y z · mon_rassociator x z y.
  Proof.
     etrans.
      2: {
        apply maponpaths_2.
        apply sym_mon_hexagon_rassociator0.
      }

      etrans.
      2: {
        rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, mon_lassociator_rassociator.
      }
      rewrite ! assoc'.
      now rewrite id_right.
  Qed.

  Proposition sym_mon_braiding_lunitor
              (x : V)
    : sym_mon_braiding x (I_{V}) · mon_lunitor x = mon_runitor x.
  Proof.
    refine (!(id_right _) @ _ @ id_left _).
    rewrite <- mon_rinvunitor_runitor.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_rinvunitor.
    rewrite tensor_comp_id_r.
    rewrite sym_mon_tensor_lassociator'.
    rewrite !assoc'.
    rewrite <- mon_lunitor_triangle.
    etrans.
    {
      do 5 apply maponpaths.
      rewrite !assoc.
      rewrite mon_rassociator_lassociator.
      apply id_left.
    }
    rewrite <- mon_rinvunitor_triangle.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_rassociator_lassociator.
      rewrite id_left.
      apply idpath.
    }
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    refine (_ @ sym_mon_braiding_inv _ _).
    apply maponpaths.
    rewrite tensor_lunitor.
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite mon_lunitor_triangle.
    rewrite <- tensor_comp_id_r.
    rewrite mon_lunitor_I_mon_runitor_I.
    rewrite mon_rinvunitor_runitor.
    apply tensor_id_id.
  Qed.

  Proposition sym_mon_braiding_runitor
              (x : V)
    : sym_mon_braiding (I_{V}) x · mon_runitor x = mon_lunitor x.
  Proof.
    rewrite <- sym_mon_braiding_lunitor.
    rewrite !assoc.
    rewrite sym_mon_braiding_inv.
    apply id_left.
  Qed.

  Proposition sym_mon_braiding_rinvunitor
              (x : V)
    : mon_rinvunitor x · sym_mon_braiding x (I_{V}) = mon_linvunitor x.
  Proof.
    refine (!(id_right _) @ _ @ id_left _).
    rewrite <- mon_lunitor_linvunitor.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite sym_mon_braiding_lunitor.
    apply mon_rinvunitor_runitor.
  Qed.

  Proposition sym_mon_braiding_linvunitor
              (x : V)
    : mon_linvunitor x · sym_mon_braiding (I_{V}) x = mon_rinvunitor x.
  Proof.
    refine (!(id_right _) @ _ @ id_left _).
    rewrite <- mon_runitor_rinvunitor.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite sym_mon_braiding_runitor.
    apply mon_linvunitor_lunitor.
  Qed.

  Proposition sym_mon_braiding_id
    : sym_mon_braiding I_{V} I_{V} = identity (I_{V} ⊗ I_{V}).
  Proof.
    refine (_ @ mon_runitor_rinvunitor _).
    rewrite <- sym_mon_braiding_lunitor.
    rewrite !assoc'.
    rewrite mon_lunitor_I_mon_runitor_I.
    rewrite mon_runitor_rinvunitor.
    rewrite id_right.
    apply idpath.
  Qed.
End Accessors.
