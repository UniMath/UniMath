(***************************************************************************

 Total categories of right modules

 In this file, the total category of right modules in some fixed monoidal
 category C. Objects are pairs (R, M) where R is a monoid in C and M is
 a right module over R.

 Given R --> R' a morphism of monoids, the pullback functor transforms modules
 over R' into modules over R.

 Contents
 1. Pullback functor
 2. Total category of right modules
 ***************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.RModules.

Import BifunctorNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section TotalCategoryOfRModules.
  Context {C : monoidal_cat}.

  Local Notation "x ⊗l f" := (x ⊗^{C}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{C}_{r} y) (at level 31).

  (**
   1. Pullback functor
   *)

  Lemma pullback_functor_funct_unit
    {R R' : C} {R_m : monoid C R} {R'_m : monoid C R'}
    (M' : C) (p' : module R' R'_m M')
    (f : R --> R') (f_m : is_monoid_mor C R_m R'_m f)
    : module_laws_unit R R_m (M' ⊗l f · p').
  Proof.
    unfold module_laws_unit; rewrite assoc.
    induction p' as [p' [w H]]; cbn.
    rewrite <- H.
    use (maponpaths (λ x, x · _)); induction f_m as [_ H2].
    rewrite <- (bifunctor_leftcomp C); now use maponpaths.
  Qed.

  Lemma pullback_functor_funct_assoc
    {R R' : C} {R_m : monoid C R} {R'_m : monoid C R'}
    (M' : C) (p' : module R' R'_m M')
    (f : R --> R') (f_m : is_monoid_mor C R_m R'_m f)
    : module_laws_assoc R R_m (M' ⊗l f · p').
  Proof.
    unfold module_laws_assoc; do 2 rewrite assoc; rewrite (bifunctor_rightcomp C).
    etrans; [etrans; etrans|].
    - refine (maponpaths (λ x, x · _) _).
      rewrite <- assoc, <- (bifunctor_leftcomp C).
      do 2 (refine (maponpaths _ _)).
      symmetry; use (pr1 f_m).
    - refine (maponpaths (λ x, _ · M' ⊗l (x · _) · _) _).
      assert (f #⊗ f = f ⊗r R · R' ⊗l f) as H by
      now rewrite tensor_split', @tensor_mor_right, @tensor_mor_left.
      use H.
    - do 2 rewrite (bifunctor_leftcomp C), assoc.
      rewrite (monoidal_associatornatleftright C).
      do 3 rewrite <- assoc; refine (maponpaths _ _).
      now rewrite assoc, (monoidal_associatornatleft C).
    - refine (maponpaths _ _); rewrite <- assoc.
      refine (maponpaths _ _); rewrite assoc.
      use (module_laws_assoc_from_module _ R'_m p').
    - do 2 rewrite <- assoc; use (maponpaths (λ x, _ · x)).
      do 2 rewrite assoc; use (maponpaths (λ x, x · _)).
      do 2 rewrite @tensor_mor_left, @tensor_mor_right.
      use tensor_swap'.
  Qed.

  Definition pullback_functor_funct
    {R R' : C} {R_m : monoid C R} {R'_m : monoid C R'}
    (M' : C) (p' : module R' R'_m M')
    (f : R --> R') (f_m : is_monoid_mor C R_m R'_m f)
    : module R R_m M'.
  Proof.
    exists (M' ⊗l f · p').
    split; [now use pullback_functor_funct_assoc | now use pullback_functor_funct_unit].
  Defined.

  Lemma pullback_functor_on_morphisms_is_module_morphism
    (R R' : C) (R_m : monoid C R) (R'_m : monoid C R')
    (f : R --> R') (f_m : is_monoid_mor C R_m R'_m f)
    (M M' : C) (p : module R' R'_m M) (p' : module R' R'_m M')
    (r : M --> M') (r_m : is_module_mor _ _ p p' r)
    : is_module_mor R R_m (pullback_functor_funct M p f f_m)
      (pullback_functor_funct M' p' f f_m) r.
  Proof.
    unfold is_module_mor; cbn; symmetry; etrans.
    + rewrite <- assoc; refine (!maponpaths _ r_m).
    + do 2 rewrite assoc; use (maponpaths (λ x, x · _)).
      do 2 rewrite @tensor_mor_left, @tensor_mor_right.
      use tensor_swap'.
  Qed.


  Definition pullback_functor_data
    (R R' : C) (R_m : monoid C R) (R'_m : monoid C R')
    (f : R --> R') (f_m : is_monoid_mor C R_m R'_m f)
    : functor_data (MOD R' R'_m) (MOD R R_m).
  Proof.
    use make_functor_data.
    - intro M; induction M as [M p].
      exists M; cbn in *.
      exact (pullback_functor_funct _ p _ f_m).
    - intros [M p] [M' p']; cbn in *; intros [ r r_m ].
      exists r.
      now use pullback_functor_on_morphisms_is_module_morphism.
  Defined.

  Definition pullback_functor_is_functor
    (R R' : C) (R_m : monoid C R) (R'_m : monoid C R')
    (f : R --> R') (f_m : is_monoid_mor C R_m R'_m f)
    : is_functor (pullback_functor_data R R' R_m R'_m f f_m).
  Proof.
    use make_is_functor.
    - intros [M p].
      use invmap; [|use path_sigma_hprop|easy].
      use isaprop_is_module_mor.
    - intros M M' M'' u v.
      use invmap; [|use path_sigma_hprop|easy].
      use isaprop_is_module_mor.
  Qed.


  Definition pullback_functor
    (R R' : C) (R_m : monoid C R) (R'_m : monoid C R')
    (f : R --> R') (f_m : is_monoid_mor C R_m R'_m f)
    : (MOD R' R'_m) ⟶ (MOD R R_m).
  Proof.
    use make_functor.
    - now use pullback_functor_data.
    - now use pullback_functor_is_functor.
  Defined.


  Definition pullback_functor' (R R' : MON C) (f : R --> R')
    : MOD (pr1 R') (pr2 R') ⟶ MOD (pr1 R) (pr2 R).
  Proof.
    induction R as [R R_m].
    induction R' as [R' R'_m].
    induction f as [f f_m].
    now use pullback_functor.
  Defined.

  (**
   2. Total category of right modules
   *)

  Definition total_category_of_modules_disp_cat_ob_mor : disp_cat_ob_mor (MON C).
  Proof.
    use tpair.
    - intros [R R_m]; now use MOD.
    - intros R R' M M' f; exact (M --> pullback_functor' R R' f M').
  Defined.

  Lemma id_is_monoid_with_module_mor (R : C) (R_m : monoid C R)
    (M : C) (p : module R R_m M) (q : is_monoid_mor C R_m R_m (identity R))
    : is_module_mor R R_m p (pullback_functor_funct M p (identity R) q) (identity M).
  Proof.
    unfold is_module_mor, pullback_functor_funct; cbn.
    now rewrite id_right, assoc, @tensor_mor_right, @tensor_mor_left, tensor_id_id, id_left, id_left.
  Qed.

  Lemma comp_is_monoid_with_module_mor
    {R R' R'' : C}
    {R_m : _} {R'_m : _} {R''_m : _}
    (f : R --> R') (f_m : is_monoid_mor C R_m R'_m f)
    (g : R' --> R'') (g_m : is_monoid_mor C R'_m R''_m g)
    (M : MOD R R_m) (M' : MOD R' R'_m) (M'' : MOD R'' R''_m)
    (r : M --> pullback_functor' (R ,, R_m) (R' ,, R'_m) (f ,, f_m) M')
    (t : M' --> pullback_functor' (R' ,, R'_m) (R'' ,, R''_m) (g ,, g_m) M'')
    (u : is_monoid_mor C R_m R''_m (f · g))
    : is_module_mor R R_m (pr2 M)
      (pullback_functor_funct (pr1 M'') (pr2 M'') (f · g) u)
      (pr1 r · pr1 t).
  Proof.
    induction r as [r r_m]; simpl in r_m.
    induction t as [t t_m]; simpl in t_m.
    unfold is_module_mor in *; cbn in *;
    rewrite (bifunctor_leftcomp C), (bifunctor_rightcomp C), assoc, assoc, assoc.
    symmetry; etrans.
    - rewrite <- r_m, assoc, <- assoc.
      refine (!maponpaths _ t_m).
    - do 2 rewrite assoc; do 2 use (maponpaths (λ x, x · _)).
      do 2 rewrite <- assoc; use maponpaths.
      do 2 rewrite @tensor_mor_left, @tensor_mor_right.
      use tensor_swap'.
  Qed.

  Definition total_category_of_modules_disp_cat_id_comp
    : disp_cat_id_comp (MON C) total_category_of_modules_disp_cat_ob_mor.
  Proof.
    split.
    - intros [R R_m] [M p]; eexists; use id_is_monoid_with_module_mor.
    - intros [R R_m] [R' R'_m] [R'' R''_m] [f f_m] [g g_m] [M p] [M' p'] [M'' p''] r t.
      exists (pr1 r · pr1 t); use (comp_is_monoid_with_module_mor _ _ _ _ _ _ _ r t _).
  Defined.

  Definition total_category_of_modules_disp_cat_data : disp_cat_data (MON C)
    := total_category_of_modules_disp_cat_ob_mor ,, total_category_of_modules_disp_cat_id_comp.

  Lemma total_category_of_modules_disp_cat_axioms : disp_cat_axioms _ total_category_of_modules_disp_cat_data.
  Proof.
    repeat split; intros;
    try use homset_property;
    (use invmap; [|use path_sigma_hprop|]);
    try use isaprop_is_module_mor;
    unfold mor_disp, transportb;
    rewrite functtransportf; cbn;
    rewrite transportf_total2; cbn;
    rewrite transportf_const.
    - use id_left.
    - use id_right.
    - use assoc.
  Qed.

  Definition total_category_of_modules_disp_cat : disp_cat (MON C)
    := total_category_of_modules_disp_cat_data ,, total_category_of_modules_disp_cat_axioms.

  Definition total_category_of_modules : category
    := total_category total_category_of_modules_disp_cat.
End TotalCategoryOfRModules.
