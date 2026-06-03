(***************************************************************************

 Total categories of modules

 In this file, the total category of modules in some fixed monoidal category C.
 Objects in such categories are pairs (R, M) where R is a monoid in C and M is
 a module over R.

 ***************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Modules.

Import BifunctorNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section TotalCategoryOfModules.
  Context {C : monoidal_cat}.

  Local Definition m : monoidal C := monoidal_cat_to_monoidal  C.

  Local Notation "x ⊗l f" := (x ⊗^{m}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{m}_{r} y) (at level 31).

  Lemma pullback_functor_funct_unit
    {R R' : C} {R_m : monoid m R} {R'_m : monoid m R'}
    (M' : C) (p' : module R' R'_m M')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : module_laws_unit R R_m (M' ⊗l f · p').
  Proof.
    unfold module_laws_unit; rewrite assoc.
    induction p' as [p' [w H]]; cbn.
    rewrite <- H.
    use (maponpaths (λ x, x · _)); induction f_m as [_ H2]. 
    rewrite <- (bifunctor_leftcomp m); now use maponpaths.
  Qed.

  Lemma pullback_functor_funct_assoc
    {R R' : C} {R_m : monoid m R} {R'_m : monoid m R'}
    (M' : C) (p' : module R' R'_m M')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : module_laws_assoc R R_m (M' ⊗l f · p').
  Proof.
    unfold module_laws_assoc; do 2 rewrite assoc; rewrite (bifunctor_rightcomp m).
    etrans; [etrans; etrans|].
    - use (maponpaths (λ x, x · _)); [shelve|].
      rewrite <- assoc, <- (bifunctor_leftcomp m).
      do 2 (use maponpaths; [shelve|]).
      symmetry; use (pr1 f_m).
    - use (maponpaths (λ x, _ · M' ⊗l (x · _) · _)); [shelve|].
      assert (f #⊗ f = f ⊗r R · R' ⊗l f) as H by
      now rewrite tensor_split', @tensor_mor_right, @tensor_mor_left.
      use H.
    - do 2 rewrite (bifunctor_leftcomp m), assoc.
      rewrite (monoidal_associatornatleftright m).
      do 3 rewrite <- assoc; use maponpaths; [shelve|rewrite assoc].
      now rewrite (monoidal_associatornatleft m).
    - use maponpaths; [shelve|rewrite <- assoc].
      use maponpaths; [shelve|rewrite assoc].
      use (module_laws_assoc_from_module _ R'_m p').
    - do 2 rewrite <- assoc; use (maponpaths (λ x, _ · x)).
      do 2 rewrite assoc; use (maponpaths (λ x, x · _)).
      do 2 rewrite @tensor_mor_left, @tensor_mor_right.
      use tensor_swap'.
  Qed.

  Definition pullback_functor_funct
    {R R' : C} {R_m : monoid m R} {R'_m : monoid m R'}
    (M' : C) (p' : module R' R'_m M')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : module R R_m M'.
  Proof.
    exists (M' ⊗l f · p').
    split; [now use pullback_functor_funct_assoc | now use pullback_functor_funct_unit].
  Defined.

  Lemma pullback_functor_on_morphisms_is_module_morphism
    (R R' : C) (R_m : monoid m R) (R'_m : monoid m R')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    (M M' : C) (p : module R' R'_m M) (p' : module R' R'_m M')
    (r : M --> M') (r_m : is_module_mor _ _ p p' r)
    : is_module_mor R R_m (pullback_functor_funct M p f f_m)
      (pullback_functor_funct M' p' f f_m) r.
  Proof.
    unfold is_module_mor; cbn; symmetry; etrans.
    + rewrite <- assoc; use maponpaths; [shelve|].
      symmetry; use r_m.
    + do 2 rewrite assoc; use (maponpaths (λ x, x · _)).
      do 2 rewrite @tensor_mor_left, @tensor_mor_right.
      use tensor_swap'.
  Qed.


  Definition pullback_functor_data
    (R R' : C) (R_m : monoid m R) (R'_m : monoid m R')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : functor_data (MOD R' R'_m) (MOD R R_m).
  Proof.
    use make_functor_data.
    - intro M; induction M as [M p].
      exists M; cbn in *.
      use pullback_functor_funct.
      + use R'.
      + use R'_m.
      + use p.
      + use f.
      + use f_m.
    - intros [M p] [M' p']; cbn in *; intros [ r r_m ].
      exists r.
      now use pullback_functor_on_morphisms_is_module_morphism.
  Defined.

  Definition pullback_functor_is_functor
    (R R' : C) (R_m : monoid m R) (R'_m : monoid m R')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
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
    (R R' : C) (R_m : monoid m R) (R'_m : monoid m R')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : (MOD R' R'_m) ⟶ (MOD R R_m).
  Proof.
    use make_functor.
    - now use pullback_functor_data.
    - now use pullback_functor_is_functor.
  Defined.


  Definition monoid_with_module : UU := ∑ (R : MON C), MOD (pr1 R) (pr2 R).

  Definition pullback_functor' (R R' : MON C) (f : R --> R')
    : MOD (pr1 R') (pr2 R') ⟶ MOD (pr1 R) (pr2 R).
  Proof.
    induction R as [R R_m].
    induction R' as [R' R'_m].
    induction f as [f f_m].
    now use pullback_functor.
  Defined.

  Definition monoid_with_module_mor (RM R'M' : monoid_with_module) : UU.
  Proof.
    induction RM as [R M].
    induction R'M' as [R' M'].
    exact (∑ (f : R --> R'), M --> pullback_functor' R R' f M').
  Defined.

  Lemma id_is_monoid_with_module_mor (R : C) (R_m : monoid C R)
    (M : C) (p : module R R_m M) (q : is_monoid_mor m R_m R_m (identity R))
    : is_module_mor R R_m p (pullback_functor_funct M p (identity R) q) (identity M).
  Proof.
    unfold is_module_mor, pullback_functor_funct; cbn.
    now rewrite id_right, assoc, @tensor_mor_right, @tensor_mor_left, tensor_id_id, id_left, id_left.
  Qed.


  Definition id_monoid_with_module_mor (RM : monoid_with_module) : monoid_with_module_mor RM RM.
  Proof.
    induction RM as [R M].
    exists (identity R).
    induction R as [R R_m].
    induction M as [M p].
    exists (identity _); cbn.
    use id_is_monoid_with_module_mor.
  Defined.

  Lemma comp_is_monoid_with_module_mor
    (R R' R'' : C) 
    (R_m : _) (R'_m : _) (R''_m : _)
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    (g : R' --> R'') (g_m : is_monoid_mor m R'_m R''_m g)
    (M : MOD R R_m) (M' : MOD R' R'_m) (M'' : MOD R'' R''_m)
    (r : M --> pullback_functor' (R ,, R_m) (R' ,, R'_m) (f ,, f_m) M')
    (t : M' --> pullback_functor' (R' ,, R'_m) (R'' ,, R''_m) (g ,, g_m) M'')
    (u : is_monoid_mor m R_m R''_m (f · g))
    : is_module_mor R R_m
      (pullback_functor_funct (pr1 M') (pr2 M') f f_m)
      (pullback_functor_funct (pr1 M'') (pr2 M'') (f · g) u)
      (pr1 t).
  Proof.
    induction t as [t t_m]; simpl in t_m.
    unfold is_module_mor in *; cbn in *;
    rewrite (bifunctor_leftcomp m), assoc, assoc.
    symmetry; etrans.
    + rewrite <- assoc; use maponpaths; [shelve|use (!t_m)].
    + do 2 rewrite assoc; 
      do 2 use (maponpaths (λ x, x · _)).
      do 2 rewrite @tensor_mor_right, @tensor_mor_left.
      use tensor_swap'.
  Qed.

  Definition comp_monoid_with_module_mor (RM RM' RM'' : monoid_with_module)
    (fr : monoid_with_module_mor RM RM') (gt : monoid_with_module_mor RM' RM'')
    : monoid_with_module_mor RM RM''.
  Proof.
    induction RM as [R M];
    induction RM' as [R' M'];
    induction RM'' as [R'' M''];
    induction fr as [f r];
    induction gt as [g t].
    exists (f·g). 
    refine (r·_).
    exists (pr1 t); simpl.
    now use (comp_is_monoid_with_module_mor _).
  Defined.

  Definition total_category_of_modules_pre_data : precategory_data
    := make_precategory_data 
        (monoid_with_module,, monoid_with_module_mor)
        id_monoid_with_module_mor 
        comp_monoid_with_module_mor.

  Lemma total_category_of_modules_is_precategory 
    : is_precategory total_category_of_modules_pre_data.
  Proof.
    split.
    - split; (
        intros [R [M p]] [R' [M' p']] [[r r_m] [f f_m]]; cbn in *;
        use invmap; [|use total2_paths_equiv|];
        use tpair; cbn
      ).
      + use invmap; [|use path_sigma_hprop|];
        [use isaprop_is_monoid_mor|use id_left].
      + use invmap; [|use path_sigma_hprop|].
        use isaprop_is_module_mor.
        rewrite transportf_total2; simpl.
        rewrite transportf_const; use id_left.
      + use invmap; [|use path_sigma_hprop|];
        [use isaprop_is_monoid_mor|use id_right].
      + use invmap; [|use path_sigma_hprop|].
        use isaprop_is_module_mor.
        rewrite transportf_total2; simpl.
        rewrite transportf_const; use id_right.
    - split; (
        intros [R [M p]] [R' [M' p']] [R'' [M'' p'']] [R''' [M''' p''']] 
          [[r r_m] [f f_m]] [[r' r'_m] [f' f'_m]] [[r'' r''_m] [f'' f''_m]]; 
        use invmap; [|use total2_paths_equiv|];
        use tpair; cbn
      ).
      + use invmap; [|use path_sigma_hprop|];
        [use isaprop_is_monoid_mor|use assoc].
      + use invmap; [|use path_sigma_hprop|].
        use isaprop_is_module_mor.
        rewrite transportf_total2; simpl.
        rewrite transportf_const; use assoc.
      + use invmap; [|use path_sigma_hprop|];
        [use isaprop_is_monoid_mor|symmetry; use assoc].
      + use invmap; [|use path_sigma_hprop|].
        use isaprop_is_module_mor.
        rewrite transportf_total2; simpl.
        rewrite transportf_const; symmetry; use assoc.
  Qed.

  Definition total_category_of_modules_has_homsets
    : has_homsets (monoid_with_module,, monoid_with_module_mor).
  Proof.
    intros RM1 RM2; use isaset_total2; [|intro]; use homset_property.
  Qed.


  Definition total_category_of_modules : category
    := make_category
        (make_precategory 
          total_category_of_modules_pre_data 
          total_category_of_modules_is_precategory)
        total_category_of_modules_has_homsets.

End TotalCategoryOfModules.
