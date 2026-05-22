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
  Local Definition I : C := monoidal_unit m.
  Local Definition lu : leftunitor_data m (monoidal_unit m) := monoidal_leftunitordata m.
  Local Definition luinv : leftunitorinv_data m (monoidal_unit m) := monoidal_leftunitorinvdata m.
  Local Definition ru : rightunitor_data m (monoidal_unit m) := monoidal_rightunitordata m.
  Local Definition ruinv : rightunitorinv_data m (monoidal_unit m) := monoidal_rightunitorinvdata m.
  Local Definition α : associator_data m := monoidal_associatordata m.
  Local Definition αinv : associatorinv_data m := monoidal_associatorinvdata m.

  Local Notation "x ⊗l f" := (x ⊗^{m}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{m}_{r} y) (at level 31).
  Local Notation "f ⊗⊗ g" := (f ⊗^{m} g) (at level 31).

  Lemma pullback_functor_funct_unit
    {R R' : C} {R_m : monoid m R} {R'_m : monoid m R'}
    (M' : C) (p' : module R' R'_m M')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : module_laws_unit R R_m (M' ⊗l f · p').
  Proof.
    unfold module_laws_unit; rewrite assoc.
    induction p' as [p' [w H]]; cbn; clear w.
    rewrite <- H.
    use (maponpaths (λ x, x · p')); induction f_m as [_ H2]. 
    rewrite <- (bifunctor_leftcomp m); now use maponpaths.
  Qed.

  Lemma pullback_functor_funct_assoc
    {R R' : C} {R_m : monoid m R} {R'_m : monoid m R'}
    (M' : C) (p' : module R' R'_m M')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : module_laws_assoc R R_m (M' ⊗l f · p').
  Proof.
    unfold module_laws_assoc; do 2 rewrite assoc; rewrite (bifunctor_rightcomp m).
    transitivity (α M' R R · (M' ⊗l (f ⊗⊗ f) · M' ⊗l μ R' R'_m) · p').
    etrans.
    2: use (maponpaths (λ x, α M' R R · x · p')); [exact (M' ⊗l μ R R_m · M' ⊗l f)|].
    1: now rewrite assoc.
    do 2 rewrite <- (bifunctor_leftcomp m).
    use maponpaths; induction f_m as [H _]; now symmetry.
    transitivity ((α M' R R · M' ⊗l (f ⊗⊗ f)) · M' ⊗l μ R' R'_m · p'); [now rewrite assoc|].
    transitivity (((M' ⊗l f) ⊗⊗ f) · α M' R' R' · M' ⊗l μ R' R'_m · p').
    use (maponpaths (λ x, x· M' ⊗l μ R' R'_m · p')).
    transitivity (α M' R R · identity M' ⊗⊗ (f ⊗⊗ f)).
    now rewrite @tensor_mor_left.
    transitivity ((identity M' ⊗⊗ f) ⊗⊗ f · α M' R' R').
    use associator_nat2. now rewrite @tensor_mor_left.
    assert ((M' ⊗l f) ⊗⊗ f = (M' ⊗l f) ⊗r R · (M' ⊗ R') ⊗l f) as H.
    etrans.
    use @tensor_split'.
    now rewrite <- @tensor_mor_left, <- @tensor_mor_right.
    rewrite H; clear H.
    transitivity ((M' ⊗l f) ⊗r R · (M' ⊗ R') ⊗l f · p' ⊗r R' · p').
    induction p' as [p' [H' H'']]; cbn.
    transitivity ((M' ⊗l f) ⊗r R · (M' ⊗ R') ⊗l f · (α M' R' R' · M' ⊗l μ R' R'_m · p')); [now do 2 rewrite assoc|].
    transitivity ((M' ⊗l f) ⊗r R · (M' ⊗ R') ⊗l f · (p' ⊗r R' · p')); [|now rewrite assoc].
    now use maponpaths.
    transitivity ((M' ⊗l f) ⊗r R · ((M' ⊗ R') ⊗l f · p' ⊗r R') · p'); [now rewrite assoc|].
    transitivity ((M' ⊗l f) ⊗r R · (p' ⊗r R · M' ⊗l f) · p'); [|now rewrite assoc].
    use (maponpaths (λ x, (M' ⊗l f) ⊗r R · x · p')).
    do 2 rewrite @tensor_mor_left, @tensor_mor_right.
    transitivity (p' #⊗ f); [symmetry; now rewrite tensor_split|now rewrite tensor_split'].
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

  Definition pullback_functor_data
    (R R' : C) (R_m : monoid m R) (R'_m : monoid m R')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : functor_data (MOD R' R'_m) (MOD R R_m).
  Proof.
    use make_functor_data.
    + intro M; induction M as [M p].
      exists M; cbn in *|-*.
      use pullback_functor_funct.
      exact R'.
      all: assumption.
    + intros [M p] [M' p']; cbn in * |- *. intros [ r r_m ].
      exists r.
      unfold is_module_mor.
      cbn; rewrite assoc.
      transitivity (r #⊗ f · p'); [now use maponpaths|].
      transitivity (M ⊗l f · (r ⊗r R' · p')).
      rewrite assoc; use (maponpaths (λ x, x · p')).
      now rewrite @tensor_mor_left, @tensor_mor_right, tensor_split.
      transitivity (M ⊗l f · (p · r)); [now use maponpaths|now rewrite assoc].
  Defined.

  Definition pullback_functor_is_functor
    (R R' : C) (R_m : monoid m R) (R'_m : monoid m R')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : is_functor (pullback_functor_data R R' R_m R'_m f f_m).
  Proof.
    use make_is_functor.
    + intros [M p].
      cbn in * |- *.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      trivial.
    + intros M M' M'' u v.
      cbn in * |- *.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      trivial.
  Qed.


  Definition pullback_functor
    (R R' : C) (R_m : monoid m R) (R'_m : monoid m R')
    (f : R --> R') (f_m : is_monoid_mor m R_m R'_m f)
    : (MOD R' R'_m) ⟶ (MOD R R_m).
  Proof.
    use make_functor.
    - now use pullback_functor_data.
    - use pullback_functor_is_functor.
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
    simpl; unfold is_module_mor; unfold pullback_functor_funct; cbn.
    now rewrite id_right, assoc, @tensor_mor_right, @tensor_mor_left, tensor_id_id, id_left, id_left.
  Qed.


  Definition id_monoid_with_module_mor (RM : monoid_with_module) : monoid_with_module_mor RM RM.
  Proof.
    induction RM as [R M].
    exists (identity R).
    induction R as [R R_m].
    induction M as [M p].
    exists (identity _); simpl.
    use id_is_monoid_with_module_mor.
  Defined.

  Lemma comp_is_monoid_with_module_mor (R R' R'' : MON C) 
    (f : R --> R') (g : R' --> R'')
    (M : MOD (pr1 R) (pr2 R))
    (M' : MOD (pr1 R') (pr2 R'))
    (M'' : MOD (pr1 R'') (pr2 R''))
    (r : M --> pullback_functor' R R' f M')
    (t : M' --> pullback_functor' R' R'' g M'')
    (u : is_monoid_mor m (pr2 R) (pr2 R'') (pr1 f · pr1 g))
    : is_module_mor (pr1 R) (pr2 R)
      (pullback_functor_funct (pr1 M') (pr2 M') (pr1 f) (pr2 f))
      (pullback_functor_funct (pr1 M'') (pr2 M'') (pr1 f · pr1 g) u)
      (pr1 t).
  Proof.
    induction t as [t t_m]; simpl in t_m.
    unfold is_module_mor in *.
    cbn in *.
    rewrite (bifunctor_leftcomp m), assoc, assoc.
    transitivity (t #⊗ pr1 f · pr1 M'' ⊗l pr1 g · pr2 M'').
    rewrite @tensor_mor_left, @tensor_mor_right; symmetry; now rewrite tensor_split'.
    transitivity (pr1 M' ⊗l pr1 f · t ⊗r pr1 R' · pr1 M'' ⊗l pr1 g · pr2 M'').
    now rewrite tensor_split, <- tensor_mor_left, <- tensor_mor_right.
    transitivity (pr1 M' ⊗l pr1 f · (t ⊗r pr1 R' · pr1 M'' ⊗l pr1 g · pr2 M''));
    [now do 2 rewrite assoc|].
    transitivity (pr1 M' ⊗l pr1 f · (pr2 M' · t)).
    2: now rewrite assoc.
    rewrite assoc in t_m; now use maponpaths.
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
    now use comp_is_monoid_with_module_mor.
  Defined.

  Definition total_category_of_modules_pre_data : precategory_data
    := make_precategory_data 
        (monoid_with_module,, monoid_with_module_mor)
        id_monoid_with_module_mor 
        comp_monoid_with_module_mor.

  Lemma total_category_of_modules_is_precategory 
    : is_precategory total_category_of_modules_pre_data.
  Proof.
    do 2 split; cbn.
    1,2: intros [R [M p]] [R' [M' p']] [[r r_m] [f f_m]]; cbn in *.
    1,2: use invmap; [|use total2_paths_equiv|].
    1,2: unfold PathPair.
    1,2: cbn.
    - assert (pr1
       (comp_monoid_with_module_mor (R,, M,, p) (R,, M,, p) 
          (R',, M',, p') (id_monoid_with_module_mor (R,, M,, p))
          ((r,, r_m),, f,, f_m)) = r,, r_m
      ) as P.
      use invmap; [|use path_sigma_hprop|]; simpl.
      use isaprop_is_monoid_mor.
      use id_left.
      exists P.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      rewrite transportf_total2; cbn; 
      now rewrite transportf_const, id_left.
    - eexists.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_module_mor.
      rewrite transportf_total2; cbn;
      now rewrite transportf_const, id_right.
      Unshelve.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_monoid_mor.
      cbn.
      now rewrite id_right.
    - shelve.
    - shelve.
    Unshelve.
    1,2: intros [R [M p]] [R' [M' p']] [R'' [M'' p'']] [R''' [M''' p''']] 
           [[r r_m] [f f_m]] [[r' r'_m] [f' f'_m]] [[r'' r''_m] [f'' f''_m]].
    1,2: cbn in *.
    1,2: use invmap; [|use total2_paths_equiv|]; unfold PathPair.
    1,2: eexists.
    1,2: use invmap; [|use path_sigma_hprop|].
    1,3: use isaprop_is_module_mor.
    1,2: cbn; rewrite transportf_total2; cbn.
    1,2: now rewrite transportf_const, assoc.
    Unshelve.
    1,2: use invmap; [|use path_sigma_hprop|].
    1,3: use isaprop_is_monoid_mor.
    1,2: cbn; now rewrite assoc.
  Qed.

  Definition total_category_of_modules_has_homsets
    : has_homsets (monoid_with_module,, monoid_with_module_mor).
  Proof.
    intros [R [M p]] [R' [M' p']].
    simpl.
    use isaset_total2.
    use homset_property.
    intro f.
    use homset_property.
  Qed.


  Definition total_category_of_modules : category
    := make_category
        (make_precategory 
          total_category_of_modules_pre_data 
          total_category_of_modules_is_precategory)
        total_category_of_modules_has_homsets.

End TotalCategoryOfModules.
