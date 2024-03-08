(******************************************************************

 Pataraia's fixpoint theorem

 In this file, we formalize Pataraia's fixpoint theorem for DCPOs.
 This theorem says that monotone function on a DCPO has a fixpoint.

 There are two fundamental notions required for this proof. The
 first one is the notion of progressive maps. A map `f` is called
 progressive if for all `x` we have `x ⊑ f x`. The second one is
 the notion of post fixpoints. A post fixpoint for a map `f` is a
 point `x` such that `x ⊑ f x`.

 The key observation of the proof is that every DCPO has a largest
 progressive map [largest_progressive_map]. This is so because the
 progressive maps form a directed set and thus one can take the
 least upperbound.

 One can then look at the largest progressive map on  the DCPO of
 post fixpoints for a function `f` ([post_fixpoint_dcpo]). By
 applying this map to the bottom element, one acquires the desired
 fixpoint.

 References:
 - Theorem 3.2 in On the Bourbaki–Witt principle in toposes https://arxiv.org/abs/1201.0340

 Contents
 1. Progressive maps
 2. Examples of progressive maps
 3. Every DCPO has a largest progressive map
 4. The DCPO of post fixpoints
 5. Pataraia's fixpoint theorem

 ******************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Examples.Products.
Require Import UniMath.OrderTheory.DCPOs.Examples.SubDCPO.

Local Open Scope dcpo.

(**
 1. Progressive maps
 *)
Definition is_progressive
           {X : dcpo}
           (f : monotone_function X X)
  : hProp
  := ∀ (x : X), x ⊑ f x.

Definition progressive_map
           (X : dcpo)
  : UU
  := ∑ (f : monotone_function X X), is_progressive f.

#[reversible=no] Coercion monotone_function_of_progressive_map
         {X : dcpo}
         (f : progressive_map X)
  : monotone_function X X
  := pr1 f.

Proposition progressive_map_is_progressive
            {X : dcpo}
            (f : progressive_map X)
  : is_progressive f.
Proof.
  exact (pr2 f).
Qed.

Definition make_progressive_map
           {X : dcpo}
           (f : monotone_function X X)
           (Hf : is_progressive f)
  : progressive_map X
  := f ,, Hf.

(**
 2. Examples of progressive maps
 *)
Proposition is_progressive_id
            (X : dcpo)
  : is_progressive (id_monotone_function X).
Proof.
  intro.
  apply refl_dcpo.
Qed.

Definition id_progressive_map
           (X : dcpo)
  : progressive_map X.
Proof.
  use make_progressive_map.
  - exact (id_monotone_function X).
  - apply is_progressive_id.
Defined.

Proposition is_progressive_comp
            {X : dcpo}
            {f g : monotone_function X X}
            (Hf : is_progressive f)
            (Hg : is_progressive g)
  : is_progressive (comp_monotone_function f g).
Proof.
  intros x ; cbn.
  exact (trans_dcpo (Hf x) (Hg (f x))).
Qed.

Definition comp_progressive_map
           {X : dcpo}
           (f g : progressive_map X)
  : progressive_map X.
Proof.
  use make_progressive_map.
  - exact (comp_monotone_function f g).
  - exact (is_progressive_comp (pr2 f) (pr2 g)).
Defined.

Proposition is_progressive_lub
            {X : dcpo}
            (D : directed_set (monotone_map_dcpo X X))
            (HD : ∏ (d : D), is_progressive (D d))
  : is_progressive (⨆ D).
Proof.
  intros x.
  assert (H := directed_set_el D).
  revert H.
  use factor_through_squash.
  {
    apply propproperty.
  }
  intro d.
  use less_than_dcpo_lub.
  - exact d.
  - exact (HD d x).
Qed.

Proposition is_directed_progressive_maps
            (X : dcpo)
  : is_directed
      (monotone_map_dcpo X X)
      (λ (f : progressive_map X), pr1 f).
Proof.
  split.
  - apply hinhpr.
    apply id_progressive_map.
  - intros f g.
    apply hinhpr.
    refine (comp_progressive_map f g ,, _ ,, _).
    + intro x ; cbn.
      exact (progressive_map_is_progressive g (f x)).
    + intro x ; cbn.
      apply (pr1 g).
      apply (progressive_map_is_progressive f x).
Qed.

(**
 3. Every DCPO has a largest progressive map
 *)
Definition directed_set_progressive_maps
           (X : dcpo)
  : directed_set (monotone_map_dcpo X X).
Proof.
  use make_directed_set.
  - exact (progressive_map X).
  - exact (λ f, pr1 f).
  - exact (is_directed_progressive_maps X).
Defined.

Definition largest_progressive_map_monotone
           (X : dcpo)
  : monotone_map_dcpo X X
  := ⨆ directed_set_progressive_maps X.

Definition largest_progressive_map
           (X : dcpo)
  : progressive_map X.
Proof.
  use make_progressive_map.
  - exact (largest_progressive_map_monotone X).
  - abstract
      (apply is_progressive_lub ;
       intro d ;
       apply progressive_map_is_progressive).
Defined.

Proposition le_largest_progressive_map
            {X : dcpo}
            (f : progressive_map X)
            (x : X)
  : f x ⊑ largest_progressive_map X x.
Proof.
  exact (less_than_dcpo_lub
           (directed_set_progressive_maps X)
           (pr1 f)
           f
           (refl_dcpo _)
           x).
Qed.

(**
 4. The DCPO of post fixpoints
 *)
Proposition lub_post_fixpoint
            {X : dcpo}
            (f : monotone_function X X)
            (D : directed_set X)
            (HD : ∏ (d : D), D d ⊑ f (D d))
  : ⨆ D ⊑ f (⨆ D).
Proof.
  use dcpo_lub_is_least.
  intro d.
  refine (trans_dcpo (HD d) _).
  apply f.
  use less_than_dcpo_lub.
  - exact d.
  - apply refl_dcpo.
Qed.

Definition post_fixpoint_dcpo
           {X : dcpo}
           (f : monotone_function X X)
  : dcpo
  := sub_dcpo X (λ x, x ⊑ f x) (lub_post_fixpoint f).

Definition restriction_to_post_fixpoint
           {X : dcpo}
           (f : monotone_function X X)
  : progressive_map (post_fixpoint_dcpo f).
Proof.
  use make_progressive_map.
  - simple refine (_ ,, _).
    + refine (λ x, f (pr1 x) ,, _).
      abstract
        (cbn ;
         apply f ;
         apply (pr2 x)).
    + abstract
        (intros x₁ x₂ p ; cbn ;
         apply f ;
         exact p).
  - abstract (exact (λ x, pr2 x)).
Defined.

Definition bot_post_fixpoint
           {X : dcppo}
           (f : monotone_function X X)
  : post_fixpoint_dcpo f
  := ⊥_{X} ,, is_min_bottom_dcppo _.

(**
 5. Pataraia's fixpoint theorem
 *)
Section PataraiaFixpoint.
  Context {X : dcppo}
          (f : monotone_function X X).

  Let m : progressive_map (post_fixpoint_dcpo f)
    := largest_progressive_map (post_fixpoint_dcpo f).

  Proposition pataraia_fixpoint_compose_lemma
              (g : progressive_map (post_fixpoint_dcpo f))
              (x : post_fixpoint_dcpo f)
    : g(m x) = m x.
  Proof.
    use antisymm_dcpo.
    - pose (le_largest_progressive_map
               (comp_progressive_map m g)
               x)
        as p.
      refine (trans_dcpo _ p).
      cbn -[largest_progressive_map].
      apply refl_dcpo.
    - exact (progressive_map_is_progressive g (m x)).
  Qed.

  Definition pataraia_fixpoint
    : X
    := pr1 (m (bot_post_fixpoint f)).

  Proposition is_fixpoint_pataraia_fixpoint
    : f pataraia_fixpoint = pataraia_fixpoint.
  Proof.
    unfold pataraia_fixpoint.
    pose (p := maponpaths
                 pr1
                 (pataraia_fixpoint_compose_lemma
                    (restriction_to_post_fixpoint f)
                    (bot_post_fixpoint f))).
    refine (p @ _).
    apply idpath.
  Qed.
End PataraiaFixpoint.
