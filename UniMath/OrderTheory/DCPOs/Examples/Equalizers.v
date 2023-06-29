(*****************************************************************

 Equalizers of DCPOs

 In this file, we construct equalizers of both DCPOs and pointed
 DCPOs, and we prove the expected universal property for these.

 Contents
 1. Equalizers
 2. Equalizers of pointed DCPOs

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.

Local Open Scope dcpo.

(**
 1. Equalizers
 *)
Section Equalizers.
  Context {X Y : dcpo}
          (f g : scott_continuous_map X Y).

  Definition Equalizer_directed_set
             (D : directed_set (Equalizer_order X Y f g))
    : directed_set X.
  Proof.
    use make_directed_set.
    - exact D.
    - exact (λ i, pr1 (D i)).
    - abstract
        (refine (directed_set_el D ,, _) ;
         intros i j ;
         assert (k := directed_set_top D i j) ;
         revert k ;
         use factor_through_squash ; [ apply propproperty | ] ;
         intros k ;
         induction k as [ k [ H₁ H₂ ]] ;
         exact (hinhpr (k ,, (H₁ ,, H₂)))).
  Defined.

  Definition equalizer_lub_el
             (D : directed_set (Equalizer_order X Y f g))
    : X
    := ⨆ Equalizer_directed_set D.

  Proposition equalizer_lub_path
              (D : directed_set (Equalizer_order X Y f g))
    : f (equalizer_lub_el D) = g (equalizer_lub_el D).
  Proof.
    unfold equalizer_lub_el.
    rewrite !scott_continuous_map_on_lub.
    use antisymm_dcpo.
    - use dcpo_lub_is_least.
      intro i.
      use less_than_dcpo_lub ; [ exact i | ].
      change ((f {{Equalizer_directed_set D}}) i) with (f (pr1 (D i))).
      change ((g {{Equalizer_directed_set D}}) i) with (g (pr1 (D i))).
      rewrite (pr2 (D i)).
      apply refl_dcpo.
    - use dcpo_lub_is_least.
      intro i.
      use less_than_dcpo_lub ; [ exact i | ].
      change ((f {{Equalizer_directed_set D}}) i) with (f (pr1 (D i))).
      change ((g {{Equalizer_directed_set D}}) i) with (g (pr1 (D i))).
      rewrite (pr2 (D i)).
      apply refl_dcpo.
  Qed.

  Proposition is_lub_equalizer_lub
              (D : directed_set (Equalizer_order X Y f g))
    : is_least_upperbound
        (Equalizer_order X Y f g) D
        (equalizer_lub_el D ,, equalizer_lub_path D).
  Proof.
    split.
    - intros i.
      refine (less_than_dcpo_lub (Equalizer_directed_set D) _ i _).
      apply refl_dcpo.
    - intros y Hy.
      use (dcpo_lub_is_least (Equalizer_directed_set D)).
      intro i.
      exact (Hy i).
  Qed.

  Definition equalizer_lub
             (D : directed_set (Equalizer_order X Y f g))
    : lub (Equalizer_order X Y f g) D.
  Proof.
    use make_lub.
    - exact (⨆ Equalizer_directed_set D ,, equalizer_lub_path D).
    - exact (is_lub_equalizer_lub D).
  Defined.

  Definition directed_complete_equalizer
    : directed_complete_poset (Equalizer_order X Y f g).
  Proof.
    intros I D HD.
    exact (equalizer_lub (I ,, (D ,, HD))).
  Defined.

  Definition equalizer_dcpo_struct
    : dcpo_struct (∑ (x : X), hProp_to_hSet (f x = g x)%logic)%set.
  Proof.
    simple refine (_ ,, _).
    - exact (Equalizer_order X _ f g).
    - exact directed_complete_equalizer.
  Defined.

  Definition equalizer_dcpo
    : dcpo
    := _ ,, equalizer_dcpo_struct.

  Proposition is_scott_continuous_equalizer_pr1
    : is_scott_continuous equalizer_dcpo X pr1.
  Proof.
    use make_is_scott_continuous.
    - exact (Equalizer_pr1_monotone X Y f g).
    - intros D ; cbn.
      use antisymm_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro i.
        use less_than_dcpo_lub ; [ exact i | ] ; cbn.
        apply refl_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro i.
        use less_than_dcpo_lub ; [ exact i | ] ; cbn.
        apply refl_dcpo.
  Qed.

  Proposition is_scott_continuous_equalizer_map
              {W : dcpo}
              (h : scott_continuous_map W X)
              (p : (λ w : W, f (h w)) = (λ w : W, g (h w)))
    : is_scott_continuous
        W
        equalizer_dcpo
        (λ w, h w ,, eqtohomot p w).
  Proof.
    use make_is_scott_continuous.
    - exact (Equalizer_map_monotone X Y f g W (pr12 h) (eqtohomot p)).
    - intro D.
      use subtypePath.
      {
        intro.
        apply propproperty.
      }
      cbn.
      rewrite scott_continuous_map_on_lub.
      use antisymm_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro i.
        use less_than_dcpo_lub ; [ exact i | ] ; cbn.
        apply refl_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro i.
        use less_than_dcpo_lub ; [ exact i | ] ; cbn.
        apply refl_dcpo.
  Qed.
End Equalizers.

(**
 2. Equalizers of pointed DCPOs
 *)
Section EqualizersDCPPO.
  Context {X Y : dcppo}
          (f g : strict_scott_continuous_map X Y).

  Definition equalizer_dcppo_struct
    : dcppo_struct (∑ (x : X), hProp_to_hSet (f x = g x)%logic)%set.
  Proof.
    simple refine (equalizer_dcpo_struct f g ,, (⊥_{X} ,, _) ,, _).
    - abstract
        (cbn ;
         refine (strict_scott_continuous_map_on_point f @ !_) ;
         apply (strict_scott_continuous_map_on_point g)).
    - abstract
        (cbn ;
         intros xp ;
         apply is_min_bottom_dcppo).
  Defined.

  Proposition is_strict_scott_continuous_equalizer_pr1
    : is_strict_scott_continuous equalizer_dcppo_struct X pr1.
  Proof.
    simple refine (_ ,, _).
    - exact (is_scott_continuous_equalizer_pr1 f g).
    - apply idpath.
  Qed.

  Proposition is_strict_scott_continuous_equalizer_map
              {W : dcppo}
              (h : strict_scott_continuous_map W X)
              (p : (λ w : W, f (h w)) = (λ w : W, g (h w)))
    : is_strict_scott_continuous
        W
        equalizer_dcppo_struct
        (λ w, h w ,, eqtohomot p w).
  Proof.
    simple refine (_ ,, _).
    - exact (is_scott_continuous_equalizer_map f g h p).
    - use subtypePath.
      {
        intro.
        apply propproperty.
      }
      cbn.
      apply strict_scott_continuous_map_on_point.
  Qed.
End EqualizersDCPPO.
