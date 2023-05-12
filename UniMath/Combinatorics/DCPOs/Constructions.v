(*****************************************************************

 Constructions on DCPOs

 In this file, we define numerous constructions on DCPOs. These
 constructions show that the category of DCPOs is complete.

 Contents
 1. The unit DCPO
 2. Binary products of DCPOs
 2.1. Upperbounds in the product
 2.2. The DCPO
 2.3. The first projection
 2.4. The second projection
 2.5. Pairing of functions
 2.6. Lemmas on upperbounds in the product
 3. Equalizers
 4. Type indexed products

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.Basics.
Require Import UniMath.Combinatorics.Posets.PointedPosets.
Require Import UniMath.Combinatorics.Posets.MonotoneFunctions.
Require Import UniMath.Combinatorics.DCPOs.DirectedSets.
Require Import UniMath.Combinatorics.DCPOs.DCPOBasics.
Require Import UniMath.Combinatorics.DCPOs.ScottContinuous.

Local Open Scope dcpo.

(**
 1. The unit DCPO
 *)
Definition unit_dcpo_struct
  : dcpo_struct unitset.
Proof.
  use make_dcpo_struct.
  - exact unit_PartialOrder.
  - intros I D HD.
    use make_lub.
    + exact tt.
    + split.
      * abstract
          (intro i ; cbn ;
           exact tt).
      * abstract
          (intros i Hi ; cbn ;
           exact tt).
Defined.

Definition unit_dcppo_struct
  : dcppo_struct unitset.
Proof.
  refine (unit_dcpo_struct ,, _).
  refine (tt ,, _).
  abstract
    (intro x ;
     cbn ;
     exact tt).
Defined.

Proposition is_scott_continuous_to_unit
            {X : hSet}
            (DX : dcpo_struct X)
  : is_scott_continuous DX unit_dcpo_struct (λ _, tt).
Proof.
  split.
  - intros x y p.
    exact tt.
  - intros I D HD x Hx.
    split.
    + intro ; cbn.
      exact tt.
    + intros ? ? ; cbn.
      exact tt.
Qed.

(**
 2. Binary products of DCPOs
 *)

(**
 2.1. Upperbounds in the product
 *)
Proposition is_least_upperbound_pair
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
            (I : UU)
            (D : I → (X × Y)%set)
            (x : X)
            (y : Y)
            (Hx : is_least_upperbound DX (λ i, pr1 (D i)) x)
            (Hy : is_least_upperbound DY (λ i, pr2 (D i)) y)
  : is_least_upperbound (prod_PartialOrder DX DY) D (x ,, y).
Proof.
  pose (x' := (x ,, Hx) : lub DX _).
  pose (y' := (y ,, Hy) : lub DY _).
  split.
  - intros i.
    exact (lub_is_upperbound x' i ,, lub_is_upperbound y' i).
  - intros z Hz.
    exact (lub_is_least x' _ (λ i, pr1 (Hz i))
           ,,
           lub_is_least y' _ (λ i, pr2 (Hz i))).
Qed.

Definition prod_lub
           {X Y : hSet}
           (DX : dcpo_struct X)
           (DY : dcpo_struct Y)
           (I : UU)
           (D : I → (X × Y)%set)
           (x : lub DX (λ i, pr1 (D i)))
           (y : lub DY (λ i, pr2 (D i)))
  : lub (prod_PartialOrder DX DY) D.
Proof.
  use make_lub.
  - exact (pr1 x ,, pr1 y).
  - use is_least_upperbound_pair.
    + exact (pr2 x).
    + exact (pr2 y).
Defined.

(**
 2.2. The DCPO
 *)
Definition prod_dcpo_struct
           {X Y : hSet}
           (DX : dcpo_struct X)
           (DY : dcpo_struct Y)
  : dcpo_struct (X × Y)%set.
Proof.
  use make_dcpo_struct.
  - exact (prod_PartialOrder DX DY).
  - intros I D HD.
    use prod_lub.
    + use (dcpo_struct_lub DX (λ i, pr1 (D i))).
      abstract
        (use (is_directed_comp _ _ HD) ;
         apply dirprod_pr1_is_monotone).
    + use (dcpo_struct_lub DY (λ i, pr2 (D i))).
      abstract
        (use (is_directed_comp _ _ HD) ;
         apply dirprod_pr2_is_monotone).
Defined.

Definition prod_dcppo_struct
           {X Y : hSet}
           (DX : dcppo_struct X)
           (DY : dcppo_struct Y)
  : dcppo_struct (X × Y)%set.
Proof.
  refine (prod_dcpo_struct DX DY ,, _).
  exact (pr2 (prod_pointed_PartialOrder DX DY)).
Defined.

Definition prod_dcpo
           (X Y : dcpo)
  : dcpo
  := _ ,, prod_dcpo_struct X Y.

Notation "X × Y" := (prod_dcpo X Y) : dcpo.

Proposition prod_dcpo_le
            {X Y : dcpo}
            (xy₁ xy₂ : (X × Y)%dcpo)
            (p : pr1 xy₁ ≤ pr1 xy₂)
            (q : pr2 xy₁ ≤ pr2 xy₂)
  : xy₁ ≤ xy₂.
Proof.
  exact (p ,, q).
Qed.

(**
 2.3. The first projection
 *)
Proposition pr1_is_least_upperbound
            {X Y : hSet}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {I : UU}
            {D : I → X × Y}
            (xy : X × Y)
            (Hxy : is_least_upperbound (prod_dcpo_struct DX DY) D xy)
  : is_least_upperbound DX (λ i, pr1 (D i)) (pr1 xy).
Proof.
  split.
  - intros i.
    exact (pr1 (is_least_upperbound_is_upperbound Hxy i)).
  - intros x Hx.
    refine (pr1 (is_least_upperbound_is_least Hxy (x ,, pr2 xy) _)).
    intros i.
    split ; cbn.
    + exact (Hx i).
    + exact (pr2 (is_least_upperbound_is_upperbound Hxy i)).
Qed.

Proposition is_scott_continuous_dirprod_pr1
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
  : is_scott_continuous
      (prod_dcpo_struct DX DY)
      DX
      dirprod_pr1.
Proof.
  split.
  - apply dirprod_pr1_is_monotone.
  - intros I DI HD x Hx.
    split.
    + intros i.
      exact (pr1 (is_least_upperbound_is_upperbound Hx i)).
    + intros x' Hx'.
      refine (pr1 (is_least_upperbound_is_least Hx (x' ,, pr2 x) _)).
      intro i.
      split ; cbn.
      * exact (Hx' i).
      * exact (pr2 (is_least_upperbound_is_upperbound Hx i)).
Qed.

Definition dirprod_pr1_scott_continuous_map
           (X Y : dcpo)
  : scott_continuous_map (X × Y) X
  := _ ,, is_scott_continuous_dirprod_pr1 X Y.

Notation "'π₁'" := (dirprod_pr1_scott_continuous_map _ _) : dcpo.

(**
 2.4. The second projection
 *)
Proposition pr2_is_least_upperbound
            {X Y : hSet}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {I : UU}
            {D : I → X × Y}
            (xy : X × Y)
            (Hxy : is_least_upperbound (prod_dcpo_struct DX DY) D xy)
  : is_least_upperbound DY (λ i, pr2 (D i)) (pr2 xy).
Proof.
  split.
  - intros i.
    exact (pr2 (is_least_upperbound_is_upperbound Hxy i)).
  - intros y Hy.
    refine (pr2 (is_least_upperbound_is_least Hxy (pr1 xy ,, y) _)).
    intros i.
    split ; cbn.
    + exact (pr1 (is_least_upperbound_is_upperbound Hxy i)).
    + exact (Hy i).
Qed.

Proposition is_scott_continuous_dirprod_pr2
            {X Y : hSet}
            (DX : dcpo_struct X)
            (DY : dcpo_struct Y)
  : is_scott_continuous
      (prod_dcpo_struct DX DY)
      DY
      dirprod_pr2.
Proof.
  split.
  - apply dirprod_pr2_is_monotone.
  - intros I DI HD x Hx.
    split.
    + intros i.
      exact (pr2 (is_least_upperbound_is_upperbound Hx i)).
    + intros y' Hy'.
      refine (pr2 (is_least_upperbound_is_least Hx (pr1 x ,, y') _)).
      intro i.
      split ; cbn.
      * exact (pr1 (is_least_upperbound_is_upperbound Hx i)).
      * exact (Hy' i).
Qed.

Definition dirprod_pr2_scott_continuous_map
           (X Y : dcpo)
  : scott_continuous_map (X × Y) Y
  := _ ,, is_scott_continuous_dirprod_pr2 X Y.

Notation "'π₂'" := (dirprod_pr2_scott_continuous_map _ _) : dcpo.

(**
 2.5. Pairing of functions
 *)
Proposition is_scott_continuous_prodtofun
            {W X Y : hSet}
            {DW : dcpo_struct W}
            {DX : dcpo_struct X}
            {DY : dcpo_struct Y}
            {f : W → X}
            (Hf : is_scott_continuous DW DX f)
            {g : W → Y}
            (Hg : is_scott_continuous DW DY g)
  : is_scott_continuous
      DW
      (prod_dcpo_struct DX DY)
      (prodtofuntoprod (f ,, g)).
Proof.
  split.
  - apply prodtofun_is_monotone.
    + exact (is_scott_continuous_monotone Hf).
    + exact (is_scott_continuous_monotone Hg).
  - intros I D HD w Hw.
    split.
    + intro i.
      split ; cbn.
      * exact (is_least_upperbound_is_upperbound
                 (is_scott_continuous_lub Hf HD w Hw)
                 i).
      * exact (is_least_upperbound_is_upperbound
                 (is_scott_continuous_lub Hg HD w Hw)
                 i).
    + intros xy Hxy.
      split ; cbn.
      * use (is_least_upperbound_is_least
               (is_scott_continuous_lub Hf HD w Hw)
               (pr1 xy)).
        intro i.
        exact (pr1 (Hxy i)).
      * use (is_least_upperbound_is_least
               (is_scott_continuous_lub Hg HD w Hw)
               (pr2 xy)).
        intro i.
        exact (pr2 (Hxy i)).
Qed.

Definition pair_scott_continuous
           {W X Y : dcpo}
           (f : scott_continuous_map W X)
           (g : scott_continuous_map W Y)
  : scott_continuous_map W (X × Y)
  := _ ,, is_scott_continuous_prodtofun (pr2 f) (pr2 g).

Notation "⟨ f , g ⟩" := (pair_scott_continuous f g) : dcpo.

(**
 2.6. Lemmas on upperbounds in the product
 *)
Proposition prod_dcpo_lub
            {X Y : dcpo}
            (D : directed_set (X × Y))
  : ⨆ D = (⨆ (π₁ {{ D }}) ,, ⨆ (π₂ {{ D }})).
Proof.
  use (eq_lub (X × Y) D).
  - apply is_least_upperbound_dcpo_lub.
  - use is_least_upperbound_pair.
    + exact (is_least_upperbound_dcpo_comp_lub
               (dirprod_pr1_scott_continuous_map X Y)
               D).
    + exact (is_least_upperbound_dcpo_comp_lub
               (dirprod_pr2_scott_continuous_map X Y)
               D).
Qed.

Definition prod_directed_set_dcpo
           {X Y : dcpo}
           (D₁ : directed_set X)
           (D₂ : directed_set Y)
  : directed_set (X × Y)
  := prod_directed_set D₁ D₂.

Proposition prod_dcpo_lub'
            {X Y : dcpo}
            (D : directed_set X)
            (D' : directed_set Y)
  : ⨆ (prod_directed_set_dcpo D D') = (⨆ D ,, ⨆ D').
Proof.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    intro i.
    use prod_dcpo_le ; cbn in *.
    + use less_than_dcpo_lub.
      * exact (pr1 i).
      * apply refl_dcpo.
    + use less_than_dcpo_lub.
      * exact (pr2 i).
      * apply refl_dcpo.
  - assert (Di := directed_set_el D).
    revert Di.
    use factor_through_squash ; [ apply propproperty | ].
    intro Di.
    assert (Di' := directed_set_el D').
    revert Di'.
    use factor_through_squash ; [ apply propproperty | ].
    intro Di'.
    use prod_dcpo_le.
    + use dcpo_lub_is_least.
      intro i.
      refine (pr1 (less_than_dcpo_lub
                     (prod_directed_set_dcpo D D')
                     (D i ,, D' Di')
                     (i ,, Di')
                     _)).
      use prod_dcpo_le ; cbn.
      * apply refl_dcpo.
      * apply refl_dcpo.
    + use dcpo_lub_is_least.
      intro i'.
      refine (pr2 (less_than_dcpo_lub
                     (prod_directed_set_dcpo D D')
                     (D Di ,, D' i')
                     (Di ,, i')
                     _)).
      use prod_dcpo_le ; cbn.
      * apply refl_dcpo.
      * apply refl_dcpo.
Qed.

(**
 3. Equalizers
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
    : is_scott_continuous (pr2 equalizer_dcpo) (pr2 X) pr1.
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
        (pr2 W)
        (pr2 equalizer_dcpo)
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
 4. Type indexed products
 *)
Section TypeIndexedProductsDCPO.
  Context {I : UU}
          (D : I → dcpo).

  Definition app_directed_set_depfun
             (E : directed_set
                    (depfunction_poset (λ i, D i) (λ i, D i)))
             (i : I)
    : directed_set (D i).
  Proof.
    use make_directed_set.
    - exact E.
    - exact (λ e, E e i).
    - split.
      + exact (directed_set_el E).
      + abstract
          (intros e₁ e₂ ;
           assert (k := directed_set_top E e₁ e₂) ;
           revert k ;
           use factor_through_squash ; [ apply propproperty | ] ;
           intros k ;
           induction k as [ k [ H₁ H₂ ]] ;
           exact (hinhpr (k ,, (H₁ i ,, H₂ i)))).
  Defined.

  Section DepFunctionLub.
    Context (E : directed_set
                   (depfunction_poset (λ i, D i) (λ i, D i))).

    Definition type_prod_pointwise_lub
               (i : I)
      : D i
      := ⨆ (app_directed_set_depfun E i).

    Proposition is_lub_type_prod_pointwise_lub
      : is_least_upperbound
          (depfunction_poset (λ i : I, D i) (λ i : I, D i))
          E
          type_prod_pointwise_lub.
    Proof.
      split.
      - intros e i ; cbn.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
      - intros f Hf i.
        use dcpo_lub_is_least.
        intro e ; cbn.
        exact (Hf e i).
    Qed.
  End DepFunctionLub.

  Definition directed_complete_depfunction
    : directed_complete_poset
        (depfunction_poset (λ i, D i) (λ i, D i)).
  Proof.
    intros J E HE.
    use make_lub.
    - exact (type_prod_pointwise_lub (J ,, (E ,, HE))).
    - exact (is_lub_type_prod_pointwise_lub (J ,, (E ,, HE))).
  Defined.

  Definition depfunction_dcpo_struct
    : dcpo_struct (∏ y, D y)%set
    := depfunction_poset _ (λ i, D i) ,, directed_complete_depfunction.

  Definition depfunction_dcpo
    : dcpo
    := _ ,, depfunction_dcpo_struct.

  Proposition is_scott_continuous_depfunction_pr
              (i : I)
    : is_scott_continuous
        depfunction_dcpo
        (D i)
        (λ f, f i).
  Proof.
    use make_is_scott_continuous.
    - exact (is_monotone_depfunction_poset_pr (λ i, D i) (λ i, D i) i).
    - intros E.
      cbn ; unfold type_prod_pointwise_lub.
      use antisymm_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro e.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro e.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
  Qed.

  Proposition is_scott_continuous_depfunction_map
              {W : dcpo}
              (fs : ∏ (i : I), scott_continuous_map W (D i))
    : is_scott_continuous W depfunction_dcpo (λ w i, fs i w).
  Proof.
    use make_is_scott_continuous.
    - exact (is_monotone_depfunction_poset_pair fs (λ i, pr12 (fs i))).
    - intros E.
      use funextsec ; intro i.
      cbn ; unfold type_prod_pointwise_lub.
      rewrite scott_continuous_map_on_lub.
      use antisymm_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro e.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
      + use dcpo_lub_is_least ; cbn.
        intro e.
        use less_than_dcpo_lub ; [ exact e | ] ; cbn.
        apply refl_dcpo.
  Qed.
End TypeIndexedProductsDCPO.
