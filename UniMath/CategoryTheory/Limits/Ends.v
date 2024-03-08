(**************************************************************

 Ends

 Ends are a special kind of limit, namely a limit over a
 bifunctor that is contravariant in its first argument and
 covariant in its second argument. In this file, we define
 the notion of ends, and show that ends can be constructed from
 products and equalizers.

 Contents
 1. Wedges
 2. Ends
 3. Accessors for ends
 4. Construction of ends from products and equalizers

 **************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Equalizers.

Local Open Scope cat.

Section Ends.
  Context {C D : category}
          (F : category_binproduct (C^opp) C ⟶ D).

  (**
   1. Wedges
   *)
  Definition wedge_data
    : UU
    := ∑ (w : D),
       ∏ (x : C), w --> F (x ,, x).

  #[reversible=no] Coercion ob_of_wedge
           (w : wedge_data)
    : D
    := pr1 w.

  Definition mor_of_wedge
             (w : wedge_data)
             (x : C)
    : w --> F (x ,, x)
    := pr2 w x.

  Definition make_wedge_data
             (w : D)
             (fs : ∏ (x : C), w --> F (x ,, x))
    : wedge_data
    := w ,, fs.

  Definition is_wedge
             (w : wedge_data)
    : UU
    := ∏ (x y : C)
         (g : x --> y),
       mor_of_wedge w x · #F (catbinprodmor (identity _) g)
       =
       mor_of_wedge w y · #F (catbinprodmor g (identity _)).

  Definition wedge
    : UU
    := ∑ (w : wedge_data), is_wedge w.

  #[reversible=no] Coercion wedge_data_of_wedge
           (w : wedge)
    : wedge_data
    := pr1 w.

  Proposition eq_of_wedge
              (w : wedge)
              {x y : C}
              (g : x --> y)
    : mor_of_wedge w x · #F (catbinprodmor (identity _) g)
      =
      mor_of_wedge w y · #F (catbinprodmor g (identity _)).
  Proof.
    exact (pr2 w x y g).
  Qed.

  Definition make_wedge
             (w : wedge_data)
             (p : is_wedge w)
    : wedge
    := w ,, p.

  Definition precomp_wedge_data
             {a : D}
             (w : wedge)
             (f : a --> w)
    : wedge_data.
  Proof.
    use make_wedge_data.
    - exact a.
    - exact (λ x, f · mor_of_wedge w x).
  Defined.

  Proposition precomp_is_wedge
              {a : D}
              (w : wedge)
              (f : a --> w)
    : is_wedge (precomp_wedge_data w f).
  Proof.
    intros x y g ; cbn.
    rewrite !assoc'.
    rewrite eq_of_wedge.
    apply idpath.
  Qed.

  Definition precomp_wedge
             {a : D}
             (w : wedge)
             (f : a --> w)
    : wedge.
  Proof.
    use make_wedge.
    - exact (precomp_wedge_data w f).
    - exact (precomp_is_wedge w f).
  Defined.

  Definition is_wedge_map
             {w₁ w₂ : wedge}
             (f : w₁ --> w₂)
    : UU
    := ∏ (x : C),
       f · mor_of_wedge w₂ x
       =
       mor_of_wedge w₁ x.

  Definition wedge_map
             (w₁ w₂ : wedge)
    : UU
    := ∑ (f : w₁ --> w₂), is_wedge_map f.

  #[reversible=no] Coercion mor_of_wedge_map
           {w₁ w₂ : wedge}
           (f : wedge_map w₁ w₂)
    : w₁ --> w₂
    := pr1 f.

  Proposition eq_of_wedge_map
              {w₁ w₂ : wedge}
              (f : wedge_map w₁ w₂)
              (x : C)
    : f · mor_of_wedge w₂ x
      =
      mor_of_wedge w₁ x.
  Proof.
    exact (pr2 f x).
  Qed.

  Definition make_wedge_map
             {w₁ w₂ : wedge}
             (f : w₁ --> w₂)
             (p : is_wedge_map f)
    : wedge_map w₁ w₂
    := f ,, p.

  Proposition wedge_map_eq
              {w₁ w₂ : wedge}
              {f₁ f₂ : wedge_map w₁ w₂}
              (p : (f₁ : w₁ --> w₂) = f₂)
    : f₁ = f₂.
  Proof.
    use subtypePath.
    {
      intro.
      use impred.
      intro.
      apply homset_property.
    }
    exact p.
  Qed.

  (**
   2. Ends
   *)
  Definition is_end
             (w : wedge)
    : UU
    := ∏ (w' : wedge), iscontr (wedge_map w' w).

  Proposition isaprop_is_end
              (w : wedge)
    : isaprop (is_end w).
  Proof.
    use impred ; intro.
    apply isapropiscontr.
  Qed.

  Definition end_limit
    : UU
    := ∑ (w : wedge), is_end w.

  #[reversible=no] Coercion end_limit_to_wedge
           (e : end_limit)
    : wedge
    := pr1 e.

  Definition is_end_end_limit
             (e : end_limit)
    : is_end e
    := pr2 e.

  (**
   3. Accessors for ends
   *)
  Section EndAccessors.
    Context {w : wedge}
            (Hw : is_end w).

    Definition mor_to_end
               (w' : wedge)
      : w' --> w
      := pr1 (Hw w').

    Definition mor_to_end'
               (w' : D)
               (fs : ∏ (x : C), w' --> F (x ,, x))
               (H : is_wedge (make_wedge_data w' fs))
      : w' --> w
      := mor_to_end (make_wedge _ H).

    Proposition mor_to_end_comm
                (w' : wedge)
                (x : C)
      : mor_to_end w' · mor_of_wedge w x
        =
        mor_of_wedge w' x.
    Proof.
      exact (eq_of_wedge_map (pr1 (Hw w')) x).
    Qed.

    Proposition mor_to_end'_comm
                (w' : D)
                (fs : ∏ (x : C), w' --> F (x ,, x))
                (H : is_wedge (make_wedge_data w' fs))
                (x : C)
      : mor_to_end' w' fs H · mor_of_wedge w x
        =
        fs x.
    Proof.
      exact (mor_to_end_comm (make_wedge _ H) x).
    Qed.

    Section MorToEndEq.
      Context (a : D)
              {f g : a --> w}
              (p : ∏ (x : C),
                   f · mor_of_wedge w x
                   =
                   g · mor_of_wedge w x).

      Let a_wedge : wedge := precomp_wedge w g.

      Let f_map : wedge_map a_wedge w
        := @make_wedge_map a_wedge w f p.

      Let g_map : wedge_map a_wedge w
        := @make_wedge_map a_wedge w g (λ _, idpath _).

      Proposition mor_to_end_eq
        : f = g.
      Proof.
        exact (maponpaths
                 pr1
                 (proofirrelevance
                    _
                    (isapropifcontr (Hw a_wedge))
                    f_map
                    g_map)).
      Qed.
    End MorToEndEq.
  End EndAccessors.

  (**
   4. Construction of ends from products and equalizers
   *)
  Section ConstructionOfEnds.
    Context (EqD : Equalizers D)
            (PD : Products C D)
            (PDM : Products (∑ (x : C) (y : C), x --> y) D).

    Let ProdF : Product C D (λ x : C, F (x,, x))
      := PD (λ x, F (x ,, x)).

    Let ProdM : Product _ D (λ f, F (pr1 f ,, pr12 f))
      := PDM (λ f, F (pr1 f ,, pr12 f)).

    Definition end_left_map
      : ProdF --> ProdM.
    Proof.
      use ProductArrow.
      intro f ; cbn.
      refine (ProductPr _ _ _ (pr1 f) · #F (_ ,, _)).
      - exact (identity _).
      - exact (pr22 f).
    Defined.

    Definition end_right_map
      : ProdF --> ProdM.
    Proof.
      use ProductArrow.
      intro f ; cbn.
      refine (ProductPr _ _ _ (pr12 f) · #F (_ ,, _)).
      - exact (pr22 f).
      - exact (identity _).
    Defined.

    Definition construction_of_ends_ob
      : Equalizer end_left_map end_right_map
      := EqD _ _ end_left_map end_right_map.

    Definition construction_of_ends_pr
               (x : C)
      : construction_of_ends_ob --> F (x ,, x)
      := EqualizerArrow _ · ProductPr _ _ _ x.

    Definition construction_of_ends_wedge_data
      : wedge_data.
    Proof.
      use make_wedge_data.
      - exact construction_of_ends_ob.
      - exact construction_of_ends_pr.
    Defined.

    Proposition construction_of_ends_wedge_laws
      : is_wedge construction_of_ends_wedge_data.
    Proof.
      intros x y f.
      cbn ; unfold construction_of_ends_pr.
      rewrite !assoc'.
      pose (maponpaths
              (λ z, z · ProductPr _ _ _ (x ,, (y ,, f)))
              (EqualizerEqAr construction_of_ends_ob))
        as p.
      cbn in p.
      rewrite !assoc' in p.
      unfold end_left_map, end_right_map in p.
      refine (_ @ p @ _).
      - apply maponpaths.
        refine (!_).
        exact (ProductPrCommutes _ _ _ ProdM _ _ (x ,, (y ,, f))).
      - apply maponpaths.
        exact (ProductPrCommutes _ _ _ ProdM _ _ (x ,, (y ,, f))).
    Qed.

    Definition construction_of_ends_wedge
      : wedge.
    Proof.
      use make_wedge.
      - exact construction_of_ends_wedge_data.
      - exact construction_of_ends_wedge_laws.
    Defined.

    Section EndUMP.
      Context (w : wedge).

      Proposition is_end_construction_of_ends_unique_map
        : isaprop (wedge_map w construction_of_ends_wedge).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use wedge_map_eq.
        use EqualizerInsEq.
        use ProductArrow_eq.
        intro i.
        rewrite !assoc'.
        exact (eq_of_wedge_map φ₁ i @ !(eq_of_wedge_map φ₂ i)).
      Qed.

      Definition is_end_construction_of_ends_mor
        : w --> construction_of_ends_wedge.
      Proof.
        use EqualizerIn.
        - use ProductArrow.
          exact (λ i, mor_of_wedge w i).
        - abstract
            (use ProductArrow_eq ;
             intro f ;
             unfold end_left_map, end_right_map ;
             rewrite !assoc' ;
             rewrite !(ProductPrCommutes _ _ _ ProdM) ;
             rewrite !assoc ;
             rewrite !(ProductPrCommutes _ _ _ ProdF) ;
             apply eq_of_wedge).
      Defined.

      Proposition is_end_construction_of_ends_comm
        : is_wedge_map is_end_construction_of_ends_mor.
      Proof.
        intros x.
        cbn.
        unfold is_end_construction_of_ends_mor.
        unfold construction_of_ends_pr.
        rewrite !assoc.
        rewrite EqualizerCommutes.
        apply (ProductPrCommutes _ _ _ ProdF).
      Qed.
    End EndUMP.

    Definition is_end_construction_of_ends
      : is_end construction_of_ends_wedge.
    Proof.
      intro w.
      use iscontraprop1.
      - exact (is_end_construction_of_ends_unique_map w).
      - use make_wedge_map.
        + exact (is_end_construction_of_ends_mor w).
        + exact (is_end_construction_of_ends_comm w).
    Defined.

    Definition construction_of_ends
      : end_limit
      := construction_of_ends_wedge
         ,,
         is_end_construction_of_ends.
  End ConstructionOfEnds.
End Ends.
