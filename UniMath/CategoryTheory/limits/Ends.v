(**************************************************************

 Ends

 Contents
 1. Wedges
 2. Ends
 3. Accessors for ends

 **************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

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

  Coercion ob_of_wedge
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

  Coercion wedge_data_of_wedge
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

  Coercion mor_of_wedge_map
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
      := mor_to_end (make_wedge _  H).

    Proposition mor_to_end_comm
                (w' : wedge)
                (x : C)
      : mor_to_end w' · mor_of_wedge w x
        =
        mor_of_wedge w' x.
    Proof.
      exact (eq_of_wedge_map (pr1 (Hw w')) x).
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
End Ends.
