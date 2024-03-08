(**************************************************************

 Coends

 Coends are a special kind of colimit, namely a colimit over a
 bifunctor that is contravariant in its first argument and
 covariant in its second argument. In this file, we define
 the notion of coends, and show that coends can be constructed from
 coproducts and coequalizers.

 Contents
 1. Coedges
 2. Coends
 3. Accessors for coends
 4. Construction of coends from coproducts and coequalizers

 **************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.

Local Open Scope cat.

Section Coends.
  Context {C D : category}
          (F : category_binproduct (C^opp) C ⟶ D).

  (** * 1. Coedges *)
  Definition cowedge_data
    : UU
    := ∑ (w : D),
       ∏ (x : C), F (x ,, x) --> w.

  #[reversible=no] Coercion ob_of_cowedge
           (w : cowedge_data)
    : D
    := pr1 w.

  Definition mor_of_cowedge
             (w : cowedge_data)
             (x : C)
    : F (x ,, x) --> w
    := pr2 w x.

  Definition make_cowedge_data
             (w : D)
             (fs : ∏ (x : C), F (x ,, x) --> w)
    : cowedge_data
    := w ,, fs.

  Definition is_cowedge
             (w : cowedge_data)
    : UU
    := ∏ (x y : C)
         (g : x --> y),
       #F (catbinprodmor (identity _) g) · mor_of_cowedge w y
       =
       #F (catbinprodmor g (identity _)) · mor_of_cowedge w x.

  Definition cowedge
    : UU
    := ∑ (w : cowedge_data), is_cowedge w.

  #[reversible=no] Coercion cowedge_data_of_cowedge
           (w : cowedge)
    : cowedge_data
    := pr1 w.

  Proposition eq_of_cowedge
              (w : cowedge)
              {x y : C}
              (g : x --> y)
    : #F (catbinprodmor (identity _) g) · mor_of_cowedge w y
      =
      #F (catbinprodmor g (identity _)) · mor_of_cowedge w x.
  Proof.
    exact (pr2 w x y g).
  Qed.

  Definition make_cowedge
             (w : cowedge_data)
             (p : is_cowedge w)
    : cowedge
    := w ,, p.

  Definition postcomp_cowedge_data
             {a : D}
             (w : cowedge)
             (f : w --> a)
    : cowedge_data.
  Proof.
    use make_cowedge_data.
    - exact a.
    - exact (λ x, mor_of_cowedge w x · f).
  Defined.

  Proposition postcomp_is_cowedge
              {a : D}
              (w : cowedge)
              (f : w --> a)
    : is_cowedge (postcomp_cowedge_data w f).
  Proof.
    intros x y g ; cbn.
    rewrite !assoc.
    rewrite eq_of_cowedge.
    apply idpath.
  Qed.

  Definition postcomp_cowedge
             {a : D}
             (w : cowedge)
             (f : w --> a)
    : cowedge.
  Proof.
    use make_cowedge.
    - exact (postcomp_cowedge_data w f).
    - exact (postcomp_is_cowedge w f).
  Defined.

  Definition is_cowedge_map
             {w₁ w₂ : cowedge}
             (f : w₁ --> w₂)
    : UU
    := ∏ (x : C),
       mor_of_cowedge w₁ x · f
       =
       mor_of_cowedge w₂ x.

  Definition cowedge_map
             (w₁ w₂ : cowedge)
    : UU
    := ∑ (f : w₁ --> w₂), is_cowedge_map f.

  #[reversible=no] Coercion mor_of_cowedge_map
           {w₁ w₂ : cowedge}
           (f : cowedge_map w₁ w₂)
    : w₁ --> w₂
    := pr1 f.

  Proposition eq_of_cowedge_map
              {w₁ w₂ : cowedge}
              (f : cowedge_map w₁ w₂)
              (x : C)
    : mor_of_cowedge w₁ x · f
      =
      mor_of_cowedge w₂ x.
  Proof.
    exact (pr2 f x).
  Qed.

  Definition make_cowedge_map
             {w₁ w₂ : cowedge}
             (f : w₁ --> w₂)
             (p : is_cowedge_map f)
    : cowedge_map w₁ w₂
    := f ,, p.

  Proposition cowedge_map_eq
              {w₁ w₂ : cowedge}
              {f₁ f₂ : cowedge_map w₁ w₂}
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

  (** * 2. Coends *)
  Definition is_coend
             (w : cowedge)
    : UU
    := ∏ (w' : cowedge), iscontr (cowedge_map w w').

  Proposition isaprop_is_coend
              (w : cowedge)
    : isaprop (is_coend w).
  Proof.
    use impred ; intro.
    apply isapropiscontr.
  Qed.

  Definition coend_colimit
    : UU
    := ∑ (w : cowedge), is_coend w.

  #[reversible=no] Coercion coend_colimit_to_cowedge
           (e : coend_colimit)
    : cowedge
    := pr1 e.

  Definition is_coend_coend_colimit
             (e : coend_colimit)
    : is_coend e
    := pr2 e.

  (** * 3. Accessors for coends *)
  Section CoendAccessors.
    Context {w : cowedge}
            (Hw : is_coend w).

    Definition mor_to_coend
               (w' : cowedge)
      : w --> w'
      := pr1 (Hw w').

    Definition mor_to_coend'
               (w' : D)
               (fs : ∏ (x : C), F (x ,, x) --> w')
               (H : is_cowedge (make_cowedge_data w' fs))
      : w --> w'
      := mor_to_coend (make_cowedge _ H).

    Proposition mor_to_coend_comm
                (w' : cowedge)
                (x : C)
      : mor_of_cowedge w x · mor_to_coend w'
        =
        mor_of_cowedge w' x.
    Proof.
      exact (eq_of_cowedge_map (pr1 (Hw w')) x).
    Qed.

    Proposition mor_to_coend'_comm
                (w' : D)
                (fs : ∏ (x : C), F (x ,, x) --> w')
                (H : is_cowedge (make_cowedge_data w' fs))
                (x : C)
      : mor_of_cowedge w x · mor_to_coend' w' fs H
        =
        fs x.
    Proof.
      exact (mor_to_coend_comm (make_cowedge _ H) x).
    Qed.

    Section MorToCoendEq.
      Context (a : D)
              {f g : w --> a}
              (p : ∏ (x : C),
                   mor_of_cowedge w x · f
                   =
                   mor_of_cowedge w x · g).

      Let a_cowedge : cowedge := postcomp_cowedge w g.

      Let f_map : cowedge_map w a_cowedge
        := @make_cowedge_map w a_cowedge f p.

      Let g_map : cowedge_map w a_cowedge
        := @make_cowedge_map w a_cowedge g (λ _, idpath _).

      Proposition mor_to_coend_eq
        : f = g.
      Proof.
        exact (maponpaths
                 pr1
                 (proofirrelevance
                    _
                    (isapropifcontr (Hw a_cowedge))
                    f_map
                    g_map)).
      Qed.
    End MorToCoendEq.
  End CoendAccessors.

  (** * 4. Construction of coends from coproducts and coequalizers *)
  Section ConstructionOfCoends.
    Context (EqD : Coequalizers D)
            (PD : Coproducts C D)
            (PDM : Coproducts (∑ (x : C) (y : C), y --> x) D).

    Let CoprodF : Coproduct C D (λ x : C, F (x,, x))
      := PD (λ x, F (x ,, x)).

    Let CoprodM : Coproduct _ D (λ f, F (pr1 f ,, pr12 f))
      := PDM (λ f, F (pr1 f ,, pr12 f)).

    Definition coend_left_map
      : CoprodM --> CoprodF.
    Proof.
      use CoproductArrow.
      intro f ; cbn.
      refine (#F (_ ,, _) · CoproductIn _ _ _ (pr1 f)).
      - exact (identity _).
      - exact (pr22 f).
    Defined.

    Definition coend_right_map
      : CoprodM --> CoprodF.
    Proof.
      use CoproductArrow.
      intro f ; cbn.
      refine (#F (_ ,, _) · CoproductIn _ _ _ (pr12 f)).
      - exact (pr22 f).
      - exact (identity _).
    Defined.

    Definition construction_of_coends_ob
      : Coequalizer coend_left_map coend_right_map
      := EqD _ _ coend_left_map coend_right_map.

    Definition construction_of_coends_in
               (x : C)
      : F (x ,, x) --> construction_of_coends_ob
      := CoproductIn _ _ _ x · CoequalizerArrow _.

    Definition construction_of_coends_cowedge_data
      : cowedge_data.
    Proof.
      use make_cowedge_data.
      - exact construction_of_coends_ob.
      - exact construction_of_coends_in.
    Defined.

    Proposition construction_of_coends_cowedge_laws
      : is_cowedge construction_of_coends_cowedge_data.
    Proof.
      intros x y f.
      cbn ; unfold construction_of_coends_in.
      rewrite !assoc.
      pose (maponpaths
              (λ z, CoproductIn _ _ _ (y ,, x ,, f) · z)
              (CoequalizerEqAr construction_of_coends_ob)).
      cbn in p.
      rewrite !assoc in p.
      unfold coend_left_map, coend_right_map in p.
      refine (_ @ p @ _).
      - apply maponpaths_2.
        refine (!_).
        exact (CoproductInCommutes _ _ _ CoprodM _ _ (y ,, (x ,, f))).
      - apply maponpaths_2.
        exact (CoproductInCommutes _ _ _ CoprodM _ _ (y ,, (x ,, f))).
    Qed.

    Definition construction_of_coends_cowedge
      : cowedge.
    Proof.
      use make_cowedge.
      - exact construction_of_coends_cowedge_data.
      - exact construction_of_coends_cowedge_laws.
    Defined.

    Section CoendUMP.
      Context (w : cowedge).

      Proposition is_coend_construction_of_coends_unique_map
        : isaprop (cowedge_map construction_of_coends_cowedge w).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use cowedge_map_eq.
        use CoequalizerOutsEq.
        use CoproductArrow_eq.
        intro i.
        rewrite !assoc.
        exact (eq_of_cowedge_map φ₁ i @ !(eq_of_cowedge_map φ₂ i)).
      Qed.

      Definition is_coend_construction_of_coends_mor
        : construction_of_coends_cowedge --> w.
      Proof.
        use CoequalizerOut.
        - use CoproductArrow.
          exact (λ i, mor_of_cowedge w i).
        - abstract
            (use CoproductArrow_eq ;
             intro f ;
             unfold coend_left_map, coend_right_map ;
             rewrite !assoc ;
             rewrite !(CoproductInCommutes _ _ _ CoprodM) ;
             rewrite !assoc' ;
             rewrite !(CoproductInCommutes _ _ _ CoprodF) ;
             apply eq_of_cowedge).
      Defined.

      Proposition is_coend_construction_of_coends_comm
        : is_cowedge_map is_coend_construction_of_coends_mor.
      Proof.
        intros x.
        cbn.
        unfold is_coend_construction_of_coends_mor.
        unfold construction_of_coends_in.
        rewrite !assoc'.
        rewrite CoequalizerCommutes.
        apply (CoproductInCommutes _ _ _ CoprodF).
      Qed.
    End CoendUMP.

    Definition is_coend_construction_of_coends
      : is_coend construction_of_coends_cowedge.
    Proof.
      intro w.
      use iscontraprop1.
      - exact (is_coend_construction_of_coends_unique_map w).
      - use make_cowedge_map.
        + exact (is_coend_construction_of_coends_mor w).
        + exact (is_coend_construction_of_coends_comm w).
    Defined.

    Definition construction_of_coends
      : coend_colimit
      := construction_of_coends_cowedge
         ,,
         is_coend_construction_of_coends.
  End ConstructionOfCoends.
End Coends.
