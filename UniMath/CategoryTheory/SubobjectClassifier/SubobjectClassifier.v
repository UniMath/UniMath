(** * Subobject classifiers *)

(** ** Contents

  - Definition
  - Accessors
  - Proof that a category with a subobject classifier
      is balanced ([subobject_classifier_balanced])
  - Derivation of [SubobjectClassifier_nat_z_iso],
      the natural (z-)isomorphism between the subobject functor and Hom(-,O)
        induced by a subobject classifier
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Limits.Equalizers.

Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Subcategory.Core.


Local Open Scope cat.

(** ** Definition *)
Definition is_subobject_classifier
           {C : category}
           (T : Terminal C)
           (Ω : C)
           (true : T --> Ω)
  : UU
  := ∏ (x y : C)
       (m : Monic _ x y),
     ∃! (χ : y --> Ω),
     ∑ (H : m · χ = TerminalArrow _ _ · true),
     isPullback H.

Proposition isaprop_is_subobject_classifier_arr
            {C : category}
            (T : Terminal C)
            (Ω : C)
            (true : T --> Ω)
            (x y : C)
            (m : Monic _ x y)
            (χ : y --> Ω)
  : isaprop
      (∑ (H : m · χ = TerminalArrow _ _ · true),
       isPullback H).
Proof.
  use isaproptotal2.
  - intro.
    apply isaprop_isPullback.
  - intros.
    apply homset_property.
Qed.

Proposition isaprop_is_subobject_classifier
            {C : category}
            (T : Terminal C)
            (Ω : C)
            (true : T --> Ω)
  : isaprop (is_subobject_classifier T Ω true).
Proof.
  do 3 (use impred ; intro).
  apply isapropiscontr.
Qed.

Definition subobject_classifier {C : category} (T : Terminal C) : UU :=
  ∑ (O : ob C) (true : C⟦T, O⟧), is_subobject_classifier T O true.

Definition make_subobject_classifier_cat
          {C : category}
          (T : Terminal C)
          (Ω : C)
          (t : T --> Ω)
          (H : is_subobject_classifier T Ω t)
  : subobject_classifier T
  := Ω ,, t ,, H.

Definition make_subobject_classifier {C : category} {T : Terminal C}
           (O : ob C) (true : C⟦T, O⟧) :
  (∏ (X Y : ob C) (m : Monic _ X Y),
    iscontr (∑ (chi : C⟦Y, O⟧)
               (H : m · chi = TerminalArrow _ _ · true),
               isPullback H)) -> subobject_classifier T.
Proof.
  intros.
  use tpair; [exact O|].
  use tpair; [exact true|].
  assumption.
Qed.

(** ** Accessors *)

Section Accessors.
  Context {C : category} {T : Terminal C} (O : subobject_classifier T).

  Definition subobject_classifier_object : ob C :=  pr1 O.

  (** [true] is monic. We only export the accessor for it them as a [Monic]
      (rather than the a morphism), as it's strictly more useful. *)
  Definition true' : C⟦T, subobject_classifier_object⟧ := pr1 (pr2 O).

  Local Lemma true_is_monic : isMonic true'.
  Proof.
    apply global_element_isMonic.
  Qed.

  Definition true : Monic _ T subobject_classifier_object :=
    make_Monic _ true' true_is_monic.

  Definition subobject_classifier_universal_property {X Y} (m : Monic _ X Y) :
    iscontr (∑ (chi : C⟦Y, subobject_classifier_object⟧)
               (H : m · chi = TerminalArrow _ _ · true'),
               isPullback H) := pr2 (pr2 O) X Y m.

  Definition characteristic_morphism {X Y} (m : Monic _ X Y) :
    C⟦Y, subobject_classifier_object⟧ :=
    pr1 (iscontrpr1 (subobject_classifier_universal_property m)).

  Definition subobject_classifier_square_commutes {X Y} (m : Monic _ X Y) :
    m · characteristic_morphism m = TerminalArrow _ _ · true :=
    pr1 (pr2 (iscontrpr1 (subobject_classifier_universal_property m))).

  Definition subobject_classifier_pullback {X Y} (m : Monic _ X Y) :
    Pullback (characteristic_morphism m) true.
  Proof.
    use make_Pullback.
    - exact X.
    - exact m.
    - apply TerminalArrow.
    - apply subobject_classifier_square_commutes.
    - apply (pr2 (pr2 (iscontrpr1 (subobject_classifier_universal_property m)))).
  Defined.

  Definition subobject_classifier_pullback_sym  {X Y} (m : Monic _ X Y) :
    Pullback true (characteristic_morphism m).
  Proof.
    refine (@switchPullback C _ _ _ _ _ (subobject_classifier_pullback m)).
  Defined.

End Accessors.

Coercion subobject_classifier_object : subobject_classifier >-> ob.
Coercion true : subobject_classifier >-> Monic.

Proposition characteristic_morphism_true
            {C : category}
            {T : Terminal C}
            (Ω : subobject_classifier T)
  : characteristic_morphism Ω (true Ω) = identity _.
Proof.
  refine (!_).
  use (maponpaths
         pr1
         (pr2 (subobject_classifier_universal_property Ω (true Ω)) (_ ,, _ ,, _))).
  - abstract
      (refine (id_right _ @ !(id_left _) @ _) ;
       unfold true' ; cbn ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - use identity_isPullback.
    + apply idpath.
    + apply TerminalArrowEq.
    + apply idpath.
Qed.

(** The arrow Goldblatt calls [true! := (! : X -> T) · true] *)
Definition const_true {C : category} {T : Terminal C} (X : ob C)
           (O : subobject_classifier T) : X --> subobject_classifier_object O :=
  TerminalArrow T X · true O.

Definition subobject_classifier_map_eq
           {C : category}
           {T : Terminal C}
           (Ω : subobject_classifier T)
           {x y : C}
           (m : Monic C x y)
           {χ₁ χ₂ : y --> Ω}
           (p₁ : m · χ₁ = const_true x Ω)
           (p₂ : m · χ₂ = const_true x Ω)
           (H₁ : isPullback p₁)
           (H₂ : isPullback p₂)
  : χ₁ = χ₂.
Proof.
  exact (maponpaths
           (λ z, pr1 z)
           (proofirrelevance
              _
              (isapropifcontr (subobject_classifier_universal_property Ω m))
              (χ₁ ,, p₁ ,, H₁)
              (χ₂ ,, p₂ ,, H₂))).
Qed.

Proposition is_subobject_classifier_eq_ar
            {C : category}
            {T : Terminal C}
            {O : C}
            {t t' : T --> O}
            (p : t = t')
            (H : is_subobject_classifier T O t)
  : is_subobject_classifier T O t'.
Proof.
  pose (Ω := (O ,, t ,, H) : subobject_classifier T).
  intros x y m.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros χ₁ χ₂ ;
       use subtypePath ; [ intro ; apply isaprop_is_subobject_classifier_arr | ] ;
       induction p ;
       exact (subobject_classifier_map_eq Ω m (pr12 χ₁) (pr12 χ₂) (pr22 χ₁) (pr22 χ₂))).
  - simple refine (_ ,, _ ,, _).
    + exact (characteristic_morphism Ω m).
    + abstract
        (rewrite <- p ;
         exact (subobject_classifier_square_commutes Ω m)).
    + cbn.
      use (isPullback_mor_paths
             _ _ _ _ _ _
             (isPullback_Pullback (subobject_classifier_pullback Ω m))).
      * apply idpath.
      * exact p.
      * apply idpath.
      * apply idpath.
Defined.

(*A category with subobjectclassifier is balanced: if a morphism is mono and epi then it is iso*)
Section balanced.
  Context {C : category} {T : Terminal C} (O : subobject_classifier T)
  {c' c : C} (f : C⟦ c' , c ⟧) (f_isM : isMonic f) (f_isE : isEpi f).

  Local Definition f_asMonic := make_Monic _ f f_isM.

  Local Definition f_asEqualizer : Equalizer (characteristic_morphism O f_asMonic) (TerminalArrow T c · (true O)).
  Proof.
    use (make_Equalizer _ _ f_asMonic).
    + rewrite
        subobject_classifier_square_commutes,
        assoc.
      use cancel_postcomposition.
      use TerminalArrowEq.
    + use make_isEqualizer.
      intros x h q.
      use unique_exists.
      - assert (p : c' = PullbackObject  (subobject_classifier_pullback O f_asMonic)).
        { apply idpath. }
        rewrite p.
        use (PullbackArrow _ _ h (TerminalArrow T x)).
        rewrite q, assoc.
        use cancel_postcomposition.
        use TerminalArrowUnique.
      - simpl.
        assert (p : f =
          PullbackPr1 (subobject_classifier_pullback O f_asMonic)).
        { apply idpath. }
        rewrite p.
        use (PullbackArrow_PullbackPr1
          ((subobject_classifier_pullback O
          f_asMonic))).
      - intro t.
        use homset_property.
      - intros t t_tri.
        simpl.
        use (PullbackArrowUnique' _ _ _ (subobject_classifier_pullback O
        f_asMonic)).
        * exact t_tri.
        * use TerminalArrowUnique.
  Defined.

  Local Lemma path_from_fepi : (characteristic_morphism O f_asMonic) = (TerminalArrow T c · (true O)).
  Proof.
    use f_isE.
    assert (p : f = f_asMonic). {apply idpath. }
    rewrite p.
    rewrite (subobject_classifier_square_commutes O f_asMonic).
    rewrite assoc.
    use cancel_postcomposition.
    use TerminalArrowEq.
  Qed.

  Theorem subobject_classifier_balanced : (is_z_isomorphism f).
  Proof.
    assert (p : f = EqualizerArrow (f_asEqualizer)).
    { apply idpath. }
    rewrite p.
    use (z_iso_Equalizer_of_same_map f_asEqualizer).
    exact path_from_fepi.
  Defined.

End balanced.


(*Given a subobject_classifier O there is a nat_z_iso between the subobject functor and Hom(-,O)*)
Section subobject_classifier_natziso.

Context {C:category} {T:Terminal C} (PB : Pullbacks C) (O : subobject_classifier T).

Definition SubobjectClassifier_nt_data : nat_trans_data (SubObj_Functor C PB) (contra_homSet_functor O).
Proof.
  intros c S.
  cbn in c.
  change (pr1hSet (SubObj c)) in S.
  cbn.
  use (squash_to_set (X:=(pr1setquot (z_iso_eqrel (C:=Subobjectscategory c)) S))).
  + use homset_property.
  + intro m.
    exact (characteristic_morphism O
      (Subobject_Monic (pr1carrier _ m))).
  + intros m m'.
    cbn.
    assert (ej : (z_iso_eqrel (C:=Subobjectscategory c)) (pr1carrier _ m') (pr1carrier _ m)). {
      use (invweq (weqpathsinsetquot _ _ _)).
      use (pathscomp0 (b:=S)).
        * use (setquotl0 (z_iso_eqrel (C:=Subobjectscategory c))).
        * use pathsinv0.
          use (setquotl0 (z_iso_eqrel (C:=Subobjectscategory c))).
    }
    use (squash_to_prop ej).
    - use homset_property.
    - intro j.
      use path_to_ctr.
      cbn.
      transparent assert (pb_aux : (Pullback ((identity c)·(characteristic_morphism O (Subobject_Monic (pr1carrier _ m)))) (true' O))). {
        use (Pullback_z_iso_of_morphisms).
          * exact (subobject_classifier_pullback O (Subobject_Monic (pr1carrier _ m))).
          * exact (Subobject_dom (pr1carrier _ m')).
          * exact (z_iso_from_z_iso_in_Subobjectcategory j).
          * exact (Subobject_mor (pr1carrier _ m')).
          * exact (identity_is_z_iso c).
          * use z_iso_is_z_isomorphism.
          * rewrite id_right.
            use (Subobjectmor_tri j).
      }
      use (isPullback_mor_paths' _ _ _ _ _ (isPullback_Pullback pb_aux)).
      * rewrite id_left.
        apply idpath.
      * apply idpath.
      * apply idpath.
      * use TerminalArrowUnique.
  + exact (eqax0 (SubObj_iseqc S)).
Defined.

Lemma SubobjectClassifier_nt_is : is_nat_trans (SubObj_Functor C PB) (contra_homSet_functor O) SubobjectClassifier_nt_data.
Proof.
  intros c c' f.
  cbn in c, c', f.
  use funextfun.
  intro S.
  use (squash_to_prop (X := pr1setquot _ S)).
  + exact (eqax0 (SubObj_iseqc S)).
  + use homset_property.
  + intro m.
    induction (setquotl0 _ _ m).
    cbn.
    rewrite id_right.
    use pathsinv0.
    use path_to_ctr.
    set (pbr := subobject_classifier_pullback O (Subobject_Monic (pr1carrier _ m))).
    cbn.
    set (pbl := PB c c' (Subobject_dom (pr1carrier _ m)) f (Subobject_mor (pr1carrier _ m))).
    transparent assert (pb_glued :
      (Pullback
        (f·(characteristic_morphism O (Subobject_Monic (pr1carrier _ m))))
        O)).
    { use make_Pullback.
    - exact pbl.
    - exact (PullbackPr1 pbl).
    - exact ((PullbackPr2 pbl)·(PullbackPr2 pbr)).
    - use glueSquares.
      * exact (PullbackPr1 pbr).
      * exact (PullbackSqrCommutes pbr).
      * exact (PullbackSqrCommutes pbl).
    - use (isPullbackGluedSquare
      (isPullback_Pullback pbr)
      (isPullback_Pullback pbl)). }
    use (isPullback_mor_paths' _ _ _ _ _ (isPullback_Pullback pb_glued)).
    - apply idpath.
    - apply idpath.
    - apply idpath.
    - use TerminalArrowUnique.
Defined.

Definition SubobjectClassifier_nat_trans : nat_trans (SubObj_Functor C PB) (contra_homSet_functor O).
Proof.
  use make_nat_trans.
  + exact SubobjectClassifier_nt_data.
  + exact SubobjectClassifier_nt_is.
Defined.

Lemma SubobjectClassifier_nt_is_nat_z_iso : is_nat_z_iso SubobjectClassifier_nat_trans.
Proof.
  intros c.
  use make_is_z_isomorphism.
  + intro phi.
    cbn in c, phi.
    use setquotpr.
    use (PullbackSubobject PB _ phi).
    use (Subobjectscategory_ob (true O)).
    apply global_element_isMonic.
  + use make_is_inverse_in_precat.
    - use funextfun.
      intro S.
      use (squash_to_prop (X:= pr1setquot _ S) ((eqax0 (SubObj_iseqc S)))).
      { use isasetsetquot. }
      intro m.
      induction (setquotl0 _ _ m).
      use weqpathsinsetquot.
      use hinhpr.
      cbn.
      set (pbc := subobject_classifier_pullback O ((Subobject_Monic (pr1carrier _ m)))).
      set (PBc := PB _ _ _ (characteristic_morphism O (Subobject_Monic (pr1carrier _ m))) O).

      induction (pullbackiso _ PBc pbc) as (PBpb_z_iso,(PBpb_z_iso1,PBpb_z_iso2)).
      use make_z_iso_in_Subobjectscategory.
      * cbn.
        exact PBpb_z_iso.
      * use z_iso_is_z_isomorphism.
      * apply pathsinv0.
        exact PBpb_z_iso1.
    - use funextfun.
      intro phi.
      cbn.
      apply pathsinv0.
      use path_to_ctr.
      cbn.
      set (pb := PB O c T phi (true' O)).
      use (isPullback_mor_paths' _ _ _ _ _ (isPullback_Pullback pb)).
      * apply idpath.
      * apply idpath.
      * apply idpath.
      * use TerminalArrowUnique.
Defined.

Definition SubobjectClassifier_nat_z_iso :
  nat_z_iso (SubObj_Functor C PB) (contra_homSet_functor O).
Proof.
  use make_nat_z_iso.
  + exact SubobjectClassifier_nat_trans.
  + exact SubobjectClassifier_nt_is_nat_z_iso.
Defined.

End subobject_classifier_natziso.
