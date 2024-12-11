Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetGroupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.

Local Open Scope cat.

(** * 1. Displayed categories that represent setgroupoids *)
Definition is_disp_setgrpd
           {C : category}
           (D : disp_cat C)
  : UU
  := (∏ (x : C), isaset (D x))
     ×
     groupoidal_disp_cat D.

Definition disp_setgrpd
           (C : category)
  : UU
  := ∑ (D : disp_cat C), is_disp_setgrpd D.

Coercion disp_setgrpd_to_disp_cat
         {C : category}
         (D : disp_setgrpd C)
  : disp_cat C
  := pr1 D.

Proposition isaset_ob_disp_set_grpd
            {C : category}
            (D : disp_setgrpd C)
            (x : C)
  : isaset (D x).
Proof.
  exact (pr12 D x).
Qed.

Definition is_z_iso_disp_set_grpd
           {C : category}
           (D : disp_setgrpd C)
           {x y : C}
           {f : x --> y}
           (Hf : is_z_isomorphism f)
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : is_z_iso_disp (make_z_iso' f Hf) ff
  := pr22 D x y f Hf xx yy ff.


Proposition idtoiso_disp_set_grpd_refl
            {C : setcategory}
            {D : disp_setgrpd C}
            {x : C}
            {p : x = x}
            {xx : D x}
            (pp : transportf D p xx = xx)
  : pr1 (idtoiso_disp p pp)
    =
    transportb
      (λ z, _ -->[ z ] _)
      (setcategory_refl_idtoiso p)
      (id_disp _).
Proof.
  assert (idpath _ = p) as s.
  {
    apply isaset_ob.
  }
  induction s.
  cbn in pp.
  assert (idpath _ = pp) as s.
  {
    apply isaset_ob_disp_set_grpd.
  }
  induction s.
  cbn.
  refine (!_).
  apply transportf_set.
  apply (homset_property C).
Qed.

Proposition idtoiso_disp_set_grpd_precomp_path
            {C : setcategory}
            {x y z : C}
            (p p' : x = y)
            (f : y --> z)
  : idtoiso p · f = idtoiso p' · f.
Proof.
  assert (p = p') as s.
  {
    apply isaset_ob.
  }
  rewrite s.
  apply idpath.
Qed.

Proposition idtoiso_disp_set_grpd_precomp
            {C : setcategory}
            {D : disp_setgrpd C}
            {x y z : C}
            {p p' : x = y}
            {f : y --> z}
            {xx : D x}
            {yy : D y}
            {zz : D z}
            (pp : transportf D p xx = yy)
            (pp' : transportf D p' xx = yy)
            (ff : yy -->[ f ] zz)
  : (transportf
       (λ z, _ -->[ z ] _)
       (idtoiso_disp_set_grpd_precomp_path p p' f)
       (idtoiso_disp p pp ;; ff)
     =
     idtoiso_disp p' pp' ;; ff)%mor_disp.
Proof.
  induction p.
  assert (idpath _ = p') as s.
  {
    apply isaset_ob.
  }
  induction s.
  cbn in pp, pp'.
  induction pp.
  assert (idpath _ = pp') as s.
  {
    apply isaset_ob_disp_set_grpd.
  }
  induction s.
  cbn.
  rewrite (id_left_disp (D := D)).
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply (homset_property C).
Qed.

Proposition idtoiso_disp_set_grpd_postcomp_path
            {C : setcategory}
            {x y z : C}
            (f : x --> y)
            (p p' : y = z)
  : f · idtoiso p = f · idtoiso p'.
Proof.
  assert (p = p') as s.
  {
    apply isaset_ob.
  }
  rewrite s.
  apply idpath.
Qed.

Proposition idtoiso_disp_set_grpd_postcomp
            {C : setcategory}
            {D : disp_setgrpd C}
            {x y z : C}
            {f : x --> y}
            {p p' : y = z}
            {xx : D x}
            {yy : D y}
            {zz : D z}
            (ff : xx -->[ f ] yy)
            (pp : transportf D p yy = zz)
            (pp' : transportf D p' yy = zz)
  : (transportf
       (λ z, _ -->[ z ] _)
       (idtoiso_disp_set_grpd_postcomp_path f p p')
       (ff ;; idtoiso_disp p pp)
     =
     ff ;; idtoiso_disp p' pp')%mor_disp.
Proof.
  induction p.
  assert (idpath _ = p') as s.
  {
    apply isaset_ob.
  }
  induction s.
  cbn in pp, pp'.
  induction pp.
  assert (idpath _ = pp') as s.
  {
    apply isaset_ob_disp_set_grpd.
  }
  induction s.
  cbn.
  rewrite (id_right_disp (D := D)).
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply (homset_property C).
Qed.

Proposition idtoiso_disp_set_grpd_prepostcomp_path
            {C : setcategory}
            {w x y z : C}
            (p p' : w = x)
            (f : x --> y)
            (q q' : y = z)
  : idtoiso p · f · idtoiso q = idtoiso p' · f · idtoiso q'.
Proof.
  assert (p = p') as s.
  {
    apply isaset_ob.
  }
  rewrite s ; clear s.
  assert (q = q') as s.
  {
    apply isaset_ob.
  }
  rewrite s ; clear s.
  apply idpath.
Qed.

Proposition idtoiso_disp_set_grpd_prepostcomp
            {C : setcategory}
            {D : disp_setgrpd C}
            {w x y z : C}
            {p p' : w = x}
            {f : x --> y}
            {q q' : y = z}
            {ww : D w}
            {xx : D x}
            {yy : D y}
            {zz : D z}
            (pp : transportf D p ww = xx)
            (pp' : transportf D p' ww = xx)
            (ff : xx -->[ f ] yy)
            (qq : transportf D q yy = zz)
            (qq' : transportf D q' yy = zz)
  : (transportf
       (λ z, _ -->[ z ] _)
       (idtoiso_disp_set_grpd_prepostcomp_path p p' f q q')
       ((idtoiso_disp p pp ;; ff) ;; idtoiso_disp q qq)
     =
     (idtoiso_disp p' pp' ;; ff) ;; idtoiso_disp q' qq')%mor_disp.
Proof.
  induction p.
  assert (idpath _ = p') as s.
  {
    apply isaset_ob.
  }
  induction s.
  cbn in pp, pp'.
  induction pp.
  assert (idpath _ = pp') as s.
  {
    apply isaset_ob_disp_set_grpd.
  }
  induction s.
  cbn.
  induction q.
  assert (idpath _ = q') as s.
  {
    apply isaset_ob.
  }
  induction s.
  cbn in qq, qq'.
  induction qq.
  assert (idpath _ = qq') as s.
  {
    apply isaset_ob_disp_set_grpd.
  }
  induction s.
  cbn.
  rewrite (id_right_disp (D := D)).
  unfold transportb.
  rewrite transport_f_f.
  rewrite (id_left_disp (D := D)).
  unfold transportb.
  rewrite !transport_f_f.
  apply maponpaths_2.
  apply (homset_property C).
Qed.


Proposition isaset_cleaving
            {C : category}
            (D : disp_cat C)
            (H : ∏ (x : C), isaset (D x))
  : isaset (cleaving D).
Proof.
  use impred_isaset ; intro y.
  use impred_isaset ; intro x.
  use impred_isaset ; intro f.
  use impred_isaset ; intro yy.
  use isaset_total2.
  - apply H.
  - intros xx.
    use isaset_total2.
    + apply homsets_disp.
    + intro ff.
      use isasetaprop.
      apply isaprop_is_cartesian.
Qed.

(** * 2. The data of the displayed category of displayed setgroupoids *)
Definition disp_cat_ob_mor_of_disp_setgrpd
  : disp_cat_ob_mor cat_of_setgroupoid.
Proof.
  simple refine (_ ,, _).
  - exact (λ (G : setgroupoid), disp_setgrpd G).
  - exact (λ (G₁ G₂ : setgroupoid)
             (D₁ : disp_setgrpd G₁)
             (D₂ : disp_setgrpd G₂)
             (F : G₁ ⟶ G₂),
           disp_functor F D₁ D₂).
Defined.

Definition disp_cat_id_comp_of_disp_setgrpd
  : disp_cat_id_comp
      cat_of_setgroupoid
      disp_cat_ob_mor_of_disp_setgrpd.
Proof.
  simple refine (_ ,, _).
  - exact (λ (G : setgroupoid)
             (D : disp_setgrpd G),
           disp_functor_identity D).
  - exact (λ (G₁ G₂ G₃ : setgroupoid)
             (F₁ : G₁ ⟶ G₂)
             (F₂ : G₂ ⟶ G₃)
             (D₁ : disp_setgrpd G₁)
             (D₂ : disp_setgrpd G₂)
             (D₃ : disp_setgrpd G₃)
             (FF₁ : disp_functor F₁ D₁ D₂)
             (FF₂ : disp_functor F₂ D₂ D₃),
           disp_functor_composite FF₁ FF₂).
Defined.

Definition disp_cat_data_of_disp_setgrpd
  : disp_cat_data cat_of_setgroupoid.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_of_disp_setgrpd.
  - exact disp_cat_id_comp_of_disp_setgrpd.
Defined.

(** * 3. Transport lemmas *)
Definition transportb_disp_functor_data_help
           {G₁ G₂ : setgroupoid}
           {F F' : G₁ ⟶ G₂}
           (p : pr1 F = pr1 F')
           {D₁ : disp_cat_data_of_disp_setgrpd G₁}
           {D₂ : disp_cat_data_of_disp_setgrpd G₂}
           (FF : D₁ -->[ F' ] D₂)
  : disp_functor_data F (pr1 D₁) (pr1 D₂).
Proof.
  simple refine (_ ,, _).
  - exact (λ x xx,
           transportb (pr1 D₂) (maponpaths (λ H, pr1 H x) p) (pr1 FF x xx)).
  - cbn.
    refine (λ x y xx yy f ff, _).
    induction F as [ FD HF ], F' as [ FD' HF' ].
    cbn in *.
    induction p ; cbn.
    exact (♯(pr1 FF) ff)%mor_disp.
Defined.

Definition transportb_disp_functor_data
           {G₁ G₂ : setgroupoid}
           {F F' : G₁ ⟶ G₂}
           (p : F = F')
           {D₁ : disp_cat_data_of_disp_setgrpd G₁}
           {D₂ : disp_cat_data_of_disp_setgrpd G₂}
           (FF : D₁ -->[ F' ] D₂)
  : disp_functor_data F (pr1 D₁) (pr1 D₂).
Proof.
  exact (transportb_disp_functor_data_help (maponpaths pr1 p) FF).
Defined.

Proposition transportb_disp_setgrpd_help
            {G₁ G₂ : setgroupoid}
            {F F' : G₁ ⟶ G₂}
            (p : F = F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
  : pr1 (transportb (mor_disp D₁ D₂) p FF)
    =
    transportb_disp_functor_data p FF.
Proof.
  induction p.
  apply idpath.
Qed.

Proposition transportb_disp_setgrpd
            {G₁ G₂ : setgroupoid}
            {FD : functor_data G₁ G₂}
            {HF₁ HF₂ : is_functor FD}
            (F := (FD ,, HF₁) : G₁ ⟶ G₂)
            (F' := (FD ,, HF₂) : G₁ ⟶ G₂)
            (p : F = F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
  : pr1 (transportb (mor_disp D₁ D₂) p FF) = pr1 FF.
Proof.
  etrans.
  {
    apply transportb_disp_setgrpd_help.
  }
  unfold F, F' in *.
  clear F F'.
  unfold transportb_disp_functor_data.
  assert (maponpaths pr1 p = idpath _) as s.
  {
    use (proofirrelevance _ (functor_data_isaset G₁ G₂ _ _ _ _)).
    - apply homset_property.
    - apply isaset_ob.
  }
  rewrite s.
  apply idpath.
Qed.

(** * 4. Verification of the axioms *)
Proposition isaset_disp_functor
            {G₁ G₂ : setgroupoid}
            (F : G₁ ⟶ G₂)
            (D₁ : disp_cat_data_of_disp_setgrpd G₁)
            (D₂ : disp_cat_data_of_disp_setgrpd G₂)
  : isaset (D₁ -->[ F ] D₂).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + do 2 (use impred_isaset ; intro).
      apply isaset_ob_disp_set_grpd.
    + intro.
      do 6 (use impred_isaset ; intro).
      apply homsets_disp.
  - intro.
    apply isasetaprop.
    apply isaprop_disp_functor_axioms.
Qed.

Proposition disp_cat_axioms_of_disp_setgrpd
  : disp_cat_axioms
      cat_of_setgroupoid
      disp_cat_data_of_disp_setgrpd.
Proof.
  repeat split.
  - intros G₁ G₂ F D₁ D₂ FF.
    use disp_functor_eq.
    refine (!_).
    etrans.
    {
      apply transportb_disp_setgrpd.
    }
    apply idpath.
  - intros G₁ G₂ F D₁ D₂ FF.
    use disp_functor_eq.
    refine (!_).
    etrans.
    {
      apply transportb_disp_setgrpd.
    }
    apply idpath.
  - intros G₁ G₂ G₃ G₄ F₁ F₂ F₃ D₁ D₂ D₃ D₄ FF₁ FF₂ FF₃.
    use disp_functor_eq.
    refine (!_).
    etrans.
    {
      apply transportb_disp_setgrpd.
    }
    apply idpath.
  - intros G₁ G₂ F D₁ D₂.
    apply isaset_disp_functor.
Qed.

Definition disp_cat_of_disp_setgrpd
  : disp_cat cat_of_setgroupoid.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_of_disp_setgrpd.
  - exact disp_cat_axioms_of_disp_setgrpd.
Defined.

(** * 5. This displayed category is univalent *)
Proposition is_univalent_disp_cat_of_disp_setgrpd
  : is_univalent_disp disp_cat_of_disp_setgrpd.
Proof.
Admitted.

Definition univ_disp_cat_of_disp_setgrpd
  : disp_univalent_category cat_of_setgroupoid.
Proof.
  use make_disp_univalent_category.
  - exact disp_cat_of_disp_setgrpd.
  - exact is_univalent_disp_cat_of_disp_setgrpd.
Defined.

(** * 6. The displayed category of isofibrations *)
Definition disp_cat_ob_mor_isofib_over_disp_setgrpd
  : disp_cat_ob_mor (total_category disp_cat_of_disp_setgrpd).
Proof.
  simple refine (_ ,, _).
  - exact (λ GD, cleaving (pr12 GD)).
  - exact (λ GD₁ GD₂ I₁ I₂ FF, preserves_cleaving I₁ I₂ (pr2 FF)).
Defined.

Proposition disp_cat_id_comp_isofib_over_disp_setgrpd
  : disp_cat_id_comp
      (total_category disp_cat_of_disp_setgrpd)
      disp_cat_ob_mor_isofib_over_disp_setgrpd.
Proof.
  split.
  - intros G I.
    apply identity_preserves_cleaving.
  - intros G₁ G₂ G₃ F₁ F₂ I₁ I₂ I₃ HF₁ HF₂.
    exact (composition_preserves_cleaving HF₁ HF₂).
Qed.

Definition disp_cat_data_isofib_over_disp_setgrpd
  : disp_cat_data (total_category disp_cat_of_disp_setgrpd).
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_isofib_over_disp_setgrpd.
  - exact disp_cat_id_comp_isofib_over_disp_setgrpd.
Defined.

Proposition disp_cat_axioms_isofib_over_disp_setgrpd
  : disp_cat_axioms
      (total_category disp_cat_of_disp_setgrpd)
      disp_cat_data_isofib_over_disp_setgrpd.
Proof.
  repeat split.
  - intros.
    apply isaprop_preserves_cleaving.
    apply isaset_ob_disp_set_grpd.
  - intros.
    apply isaprop_preserves_cleaving.
    apply isaset_ob_disp_set_grpd.
  - intros.
    apply isaprop_preserves_cleaving.
    apply isaset_ob_disp_set_grpd.
  - intros.
    apply isasetaprop.
    apply isaprop_preserves_cleaving.
    apply isaset_ob_disp_set_grpd.
Qed.

Definition disp_cat_isofib_over_disp_setgrpd
  : disp_cat (total_category disp_cat_of_disp_setgrpd).
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_isofib_over_disp_setgrpd.
  - exact disp_cat_axioms_isofib_over_disp_setgrpd.
Defined.

Proposition is_univalent_disp_cat_isofib_over_disp_setgrpd
  : is_univalent_disp disp_cat_isofib_over_disp_setgrpd.
Proof.
  use is_univalent_disp_from_fibers.
  intros G I₁ I₂.
  induction G as [ G D ].
  cbn -[idtoiso_disp] in G, D, I₁, I₂.
  use isweqimplimpl.
  - intros FF.
    induction FF as [ HFF iso ] ; clear iso ; cbn in HFF.
    use funextsec ; intro y.
    use funextsec ; intro x.
    use funextsec ; intro f.
    use funextsec ; intro yy.
    use total2_paths_f.
    + exact (preserves_cleaving_ob HFF f yy).
    + use total2_paths_f.
      * rewrite pr1_transportf.
        use (@transportf_transpose_left _ (λ z, z -->[ _ ] _)).
        etrans.
        {
          exact (preserves_cleaving_mor_alt HFF f yy).
        }
        unfold transportb.
        cbn -[idtoiso_disp].
        refine (!_).
        etrans.
        {
          apply transportf_precompose_disp.
        }
        rewrite idtoiso_disp_inv.
        rewrite pathsinv0inv0.
        apply idpath.
      * apply isaprop_is_cartesian.
  - apply isaset_cleaving.
    intro x.
    apply isaset_ob_disp_set_grpd.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_z_iso_disp.
    + intros.
      apply isaprop_preserves_cleaving.
      intros.
      apply isaset_ob_disp_set_grpd.
Qed.

Definition disp_cat_isofib
  : disp_cat cat_of_setgroupoid
  := sigma_disp_cat disp_cat_isofib_over_disp_setgrpd.

Proposition is_univalent_disp_cat_isofib
  : is_univalent_disp disp_cat_isofib.
Proof.
  use is_univalent_sigma_disp.
  - exact is_univalent_disp_cat_of_disp_setgrpd.
  - exact is_univalent_disp_cat_isofib_over_disp_setgrpd.
Qed.

Proposition mor_eq_disp_cat_isofib
            {G₁ G₂ : setgroupoid}
            {F : G₁ ⟶ G₂}
            {D₁ : disp_cat_isofib G₁}
            {D₂ : disp_cat_isofib G₂}
            {FF FF' : D₁ -->[ F ] D₂}
            (p : pr1 FF = pr1 FF')
  : FF = FF'.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_preserves_cleaving ; cbn.
    intro.
    apply isaset_ob_disp_set_grpd.
  }
  exact p.
Qed.

(********************************)

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.

Section Cleaving.
  Context {G₁ G₂ : setgroupoid}
          (F : G₂ ⟶ G₁)
          (D : disp_setgrpd G₁)
          (I : cleaving D).

  Let DD : disp_cat_isofib G₁ := D ,, I.

  Definition disp_cat_isofib_subst_setgrpd
    : disp_setgrpd G₂.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (reindex_disp_cat F D).
    - abstract
        (intros x ; cbn ;
         apply isaset_ob_disp_set_grpd).
    - cbn.
      intros x y f Hf xx yy ff.
      use (is_z_isomorphism_reindex_disp_cat F D Hf ff).
      apply is_z_iso_disp_set_grpd.
  Defined.

  Definition disp_cat_isofib_subst
    : disp_cat_isofib G₂.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_isofib_subst_setgrpd.
    - apply cleaving_reindex_disp_cat.
      exact I.
  Defined.

  Definition disp_cat_isofib_subst_mor
    : disp_cat_isofib_subst -->[ F ] DD.
  Proof.
    simple refine (_ ,, _).
    - apply reindex_disp_cat_disp_functor.
    - apply preserves_cleaving_reindex.
  Defined.

  Definition is_cartesian_disp_cat_isofib_subst
    : is_cartesian disp_cat_isofib_subst_mor.
  Proof.
    intros G₃ F' D' FF.
    simple refine (_ ,, _).
    - simple refine ((_ ,, _) ,, _).
      + exact (lift_functor_into_reindex (pr1 FF)).
      + apply preserves_cleaving_lift_reindex.
        exact (pr2 FF).
      + abstract
          (use mor_eq_disp_cat_isofib ;
           use disp_functor_eq ;
           apply idpath).
    - abstract
        (intros H ;
         induction H as [ H HH ] ;
         use subtypePath ; [ intro ; apply homsets_disp | ] ;
         use mor_eq_disp_cat_isofib ;
         use disp_functor_eq ;
         cbn ; cbn in HH ;
         exact (maponpaths (λ z, pr11 z) HH)).
  Defined.
End Cleaving.

Definition cleaving_disp_cat_isofib
  : cleaving disp_cat_isofib.
Proof.
  intros G₁ G₂ F D.
  simple refine (_ ,, _ ,, _).
  - exact (disp_cat_isofib_subst F (pr1 D) (pr2 D)).
  - exact (disp_cat_isofib_subst_mor F (pr1 D) (pr2 D)).
  - exact (is_cartesian_disp_cat_isofib_subst F (pr1 D) (pr2 D)).
Defined.


Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.Groupoids.

Definition total_set_groupoid
           {G : setgroupoid}
           (D : disp_cat_isofib G)
  : setgroupoid.
Proof.
  use make_setgroupoid.
  - use make_setcategory.
    + exact (total_category (pr11 D)).
    + abstract
        (use isaset_total2 ; [ apply isaset_ob | ] ;
         apply isaset_ob_disp_set_grpd).
  - intros x y f.
    use is_z_iso_total.
    + apply G.
    + apply is_z_iso_disp_set_grpd.
Defined.

Proposition total_functor_commute_eq
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (FF : disp_functor F D₁ D₂)
  : total_functor FF ∙ pr1_category D₂
    =
    pr1_category D₁ ∙ F.
Proof.
  use functor_eq.
  {
    apply homset_property.
  }
  apply idpath.
Qed.

Definition disp_cat_isofib_comprehension_data
  : disp_functor_data
      (functor_identity _)
      disp_cat_isofib
      (disp_codomain _).
Proof.
  simple refine (_ ,, _).
  - exact (λ (G : setgroupoid)
             (D : disp_cat_isofib G),
           total_set_groupoid D
           ,,
           pr1_category _).
  - refine (λ (G₁ G₂ : setgroupoid)
              (D₁ : disp_cat_isofib G₁)
              (D₂ : disp_cat_isofib G₂)
              (F : G₁ ⟶ G₂)
              (FF : D₁ -->[ F ] D₂),
             total_functor (pr1 FF)
             ,,
             _).
    exact (total_functor_commute_eq (pr1 FF)).
Defined.

Proposition disp_cat_isofib_comprehension_axioms
  : disp_functor_axioms disp_cat_isofib_comprehension_data.
Proof.
  split.
  - intros.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use functor_eq ; [ apply homset_property | ] ; cbn.
    apply idpath.
  - intros.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use functor_eq ; [ apply homset_property | ] ; cbn.
    apply idpath.
Qed.

Definition disp_cat_isofib_comprehension
  : disp_functor
      (functor_identity _)
      disp_cat_isofib
      (disp_codomain _).
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_isofib_comprehension_data.
  - exact disp_cat_isofib_comprehension_axioms.
Defined.


Require Import UniMath.CategoryTheory.Limits.Pullbacks.


Definition transportf_functor_disp_ob
           {C₁ C₂ : category}
           {D : disp_cat C₂}
           {F₁ F₂ : C₁ ⟶ C₂}
           (p : F₁ = F₂)
           {x : C₁}
           (xx : D (F₁ x))
  : D (F₂ x)
  := transportf D (maponpaths (λ (F : _ ⟶ _), F x) p) xx.

Proposition transportf_functor_disp_ob_eq_b
            {C₁ C₂ : category}
            {D : disp_cat C₂}
            {F₁ F₂ : C₁ ⟶ C₂}
            (p : F₁ = F₂)
            {x : C₁}
            (xx : D (F₁ x))
  : transportb D (path_functor_ob p _) (transportf_functor_disp_ob p xx)
    =
    xx.
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Proposition transportf_functor_disp_ob_eq_f
            {C₁ C₂ : category}
            {D : disp_cat C₂}
            {F₁ F₂ : C₁ ⟶ C₂}
            (p : F₁ = F₂)
            {x : C₁}
            (xx : D (F₁ x))
  : transportf D (path_functor_ob p _) xx
    =
    transportf_functor_disp_ob p xx.
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Definition transportf_functor_disp_mor
           {C₁ C₂ : category}
           {D : disp_cat C₂}
           {F₁ F₂ : C₁ ⟶ C₂}
           (p : F₁ = F₂)
           {x y : C₁}
           {f : x --> y}
           {xx : D (F₁ x)}
           {yy : D (F₁ y)}
           (ff : xx -->[ #F₁ f ] yy)
  : transportf_functor_disp_ob p xx
    -->[ #F₂ f ]
    transportf_functor_disp_ob p yy.
Proof.
  induction p.
  exact ff.
Defined.

Proposition transportf_functor_disp_mor_eq
            {C₁ C₂ : category}
            {D : disp_cat C₂}
            {F₁ F₂ : C₁ ⟶ C₂}
            (p : F₁ = F₂)
            {x y : C₁}
            {f : x --> y}
            {xx : D (F₁ x)}
            {yy : D (F₁ y)}
            (ff : xx -->[ #F₁ f ] yy)
  : transportf_functor_disp_mor p ff
    =
    transportf
      (λ z, _ -->[ z ] _)
      (path_functor_mor_left p f)
      (idtoiso_disp _ (transportf_functor_disp_ob_eq_b p xx)
       ;; ff
       ;; idtoiso_disp _ (transportf_functor_disp_ob_eq_f p yy))%mor_disp.
Proof.
  induction p.
  cbn.
  rewrite id_left_disp.
  rewrite id_right_disp.
  unfold transportb.
  rewrite !transport_f_f.
  refine (!_).
  use transportf_set.
  apply homset_property.
Qed.


Proposition transportf_functor_disp_mor_id
            {C₁ C₂ : category}
            {D : disp_cat C₂}
            {F₁ F₂ : C₁ ⟶ C₂}
            (p : F₁ = F₂)
            {x : C₁}
            (xx : D (F₁ x))
  : transportf_functor_disp_mor
      p
      (transportb (λ z, _ -->[ z ] _) (functor_id _ _) (id_disp xx))
    =
    transportb
      (λ z, _ -->[ z ] _)
      (functor_id F₂ x)
      (id_disp _).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition transportf_functor_disp_mor_comp
            {C₁ C₂ : category}
            {D : disp_cat C₂}
            {F₁ F₂ : C₁ ⟶ C₂}
            (p : F₁ = F₂)
            {x y z : C₁}
            {f : x --> y}
            {g : y --> z}
            {xx : D (F₁ x)}
            {yy : D (F₁ y)}
            {zz : D (F₁ z)}
            (ff : xx -->[ #F₁ f ] yy)
            (gg : yy -->[ #F₁ g ] zz)
  : (transportf_functor_disp_mor
       p
       (transportb (λ z, _ -->[ z ] _) (functor_comp F₁ _ _) (ff ;; gg))
     =
     transportb
       (λ z, _ -->[ z ] _)
       (functor_comp F₂ _ _)
       (transportf_functor_disp_mor p ff ;; transportf_functor_disp_mor p gg))%mor_disp.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Section ComprehensionPullback.
  Context {G₀ G₁ G₂ : setgroupoid}
          {F : G₁ ⟶ G₂}
          {D : disp_setgrpd G₂}
          (I : cleaving D)
          {H₁ : G₀ ⟶ total_category D}
          {H₂ : G₀ ⟶ G₁}
          (p : H₁ ∙ pr1_category _ = H₂ ∙ F).

  Definition isofib_comprehension_pb_mor_data
    : functor_data G₀ (total_category (reindex_disp_cat F D)).
  Proof.
    use make_functor_data.
    - exact (λ x, H₂ x ,, transportf_functor_disp_ob p (pr2 (H₁ x))).
    - exact (λ x y f,
             #H₂ f
             ,,
             transportf_functor_disp_mor p (pr2 (#H₁ f))).
  Defined.

  Proposition isofib_comprehension_pb_mor_laws
    : is_functor isofib_comprehension_pb_mor_data.
  Proof.
    split.
    - intros x.
      use total2_paths_f.
      + cbn.
        apply functor_id.
      + cbn.
        etrans.
        {
          do 2 apply maponpaths.
          exact (!fiber_paths (!(functor_id H₁ x))).
        }
        etrans.
        {
          apply maponpaths.
          refine (_ @ transportf_functor_disp_mor_id p _).
          apply maponpaths.
          unfold transportb.
          apply maponpaths_2.
          apply (homset_property G₂).
        }
        unfold transportb.
        cbn.
        refine (transportf_reindex (F := F) _ _ @ _).
        rewrite transport_f_f.
        apply maponpaths_2.
        apply homset_property.
    - intros x y z f g.
      use total2_paths_f.
      + cbn.
        apply functor_comp.
      + cbn.
        etrans.
        {
          do 2 apply maponpaths.
          exact (!fiber_paths (!(functor_comp H₁ f g))).
        }
        etrans.
        {
          apply maponpaths.
          refine (_ @ transportf_functor_disp_mor_comp p _ _).
          apply maponpaths.
          unfold transportb.
          apply maponpaths_2.
          apply (homset_property G₂).
        }
        unfold transportb.
        cbn.
        refine (transportf_reindex (F := F) _ _ @ _).
        rewrite transport_f_f.
        apply maponpaths_2.
        apply homset_property.
  Qed.

  Definition isofib_comprehension_pb_mor
    : G₀ ⟶ total_category (reindex_disp_cat F D).
  Proof.
    use make_functor.
    - exact isofib_comprehension_pb_mor_data.
    - exact isofib_comprehension_pb_mor_laws.
  Defined.

  Local Arguments transportf {X} P {x x' e} _.

  Proposition isofib_comprehension_pb_mor_pr1
    : isofib_comprehension_pb_mor
      ∙ total_functor (reindex_disp_cat_disp_functor F D)
      =
      H₁.
  Proof.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq_alt.
    - abstract
        (intro x ;
         use total2_paths_f ; [ exact (!(path_functor_ob p x)) | ] ;
         cbn ;
         unfold transportf_functor_disp_ob ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply isaset_ob).
    - intros x y f.
      etrans.
      {
        apply maponpaths.
        apply idtoiso_total_category.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply idtoiso_total_category.
      }
      refine (!_).
      use total2_paths_f.
      + abstract
          (cbn ;
           refine (maponpaths (λ z, _ · z) _
                   @ path_functor_mor (!p) f
                   @ maponpaths (λ z, z · _) _) ;
           apply setcategory_eq_idtoiso).
      + cbn.
        rewrite transportf_functor_disp_mor_eq.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite assoc_disp_var.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite (assoc_disp_var (D := D)).
        rewrite transport_f_f.
        rewrite (assoc_disp_var (D := D)).
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          do 3 apply maponpaths.
          apply (idtoiso_disp_comp' (D := D)).
        }
        rewrite !mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          do 3 apply maponpaths.
          apply idtoiso_disp_set_grpd_refl.
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite id_right_disp.
        unfold transportb.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        refine (_ @ idtoiso_disp_set_grpd_precomp _ _ _).
        apply maponpaths_2.
        apply (homset_property G₂).
  Qed.

  Proposition isofib_comprehension_pb_mor_pr2
    : isofib_comprehension_pb_mor
      ∙ pr1_category (reindex_disp_cat F D)
      =
      H₂.
  Proof.
    use functor_eq.
    {
      apply homset_property.
    }
    apply idpath.
  Qed.

  Context {H' : G₀ ⟶ total_category (reindex_disp_cat F D)}
          (p₁ : H' ∙ total_functor (reindex_disp_cat_disp_functor F (pr1 D))
                =
                H₁)
          (p₂ : H' ∙ pr1_category (reindex_disp_cat F (pr1 D)) = H₂).

  Lemma isofib_comprehension_pb_mor_unique_ob
    : H' ~ isofib_comprehension_pb_mor.
  Proof.
    intro x.
    use total2_paths_f.
    - exact (path_functor_ob p₂ x).
    - rewrite transportf_reindex_ob ; cbn.
      unfold transportf_functor_disp_ob.
      use transportf_transpose_right.
      unfold transportb.
      rewrite transport_f_f.
      refine (_ @ fiber_paths (path_functor_ob p₁ x)).
      cbn.
      apply maponpaths_2.
      apply isaset_ob.
  Qed.

  Local Notation "'idtoiso_d'" := (idtoiso_disp _ _) (only printing).

  Proposition isofib_comprehension_pb_mor_unique
    : H' = isofib_comprehension_pb_mor.
  Proof.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq.
    - exact isofib_comprehension_pb_mor_unique_ob.
    - intros x₁ x₂ f.
      rewrite double_transport_idtoiso.
      rewrite assoc'.
      use z_iso_inv_on_right.
      etrans.
      {
        apply maponpaths.
        apply idtoiso_total_category.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply idtoiso_total_category.
      }
      use total2_paths_f.
      + cbn.
        refine (_ @ !(path_functor_mor p₂ f) @ _).
        * cbn.
          apply maponpaths_2.
          use setcategory_eq_idtoiso.
        * cbn.
          apply maponpaths.
          use setcategory_eq_idtoiso.
      + etrans.
        {
          apply transportf_reindex.
        }
        cbn.
        unfold transportf_functor_disp_ob, transportb.
        rewrite transport_f_f.
        pose proof (transportb_transpose_right
                      (fiber_paths (path_functor_mor p₁ f))) as q.
        cbn in q.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          simple refine (_ @ maponpaths
                               (λ f,
                                 transportf
                                   (λ z, _ -->[ z ] _)
                                   (f ;; idtoiso_disp _ (idpath _))%mor_disp)
                               q).
          * cbn.
            refine (!_).
            rewrite (assoc_disp_var (D := D)).
            rewrite transport_f_f.
            etrans.
            {
              do 2 apply maponpaths.
              apply maponpaths_2.
              exact (idtoiso_total_category_pr2 (path_functor_ob p₁ x₂)).
            }
            rewrite mor_disp_transportf_postwhisker.
            rewrite mor_disp_transportf_prewhisker.
            rewrite transport_f_f.
            etrans.
            {
              do 2 apply maponpaths.
              exact (idtoiso_disp_comp' _ _).
            }
            rewrite mor_disp_transportf_prewhisker.
            rewrite transport_f_f.
            rewrite idtoiso_reindex_disp_cat'.
            rewrite mor_disp_transportf_prewhisker.
            use transportf_transpose_right.
            unfold transportb.
            rewrite transport_f_f.
            refine (_ @ idtoiso_disp_set_grpd_postcomp _ _ _).
            apply maponpaths_2.
            apply (homset_property G₂).
          * rewrite !assoc'.
            apply maponpaths.
            refine (_ @ pr1_maponpaths_idtoiso _ _).
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths.
              exact (idtoiso_total_category (D := D) (path_functor_ob p₁ x₂)).
            }
            cbn.
            refine (!(pr1_idtoiso_concat (C := G₂) _ _) @ _).
            use setcategory_eq_idtoiso.
        }
        cbn.
        unfold transportb.
        rewrite transport_f_f.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite transportf_functor_disp_mor_eq.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        unfold transportf_functor_disp_ob.
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          exact (idtoiso_total_category_pr2 (path_functor_ob p₁ x₁)).
        }
        rewrite !mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        refine (!_).
        rewrite !(assoc_disp (D := D)).
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        rewrite idtoiso_reindex_disp_cat'.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          exact (idtoiso_disp_comp' (D := D) _ _).
        }
        rewrite !mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        use transportf_transpose_right.
        unfold transportb.
        rewrite transport_f_f.
        refine (_ @ idtoiso_disp_set_grpd_prepostcomp _ _ _ _ _).
        apply maponpaths_2.
        apply (homset_property G₂).
  Qed.
End ComprehensionPullback.

Definition disp_cat_isofib_comprehension_cartesian
  : is_cartesian_disp_functor disp_cat_isofib_comprehension.
Proof.
  use is_cartesian_disp_functor_chosen_lifts.
  - exact cleaving_disp_cat_isofib.
  - intros G₁ G₂ F D.
    use isPullback_cartesian_in_cod_disp.
    intros G₀ H₁ H₂ p.
    simple refine (_ ,, _).
    + simple refine (_ ,, _ ,, _).
      * exact (isofib_comprehension_pb_mor p).
      * apply isofib_comprehension_pb_mor_pr1.
      * apply isofib_comprehension_pb_mor_pr2.
    + abstract
        (intros H' ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         exact (isofib_comprehension_pb_mor_unique
                  (pr2 D)
                  _
                  (pr12 H')
                  (pr22 H'))).
Defined.
