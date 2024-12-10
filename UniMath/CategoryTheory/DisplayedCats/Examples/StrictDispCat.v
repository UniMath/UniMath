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

(********************************)

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.

Section Cleaving.
  Context {G₁ G₂ : setgroupoid}
          (F : G₂ ⟶ G₁)
          (D : disp_setgrpd G₁)
          (I : cleaving D).

  Definition disp_cat_iso_subst
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
End Cleaving.

Definition cleaving_disp_cat_isofib
  : cleaving disp_cat_isofib.
Proof.
  intros G₁ G₂ F D.
  simple refine ((_ ,, _) ,, _ ,, _) ; cbn.
  - exact (disp_cat_iso_subst F (pr1 D)).
  - apply cleaving_reindex_disp_cat.
    exact (pr2 D).
  - simple refine (_ ,, _).
    + apply reindex_disp_cat_disp_functor.
    + apply preserves_cleaving_reindex.
  - intros G₃ F' D' F''.
    use iscontraprop1.
    + admit.
    + simple refine ((_ ,, _) ,, _).
      * exact (lift_functor_into_reindex (pr1 F'')).
      * cbn in *.
        use make_preserves_cleaving.
        ** intros x y f yy.
           cbn.
