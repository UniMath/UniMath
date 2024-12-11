(*****************************************************************************************

 The comprehension functor of setgroupoids

 In this file, we define the comprehension functor that sends isofibrations on some
 setgroupoid [Γ] to a functor into [Γ]. Since we represent isofibrations using displayed
 categories, we use the total category and the projection of a displayed category. We
 also show that this functor is Cartesian. To do so, we verify that the chosen lifts, which
 are given by reindexing, are sent to pullback squares.

 Content
 1. The total category of an isofibration
 2. The comprehension functor
 3. Some transport lemmas that we need
 4. The comprehension functor is Cartesian

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetGroupoids.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.SetGroupoidsIsoFib.

Local Open Scope cat.

(** * 1. The total category of an isofibration *)
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

(** * 2. The comprehension functor *)
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

(** * 3. Some transport lemmas that we need *)
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

(** * 4. The comprehension functor is Cartesian *)
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
                  _
                  (pr12 H')
                  (pr22 H'))).
Defined.
