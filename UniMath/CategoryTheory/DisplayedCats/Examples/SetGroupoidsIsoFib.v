(*****************************************************************************************

 The displayed category of isofibrations over setgroupoids

 In this file, we define the displayed category of isofibrations of setgroupoids. We also
 show that this displayed category is univalent and we equip it with a cleaving.

 This (univalent) displayed category is a key ingredient to represent the setgroupoid
 model of type theory. This model, which was used by Hofmann and Streicher to show that UIP
 is independent from MLTT, is represented by a comprehension category whose category of
 contexts is the (univalent) category of setgroupoids, and types in some setgroupoid [Γ] are
 the same as isofibrations into [Γ].

 Concretely, we represent an isofibration into a setgroupoid [Γ] by a displayed category [D]
 together with a cleaving on [D]. We assume that the type of objects over [x] forms a set
 and that every displayed morphism in [D] is invertible, so that the total category of [D]
 also is a setgroupoid.

 References
 - 'The groupoid interpretation of type theory' by Hofmann and Streicher

 Content
 1. Displayed categories that represent setgroupoids
 2. Properties of displayed setgroupoids
 3. The data of the displayed category of displayed setgroupoids
 4. Transport lemmas
 5. Verification of the axioms
 6. This displayed category is univalent
 6.1. Isos of displayed setgroupoids
 6.2. Proof of univalence
 7. The displayed category of isofibrations
 8. A cleaving for the displayed category of isofibrations

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetGroupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.

Local Open Scope cat.

(** * 1. Displayed categories that represent setgroupoids *)
Definition is_disp_setgrpd
           {C : category}
           (D : disp_cat C)
  : UU
  := (∏ (x : C), isaset (D x))
     ×
     groupoidal_disp_cat D.

Proposition isaprop_is_disp_setgrpd
            {C : category}
            (D : disp_cat C)
  : isaprop (is_disp_setgrpd D).
Proof.
  use isapropdirprod.
  - use impred ; intro.
    apply isapropisaset.
  - apply isaprop_groupoidal_disp_cat.
Qed.

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

(** * 2. Properties of displayed setgroupoids *)
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

(** * 3. The data of the displayed category of displayed setgroupoids *)
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

(** * 4. Transport lemmas *)
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

Proposition transportb_disp_functor_data_help_on_mor_base
            {G₁ G₂ : setgroupoid}
            {F F' : G₁ ⟶ G₂}
            (p : pr1 F = pr1 F')
            {x y : G₁}
            (f : x --> y)
  : idtoiso (maponpaths (λ z, pr1 z x) p)
    · # F' f
    · idtoiso (maponpaths (λ z, pr1 z y) (! p))
    =
    # F f.
Proof.
  induction F as [ FD HF ], F' as [ FD' HF' ].
  cbn in *.
  induction p ; cbn.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Proposition transportb_disp_functor_data_help_on_mor_path
            {G₁ G₂ : setgroupoid}
            {F F' : G₁ ⟶ G₂}
            (p : pr1 F = pr1 F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
            {y : G₁}
            (yy : pr1 D₁ y)
  : transportf (pr1 D₂) (maponpaths (λ z, pr1 z y) (!p)) (pr1 FF y yy)
    =
    transportb_disp_functor_data_help p FF y yy.
Proof.
  induction F as [ FD HF ], F' as [ FD' HF' ].
  cbn in *.
  induction p ; cbn.
  apply idpath.
Defined.

Proposition transportb_disp_functor_data_help_on_mor
            {G₁ G₂ : setgroupoid}
            {F F' : G₁ ⟶ G₂}
            (p : pr1 F = pr1 F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
            {x y : G₁}
            {f : x --> y}
            {xx : pr1 D₁ x}
            {yy : pr1 D₁ y}
            (ff : xx -->[ f ] yy)
  : (♯(transportb_disp_functor_data_help p FF) ff
     =
     transportf
       (λ z,
        transportb_disp_functor_data_help p FF x xx
        -->[ z ]
        transportb_disp_functor_data_help p FF y yy)
       (transportb_disp_functor_data_help_on_mor_base p f)
       (idtoiso_disp (maponpaths (λ z, pr1 z x) p) (transportfbinv _ _ _)
        ;; ♯(pr1 FF) ff
        ;; idtoiso_disp
             (maponpaths (λ z, pr1 z y) (!p))
             (transportb_disp_functor_data_help_on_mor_path p FF yy)))%mor_disp.
Proof.
  induction F as [ FD HF ], F' as [ FD' HF' ].
  cbn in *.
  induction p ; cbn.
  rewrite (id_right_disp (D := pr1 D₂)).
  unfold transportb.
  rewrite transport_f_f.
  rewrite (id_left_disp (D := pr1 D₂)).
  unfold transportb.
  rewrite transport_f_f.
  refine (!_).
  apply transportf_set.
  apply (homset_property G₂).
Qed.

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

Proposition transportb_disp_setgrpd_help_ob
            {G₁ G₂ : setgroupoid}
            {F F' : G₁ ⟶ G₂}
            (p : F = F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
            {x : G₁}
            (xx : pr1 D₁ x)
  : pr1 (transportb (mor_disp D₁ D₂) p FF) x xx
    =
    transportb_disp_functor_data p FF x xx.
Proof.
  induction p.
  apply idpath.
Defined.

Proposition transportb_disp_setgrpd_mor_help
            {G₁ G₂ : setgroupoid}
            {F F' : G₁ ⟶ G₂}
            (p : F = F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
            {x y : G₁}
            {f : x --> y}
            {xx : pr1 D₁ x}
            {yy : pr1 D₁ y}
            (ff : xx -->[ f ] yy)
  : disp_functor_on_morphisms
      (pr1 (transportb (mor_disp D₁ D₂) p FF))
      ff
    =
    transportf
      (λ z,
       pr1 (transportb (mor_disp D₁ D₂) p FF) x xx
       -->[ z ]
       pr1 (transportb (mor_disp D₁ D₂) p FF) y yy)
      (id_right _ @ id_left _)
      (idtoiso_disp (idpath _) (transportb_disp_setgrpd_help_ob p FF xx)
       ;; (disp_functor_on_morphisms (transportb_disp_functor_data p FF) ff)
       ;; idtoiso_disp (idpath _) (!(transportb_disp_setgrpd_help_ob p FF yy)))%mor_disp.
Proof.
  induction p ; cbn.
  rewrite (id_right_disp (D := pr1 D₂)).
  unfold transportb.
  rewrite transport_f_f.
  rewrite (id_left_disp (D := pr1 D₂)).
  unfold transportb.
  rewrite transport_f_f.
  refine (!_).
  use transportf_set.
  apply (homset_property G₂).
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

Proposition transportb_disp_setgrpd_ob
            {G₁ G₂ : setgroupoid}
            {FD : functor_data G₁ G₂}
            {HF₁ HF₂ : is_functor FD}
            (F := (FD ,, HF₁) : G₁ ⟶ G₂)
            (F' := (FD ,, HF₂) : G₁ ⟶ G₂)
            (p : F = F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
            {x : G₁}
            (xx : pr1 D₁ x)
  : pr1 (transportb (mor_disp D₁ D₂) p FF) x xx = pr1 FF x xx.
Proof.
  exact (maponpaths (λ z, pr1 z x xx) (transportb_disp_setgrpd p FF)).
Qed.

Proposition transportb_disp_setgrpd_mor
            {G₁ G₂ : setgroupoid}
            {FD : functor_data G₁ G₂}
            {HF₁ HF₂ : is_functor FD}
            (F := (FD ,, HF₁) : G₁ ⟶ G₂)
            (F' := (FD ,, HF₂) : G₁ ⟶ G₂)
            (p : F = F')
            {D₁ : disp_cat_data_of_disp_setgrpd G₁}
            {D₂ : disp_cat_data_of_disp_setgrpd G₂}
            (FF : D₁ -->[ F' ] D₂)
            {x y : G₁}
            {f : x --> y}
            {xx : pr1 D₁ x}
            {yy : pr1 D₁ y}
            (ff : xx -->[ f ] yy)
  : disp_functor_on_morphisms
      (pr1 (transportb (mor_disp D₁ D₂) p FF))
      ff
    =
    transportf
      (λ z,
       pr1 (transportb (mor_disp D₁ D₂) p FF) x xx
       -->[ z ]
       pr1 (transportb (mor_disp D₁ D₂) p FF) y yy)
      (id_right _ @ id_left _)
      (idtoiso_disp (idpath _) (transportb_disp_setgrpd_ob p FF xx)
       ;; disp_functor_on_morphisms (pr1 FF) ff
       ;; idtoiso_disp (idpath _) (!(transportb_disp_setgrpd_ob p FF yy)))%mor_disp.
Proof.
  (**
     We change the implicit arguments in this proof to make the goals more readable
   *)
  Local Arguments transportf {X P x x' e} _.
  Local Arguments idtoiso_disp {_ _ _ _ _ _ _ _}.
  etrans.
  {
    apply transportb_disp_setgrpd_mor_help.
  }
  apply maponpaths.
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply transportb_disp_functor_data_help_on_mor.
  }
  rewrite mor_disp_transportf_prewhisker.
  rewrite mor_disp_transportf_postwhisker.
  rewrite !(assoc_disp_var (D := pr1 D₂)).
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    do 4 apply maponpaths.
    apply (idtoiso_disp_comp' (D := pr1 D₂)).
  }
  rewrite !(assoc_disp (D := pr1 D₂)).
  unfold transportb.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    apply maponpaths.
    do 2 apply maponpaths_2.
    apply (idtoiso_disp_comp' (D := pr1 D₂)).
  }
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  use transportf_transpose_right.
  unfold transportb.
  rewrite transport_f_f.
  cbn -[idtoiso_disp].
  refine (_ @ idtoiso_disp_set_grpd_prepostcomp (p' := idpath _) (q' := idpath _) _ _ _ _ _).
  apply maponpaths_2.
  apply (homset_property G₂).
Qed.

Arguments transportf {X} P {x x'} e _.
Arguments idtoiso_disp {_ _ _ _} _ {_ _} _.

(** * 5. Verification of the axioms *)
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

(** * 6. This displayed category is univalent *)

(** ** 6.1. Isos of displayed setgroupoids *)
Section Isos.
  Context {G : setgroupoid}
          {D₁ D₂ : disp_setgrpd G}
          (F : disp_functor (functor_identity G) D₁ D₂).

  Section ToIso.
    Context (HF₁ : ∏ (x : G), isweq (F x))
            (HF₂ : disp_functor_ff F).

    Let Fo (x : G) : D₁ x ≃ D₂ x := make_weq _ (HF₁ x).

    Definition to_is_z_iso_disp_disp_setgrpd_inv_data
      : disp_functor_data (functor_identity (pr1 G)) D₂ D₁.
    Proof.
      simple refine (_ ,, _).
      - exact (λ x xx, invmap (Fo x) xx).
      - refine (λ x y xx yy f ff,
                disp_functor_ff_inv
                  F
                  HF₂
                  (transportb
                     (λ z, _ -->[ z ] _)
                     _
                     (idtoiso_disp (idpath _) (homotweqinvweq (Fo x) xx)
                      ;; ff
                      ;; idtoiso_disp (idpath _) (!(homotweqinvweq (Fo y) yy)))%mor_disp)).
        abstract
          (cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Proposition to_is_z_iso_disp_disp_setgrpd_inv_laws
      : disp_functor_axioms to_is_z_iso_disp_disp_setgrpd_inv_data.
    Proof.
      split.
      - intros x xx ; cbn -[idtoiso_disp].
        unfold transportb.
        rewrite (id_right_disp (D := D₂)).
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply (idtoiso_disp_comp (D := D₂)).
        }
        unfold transportb.
        rewrite transport_f_f.
        rewrite pathsinv0r.
        cbn.
        refine (_ @ disp_functor_ff_inv_identity F HF₂ _).
        apply maponpaths.
        unfold transportb.
        apply maponpaths_2.
        apply (homset_property G).
      - intros x y z xx yy zz f g ff gg ; cbn -[idtoiso_disp].
        refine (_ @ disp_functor_ff_inv_compose F HF₂ _ _).
        apply maponpaths.
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite !(assoc_disp_var (D := D₂)).
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        refine (!_).
        etrans.
        {
          do 3 apply maponpaths.
          rewrite assoc_disp.
          apply maponpaths.
          apply maponpaths_2.
          etrans.
          {
            apply (idtoiso_disp_comp (D := D₂)).
          }
          rewrite pathsinv0l ; cbn.
          apply idpath.
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite (id_left_disp (D := D₂)).
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        apply maponpaths_2.
        apply (homset_property G).
    Qed.

    Definition to_is_z_iso_disp_disp_setgrpd_inv
      : disp_functor (functor_identity (pr1 G)) D₂ D₁.
    Proof.
      simple refine (_ ,, _).
      - exact to_is_z_iso_disp_disp_setgrpd_inv_data.
      - exact to_is_z_iso_disp_disp_setgrpd_inv_laws.
    Defined.

    Proposition to_is_z_iso_disp_disp_setgrpd_left
      : disp_functor_composite_data to_is_z_iso_disp_disp_setgrpd_inv F
        =
        pr1 (disp_functor_identity D₂).
    Proof.
      use disp_functor_data_over_id_eq.
      - intros x xx ; cbn.
        apply (homotweqinvweq (Fo x)).
      - intros x y f xx yy ff ; cbn -[idtoiso_disp].
        etrans.
        {
          apply maponpaths_2.
          apply (FF_disp_functor_ff_inv HF₂).
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite !(assoc_disp_var (D := D₂)).
        rewrite !transport_f_f.
        etrans.
        {
          do 3 apply maponpaths.
          apply (idtoiso_disp_comp (D := D₂)).
        }
        rewrite pathsinv0l.
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply id_right_disp.
        }
        unfold transportb.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        apply maponpaths_2.
        apply (homset_property G).
    Qed.

    Proposition to_is_z_iso_disp_disp_setgrpd_right
      : disp_functor_composite_data F to_is_z_iso_disp_disp_setgrpd_inv
        =
        pr1 (disp_functor_identity D₁).
    Proof.
      use disp_functor_data_over_id_eq.
      - intros x xx ; cbn.
        apply (homotinvweqweq (Fo x)).
      - intros x y f xx yy ff ; cbn -[idtoiso_disp].
        unfold transportb.
        refine (_ @ disp_functor_ff_FF_inv HF₂ _).
        etrans.
        {
          apply maponpaths.
          exact (!(disp_functor_ff_FF_inv HF₂ _)).
        }
        etrans.
        {
          refine (!_).
          apply (disp_functor_ff_inv_compose F HF₂).
        }
        apply maponpaths.
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite (disp_functor_transportf _ F).
        etrans.
        {
          do 2 apply maponpaths.
          apply (disp_functor_idtoiso_disp F).
        }
        unfold transportb.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite (assoc_disp_var (D := D₂)).
        rewrite transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply (idtoiso_disp_comp (D := D₂)).
        }
        unfold transportb.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          do 4 apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply (homotweqinvweqweq (Fo y)).
          }
          apply pathsinv0l.
        }
        etrans.
        {
          apply maponpaths.
          apply id_right_disp.
        }
        unfold transportb.
        rewrite transport_f_f.
        refine (!_).
        rewrite (disp_functor_comp F).
        unfold transportb.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply (disp_functor_idtoiso_disp F).
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          do 2 apply maponpaths.
          apply (homotweqinvweqweq (Fo x)).
        }
        apply maponpaths_2.
        apply homset_property.
    Qed.

    Definition to_is_z_iso_disp_disp_setgrpd
      : is_z_iso_disp (D := disp_cat_of_disp_setgrpd) (identity_z_iso _) F.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact to_is_z_iso_disp_disp_setgrpd_inv.
      - abstract
          (use disp_functor_eq ;
           rewrite transportb_disp_setgrpd ;
           exact to_is_z_iso_disp_disp_setgrpd_left).
      - abstract
          (use disp_functor_eq ;
           rewrite transportb_disp_setgrpd ;
           exact to_is_z_iso_disp_disp_setgrpd_right).
    Defined.
  End ToIso.

  Section FromIso.
    Context (HF : is_z_iso_disp
                    (D := disp_cat_of_disp_setgrpd)
                    (identity_z_iso _)
                    F).

    Let F' : disp_functor (functor_identity G) D₂ D₁
      := inv_mor_disp_from_z_iso HF.

    Lemma is_z_iso_disp_setgrpd_left_law
          {x : G}
          (xx : D₁ x)
      : F' x (F x xx) = xx.
    Proof.
      refine (disp_functor_eq_ob (inv_mor_after_z_iso_disp HF) xx @ _).
      apply transportb_disp_setgrpd_ob.
    Qed.

    Lemma is_z_iso_disp_setgrpd_right_law
          {x : G}
          (xx : D₂ x)
      : F x (F' x xx) = xx.
    Proof.
      refine (disp_functor_eq_ob (z_iso_disp_after_inv_mor HF) xx @ _).
      apply transportb_disp_setgrpd_ob.
    Qed.

    Definition is_z_iso_disp_to_isweq
               (x : G)
      : isweq (F x).
    Proof.
      use isweq_iso.
      - exact (λ xx, F' x xx).
      - intros xx ; cbn.
        apply is_z_iso_disp_setgrpd_left_law.
      - intros xx ; cbn.
        apply is_z_iso_disp_setgrpd_right_law.
    Qed.

    Definition is_z_iso_disp_to_ff
      : disp_functor_ff F.
    Proof.
      intros x y xx yy f.
      use isweq_iso.
      - intros ff.
        refine (transportf
                  (λ z, _ -->[ z ] _)
                  _
                  (idtoiso_disp (idpath _) (!(is_z_iso_disp_setgrpd_left_law xx))
                   ;; ♯ F' ff
                   ;; idtoiso_disp (idpath _) (is_z_iso_disp_setgrpd_left_law yy))%mor_disp).
        abstract
          (cbn ;
           rewrite id_left, id_right ;
           apply idpath).
      - intro ff ; cbn -[idtoiso_disp].
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          exact (!(disp_functor_eq_mor (!(inv_mor_after_z_iso_disp HF)) ff)).
        }
        rewrite mor_disp_transportf_prewhisker.
        rewrite mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply transportb_disp_setgrpd_mor.
        }
        cbn -[idtoiso_disp].
        rewrite !(assoc_disp_var (D := D₁)).
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 4 apply maponpaths.
          apply (idtoiso_disp_comp (D := D₁)).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite !(assoc_disp_var (D := D₁)).
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 5 apply maponpaths.
          apply (idtoiso_disp_comp (D := D₁)).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite !(assoc_disp (D := D₁)).
        unfold transportb.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 3 apply maponpaths_2.
          apply (idtoiso_disp_comp (D := D₁)).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          apply (idtoiso_disp_comp (D := D₁)).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply idtoiso_disp_set_grpd_refl.
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite id_right_disp.
        unfold transportb.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply idtoiso_disp_set_grpd_refl.
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        rewrite id_left_disp.
        unfold transportb.
        rewrite !transport_f_f.
        apply transportf_set.
        apply (homset_property G).
      - intro ff.
        cbn -[idtoiso_disp].
        rewrite (disp_functor_transportf _ F).
        rewrite (disp_functor_comp F).
        unfold transportb.
        rewrite transport_f_f.
        rewrite (disp_functor_comp F).
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply (disp_functor_idtoiso_disp F).
        }
        unfold transportb.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          apply (disp_functor_idtoiso_disp F).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          exact (!(disp_functor_eq_mor (!(z_iso_disp_after_inv_mor HF)) ff)).
        }
        rewrite mor_disp_transportf_prewhisker.
        rewrite mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply transportb_disp_setgrpd_mor.
        }
        cbn -[idtoiso_disp].
        rewrite !(assoc_disp_var (D := D₂)).
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 4 apply maponpaths.
          apply (idtoiso_disp_comp (D := D₂)).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite !(assoc_disp_var (D := D₂)).
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 5 apply maponpaths.
          apply (idtoiso_disp_comp (D := D₂)).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite !(assoc_disp (D := D₂)).
        unfold transportb.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 3 apply maponpaths_2.
          apply (idtoiso_disp_comp (D := D₂)).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          apply (idtoiso_disp_comp (D := D₂)).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          apply idtoiso_disp_set_grpd_refl.
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        rewrite id_right_disp.
        unfold transportb.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply idtoiso_disp_set_grpd_refl.
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        rewrite id_left_disp.
        unfold transportb.
        rewrite !transport_f_f.
        apply transportf_set.
        apply (homset_property G).
    Qed.
  End FromIso.
End Isos.

Definition disp_setgrpd_iso_weq
           {G : setgroupoid}
           {D₁ D₂ : disp_setgrpd G}
           (F : disp_functor (functor_identity G) D₁ D₂)
  : ((∏ (x : G), isweq (F x)) × disp_functor_ff F)
    ≃
    is_z_iso_disp (D := disp_cat_of_disp_setgrpd) (identity_z_iso _) F.
Proof.
  use weqimplimpl.
  - intro HF.
    use to_is_z_iso_disp_disp_setgrpd.
    + exact (pr1 HF).
    + exact (pr2 HF).
  - intro HF.
    split.
    + exact (is_z_iso_disp_to_isweq F HF).
    + exact (is_z_iso_disp_to_ff F HF).
  - abstract
      (use isapropdirprod ; [ | apply isaprop_disp_functor_ff ] ;
       use impred ; intro ;
       apply isapropisweq).
  - abstract
      (apply isaprop_is_z_iso_disp).
Defined.

(** ** 6.2. Proof of univalence *)
Proposition is_univalent_disp_cat_of_disp_setgrpd
  : is_univalent_disp disp_cat_of_disp_setgrpd.
Proof.
  use is_univalent_disp_from_fibers.
  intros G D₁ D₂.
  cbn in G, D₁, D₂.
  use weqhomot.
  - refine (_
            ∘ disp_cat_eq _ _
            ∘ path_sigma_hprop _ _ _ (isaprop_is_disp_setgrpd _))%weq.
    use weqfibtototal.
    intro F ; cbn.
    apply disp_setgrpd_iso_weq.
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_z_iso_disp.
    }
    use subtypePath.
    {
      intro.
      apply isaprop_disp_functor_axioms.
    }
    apply idpath.
Qed.

Definition univ_disp_cat_of_disp_setgrpd
  : disp_univalent_category cat_of_setgroupoid.
Proof.
  use make_disp_univalent_category.
  - exact disp_cat_of_disp_setgrpd.
  - exact is_univalent_disp_cat_of_disp_setgrpd.
Defined.

(** * 7. The displayed category of isofibrations *)
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

Definition univalent_disp_cat_isofib
  : disp_univalent_category univalent_cat_of_setgroupoid.
Proof.
  use make_disp_univalent_category.
  - exact disp_cat_isofib.
  - exact is_univalent_disp_cat_isofib.
Defined.

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

(** * 8. A cleaving for the displayed category of isofibrations *)
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
