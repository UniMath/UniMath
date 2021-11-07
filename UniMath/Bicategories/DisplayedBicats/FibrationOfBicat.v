Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

(** MOVE *)
Definition rwhisker_of_invertible_2cell
           {B : bicat}
           {x y z : B}
           {f₁ f₂ : x --> y}
           (g : y --> z)
           (α : invertible_2cell f₁ f₂)
  : invertible_2cell (f₁ · g) (f₂ · g).
Proof.
  use make_invertible_2cell.
  - exact (α ▹ g).
  - is_iso.
    apply α.
Defined.
(** END MOVE *)

(** MOVE *)
Definition is_cartesian_id_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           (xx : D x)
  : is_cartesian (id_disp xx).
Proof.
  intros z g zz hh.
  use iscontraprop1.
  - use invproofirrelevance.
    intros f₁ f₂.
    use subtypePath.
    {
      intro ; intros.
      apply D.
    }
    refine (id_right_disp_var _ @ _ @ !(id_right_disp_var _)).
    rewrite (pr2 f₁), (pr2 f₂).
    apply idpath.
  - use tpair.
    + exact (transportf _ (id_right _) hh).
    + simpl.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite pathsinv0r.
      apply idpath.
Qed.

Definition is_cartesian_comp_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx : D x}
           {y : C}
           {yy : D y}
           {z : C}
           {zz : D z}
           {f : x --> y} {g : y --> z}
           {ff : xx -->[ f ] yy} {gg : yy -->[ g ] zz}
           (Hff : is_cartesian ff) (Hgg : is_cartesian gg)
  : is_cartesian (ff ;; gg)%mor_disp.
Proof.
  intros w h ww hh'.
  use iscontraprop1.
  - use invproofirrelevance.
    intros f₁ f₂.
    use subtypePath.
    {
      intro ; intros.
      apply D.
    }
    pose (hh'' := transportf _ (assoc _ _ _) hh').
    specialize (Hgg _ _ _ hh'').
    pose (pr1 Hgg) as t.
    specialize (Hff w h ww (pr1 t)).
    pose (isapropifcontr Hff) as i.
    refine (maponpaths pr1 (proofirrelevance _ i (_ ,, _) (_ ,, _))).
    + pose (isapropifcontr Hgg) as j.
      refine (maponpaths pr1 (proofirrelevance _ j (_ ,, _) (_ ,, _))).
      etrans.
      {
        apply assoc_disp_var.
      }
      unfold hh''.
      apply maponpaths.
      exact (pr2 f₁).
    + pose (isapropifcontr Hgg) as j.
      refine (maponpaths pr1 (proofirrelevance _ j (_ ,, _) (_ ,, _))).
      etrans.
      {
        apply assoc_disp_var.
      }
      unfold hh''.
      apply maponpaths.
      exact (pr2 f₂).
  - pose (transportf _ (assoc _ _ _) hh') as hh''.
    pose (Hgg _ _ _ hh'') as φ.
    pose (pr1 φ) as φar.
    pose (Hff _ _ _ (pr1 φar)) as ψ.
    use tpair.
    + exact (pr11 ψ).
    + simpl.
      rewrite assoc_disp.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (pr21 ψ).
      }
      etrans.
      {
        apply maponpaths.
        exact (pr21 φ).
      }
      unfold hh''.
      etrans.
      {
        apply transport_f_f.
      }
      rewrite pathsinv0r.
      apply idpath.
Qed.

Definition is_cartesian_disp_iso
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx : D x}
           {y : C}
           {yy : D y}
           {f : x --> y}
           {Hf : is_iso f}
           {ff : xx -->[ f ] yy}
           (Hff : is_iso_disp (make_iso f Hf) ff)
  : is_cartesian ff.
Proof.
  intros z g zz gf.
  use iscontraprop1.
  - abstract
      (apply invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       pose (pr2 φ₁ @ !(pr2 φ₂)) as r ;
       refine (id_right_disp_var _ @ _ @ !(id_right_disp_var _)) ;
       pose (transportf_transpose_left (inv_mor_after_iso_disp Hff)) as r' ;
       rewrite <- !r' ; clear r' ;
       rewrite !mor_disp_transportf_prewhisker ;
       rewrite !assoc_disp ;
       unfold transportb ;
       rewrite !transport_f_f ;
       apply maponpaths ;
       apply maponpaths_2 ;
       exact r).
  - simple refine (_ ,, _).
    + refine (transportf
                (λ z, _ -->[ z ] _)
                _
                (gf ;; inv_mor_disp_from_iso Hff)%mor_disp).
      abstract
        (rewrite assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         apply (iso_inv_after_iso (make_iso f Hf))).
    + abstract
        (simpl ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite assoc_disp_var ;
         rewrite transport_f_f ;
         etrans ;
           [ do 2 apply maponpaths ;
             apply (iso_disp_after_inv_mor Hff)
           | ] ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         rewrite id_right_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property ;
         rewrite disp_id_right).
Defined.

(** MOVE *)
Definition disp_hom_ob_mor
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           (xx : D x)
           (yy : D y)
  : disp_cat_ob_mor (hom x y).
Proof.
  simple refine (_ ,, _).
  - exact (λ f, xx -->[ f ] yy).
  - exact (λ f g ff gg α, ff ==>[ α ] gg).
Defined.

Definition disp_hom_id_comp
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           (xx : D x)
           (yy : D y)
  : disp_cat_id_comp _ (disp_hom_ob_mor xx yy).
Proof.
  simple refine (_ ,, _).
  - exact (λ f ff, disp_id2 ff).
  - exact (λ f g h α β ff gg hh αα ββ, αα •• ββ).
Defined.

Definition disp_hom_data
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           (xx : D x)
           (yy : D y)
  : disp_cat_data (hom x y).
Proof.
  simple refine (_ ,, _).
  - exact (disp_hom_ob_mor xx yy).
  - exact (disp_hom_id_comp xx yy).
Defined.

Definition disp_hom_laws
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           (xx : D x)
           (yy : D y)
  : disp_cat_axioms _ (disp_hom_data xx yy).
Proof.
  repeat split ; intro ; intros ; cbn.
  - rewrite disp_id2_left.
    apply maponpaths_2.
    apply cellset_property.
  - rewrite disp_id2_right.
    apply maponpaths_2.
    apply cellset_property.
  - rewrite disp_vassocr.
    apply maponpaths_2.
    apply cellset_property.
  - apply D.
Qed.

Definition disp_hom
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           (xx : D x)
           (yy : D y)
  : disp_cat (hom x y).
Proof.
  simple refine (_ ,, _).
  - exact (disp_hom_data xx yy).
  - exact (disp_hom_laws xx yy).
Defined.

Definition disp_hom_disp_iso_to_invertible_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {Hα : is_invertible_2cell α}
           {xx : D x}
           {yy : D y}
           {ff : disp_hom xx yy f}
           {gg : disp_hom xx yy g}
           (αα : ff -->[ α ] gg)
           (Hαα : @is_iso_disp
                    _
                    (disp_hom xx yy)
                    _ _
                    (α ,, is_inv2cell_to_is_iso _ _ _ Hα)
                    _ _
                    αα)
  : is_disp_invertible_2cell Hα αα.
Proof.
  simple refine (_ ,, (_ ,, _)).
  - exact (transportf
             (λ z, _ ==>[ z ] _)
             (id2_right _ )
             (inv_mor_disp_from_iso Hαα)).
  - abstract
      (cbn ;
       rewrite disp_mor_transportf_prewhisker ;
       etrans ;
       [ apply maponpaths ;
         exact (inv_mor_after_iso_disp Hαα)
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply cellset_property).
  - abstract
      (cbn ;
       rewrite disp_mor_transportf_postwhisker ;
       etrans ;
       [ apply maponpaths ;
         exact (iso_disp_after_inv_mor Hαα)
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply cellset_property).
Defined.

Definition disp_hom_disp_invertible_2cell_to_iso
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {Hα : is_invertible_2cell α}
           {xx : D x}
           {yy : D y}
           {ff : disp_hom xx yy f}
           {gg : disp_hom xx yy g}
           (αα : ff -->[ α ] gg)
           (Hαα : is_disp_invertible_2cell Hα αα)
  : @is_iso_disp
      _
      (disp_hom xx yy)
      _ _
      (α ,, is_inv2cell_to_is_iso _ _ _ Hα)
      _ _
      αα.
Proof.
  pose (d := (αα ,, Hαα) : disp_invertible_2cell (α ,, Hα) ff gg).
  simple refine (_ ,, (_ ,, _)).
  - exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_right _)
             (disp_inv_cell d)).
  - abstract
      (cbn ;
       unfold transportb ;
       rewrite disp_mor_transportf_postwhisker ;
       etrans ;
       [ apply maponpaths ;
         exact (disp_vcomp_linv d)
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply cellset_property).
  - abstract
      (cbn ;
       unfold transportb ;
       rewrite disp_mor_transportf_prewhisker ;
       etrans ;
       [ apply maponpaths ;
         exact (disp_vcomp_rinv d)
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply cellset_property).
Defined.

Definition disp_hom_disp_iso_weq_invertible_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {Hα : is_invertible_2cell α}
           {xx : D x}
           {yy : D y}
           {ff : disp_hom xx yy f}
           {gg : disp_hom xx yy g}
           (αα : ff -->[ α ] gg)
  : (@is_iso_disp
       _
       (disp_hom xx yy)
       _ _
       (α ,, is_inv2cell_to_is_iso _ _ _ Hα)
       _ _
       αα)
    ≃
    is_disp_invertible_2cell Hα αα.
Proof.
  use weqimplimpl.
  - apply disp_hom_disp_iso_to_invertible_2cell.
  - apply disp_hom_disp_invertible_2cell_to_iso.
  - apply isaprop_is_iso_disp.
  - apply (@isaprop_is_disp_invertible_2cell _ D _ _ _ _ (α ,, Hα)).
Qed.

(** END MOVE *)

Section BicatFibration.
  Context {B : bicat}.
  Variable (D : disp_bicat B).

  Section Cartesian1cell.
    Context {a b : B}
            {f : a --> b}
            {aa : D a}
            {bb : D b}.
    Variable (ff : aa -->[ f ] bb).

    Definition lift_1cell
               {c : B}
               {cc : D c}
               {h : c --> a}
               (gg : cc -->[ h · f ] bb)
      : UU
      := ∑ (hh : cc -->[ h ] aa),
         disp_invertible_2cell
           (id2_invertible_2cell _)
           (hh ;; ff)
           gg.

    Definition disp_mor_lift_1cell
               {c : B}
               {cc : D c}
               {h : c --> a}
               {gg : cc -->[ h · f ] bb}
               (Lh : lift_1cell gg)
      : cc -->[ h ] aa
      := pr1 Lh.

    Definition disp_cell_lift_1cell
               {c : B}
               {cc : D c}
               {h : c --> a}
               {gg : cc -->[ h · f ] bb}
               (Lh : lift_1cell gg)
      : disp_invertible_2cell _ (disp_mor_lift_1cell Lh;; ff) gg
      := pr2 Lh.

    Definition lift_2cell_type
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell gg)
               (Lh' : lift_1cell gg')
      : UU
      := ∑ (δδ : disp_mor_lift_1cell Lh ==>[ δ ] disp_mor_lift_1cell Lh'),
         transportf
           (λ z, _ ==>[ z ] _)
           (id2_right _ @ ! id2_left _ )
           (δδ ▹▹ ff •• disp_cell_lift_1cell Lh')
         =
         disp_cell_lift_1cell Lh •• σσ.

    Definition lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell gg)
               (Lh' : lift_1cell gg')
      : UU
      := iscontr (lift_2cell_type σσ Lh Lh').

    Definition cartesian_1cell
      : UU
      :=
        ∑ (Lh : ∏ (c : B)
                 (cc : D c)
                 (h : c --> a)
                 (gg : cc -->[ h · f ] bb),
                lift_1cell gg),
        ∏ (c : B)
          (cc : D c)
          (h h' : c --> a)
          (gg : cc -->[h · f ] bb)
          (gg' : cc -->[h' · f ] bb)
          (δ : h ==> h')
          (σσ : gg ==>[ δ ▹ f] gg'),
        lift_2cell
          σσ
          (Lh _ _ _ gg)
          (Lh _ _ _ gg').
  End Cartesian1cell.

  Definition is_cartesian_2cell
             {x y : B}
             {xx : D x} {yy : D y}
             {f g : x --> y}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             {α : f ==> g}
             (αα : ff ==>[ α ] gg)
    : UU
    := ∏ (h : x --> y)
         (hh : xx -->[ h ] yy)
         (γ : h ==> f)
         (ββ : hh ==>[ γ • α ] gg),
       ∃! (γγ : hh ==>[ γ ] ff), (γγ •• αα) = ββ.

  Definition cartesian_lift_2cell
             {x y : B}
             {xx : D x}
             {yy : D y}
             {f g : x --> y}
             (gg : xx -->[ g ] yy)
             (α : f ==> g)
    : UU
    := ∑ (ff : xx -->[ f ] yy) (αα : ff ==>[ α ] gg), is_cartesian_2cell αα.

  Definition local_cleaving
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (gg : xx -->[ g ] yy)
         (α : f ==> g),
       cartesian_lift_2cell gg α.

  Definition global_cleaving
    : UU
    := ∏ (a b : B)
         (bb : D b)
         (f : a --> b),
       ∑ (aa : D a) (ff : aa -->[ f ] bb), cartesian_1cell ff.

  Definition lwhisker_cartesian
    : UU
    := ∏ (w x y : B)
         (ww : D w) (xx : D x) (yy : D y)
         (h : w --> x)
         (f g : x --> y)
         (hh : ww -->[ h ] xx)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       is_cartesian_2cell αα → is_cartesian_2cell (hh ◃◃ αα).

  Definition rwhisker_cartesian
    : UU
    := ∏ (x y z : B)
         (xx : D x) (yy : D y) (zz : D z)
         (f g : x --> y) (h : y --> z)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (hh : yy -->[ h ] zz)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       is_cartesian_2cell αα → is_cartesian_2cell (αα ▹▹ hh).

  Definition fibration_of_bicats
    : UU
    := local_cleaving
       × global_cleaving
       × lwhisker_cartesian
       × rwhisker_cartesian.
End BicatFibration.

Definition local_fib
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∏ (x y : B)
       (xx : D x)
       (yy : D y),
     cleaving (disp_hom xx yy).

(** Being a cartesian 2-cell is a proposition *)
Definition isaprop_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
  : isaprop (is_cartesian_2cell D αα).
Proof.
  unfold is_cartesian_2cell.
  repeat (use impred ; intro).
  apply isapropiscontr.
Qed.

(** The two definitions of local cleavings coincide *)
Definition cartesian_2cell_to_cartesian
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
           (Hαα : is_cartesian_2cell D αα)
  : @is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα.
Proof.
  intros h γ hh γα.
  exact (Hαα h hh γ γα).
Qed.

Definition cartesian_to_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
           (Hαα : @is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
  : is_cartesian_2cell D αα.
Proof.
  intros h hh γ γα.
  exact (Hαα h γ hh γα).
Qed.

Definition cartesian_2cell_weq_cartesian
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
  : (@is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
    ≃
    is_cartesian_2cell D αα.
Proof.
  use weqimplimpl.
  - apply cartesian_to_cartesian_2cell.
  - apply cartesian_2cell_to_cartesian.
  - apply isaprop_is_cartesian.
  - apply isaprop_is_cartesian_2cell.
Qed.

Definition local_cleaving_to_local_fib
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_cleaving D)
  : local_fib D.
Proof.
  intros x y xx yy g f α gg ; cbn in *.
  pose (HD x y xx yy f g gg α) as lift.
  unfold cartesian_lift.
  unfold cartesian_lift_2cell in lift.
  cbn.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply cartesian_2cell_to_cartesian.
  exact (pr22 lift).
Defined.

Definition local_fib_to_local_cleaving
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_fib D)
  : local_cleaving D.
Proof.
  intros x y xx yy g f α gg ; cbn in *.
  pose (HD x y xx yy f g gg α) as lift.
  unfold cartesian_lift in lift.
  unfold cartesian_lift_2cell.
  cbn.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply cartesian_to_cartesian_2cell.
  exact (pr22 lift).
Defined.

Definition local_fib_weq_local_cleaving
           {B : bicat}
           (D : disp_bicat B)
  : local_cleaving D ≃ local_fib D.
Proof.
  use make_weq.
  - exact local_cleaving_to_local_fib.
  - use gradth.
    + exact local_fib_to_local_cleaving.
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_cartesian_2cell).
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_cartesian).
Defined.

(** Properties of cartesian 2-cells *)
Definition identity_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f : x --> y}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : is_cartesian_2cell D (disp_id2 ff).
Proof.
  apply cartesian_to_cartesian_2cell.
  exact (@is_cartesian_id_disp _ (disp_hom xx yy) f ff).
Defined.

Definition vcomp_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g h : x --> y}
           {α : f ==> g} {β : g ==> h}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           {hh : xx -->[ h ] yy}
           {αα : ff ==>[ α ] gg}
           {ββ : gg ==>[ β ] hh}
           (Hαα : is_cartesian_2cell D αα)
           (Hββ : is_cartesian_2cell D ββ)
  : is_cartesian_2cell D (αα •• ββ).
Proof.
  apply cartesian_to_cartesian_2cell.
  exact (@is_cartesian_comp_disp
           _ (disp_hom xx yy)
           f ff
           g gg
           h hh
           α β
           αα ββ
           (cartesian_2cell_to_cartesian _ Hαα)
           (cartesian_2cell_to_cartesian _ Hββ)).
Defined.

Definition invertible_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {Hα : is_invertible_2cell α}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           {αα : ff ==>[ α ] gg}
           (Hαα : is_disp_invertible_2cell Hα αα)
  : is_cartesian_2cell D αα.
Proof.
  apply cartesian_to_cartesian_2cell.
  apply (is_cartesian_disp_iso (disp_hom_disp_invertible_2cell_to_iso _ Hαα)).
Defined.
