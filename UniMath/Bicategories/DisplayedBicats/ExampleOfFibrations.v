Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.FibrationOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Domain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

(**
The trivial bicategory is a fibration
 *)
Section ConstantFibration.
  Variable (B₁ B₂ : bicat).

  Definition trivial_invertible_is_cartesian_2cell
             {x₁ x₂ : B₁}
             {y₁ : trivial_displayed_bicat B₁ B₂ x₁}
             {y₂ : trivial_displayed_bicat B₁ B₂ x₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ : y₁ -->[ f₁ ] y₂}
             {g₂ : y₁ -->[ f₂ ] y₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==>[ α ] g₂)
             (Hβ : is_invertible_2cell β)
    : is_cartesian_2cell (trivial_displayed_bicat B₁ B₂) β.
  Proof.
    intros h h' γ ββ ; cbn in *.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         use (vcomp_rcancel _ Hβ) ;
         exact (pr2 τ₁ @ !(pr2 τ₂))).
    - refine (ββ • Hβ^-1 ,, _).
      abstract
        (rewrite !vassocl ;
         rewrite vcomp_linv ;
         apply id2_right).
  Defined.

  Definition trivial_cartesian_2cell_is_invertible
             {x₁ x₂ : B₁}
             {y₁ : trivial_displayed_bicat B₁ B₂ x₁}
             {y₂ : trivial_displayed_bicat B₁ B₂ x₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ : y₁ -->[ f₁ ] y₂}
             {g₂ : y₁ -->[ f₂ ] y₂}
             (α : f₁ ==> f₂)
             (β : g₁ ==>[ α ] g₂)
             (Hβ : is_cartesian_2cell (trivial_displayed_bicat B₁ B₂) β)
    : is_invertible_2cell β.
  Proof.
    cbn in *.
    unfold is_cartesian_2cell in Hβ.
    pose (Hβ f₁ g₂ (id2 _) (id2 _)) as lift.
    pose (inv := iscontrpr1 lift).
    cbn in lift, inv.
    use make_is_invertible_2cell.
    - exact (pr1 inv).
    - abstract
        (pose (Hβ f₁ g₁ (id2 _) β) as m ;
         cbn in m ;
         pose (proofirrelevance _ (isapropifcontr m)) as i ;
         simple refine (maponpaths pr1 (i (β • pr1 inv ,, _) (id₂ g₁ ,, _))) ; cbn ;
         [ cbn ;
           rewrite vassocl ;
           rewrite (pr2 inv) ;
           apply id2_right
         | apply id2_left ]).
    - abstract
        (exact (pr2 inv)).
  Defined.

  Definition trivial_local_cleaving
    : local_cleaving (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros x₁ x₂ y₁ y₂ f₁ f₂ f α.
    simple refine (f ,, id2 _ ,, _) ; cbn.
    apply trivial_invertible_is_cartesian_2cell.
    is_iso.
  Defined.

  Definition trivial_global_cleaving
    : global_cleaving (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros x₁ x₂ y₁ y₂ ; cbn in *.
    simple refine (y₁ ,, id₁ _ ,, _) ; cbn.
    apply TODO.
  Defined.

  Definition trivial_lwhisker_cartesian
    : lwhisker_cartesian (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hαα.
    apply trivial_invertible_is_cartesian_2cell.
    cbn.
    is_iso.
    apply trivial_cartesian_2cell_is_invertible.
    apply Hαα.
  Qed.

  Definition trivial_rwhisker_cartesian
    : rwhisker_cartesian (trivial_displayed_bicat B₁ B₂).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hαα.
    apply trivial_invertible_is_cartesian_2cell.
    cbn.
    is_iso.
    apply trivial_cartesian_2cell_is_invertible.
    apply Hαα.
  Qed.

  Definition trivial_fibration_of_bicats
    : fibration_of_bicats (trivial_displayed_bicat B₁ B₂).
  Proof.
    repeat split.
    - exact trivial_local_cleaving.
    - exact trivial_global_cleaving.
    - exact trivial_lwhisker_cartesian.
    - exact trivial_rwhisker_cartesian.
  Defined.
End ConstantFibration.

(**
The domain displayed bicategory is a fibration
 *)
Section DomainFibration.
  Context {B : bicat}
          (a : B).

  Definition dom_is_cartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : dom_disp_bicat B a c₁}
             {t₂ : dom_disp_bicat B a c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
    : is_cartesian_2cell (dom_disp_bicat B a) αα.
  Proof.
    intros s₃ ss₃ γ γα.
    use iscontraprop1.
    - use isaproptotal2.
      + intro ; apply (dom_disp_bicat B a).
      + intros.
        apply cellset_property.
    - simple refine (_ ,, _).
      + cbn in *.
        rewrite γα, αα.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite rwhisker_vcomp.
        apply idpath.
      + apply cellset_property.
  Qed.

  Definition dom_local_cleaving
    : local_cleaving (dom_disp_bicat B a).
  Proof.
    intros c₁ c₂ t₁ t₂ s₁ s₂ α β ; cbn in *.
    simple refine (_ ,, _) ; cbn.
    - exact ((β ▹ t₂) • α).
    - simple refine (idpath _ ,, _).
      apply dom_is_cartesian_2cell.
  Defined.

  Definition dom_fibration_of_bicats
    : fibration_of_bicats (dom_disp_bicat B a).
  Proof.
    repeat split.
    - exact dom_local_cleaving.
    - apply TODO.
    - intro ; intros.
      apply dom_is_cartesian_2cell.
    - intro ; intros.
      apply dom_is_cartesian_2cell.
  Defined.
End DomainFibration.

(**
The codomain displayed bicategory is a fibration
Here we assume that every 2-cell is invertible
 *)
Section CodomainFibration.
  Context (B : bicat).

  Definition cod_invertible_is_cartesian_2cell
             {c₁ c₂ : B}
             {s₁ s₂ : c₁ --> c₂}
             {α : s₁ ==> s₂}
             {t₁ : cod_disp_bicat B c₁}
             {t₂ : cod_disp_bicat B c₂}
             {ss₁ : t₁ -->[ s₁ ] t₂}
             {ss₂ : t₁ -->[ s₂ ] t₂}
             (αα : ss₁ ==>[ α ] ss₂)
             (Hαα : is_invertible_2cell (pr1 αα))
    : is_cartesian_2cell (cod_disp_bicat B) αα.
  Proof.
    intros h hh γ γα.
    cbn in *.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply (cod_disp_bicat B) | ] ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         pose (maponpaths pr1 (pr2 φ₁)) as p₁ ;
         cbn in p₁ ;
         pose (maponpaths pr1 (pr2 φ₂)) as p₂ ;
         cbn in p₂ ;
         pose (r := p₁ @ !p₂) ;
         use (vcomp_rcancel _ Hαα) ;
         exact r).
    - simple refine ((_ ,, _) ,, _).
      + exact (pr1 γα • Hαα^-1).
      + abstract
          (cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocr ;
           rewrite (pr2 γα) ;
           rewrite <- lwhisker_vcomp ;
           rewrite !vassocl ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite <- (pr2 αα) ;
           rewrite !vassocl ;
           rewrite rwhisker_vcomp ;
           rewrite vcomp_rinv ;
           rewrite id2_rwhisker ;
           apply id2_right).
      + abstract
          (use subtypePath ; [ intro ; apply cellset_property | ] ;
           cbn ;
           rewrite !vassocl ;
           rewrite vcomp_linv ;
           apply id2_right).
  Defined.

  Definition cod_local_cleaving
    : local_cleaving (cod_disp_bicat B).
  Proof.
    intros x y hx hy f g hf hg.
    simple refine (_ ,, _).
    - exact (pr1 hf ,, pr2 hx ◃ hg • pr2 hf).
    - simple refine (_ ,, _).
      + simple refine (id2 _ ,, _).
        abstract
          (cbn ;
           rewrite id2_rwhisker ;
           rewrite id2_right ;
           apply idpath).
      + simpl.
        apply cod_invertible_is_cartesian_2cell ; cbn.
        is_iso.
  Defined.

  Context (inv_B : ∏ (x y : B) (f g : x --> y) (α : f ==> g), is_invertible_2cell α).

  Definition cod_fibration_of_bicats
    : fibration_of_bicats (cod_disp_bicat B).
  Proof.
    repeat split.
    - exact cod_local_cleaving.
    - apply TODO.
    - intro ; intros.
      apply cod_invertible_is_cartesian_2cell.
      apply inv_B.
    - intro ; intros.
      apply cod_invertible_is_cartesian_2cell.
      apply inv_B.
  Defined.
End CodomainFibration.

(**
Fibration of fibrations over categories
 *)
Definition fib_of_fibs_is_cartesian_2cell
           {C₁ C₂ : bicat_of_cats}
           {F₁ F₂ : C₁ --> C₂}
           {α : F₁ ==> F₂}
           {D₁ : DispBicatOfFibs C₁}
           {D₂ : DispBicatOfFibs C₂}
           {FF₁ : D₁ -->[ F₁ ] D₂}
           {FF₂ : D₁ -->[ F₂ ] D₂}
           (αα : FF₁ ==>[ α ] FF₂)
           (Hαα : ∏ (x : (C₁ : univalent_category))
                    (xx : (pr1 D₁ : disp_cat _) x),
                  is_cartesian (pr11 αα x xx))
  : is_cartesian_2cell DispBicatOfFibs αα.
Proof.
  intros G GG β βα.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply DispBicatOfFibs | ] ;
       use subtypePath ; [ intro ; apply isapropunit | ] ;
       use disp_nat_trans_eq ;
       intros x xx ;
       assert (p₁ := maponpaths (λ z, (pr11 z) x xx) (pr2 φ₁)) ;
       assert (p₂ := maponpaths (λ z, (pr11 z) x xx) (pr2 φ₂)) ;
       cbn in p₁, p₂ ;
       pose (r := p₁ @ !p₂) ;
       use (cartesian_factorisation_unique (Hαα x xx)) ;
       exact r).
  - simple refine ((_ ,, tt) ,, _).
    + cbn in *.

      (* FACTOR THIS PART OUT, cartesian factorisation of disp_nat_trans *)
      simple refine (_ ,, _).
      * exact (λ x xx, cartesian_factorisation (Hαα x xx) (β x) (pr1 βα x xx)).
      * abstract
          (intros x y f xx yy ff ; cbn in * ;
        use (cartesian_factorisation_unique (Hαα y yy)) ;
        rewrite assoc_disp_var ;
        rewrite cartesian_factorisation_commutes ;
        refine (maponpaths _ (disp_nat_trans_ax (pr1 βα) ff) @ _) ;
        unfold transportb ;
        rewrite !transport_f_f ;
        rewrite mor_disp_transportf_postwhisker ;
        rewrite assoc_disp_var ;
        rewrite transport_f_f ;
        refine (!_) ;
        etrans ;
          [ do 2 apply maponpaths ;
            exact (disp_nat_trans_ax (pr1 αα) ff)
          | ] ;
        unfold transportb ;
        rewrite mor_disp_transportf_prewhisker ;
        rewrite transport_f_f ;
        rewrite assoc_disp ;
        unfold transportb ;
        rewrite transport_f_f ;
        rewrite cartesian_factorisation_commutes ;
        apply maponpaths_2 ;
        apply homset_property).
    + abstract
        (use subtypePath ; [ intro ; apply isapropunit | ] ;
         use subtypePath ; [ intro ; apply isaprop_disp_nat_trans_axioms| ] ;
         use funextsec ; intro x ;
         use funextsec ; intro xx ;
         apply cartesian_factorisation_commutes).
Defined.


(** MOVE *)
Definition is_cartesian_transportf
           {C : category}
           {D : disp_cat C}
           {x y : C}
           {f f' : x --> y}
           (p : f = f')
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           (Hff : is_cartesian ff)
  : is_cartesian (transportf (λ z, _ -->[ z ] _) p ff).
Proof.
  induction p.
  exact Hff.
Qed.
(* END MOVE *)


(**
BETTER NAME?? MOVE IT

If    `ff ;; gg = hh`
      `gg` and `hh` are cartesian
Then  `ff` is cartesian
 *)
Definition is_cartesian_precomp
           {C : category}
           {D : disp_cat C}
           {x y z : C}
           {f : x --> y}
           {g : y --> z}
           {h : x --> z}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {ff : xx -->[ f ] yy}
           {gg : yy -->[ g ] zz}
           {hh : xx -->[ h ] zz}
           (p : h = f · g)
           (pp : (ff ;; gg = transportf (λ z, _ -->[ z ] _) p hh)%mor_disp)
           (Hgg : is_cartesian gg)
           (Hhh : is_cartesian hh)
  : is_cartesian ff.
Proof.
  intros w φ ww φφ.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros ψ₁ ψ₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       use (cartesian_factorisation_unique Hhh) ;
       rewrite <- (transportb_transpose_left pp) ;
       unfold transportb ;
       rewrite !mor_disp_transportf_prewhisker ;
       rewrite !assoc_disp ;
       rewrite (pr2 ψ₁), (pr2 ψ₂) ;
       apply idpath).
  - simple refine (_ ,, _).
    + refine (cartesian_factorisation
                Hhh
                φ
                (transportf (λ z, _ -->[ z ] _) _ (φφ ;; gg)%mor_disp)).
      abstract
        (rewrite p ;
         rewrite assoc ;
         apply idpath).
    + abstract
        (simpl ;
         use (cartesian_factorisation_unique Hgg) ;
         rewrite assoc_disp_var ;
         rewrite pp ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         rewrite cartesian_factorisation_commutes ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
Qed.

Section CartesianFactorisationDispFunctor.
  Context {C₁ C₂ : category}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          (HD₁ : cleaving D₂)
          {F G : C₁ ⟶ C₂}
          (GG : disp_functor G D₁ D₂)
          (α : F ⟹ G).

  Definition cartesian_factorisation_disp_functor_data
    : disp_functor_data F D₁ D₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, pr1 (HD₁ (G x) (F x) (α x) (GG x xx))).
    - exact (λ x y xx yy f ff,
             cartesian_factorisation
               (pr22 (HD₁ (G y) (F y) (α y) (GG y yy)))
               _
               (transportb
                  (λ z, _ -->[ z ] _)
                  (nat_trans_ax α _ _ f)
                  (pr12 (HD₁ (G x) (F x) (α x) (GG x xx)) ;; #GG ff)%mor_disp)).
  Defined.

  Definition cartesian_factorisation_disp_functor_axioms
    : disp_functor_axioms cartesian_factorisation_disp_functor_data.
  Proof.
    repeat split.
    - intros x xx ; cbn.
      use (cartesian_factorisation_unique
             (pr22 (HD₁ (G x) (F x) (α x) (GG x xx)))).
      rewrite cartesian_factorisation_commutes.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite mor_disp_transportf_postwhisker.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros x y z xx yy zz f g ff hh ; cbn.
      use (cartesian_factorisation_unique
             (pr22 (HD₁ (G z) (F z) (α z) (GG z zz)))).
      unfold transportb.
      rewrite cartesian_factorisation_commutes.
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite !assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition cartesian_factorisation_disp_functor
    : disp_functor F D₁ D₂.
  Proof.
    simple refine (_ ,, _).
    - exact cartesian_factorisation_disp_functor_data.
    - exact cartesian_factorisation_disp_functor_axioms.
  Defined.

  Definition cartesian_factorisation_disp_functor_is_cartesian
             (HGG : is_cartesian_disp_functor GG)
    : is_cartesian_disp_functor cartesian_factorisation_disp_functor.
  Proof.
    intros x y f xx yy ff Hff ; cbn.
    pose (HGff := HGG _ _ _ _ _ _ Hff).
    refine (is_cartesian_precomp
              (idpath _)
              _
              (pr22 (HD₁ (G x) (F x) (α x) (GG x xx)))
              (is_cartesian_transportf
                 (!(nat_trans_ax α _ _ f))
                 (is_cartesian_comp_disp
                    (pr22 (HD₁ (G y) (F y) (α y) (GG y yy)))
                    HGff))).
    rewrite cartesian_factorisation_commutes.
    apply idpath.
  Qed.

  Definition cartesian_factorisation_disp_functor_cell_data
    : disp_nat_trans_data α cartesian_factorisation_disp_functor_data GG
    := λ x xx, pr12 (HD₁ (G x) (F x) (α x) (GG x xx)).

  Definition cartesian_factorisation_disp_functor_cell_axioms
    : disp_nat_trans_axioms cartesian_factorisation_disp_functor_cell_data.
  Proof.
    intros x y f xx yy ff ; cbn ; unfold cartesian_factorisation_disp_functor_cell_data.
    unfold transportb.
    rewrite cartesian_factorisation_commutes.
    apply idpath.
  Qed.

  Definition cartesian_factorisation_disp_functor_cell
    : disp_nat_trans
        α
        cartesian_factorisation_disp_functor_data
        GG.
  Proof.
    simple refine (_ ,, _).
    - exact cartesian_factorisation_disp_functor_cell_data.
    - exact cartesian_factorisation_disp_functor_cell_axioms.
  Defined.

  Definition cartesian_factorisation_disp_functor_cell_is_cartesian
             {x : C₁}
             (xx : D₁ x)
    : is_cartesian (cartesian_factorisation_disp_functor_cell x xx).
  Proof.
    exact (pr22 (HD₁ (G x) (F x) (α x) (GG x xx))).
  Defined.
End CartesianFactorisationDispFunctor.

Definition fib_of_fibs_local_cleaving
  : local_cleaving DispBicatOfFibs.
Proof.
  intros C₁ C₂ D₁ D₂ F G GG α.
  cbn in *.
  simple refine (_ ,, _).
  - simple refine (_ ,, _).
    + exact (cartesian_factorisation_disp_functor (pr22 D₂) (pr1 GG) α).
    + apply cartesian_factorisation_disp_functor_is_cartesian.
      exact (pr2 GG).
  - simpl.
    simple refine ((_ ,, tt) ,, _).
    + exact (cartesian_factorisation_disp_functor_cell (pr22 D₂) (pr1 GG) α).
    + apply fib_of_fibs_is_cartesian_2cell.
      apply cartesian_factorisation_disp_functor_cell_is_cartesian.
Defined.

Definition fib_of_fibs
  : fibration_of_bicats DispBicatOfFibs.
Proof.
  repeat split.
  - exact fib_of_fibs_local_cleaving.
  - apply TODO.
  - apply TODO.
  - apply TODO.
Defined.
