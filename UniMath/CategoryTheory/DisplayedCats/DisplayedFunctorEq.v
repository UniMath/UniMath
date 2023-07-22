(*********************************************************************************

 Equality of displayed functors

 We are interested in the following bicategories:
 - The bicategory of displayed categories
 - The bicategory of fibrations over a fixed category
 - The bicategory of fibrations
 For each of these bicategories, we want to prove that it is univalent. That
 requires two things:
 - Proving that the identity of displayed functors is equivalent to the type of
   displayed natural isomorphisms between them
 - Proving that the identity of displayed categories is equivalent to the type of
   displayed adjoint equivalences between them.

 In this file, we look at the first of these two statements. The main idea of the
 proof is to characterize the identity relation for displayed functors step by
 step. For example, we start by proving [disp_functor_eq_step_1], which says that
 two displayed functors are equal if their data is equal. After that, we use the
 characterization of paths in sigma types to prove [disp_functor_eq_step_2]. In
 [disp_functor_eq_step_3], we further refine the obtained characterizations using
 function extensionality. In [disp_functor_eq_step_4], we use displayed univalence
 and in [disp_functor_eq_step_5] we recover displayed natural isomorphisms. By
 composing all these equivalences ([disp_functor_eq_weq]), we obtain the desired
 equivalence.

 In addition, there is one important trick in this proof: we characterize the
 identity relation for displayed functors lying over a fixed functor `F` instead of
 displayed functors `FF` and `GG` lying over `F` and `G` with a path `p : F = G`.
 This simplifies the construction, while no generality is lost.

 Contents
 1. Lemmas about equality of displayed functors
 2. Equality of displayed functors is the same as natural isomorphisms

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp.

Section DisplayedFunctorEq.
  Context {C₁ C₂ : category}
          {F : C₁ ⟶ C₂}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          (FF GG : disp_functor F D₁ D₂)
          (HD₂ : is_univalent_disp D₂).

  (**
   1. Lemmas about equality of displayed functors
   *)
  Definition disp_functor_eq_step_1
    : FF = GG ≃ pr1 FF = pr1 GG.
  Proof.
    use path_sigma_hprop.
    apply isaprop_disp_functor_axioms.
  Defined.

  Definition disp_functor_eq_step_2
    : pr1 FF = pr1 GG ≃ pr1 FF ╝ pr1 GG.
  Proof.
    exact (total2_paths_equiv _ (pr1 FF) (pr1 GG)).
  Defined.

  Definition disp_functor_eq_step_3
    : pr1 FF ╝ pr1 GG
      ≃
      ∑ (p : ∏ (x : C₁) (xx : D₁ x), FF x xx = GG x xx),
      ∏ (x y : C₁)
        (xx : D₁ x)
        (yy : D₁ y)
        (f : x --> y)
        (ff : xx -->[ f ] yy),
      ♯FF ff ;; idtoiso_disp (idpath _) (p y yy)
      =
      transportb
        _
        (id_right _ @ !(id_left _))
        (idtoiso_disp (idpath _) (p x xx) ;; ♯GG ff).
  Proof.
    use weqbandf.
    - exact (weqonsecfibers _ _ (λ x, weqtoforallpaths _ _ _)
             ∘ weqtoforallpaths _ _ _)%weq.
    - intro p.
      induction FF as [ [ FFo FFm ] FFp ].
      induction GG as [ [ GGo GGm ] GGp ].
      cbn in p.
      induction p ; cbn.
      refine (weqonsecfibers _ _ (λ x, _) ∘ weqtoforallpaths _ _ _)%weq.
      refine (weqonsecfibers _ _ (λ y, _) ∘ weqtoforallpaths _ _ _)%weq.
      refine (weqonsecfibers _ _ (λ xx, _) ∘ weqtoforallpaths _ _ _)%weq.
      refine (weqonsecfibers _ _ (λ yy, _) ∘ weqtoforallpaths _ _ _)%weq.
      refine (weqonsecfibers _ _ (λ f, _) ∘ weqtoforallpaths _ _ _)%weq.
      refine (weqonsecfibers _ _ (λ ff, _) ∘ weqtoforallpaths _ _ _)%weq.
      use weqimplimpl.
      + intro pp.
        rewrite id_right_disp.
        rewrite id_left_disp.
        rewrite pp.
        unfold transportb.
        rewrite transport_f_f.
        apply maponpaths_2.
        apply homset_property.
      + intro pp.
        rewrite id_right_disp, id_left_disp in pp.
        unfold transportb in pp.
        rewrite transport_f_f in pp.
        refine (!_ @ maponpaths (λ z, transportf _ (id_right _) z) pp @ _).
        * rewrite transport_f_f.
          apply transportf_set.
          apply homset_property.
        * rewrite transport_f_f.
          apply transportf_set.
          apply homset_property.
      + apply D₂.
      + apply D₂.
  Defined.

  Definition disp_functor_eq_step_4
    : (∑ (p : ∏ (x : C₁) (xx : D₁ x), FF x xx = GG x xx),
       ∏ (x y : C₁)
         (xx : D₁ x)
         (yy : D₁ y)
         (f : x --> y)
         (ff : xx -->[ f ] yy),
       ♯FF ff ;; idtoiso_disp (idpath _) (p y yy)
       =
       transportb
         _
         (id_right _ @ !(id_left _))
         (idtoiso_disp (idpath _) (p x xx) ;; ♯GG ff))
      ≃
      (∑ (p : ∏ (x : C₁) (xx : D₁ x), z_iso_disp (identity_z_iso _) (FF x xx) (GG x xx)),
       ∏ (x y : C₁)
         (xx : D₁ x)
         (yy : D₁ y)
         (f : x --> y)
         (ff : xx -->[ f ] yy),
       ♯FF ff ;; p y yy
       =
       transportb
         _
         (id_right _ @ !(id_left _))
         (p x xx ;; ♯GG ff)).
  Proof.
    use weqbandf.
    - exact (weqonsecfibers
               _ _
               (λ x,
                weqonsecfibers
                  _ _
                  (λ y, make_weq _ (HD₂ _ _ (idpath _) _ _)))).
    - intro p.
      use weqimplimpl.
      + intros pp x y xx yy f ff.
        cbn -[idtoiso_disp].
        exact (pp x y xx yy f ff).
      + intros pp x y xx yy f ff.
        cbn -[idtoiso_disp].
        exact (pp x y xx yy f ff).
      + repeat (use impred ; intro).
        apply D₂.
      + repeat (use impred ; intro).
        apply D₂.
  Defined.

  Definition disp_functor_eq_step_5_left
    : (∑ (p : ∏ (x : C₁) (xx : D₁ x), z_iso_disp (identity_z_iso _) (FF x xx) (GG x xx)),
       ∏ (x y : C₁)
         (xx : D₁ x)
         (yy : D₁ y)
         (f : x --> y)
         (ff : xx -->[ f ] yy),
       ♯FF ff ;; p y yy
       =
       transportb
         _
         (id_right _ @ !(id_left _))
         (p x xx ;; ♯GG ff))
      →
      disp_nat_z_iso FF GG (nat_z_iso_id F).
  Proof.
    simple refine (λ p, (_ ,, _) ,, _).
    - exact (λ x xx, pr1 (pr1 p x xx)).
    - abstract
        (intros x y f xx yy ff ;
         refine (pr2 p x y xx yy f ff @ _) ;
         apply maponpaths_2 ;
         apply homset_property).
    - intros x xx.
      exact (pr2 (pr1 p x xx)).
  Defined.

  Definition disp_functor_eq_step_5_right
    : disp_nat_z_iso FF GG (nat_z_iso_id F)
      →
      ∑ (p : ∏ (x : C₁) (xx : D₁ x), z_iso_disp (identity_z_iso _) (FF x xx) (GG x xx)),
      ∏ (x y : C₁)
        (xx : D₁ x)
        (yy : D₁ y)
        (f : x --> y)
        (ff : xx -->[ f ] yy),
      ♯FF ff ;; p y yy
      =
      transportb
        _
        (id_right _ @ !(id_left _))
        (p x xx ;; ♯GG ff).
  Proof.
    simple refine (λ p, (λ x xx, _ ,, _) ,, _).
    - exact (p x xx).
    - exact (pr2 p x xx).
    - abstract
        (intros x y f xx yy ff ;
         refine (disp_nat_trans_ax p ff @ _) ;
         apply maponpaths_2 ;
         apply homset_property).
  Defined.

  Definition disp_functor_eq_step_5
    : (∑ (p : ∏ (x : C₁) (xx : D₁ x), z_iso_disp (identity_z_iso _) (FF x xx) (GG x xx)),
       ∏ (x y : C₁)
         (xx : D₁ x)
         (yy : D₁ y)
         (f : x --> y)
         (ff : xx -->[ f ] yy),
       ♯FF ff ;; p y yy
       =
       transportb
         _
         (id_right _ @ !(id_left _))
         (p x xx ;; ♯GG ff))
      ≃
      disp_nat_z_iso FF GG (nat_z_iso_id F).
  Proof.
    use weq_iso.
    - exact disp_functor_eq_step_5_left.
    - exact disp_functor_eq_step_5_right.
    - intro p.
      use subtypePath.
      {
        intro.
        repeat (use impred ; intro).
        apply D₂.
      }
      use funextsec ; intro x.
      use funextsec ; intro xx.
      use subtypePath.
      {
        intro.
        apply isaprop_is_z_iso_disp.
      }
      apply idpath.
    - intro p.
      use subtypePath.
      {
        intro.
        repeat (use impred ; intro).
        apply isaprop_is_z_iso_disp.
      }
      use disp_nat_trans_eq.
      intros x xx.
      apply idpath.
  Defined.

  (**
   2. Equality of displayed functors is the same as natural isomorphisms
   *)
  Definition disp_functor_eq_weq
    : FF = GG ≃ disp_nat_z_iso FF GG (nat_z_iso_id F)
    := (disp_functor_eq_step_5
        ∘ disp_functor_eq_step_4
        ∘ disp_functor_eq_step_3
        ∘ disp_functor_eq_step_2
        ∘ disp_functor_eq_step_1)%weq.
End DisplayedFunctorEq.
