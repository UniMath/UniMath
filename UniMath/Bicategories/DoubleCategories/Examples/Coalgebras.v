(*********************************************************************************************

 The double category of coalgebras for a lax double functor

 Let `F` be a lax double endofunctor on a double category `C`. We define the double category of
 coalgebras as follows:
 - Objects: objects `x` in `C` together with a vertical morphism `x -->v F x`
 - Vertical morphisms from `fx : x -->v F x` to `fy : y -->v F y`: vertical morphisms
   `v : x -->v y` making the usual diagram commute (`fx · #v F v = v · fy`)
 - Horizontal morphisms from `fx : x -->v F x` to `fy : y -->v F y`: horizontal morphisms
   `h : x -->h y` together with a square with horizontal sides `h` and `#h F h` and vertical
   sides `fx` and `fy`.
 Squares are defined to be squares in `C` satisfying an additional commutativity requirement.
 We define this double category in this file, and we prove that it is univalent.

 Note that this construction does not necessarily work for oplax double functors. For oplax
 double functors however, one can define the double category of algebras. This is similar to
 the situation for monoidal categories.

 This construction is based on the talk "On the double category of coalgebras" by Hofmann.
 The difference is that in that talk, it is assumed that squares in `C` are unique, which we
 do not assume in this file. In addition, different conventions on what are the horizontal
 and the vertical morphisms.

 References
 - "On the double category of coalgebras", Dirk Hofmann
   https://www.mat.uc.pt/~tacl2022/slides/slidesDHofmann.pdf

 Content
 1. Basic definitions
 2. The 2-sided displayed category
 3. Builders and accessors for horizontal morphisms
 4. Builders and accessors for squares
 5. Horizontal identities
 6. Horizontal composition
 7. Globular isomorphism squares
 8. The left unitor
 9. The right unitor
 10. The associator
 11. The coherences
 12. The double category of coalgebras of a lax double functor
 13. The univalence of the double category of coalgebra
 14. The univalent double category of coalgebras of a lax double functor
 15. Flatness of the double category of coalgebras

 *********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.TwoSidedDispCatOnDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Basic definitions *)
Definition double_coalg
           {C : univalent_double_cat}
           (F : lax_double_functor C C)
  : UU
  := coalgebra_ob F.

Coercion double_coalg_carrier
         {C : univalent_double_cat}
         {F : lax_double_functor C C}
         (X : double_coalg F)
  : C.
Proof.
  exact (coalg_carrier F X).
Defined.

Definition double_coalg_map
           {C : univalent_double_cat}
           {F : lax_double_functor C C}
           (X : double_coalg F)
  : X -->v F X
  := coalg_map F X.

Definition double_coalg_ver
           {C : univalent_double_cat}
           {F : lax_double_functor C C}
           (X Y : double_coalg F)
  : UU
  := X --> Y.

Coercion double_coalg_ver_to_mor
         {C : univalent_double_cat}
         {F : lax_double_functor C C}
         {X Y : double_coalg F}
         (v : double_coalg_ver X Y)
  : X -->v Y.
Proof.
  exact (pr1 v).
Defined.

Proposition double_coalg_ver_comm
            {C : univalent_double_cat}
            {F : lax_double_functor C C}
            {X Y : double_coalg F}
            (v : double_coalg_ver X Y)
  : double_coalg_map X ·v #v F v
    =
    v ·v double_coalg_map Y.
Proof.
  exact (pr2 v).
Defined.

Definition double_coalg_hor_struct
           {C : univalent_double_cat}
           {F : lax_double_functor C C}
           (X Y : double_coalg F)
           (f : X -->h Y)
  : UU
  := square (double_coalg_map X) (double_coalg_map Y) f (#h F f).

Definition is_double_coalg_sqr
           {C : univalent_double_cat}
           {F : lax_double_functor C C}
           {X₁ : double_coalg F}
           {Y₁ : double_coalg F}
           {f₁ : X₁ -->h Y₁}
           (s₁ : square
                   (double_coalg_map X₁)
                   (double_coalg_map Y₁)
                   f₁ (#h F f₁))
           {X₂ : double_coalg F}
           {Y₂ : double_coalg F}
           {f₂ : X₂ -->h Y₂}
           (s₂ : square
                   (double_coalg_map X₂)
                   (double_coalg_map Y₂)
                   f₂ (#h F f₂))
           (v : double_coalg_ver X₁ X₂)
           (w : double_coalg_ver Y₁ Y₂)
           (r : square v w f₁ f₂)
  : UU
  := transportf_square
       (double_coalg_ver_comm v)
       (double_coalg_ver_comm w)
       (s₁ ⋆v #s F r)
     =
     r ⋆v s₂.

Arguments double_coalg_hor_struct {C F} X Y f /.
Arguments is_double_coalg_sqr {C F X₁ Y₁ f₁} s₁ {X₂ Y₂ f₂} s₂ v w r /.

Section CoalegbraDoubleCat.
  Context {C : univalent_double_cat}
          (F : lax_double_functor C C).

  Let E : category := total_twosided_disp_category
                        (twosided_disp_cat_on_disp_cat
                           (coalgebra_disp_cat F)
                           (coalgebra_disp_cat F)
                           (hor_mor C)).

  (** * 2. The 2-sided displayed category *)
  Definition double_coalg_disp_cat_ob_mor_on_twosided_disp_cat
    : disp_cat_ob_mor E.
  Proof.
    simple refine (_ ,, _).
    - exact (λ XYf,
             double_coalg_hor_struct (pr1 XYf) (pr12 XYf) (pr22 XYf)).
    - exact (λ XYf₁ XYf₂ s₁ s₂ vwr,
             is_double_coalg_sqr s₁ s₂ _ _ (pr22 vwr)).
  Defined.

  Proposition double_coalg_disp_cat_id_comp_on_twosided_disp_cat
    : disp_cat_id_comp E double_coalg_disp_cat_ob_mor_on_twosided_disp_cat.
  Proof.
    split.
    - intros X s.
      cbn.
      etrans.
      {
        do 2 apply maponpaths.
        apply lax_double_functor_id_square.
      }
      unfold transportb_square.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      rewrite square_id_right_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      refine (_ @ !(square_id_left_v s)).
      unfold transportb_square.
      apply transportf_square_eq.
      apply idpath.
    - intros X Y Z f g h₁ h₂ h₃ s₁ s₂.
      cbn in s₁, s₂ ; cbn.
      refine (_ @ square_assoc_v' _ _ _).
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (!s₂).
      }
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply (square_assoc_v (C := C)).
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (!s₁).
      }
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        exact (!(square_assoc_v' _ _ _)).
      }
      rewrite transportf_f_square.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply lax_double_functor_comp_v_square.
      }
      unfold transportb_square.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      apply transportf_square_eq.
      apply idpath.
  Qed.

  Definition double_coalg_disp_cat_data_on_twosided_disp_cat
    : disp_cat_data E.
  Proof.
    simple refine (_ ,, _).
    - exact double_coalg_disp_cat_ob_mor_on_twosided_disp_cat.
    - exact double_coalg_disp_cat_id_comp_on_twosided_disp_cat.
  Defined.

  Proposition double_coalg_disp_cat_axioms_on_twosided_disp_cat
    : disp_cat_axioms E double_coalg_disp_cat_data_on_twosided_disp_cat.
  Proof.
    repeat split ; intros.
    - apply isaset_square.
    - apply isaset_square.
    - apply isaset_square.
    - apply isasetaprop.
      apply isaset_square.
  Qed.

  Definition double_coalg_disp_cat_on_twosided_disp_cat
    : disp_cat E.
  Proof.
    simple refine (_ ,, _).
    - exact double_coalg_disp_cat_data_on_twosided_disp_cat.
    - exact double_coalg_disp_cat_axioms_on_twosided_disp_cat.
  Defined.

  Definition double_coalg_twosided_disp_cat
    : twosided_disp_cat (CoAlg_category F) (CoAlg_category F)
    := sigma_twosided_disp_cat _ double_coalg_disp_cat_on_twosided_disp_cat.

  (** * 3. Builders and accessors for horizontal morphisms *)
  Definition double_coalg_hor
             (X Y : double_coalg F)
    : UU
    := double_coalg_twosided_disp_cat X Y.

  Definition make_double_coalg_hor
             {X Y : double_coalg F}
             (h : X -->h Y)
             (s : double_coalg_hor_struct X Y h)
    : double_coalg_hor X Y
    := h ,, s.

  Coercion mor_of_double_coalg_hor
           {X Y : double_coalg F}
           (h : double_coalg_hor X Y)
    : X -->h Y.
  Proof.
    exact (pr1 h).
  Defined.

  (** * 4. Builders and accessors for squares *)
  Definition sqr_of_double_coalg_hor
             {X Y : double_coalg F}
             (h : double_coalg_hor X Y)
    : square (double_coalg_map X) (double_coalg_map Y) h (#h F h)
    := pr2 h.

  Definition double_coalg_sqr
             {X₁ X₂ Y₁ Y₂ : double_coalg F}
             (v : double_coalg_ver X₁ X₂)
             (w : double_coalg_ver Y₁ Y₂)
             (h₁ : double_coalg_hor X₁ Y₁)
             (h₂ : double_coalg_hor X₂ Y₂)
    : UU
    := h₁ -->[ v ][ w ] h₂.

  Coercion sqr_of_double_coalg_sqr
           {X₁ X₂ Y₁ Y₂ : double_coalg F}
           {v : double_coalg_ver X₁ X₂}
           {w : double_coalg_ver Y₁ Y₂}
           {h₁ : double_coalg_hor X₁ Y₁}
           {h₂ : double_coalg_hor X₂ Y₂}
           (s : double_coalg_sqr v w h₁ h₂)
    : square v w h₁ h₂.
  Proof.
    exact (pr1 s).
  Defined.

  Proposition eq_of_double_coalg_sqr
              {X₁ X₂ Y₁ Y₂ : double_coalg F}
              {v : double_coalg_ver X₁ X₂}
              {w : double_coalg_ver Y₁ Y₂}
              {h₁ : double_coalg_hor X₁ Y₁}
              {h₂ : double_coalg_hor X₂ Y₂}
              (s : double_coalg_sqr v w h₁ h₂)
    : transportf_square
       (double_coalg_ver_comm v)
       (double_coalg_ver_comm w)
       (sqr_of_double_coalg_hor h₁ ⋆v #s F s)
     =
     s ⋆v sqr_of_double_coalg_hor h₂.
  Proof.
    exact (pr2 s).
  Defined.

  Proposition eq_of_double_coalg_sqr'
              {X₁ X₂ Y₁ Y₂ : double_coalg F}
              {v : double_coalg_ver X₁ X₂}
              {w : double_coalg_ver Y₁ Y₂}
              {h₁ : double_coalg_hor X₁ Y₁}
              {h₂ : double_coalg_hor X₂ Y₂}
              (s : double_coalg_sqr v w h₁ h₂)
    : sqr_of_double_coalg_hor h₁ ⋆v #s F s
      =
      transportb_square
        (double_coalg_ver_comm v)
        (double_coalg_ver_comm w)
        (s ⋆v sqr_of_double_coalg_hor h₂).
  Proof.
    rewrite <- eq_of_double_coalg_sqr.
    rewrite transportbf_square.
    apply idpath.
  Qed.

  Definition make_double_coalg_sqr
             {X₁ X₂ Y₁ Y₂ : double_coalg F}
             {v : double_coalg_ver X₁ X₂}
             {w : double_coalg_ver Y₁ Y₂}
             {h₁ : double_coalg_hor X₁ Y₁}
             {h₂ : double_coalg_hor X₂ Y₂}
             (s : square v w h₁ h₂)
             (p : is_double_coalg_sqr (pr2 h₁) (pr2 h₂) _ _ s)
    : double_coalg_sqr v w h₁ h₂
    := s ,, p.

  Proposition eq_double_coalg_sqr
              {X₁ X₂ Y₁ Y₂ : double_coalg F}
              {v : double_coalg_ver X₁ X₂}
              {w : double_coalg_ver Y₁ Y₂}
              {h₁ : double_coalg_hor X₁ Y₁}
              {h₂ : double_coalg_hor X₂ Y₂}
              {s₁ s₂ : double_coalg_sqr v w h₁ h₂}
              (p : sqr_of_double_coalg_sqr s₁
                   =
                   sqr_of_double_coalg_sqr s₂)
    : s₁ = s₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaset_square.
    }
    exact p.
  Qed.

  Proposition transportf_double_coalg_sqr
              {X₁ X₂ Y₁ Y₂ : double_coalg F}
              {v v' : double_coalg_ver X₁ X₂}
              (p : v = v')
              {w w' : double_coalg_ver Y₁ Y₂}
              (q : w = w')
              {h₁ : double_coalg_hor X₁ Y₁}
              {h₂ : double_coalg_hor X₂ Y₂}
              (s : double_coalg_sqr v w h₁ h₂)
    : pr1 (transportf_disp_mor2 p q s)
      =
      transportf_square
        (maponpaths double_coalg_ver_to_mor p)
        (maponpaths double_coalg_ver_to_mor q)
        s.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_double_coalg_sqr
              {X₁ X₂ Y₁ Y₂ : double_coalg F}
              {v v' : double_coalg_ver X₁ X₂}
              (p : v' = v)
              {w w' : double_coalg_ver Y₁ Y₂}
              (q : w' = w)
              {h₁ : double_coalg_hor X₁ Y₁}
              {h₂ : double_coalg_hor X₂ Y₂}
              (s : double_coalg_sqr v w h₁ h₂)
    : pr1 (transportb_disp_mor2 p q s)
      =
      transportb_square
        (maponpaths double_coalg_ver_to_mor p)
        (maponpaths double_coalg_ver_to_mor q)
        s.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  (** * 5. Horizontal identities *)
  Definition double_coalg_id_hor_struct
             (X : double_coalg F)
    : double_coalg_hor_struct X X (identity_h (coalg_carrier F X))
    := transportf_square
         (id_right _) (id_right _)
         (id_h_square _ ⋆v lax_double_functor_id_h F (pr1 X)).

  Arguments double_coalg_id_hor_struct X /.

  Definition double_coalg_id_hor
             (X : double_coalg F)
    : double_coalg_hor X X.
  Proof.
    use make_double_coalg_hor.
    - exact (identity_h _).
    - exact (double_coalg_id_hor_struct X).
  Defined.

  Proposition double_coalg_id_is_sqr
              {X Y : double_coalg F}
              (v : double_coalg_ver X Y)
    : is_double_coalg_sqr
        (double_coalg_id_hor_struct X)
        (double_coalg_id_hor_struct Y)
        _ _
        (id_h_square v).
  Proof.
    cbn.
    rewrite transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (square_assoc_v' (C := C)).
    }
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply (lax_double_functor_id_h_mor' F).
    }
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply (square_assoc_v (C := C)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    rewrite <- id_h_square_comp.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (id_h_square_eq (coalgebra_mor_commutes F v)).
    }
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (square_assoc_v (C := C)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    rewrite <- id_h_square_comp.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition double_coalg_id_sqr
             {X Y : double_coalg F}
             (v : double_coalg_ver X Y)
    : double_coalg_sqr v v (double_coalg_id_hor X) (double_coalg_id_hor Y).
  Proof.
    use make_double_coalg_sqr.
    - exact (id_h_square _).
    - exact (double_coalg_id_is_sqr v).
  Defined.

  Definition double_coalg_hor_id_data
    : hor_id_data double_coalg_twosided_disp_cat.
  Proof.
    use make_hor_id_data.
    - exact double_coalg_id_hor.
    - exact (λ _ _ v, double_coalg_id_sqr v).
  Defined.

  Proposition double_coalg_hor_id_laws
    : hor_id_laws double_coalg_hor_id_data.
  Proof.
    split.
    - intros.
      use eq_double_coalg_sqr ; cbn.
      apply (id_h_square_id (C := C)).
    - intros.
      use eq_double_coalg_sqr ; cbn.
      apply (id_h_square_comp (C := C)).
  Qed.

  Definition double_coalg_hor_id
    : hor_id double_coalg_twosided_disp_cat.
  Proof.
    use make_hor_id.
    - exact double_coalg_hor_id_data.
    - exact double_coalg_hor_id_laws.
  Defined.

  (** * 6. Horizontal composition *)
  Definition double_coalg_comp_hor_struct
             {X Y Z : double_coalg F}
             (h : double_coalg_hor X Y)
             (k : double_coalg_hor Y Z)
    : double_coalg_hor_struct X Z (h ·h k)
    := transportf_square
         (id_right _)
         (id_right _)
         (sqr_of_double_coalg_hor h ⋆h sqr_of_double_coalg_hor k
          ⋆v lax_double_functor_comp_h F _ _).

  Arguments double_coalg_comp_hor_struct {X Y Z} h k /.

  Definition double_coalg_comp_hor
             {X Y Z : double_coalg F}
             (h : double_coalg_hor X Y)
             (k : double_coalg_hor Y Z)
    : double_coalg_hor X Z.
  Proof.
    use make_double_coalg_hor.
    - exact (h ·h k).
    - exact (double_coalg_comp_hor_struct h k).
  Defined.

  Proposition double_coalg_comp_hor_is_sqr
              {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : double_coalg F}
              {v₁ : double_coalg_ver X₁ X₂}
              {v₂ : double_coalg_ver Y₁ Y₂}
              {v₃ : double_coalg_ver Z₁ Z₂}
              {h₁ : double_coalg_hor X₁ Y₁}
              {h₂ : double_coalg_hor Y₁ Z₁}
              {k₁ : double_coalg_hor X₂ Y₂}
              {k₂ : double_coalg_hor Y₂ Z₂}
              (s₁ : double_coalg_sqr v₁ v₂ h₁ k₁)
              (s₂ : double_coalg_sqr v₂ v₃ h₂ k₂)
    : is_double_coalg_sqr
        (double_coalg_comp_hor_struct h₁ h₂)
        (double_coalg_comp_hor_struct k₁ k₂)
        _ _
        (s₁ ⋆h s₂).
  Proof.
    cbn.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (square_assoc_v' (C := C)).
    }
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      exact (lax_double_functor_comp_h_mor' F s₁ s₂).
    }
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_assoc_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      rewrite <- comp_h_square_comp.
      etrans.
      {
        apply maponpaths_2.
        apply eq_of_double_coalg_sqr'.
      }
      apply maponpaths.
      apply eq_of_double_coalg_sqr'.
    }
    unfold transportb_square.
    rewrite transportf_hcomp_l.
    rewrite transportf_square_prewhisker.
    rewrite !transportf_f_square.
    rewrite pathsinv0r.
    rewrite transportf_hcomp_r.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (square_assoc_v (C := C)).
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    rewrite <- comp_h_square_comp.
    apply transportf_square_eq.
    apply idpath.
  Qed.

  Definition double_coalg_comp_hor_sqr
             {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : double_coalg F}
             {v₁ : double_coalg_ver X₁ X₂}
             {v₂ : double_coalg_ver Y₁ Y₂}
             {v₃ : double_coalg_ver Z₁ Z₂}
             {h₁ : double_coalg_hor X₁ Y₁}
             {h₂ : double_coalg_hor Y₁ Z₁}
             {k₁ : double_coalg_hor X₂ Y₂}
             {k₂ : double_coalg_hor Y₂ Z₂}
             (s₁ : double_coalg_sqr v₁ v₂ h₁ k₁)
             (s₂ : double_coalg_sqr v₂ v₃ h₂ k₂)
    : double_coalg_sqr
        v₁ v₃
        (double_coalg_comp_hor h₁ h₂)
        (double_coalg_comp_hor k₁ k₂).
  Proof.
    use make_double_coalg_sqr.
    - exact (s₁ ⋆h s₂).
    - apply double_coalg_comp_hor_is_sqr.
  Defined.

  Definition double_coalg_hor_comp_data
    : hor_comp_data double_coalg_twosided_disp_cat.
  Proof.
    use make_hor_comp_data.
    - exact (λ X Y Z h k, double_coalg_comp_hor h k).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂,
             double_coalg_comp_hor_sqr s₁ s₂).
  Defined.

  Proposition double_coalg_hor_comp_laws
    : hor_comp_laws double_coalg_hor_comp_data.
  Proof.
    split.
    - intros.
      use eq_double_coalg_sqr ; cbn.
      apply (comp_h_square_id (C := C)).
    - intros.
      use eq_double_coalg_sqr ; cbn.
      apply (comp_h_square_comp (C := C)).
  Qed.

  Definition double_coalg_hor_comp
    : hor_comp double_coalg_twosided_disp_cat.
  Proof.
    use make_hor_comp.
    - exact double_coalg_hor_comp_data.
    - exact double_coalg_hor_comp_laws.
  Defined.

  (** * 7. Globular isomorphism squares *)
  Section IsoSquare.
    Context {X Y : double_coalg F}
            {h₁ : double_coalg_hor X Y}
            {h₂ : double_coalg_hor X Y}
            (s : double_coalg_sqr (identity _) (identity _) h₁ h₂)
            (s' : square (identity _) (identity _) h₂ h₁)
            (p : s ⋆v s'
                 =
                 transportb_square (id_left _) (id_left _) (id_v_square _))
            (q : s' ⋆v s
                 =
                 transportb_square (id_left _) (id_left _) (id_v_square _)).

    Proposition is_double_coalg_sqr_inv_sqr
      : is_double_coalg_sqr
          (sqr_of_double_coalg_hor h₂)
          (sqr_of_double_coalg_hor h₁)
          (identity _) (identity _)
          s'.
    Proof.
      cbn.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply square_id_left_v'.
      }
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (_ @ !(maponpaths (transportf_square (id_left _) (id_left _)) q)).
        rewrite transportfb_square.
        apply idpath.
      }
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (square_assoc_v' (C := C)).
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      etrans.
      {
        do 2 apply maponpaths.
        apply (square_assoc_v (C := C)).
      }
      unfold transportb_square.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        exact (!(eq_of_double_coalg_sqr s)).
      }
      rewrite transportf_square_prewhisker.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply square_assoc_v'.
      }
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        do 3 apply maponpaths.
        apply lax_double_functor_comp_v_square'.
      }
      rewrite !transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        do 4 apply maponpaths.
        exact p.
      }
      rewrite lax_double_functor_transportb_square.
      unfold transportb_square.
      rewrite !transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        do 3 apply maponpaths.
        apply lax_double_functor_id_square.
      }
      unfold transportb_square.
      rewrite !transportf_square_postwhisker.
      rewrite transportf_f_square.
      rewrite square_id_right_v.
      unfold transportb_square.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      apply transportf_square_id.
    Qed.

    Definition double_coalg_inv_sqr
      : double_coalg_sqr (identity _) (identity _) h₂ h₁.
    Proof.
      use make_double_coalg_sqr.
      - exact s'.
      - exact is_double_coalg_sqr_inv_sqr.
    Defined.

    Proposition double_coalg_inv_sqr_left
      : s ;;2 double_coalg_inv_sqr
        =
        transportb_disp_mor2 (id_left _) (id_left _) (id_two_disp _).
    Proof.
      use eq_double_coalg_sqr.
      cbn.
      refine (!_).
      etrans.
      {
        exact (transportf_double_coalg_sqr (!id_left _) (!id_left _) (id_two_disp _)).
      }
      refine (_ @ !p).
      use transportf_square_eq.
      apply idpath.
    Qed.

    Proposition double_coalg_inv_sqr_right
      : double_coalg_inv_sqr ;;2 s
        =
        transportb_disp_mor2 (id_left _) (id_left _) (id_two_disp _).
    Proof.
      use eq_double_coalg_sqr.
      cbn.
      refine (!_).
      etrans.
      {
        exact (transportf_double_coalg_sqr (!id_left _) (!id_left _) (id_two_disp _)).
      }
      refine (_ @ !q).
      use transportf_square_eq.
      apply idpath.
    Qed.

    Definition is_iso_twosided_double_coalg_sqr
      : is_iso_twosided_disp (identity_is_z_iso _) (identity_is_z_iso _) s.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact double_coalg_inv_sqr.
      - exact double_coalg_inv_sqr_left.
      - exact double_coalg_inv_sqr_right.
    Defined.
  End IsoSquare.

  Import TransportSquare.

  (** * 8. The left unitor *)
  Proposition is_double_coalg_sqr_lunitor
              {X Y : double_coalg F}
              (h : double_coalg_hor X Y)
    : is_double_coalg_sqr
        (double_coalg_comp_hor_struct (double_coalg_id_hor X) h)
        (sqr_of_double_coalg_hor h)
        (identity X)
        (identity Y)
        (lunitor_h h).
  Proof.
    cbn.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    rewrite transportf_hcomp_l.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_f_square.
    refine (_ @ lunitor_square' _).
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      exact (lax_double_functor_lunitor_h F h).
    }
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      refine (!_).
      apply comp_h_square_comp.
    }
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_hcomp_r.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_f_square.
    use transportf_square_eq.
    do 2 apply maponpaths_2.
    rewrite transportf_hcomp_r.
    rewrite transportf_square_id.
    apply maponpaths_2.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition double_coalg_lunitor_sqr
             {X Y : double_coalg F}
             (h : double_coalg_hor X Y)
    : double_coalg_sqr
        (identity X)
        (identity Y)
        (double_coalg_comp_hor (double_coalg_id_hor X) h)
        h.
  Proof.
    use make_double_coalg_sqr.
    - exact (lunitor_h h).
    - exact (is_double_coalg_sqr_lunitor h).
  Defined.

  Definition double_coalg_lunitor_data
    : double_lunitor_data
        double_coalg_hor_id
        double_coalg_hor_comp.
  Proof.
    intros X Y h.
    simple refine (_ ,, _).
    - exact (double_coalg_lunitor_sqr h).
    - use is_iso_twosided_double_coalg_sqr.
      + exact (linvunitor_h _).
      + exact (lunitor_linvunitor_h _).
      + exact (linvunitor_lunitor_h _).
  Defined.

  Proposition double_coalg_lunitor_laws
    : double_lunitor_laws double_coalg_lunitor_data.
  Proof.
    intro ; intros.
    use eq_double_coalg_sqr.
    refine (_ @ !(lunitor_square _)).
    etrans.
    {
      exact (transportb_double_coalg_sqr
               (id_right _ @ !(id_left _))
               (id_right _ @ !(id_left _))
               (double_coalg_lunitor_sqr _ ;;2 _)).
    }
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition double_coalg_lunitor
    : double_cat_lunitor
        double_coalg_hor_id
        double_coalg_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact double_coalg_lunitor_data.
    - exact double_coalg_lunitor_laws.
  Defined.

  (** * 9. The right unitor *)
  Proposition is_double_coalg_sqr_runitor
              {X Y : double_coalg F}
              (h : double_coalg_hor X Y)
    : is_double_coalg_sqr
        (double_coalg_comp_hor_struct h (double_coalg_id_hor Y))
        (sqr_of_double_coalg_hor h)
        (identity X)
        (identity Y)
        (runitor_h h).
  Proof.
    cbn.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    rewrite transportf_hcomp_r.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_f_square.
    refine (_ @ runitor_square' _).
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      exact (lax_double_functor_runitor_h F h).
    }
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      refine (!_).
      apply comp_h_square_comp.
    }
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_hcomp_l.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_f_square.
    use transportf_square_eq.
    do 2 apply maponpaths_2.
    rewrite transportf_hcomp_r.
    rewrite transportf_square_id.
    apply maponpaths_2.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition double_coalg_runitor_sqr
             {X Y : double_coalg F}
             (h : double_coalg_hor X Y)
    : double_coalg_sqr
        (identity X)
        (identity Y)
        (double_coalg_comp_hor h (double_coalg_id_hor Y))
        h.
  Proof.
    use make_double_coalg_sqr.
    - exact (runitor_h h).
    - exact (is_double_coalg_sqr_runitor h).
  Defined.

  Definition double_coalg_runitor_data
    : double_runitor_data
        double_coalg_hor_id
        double_coalg_hor_comp.
  Proof.
    intros X Y h.
    simple refine (_ ,, _).
    - exact (double_coalg_runitor_sqr h).
    - use is_iso_twosided_double_coalg_sqr.
      + exact (rinvunitor_h _).
      + exact (runitor_rinvunitor_h _).
      + exact (rinvunitor_runitor_h _).
  Defined.

  Proposition double_coalg_runitor_laws
    : double_runitor_laws double_coalg_runitor_data.
  Proof.
    intro ; intros.
    use eq_double_coalg_sqr.
    refine (_ @ !(runitor_square _)).
    etrans.
    {
      exact (transportb_double_coalg_sqr
               (id_right _ @ !(id_left _))
               (id_right _ @ !(id_left _))
               (double_coalg_runitor_sqr _ ;;2 _)).
    }
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition double_coalg_runitor
    : double_cat_runitor
        double_coalg_hor_id
        double_coalg_hor_comp.
  Proof.
    use make_double_runitor.
    - exact double_coalg_runitor_data.
    - exact double_coalg_runitor_laws.
  Defined.

  (** * 10. The associator *)
  Proposition is_double_coalg_sqr_lassociator
              {W X Y Z : double_coalg F}
              (h₁ : double_coalg_hor W X)
              (h₂ : double_coalg_hor X Y)
              (h₃ : double_coalg_hor Y Z)
    : is_double_coalg_sqr
        (double_coalg_comp_hor_struct h₁ (double_coalg_comp_hor h₂ h₃))
        (double_coalg_comp_hor_struct (double_coalg_comp_hor h₁ h₂) h₃)
        (identity _)
        (identity _)
        (lassociator_h h₁ h₂ h₃).
  Proof.
    cbn.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite transportf_hcomp_r.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      use hcomp_vcomp_r_id_r.
    }
    rewrite !transportf_square_prewhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      do 3 apply maponpaths_2.
      rewrite transportf_hcomp_l.
      rewrite transportf_f_square.
      rewrite !transportf_square_id.
      apply idpath.
    }
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply square_assoc_v'.
    }
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply (lax_double_functor_lassociator_h' F).
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_assoc_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    rewrite square_assoc_v.
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply lassociator_square.
    }
    unfold transportb_square.
    rewrite !transportf_square_prewhisker.
    rewrite transportf_f_square.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths.
      apply maponpaths_2.
      use hcomp_vcomp_l_id_r.
    }
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_assoc_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition double_coalg_lassociator_sqr
             {W X Y Z : double_coalg F}
             (h₁ : double_coalg_hor W X)
             (h₂ : double_coalg_hor X Y)
             (h₃ : double_coalg_hor Y Z)
    : double_coalg_sqr
        (identity _)
        (identity _)
        (double_coalg_comp_hor h₁ (double_coalg_comp_hor h₂ h₃))
        (double_coalg_comp_hor (double_coalg_comp_hor h₁ h₂) h₃).
  Proof.
    use make_double_coalg_sqr.
    - exact (lassociator_h h₁ h₂ h₃).
    - apply is_double_coalg_sqr_lassociator.
  Defined.

  Definition double_coalg_associator_data
    : double_associator_data double_coalg_hor_comp.
  Proof.
    intros W X Y Z h₁ h₂ h₃.
    simple refine (_ ,, _).
    - exact (double_coalg_lassociator_sqr h₁ h₂ h₃).
    - use is_iso_twosided_double_coalg_sqr.
      + exact (rassociator_h _ _ _).
      + exact (lassociator_rassociator_h _ _ _).
      + exact (rassociator_lassociator_h _ _ _).
  Defined.

  Proposition double_coalg_associator_laws
    : double_associator_laws double_coalg_associator_data.
  Proof.
    intro ; intros.
    use eq_double_coalg_sqr.
    refine (_ @ !(lassociator_square _ _ _)).
    etrans.
    {
      exact (transportb_double_coalg_sqr
               (id_right _ @ !(id_left _))
               (id_right _ @ !(id_left _))
               (double_coalg_lassociator_sqr _ _ _
                ;;2
                double_coalg_comp_hor_sqr (double_coalg_comp_hor_sqr _ _) _)).
    }
    use transportf_square_eq.
    apply idpath.
  Qed.

  Definition double_coalg_associator
    : double_cat_associator double_coalg_hor_comp.
  Proof.
    use make_double_associator.
    - exact double_coalg_associator_data.
    - exact double_coalg_associator_laws.
  Defined.

  (** * 11. The coherences *)
  Proposition double_coalg_triangle_law
    : triangle_law
        double_coalg_lunitor
        double_coalg_runitor
        double_coalg_associator.
  Proof.
    intros X Y Z h k.
    use eq_double_coalg_sqr.
    refine (double_triangle _ _ @ _).
    refine (!_).
    etrans.
    {
      exact (transportb_double_coalg_sqr
               (id_left _) (id_left _)
               (double_coalg_comp_hor_sqr
                  (id_two_disp h)
                  (double_lunitor double_coalg_lunitor k))).
    }
    use transportf_square_eq.
    apply idpath.
  Qed.

  Proposition double_coalg_pentagon_law
    : pentagon_law double_coalg_associator.
  Proof.
    intros V W X Y Z h₁ h₂ h₃ h₄.
    use eq_double_coalg_sqr.
    refine (_ @ double_pentagon _ _ _ _).
    etrans.
    {
      exact (transportb_double_coalg_sqr
               (id_right _) (id_right _)
               (double_coalg_lassociator_sqr _ _ _
                ;;2
                double_coalg_lassociator_sqr _ _ _)).
    }
    use transportf_square_eq.
    apply idpath.
  Qed.

  (** * 12. The double category of coalgebras of a lax double functor *)
  Definition double_cat_of_double_coalg
    : double_cat.
  Proof.
    use make_double_cat.
    - exact (CoAlg_category F).
    - exact double_coalg_twosided_disp_cat.
    - exact double_coalg_hor_id.
    - exact double_coalg_hor_comp.
    - exact double_coalg_lunitor.
    - exact double_coalg_runitor.
    - exact double_coalg_associator.
    - exact double_coalg_triangle_law.
    - exact double_coalg_pentagon_law.
  Defined.

  (** * 13. The univalence of the double category of coalgebra *)
  Proposition double_coalg_hor_eq
              {X Y : double_coalg F}
              (h k : double_coalg_hor X Y)
    : h = k
      ≃
      ∑ (s : globular_iso_square h k),
      is_double_coalg_sqr
        (sqr_of_double_coalg_hor h) (sqr_of_double_coalg_hor k)
        (identity _) (identity _)
        s.
  Proof.
    simple refine (weqtotal2 _ _ ∘ total2_paths_equiv _ _ _)%weq.
    - exact (make_weq
               _
               (is_univalent_twosided_disp_cat_hor_mor
                  C
                  _ _ _ _
                  (idpath _) (idpath _)
                  h k)).
    - intro p.
      induction h as [ h Hh ].
      induction k as [ k Hk ].
      cbn ; cbn in p.
      induction p ; cbn.
      use weqimplimpl.
      + abstract
          (intro p ;
           induction p ; cbn ;
           etrans ;
           [ do 2 apply maponpaths ;
             apply lax_double_functor_id_square
           | ] ;
           unfold transportb_square ;
           rewrite transportf_square_postwhisker ;
           rewrite transportf_f_square ;
           rewrite square_id_right_v ;
           refine (_ @ !(square_id_left_v _)) ;
           unfold transportb_square ;
           rewrite transportf_f_square ;
           use transportf_square_eq ;
           apply idpath).
      + abstract
          (intro p ;
           pose proof (p @ square_id_left_v _) as p' ;
           clear p ;
           pose proof (maponpaths
                         (λ z, transportf_square _ _ (_ ⋆v z))
                         (!(lax_double_functor_id_square _ _))
                       @ p')
             as p'' ;
           clear p' ;
           unfold transportb_square in p'' ;
           rewrite transportf_square_postwhisker in p'' ;
           rewrite transportf_f_square in p'' ;
           rewrite square_id_right_v in p'' ;
           unfold transportb_square in p'' ;
           rewrite transportf_f_square in p'' ;
           refine (!_ @ maponpaths (transportf_square (id_left _) (id_left _)) p'' @ _) ;
           unfold transportb_square ;
           rewrite transportf_f_square ;
           apply transportf_square_id).
      + abstract
          (apply isaset_square).
      + abstract
          (apply isaset_square).
  Defined.

  Definition to_double_coalg_twosided_iso
             {X Y : double_coalg F}
             {h k : double_coalg_hor X Y}
             (s : globular_iso_square h k)
             (H : is_double_coalg_sqr
                    (sqr_of_double_coalg_hor h)
                    (sqr_of_double_coalg_hor k)
                    (identity X) (identity Y)
                    s)
    : iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) h k.
  Proof.
    refine ((pr1 s ,, H) ,, _).
    use is_iso_twosided_double_coalg_sqr.
    - exact (pr12 s).
    - exact (pr122 s).
    - exact (pr222 s).
  Defined.

  Definition from_double_coalg_twosided_iso
             {X Y : double_coalg F}
             {h k : double_coalg_hor X Y}
             (s : iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) h k)
    : ∑ (s : globular_iso_square h k),
      is_double_coalg_sqr
        (sqr_of_double_coalg_hor h) (sqr_of_double_coalg_hor k)
        (identity _) (identity _)
        s.
  Proof.
    simple refine ((_ ,, _ ,, _ ,, _) ,, _).
    - exact (pr11 s).
    - exact (pr1 (pr12 s)).
    - abstract
        (refine (maponpaths pr1 (pr122 s) @ _) ;
         refine (transportb_double_coalg_sqr (id_left _) (id_left _) _ @ _) ;
         use transportf_square_eq ;
         apply idpath).
    - abstract
        (refine (maponpaths pr1 (pr222 s) @ _) ;
         refine (transportb_double_coalg_sqr (id_left _) (id_left _) _ @ _) ;
         use transportf_square_eq ;
         apply idpath).
    - exact (pr21 s).
  Defined.

  Definition double_coalg_twosided_iso_weq
             {X Y : double_coalg F}
             (h k : double_coalg_hor X Y)
    : (∑ (s : globular_iso_square h k),
       is_double_coalg_sqr
         (sqr_of_double_coalg_hor h)
         (sqr_of_double_coalg_hor k)
         (identity X) (identity Y)
         s)
      ≃
      iso_twosided_disp (identity_z_iso X) (identity_z_iso Y) h k.
  Proof.
    use weq_iso.
    - exact (λ s, to_double_coalg_twosided_iso (pr1 s) (pr2 s)).
    - exact from_double_coalg_twosided_iso.
    - abstract
        (intro s ;
         use subtypePath ; [ intro ; apply isaset_square | ] ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
    - abstract
        (intro s ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         use eq_double_coalg_sqr ;
         apply idpath).
  Defined.

  Proposition is_univalent_double_coalg_twosided_disp_cat
    : is_univalent_twosided_disp_cat
        double_coalg_twosided_disp_cat.
  Proof.
    intros X X' Y Y' p q h k.
    induction p, q ; cbn.
    use weqhomot.
    - exact (double_coalg_twosided_iso_weq h k ∘ double_coalg_hor_eq h k)%weq.
    - intro p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_iso_twosided_disp.
      }
      use eq_double_coalg_sqr.
      apply idpath.
  Qed.

  (** * 14. The univalent double category of coalgebras of a lax double functor *)
  Definition univalent_double_cat_of_double_coalg
    : univalent_double_cat.
  Proof.
    use make_univalent_double_cat.
    - exact double_cat_of_double_coalg.
    - split.
      + apply is_univalent_coalg_category.
      + exact is_univalent_double_coalg_twosided_disp_cat.
  Defined.

  (** * 15. Flatness of the double category of coalgebras *)
  Proposition is_flat_double_cat_of_double_coalg
              (H : is_flat_double_cat C)
    : is_flat_double_cat
        double_cat_of_double_coalg.
  Proof.
    intro ; intros.
    use eq_double_coalg_sqr.
    apply H.
  Qed.
End CoalegbraDoubleCat.

Arguments double_coalg_id_hor_struct {C F} X /.
Arguments double_coalg_comp_hor_struct {C F X Y Z} h k /.
