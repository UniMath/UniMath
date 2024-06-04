Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Section NiceBuilders.

  Context {B₁ B₂ : bicat}
          {D₁ : disp_bicat B₁}
          {D₂ : disp_bicat B₂}
          (HD₁ : disp_2cells_isaprop D₂)
          (HD₂ : disp_locally_groupoid D₂).

  Definition make_disp_psfunctor
             {F : psfunctor B₁ B₂}
             (obFF : ∏ x:B₁, D₁ x → D₂ (F x))
             (morFF : ∏ (x y : B₁) (f : B₁⟦x,y⟧) (xx : D₁ x) (yy : D₁ y),
                      (xx -->[f] yy) →
                      (obFF x xx -->[#F f] obFF y yy))
             (cellFF : ∏ (x y : B₁) (f g : B₁⟦x,y⟧) (α : f ==> g) (xx : D₁ x) (yy : D₁ y)
                         (ff : xx -->[f] yy) (gg : xx -->[g] yy),
                       (ff ==>[α] gg) → (morFF x y f xx yy ff ==>[##F α] morFF x y g xx yy gg))
             (disp_psfunctor_id : ∏ (x : B₁) (xx : D₁ x),
                                  id_disp (obFF x xx) ==>[ psfunctor_id F x ] morFF x x (id₁ x) xx xx (id_disp xx))
             (disp_psfunctor_comp : ∏ (x y z : B₁) (f : x --> y) (g : y --> z)
                                      (xx : D₁ x) (yy : D₁ y) (zz : D₁ z)
                                      (ff : xx -->[f] yy) (gg : yy -->[g] zz),
                                    (comp_disp (morFF x y f xx yy ff) (morFF y z g yy zz gg))
                                      ==>[ psfunctor_comp F f g ]
                                      morFF x z (f · g) xx zz (comp_disp ff gg))
    : disp_psfunctor D₁ D₂ F.
  Proof.
    use tpair.
    - use make_disp_psfunctor_data.
      + exact obFF.
      + exact morFF.
      + exact cellFF.
      + intros.
        use tpair.
        * apply disp_psfunctor_id.
        * apply HD₂.
      + intros.
        use tpair.
        * apply disp_psfunctor_comp.
        * apply HD₂.
    - abstract (repeat split; intro; intros; apply HD₁).
  Defined.

  Definition make_disp_pstrans
             {F₁ F₂ : psfunctor B₁ B₂}
             {FF₁ : disp_psfunctor D₁ D₂ F₁}
             {FF₂ : disp_psfunctor D₁ D₂ F₂}
             {α : pstrans F₁ F₂}
             (αα₁ : ∏ (x : B₁) (xx : D₁ x), FF₁ x xx -->[ α x] FF₂ x xx)
             (αα₂ : ∏ (x y : B₁) (f : B₁ ⟦ x, y ⟧) (xx : D₁ x) (yy : D₁ y) (ff : xx -->[ f] yy),
                    (αα₁ x xx;; disp_psfunctor_mor D₁ D₂ F₂ FF₂ ff)
                      ==>[ psnaturality_of α f ]
                      disp_psfunctor_mor D₁ D₂ F₁ FF₁ ff;; αα₁ y yy)
    : disp_pstrans FF₁ FF₂ α.
  Proof.
    use tpair.
    - use make_disp_pstrans_data.
      + exact αα₁.
      + intros.
        use tpair.
        * apply αα₂.
        * apply HD₂.
    - abstract (repeat split; intro; intros; apply HD₁).
  Defined.

  Definition make_disp_invmodification
            {F₁ F₂ : psfunctor B₁ B₂}
            {α β : pstrans F₁ F₂}
            {FF₁ : disp_psfunctor D₁ D₂ F₁}
            {FF₂ : disp_psfunctor D₁ D₂ F₂}
            {αα : disp_pstrans FF₁ FF₂ α}
            {ββ : disp_pstrans FF₁ FF₂ β}
            {m : invertible_modification α β}
            (mm : ∏ (x : B₁) (xx : D₁ x),
                  αα x xx ==>[ invertible_modcomponent_of m x ] ββ x xx)
    : disp_invmodification _ _ _ _ αα ββ m.
  Proof.
    use tpair.
    - intro ; intros.
      use tpair.
      + apply mm.
      + apply HD₂.
    - abstract (repeat split; intro; intros; apply HD₁).
  Defined.

  Definition make_disp_invmodification'
      {F₁ F₂ : psfunctor B₁ B₂}
      {α β : pstrans F₁ F₂}
      {FF₁ : disp_psfunctor D₁ D₂ F₁}
      {FF₂ : disp_psfunctor D₁ D₂ F₂}
      (αα : disp_pstrans FF₁ FF₂ α)
      (ββ : disp_pstrans FF₁ FF₂ β)
      (m : modification α β)
      (Hm : is_invertible_modification m)
      (mm : disp_modification _ _ _ _ αα ββ m)
      (Hmm : ∏ (x : B₁) (xx : D₁ x),
             is_disp_invertible_2cell (is_invertible_modcomponent_of m Hm x) (pr1 mm x xx))
    : disp_invmodification _ _ _ _ αα ββ (m,,Hm).
  Proof.
    use tpair.
    - intros x xx. use tpair.
      + exact (pr1 mm x xx).
      + simpl. exact (Hmm x xx).
    - simpl. exact (pr2 mm).
  Defined.

End NiceBuilders.

Section NiceBuildersContr.

  Context {B₁ B₂ : bicat}
          {D₁ : disp_bicat B₁}
          {D₂ : disp_bicat B₂}
          (HD₁ : disp_2cells_iscontr D₂)
          (HD₂ : disp_locally_groupoid D₂).

  Definition make_disp_psfunctor_contr
             {F : psfunctor B₁ B₂}
             (obFF : ∏ x:B₁, D₁ x → D₂ (F x))
             (morFF : ∏ (x y : B₁) (f : B₁⟦x,y⟧) (xx : D₁ x) (yy : D₁ y),
                      (xx -->[f] yy) →
                      (obFF x xx -->[#F f] obFF y yy))
    : disp_psfunctor D₁ D₂ F.
  Proof.
    use make_disp_psfunctor.
    - intros x y f g τ xx yy ff gg.
      apply isapropifcontr.
      apply HD₁.
    - exact HD₂.
    - exact obFF.
    - exact morFF.
    - intros.
      apply HD₁.
    - intros.
      apply HD₁.
    - intros.
      apply HD₁.
  Defined.

  Definition make_disp_pstrans_contr
             {F₁ F₂ : psfunctor B₁ B₂}
             {FF₁ : disp_psfunctor D₁ D₂ F₁}
             {FF₂ : disp_psfunctor D₁ D₂ F₂}
             {α : pstrans F₁ F₂}
             (αα₁ : ∏ (x : B₁) (xx : D₁ x), FF₁ x xx -->[ α x ] FF₂ x xx)
    : disp_pstrans FF₁ FF₂ α.
  Proof.
    use make_disp_pstrans.
    - intros x y f g τ xx yy ff gg.
      apply isapropifcontr.
      apply HD₁.
    - exact HD₂.
    - exact αα₁.
    - intros.
      apply HD₁.
  Defined.

  Definition make_disp_pstrans_inv_contr
             (HB₂ : is_univalent_2 B₂)
             {F₁ F₂ : psfunctor B₁ B₂}
             {FF₁ : disp_psfunctor D₁ D₂ F₁}
             {FF₂ : disp_psfunctor D₁ D₂ F₂}
             {α : pstrans F₁ F₂}
             (Hα : ∏ (x : B₁), left_adjoint_equivalence (α x))
             (αα₁ : ∏ (x : B₁) (xx : D₁ x), FF₁ x xx -->[ α x ] FF₂ x xx)
             (Hαα₁ : ∏ (x : B₁) (xx : D₁ x),
                     disp_left_adjoint_equivalence (Hα x) (αα₁ x xx))
    : disp_pstrans
        FF₂
        FF₁
        (left_adjoint_right_adjoint (pointwise_adjequiv_to_adjequiv HB₂ α Hα)).
  Proof.
    use make_disp_pstrans_contr.
    intros x xx.
    refine (transportf
              (λ z, _ -->[ z ] _)
              (!(right_adjoint_pointwise_adjequiv _ _ _ _))
              _).
    exact (pr11 (Hαα₁ x xx)).
  Qed.

  Definition make_disp_invmodification_contr
             {F₁ F₂ : psfunctor B₁ B₂}
             {α β : pstrans F₁ F₂}
             {FF₁ : disp_psfunctor D₁ D₂ F₁}
             {FF₂ : disp_psfunctor D₁ D₂ F₂}
             {αα : disp_pstrans FF₁ FF₂ α}
             {ββ : disp_pstrans FF₁ FF₂ β}
             (m : invertible_modification α β)
    : disp_invmodification _ _ _ _ αα ββ m.
  Proof.
    use make_disp_invmodification.
    - intros x y f g τ xx yy ff gg.
      apply isapropifcontr.
      apply HD₁.
    - exact HD₂.
    - intros.
      apply HD₁.
  Defined.
End NiceBuildersContr.
