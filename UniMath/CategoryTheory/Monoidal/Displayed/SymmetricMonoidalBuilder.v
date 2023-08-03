Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Comonoids.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsCategory.

Local Open Scope cat.
Import MonoidalNotations.

Section Construct_SymmetricMonoidal_On_LocallyProp_DisplayedCategories.

  Context {C : category} {M : monoidal C} (S : symmetric M) (D : disp_cat C).

  Context (T_ob : ∏ x y : C, D x → D y → D (x ⊗_{ M} y)).
  Definition T {x y : C} (xx : D x) (yy : D y) : D (x ⊗_{ M} y) := T_ob _ _ xx yy.

  Context (T_mor : ∏ (x y1 y2 : C) (g : C ⟦ y1, y2 ⟧) (xx : D x) (yy1 : D y1) (yy2 : D y2),
              yy1 -->[ g] yy2 → T xx yy1 -->[ x ⊗^{ M}_{l} g] T xx yy2).
  Definition Tl
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧} (xx : D x) {yy1 : D y1} {yy2 : D y2}
    (gg : yy1 -->[ g] yy2)
    : T xx yy1 -->[ x ⊗^{ M}_{l} g] T xx yy2
    := T_mor _ _ _ _ _ _ _ gg.

  Context (B : ∏ (x y : C) (xx : D x) (yy : D y), T xx yy -->[pr1 S x y] T yy xx).

  Definition Tr
    {x1 x2 y : C} {f : C ⟦ x1, x2 ⟧}
    {xx1 : D x1} {xx2 : D x2}
    (yy : D y) (ff : xx1 -->[ f] xx2)
    : T xx1 yy -->[ f ⊗^{ M}_{r} y] T xx2 yy.
  Proof.
    set (t := B _ _ xx1 yy ;; Tl _ ff ;; B _ _ yy xx2).
    use (transportf _ _ t).
    etrans. {
      apply maponpaths_2.
      apply (pr212 S).
    }
    refine (assoc' _ _ _ @ _).
    etrans. {
      apply maponpaths.
      exact (pr1 ((pr122 S) x2 y)).
    }
    apply id_right.
  Defined.

  Context (Tl_preserves_id : ∏ (x y : C) (xx : D x) (yy : D y),
              T_mor x y y (identity y) xx yy yy (id_disp yy) =
  transportb (mor_disp (T_ob x y xx yy) (T_ob x y xx yy)) (bifunctor_leftid M x y)
    (id_disp (T_ob x y xx yy))).

  Context (B_inv : ∏ (x y : C) (xx : D x) (yy : D y), B x y xx yy ;; B y x yy xx = transportb _ (pr1 (pr122 S x y)) (id_disp _)).

  Lemma Tr_preserves_id
    {x y : C} (xx : D x) (yy : D y)
    : Tr yy (id_disp xx) =
        transportb (mor_disp (T_ob x y xx yy) (T_ob x y xx yy)) (bifunctor_rightid M y x)
          (id_disp (T_ob x y xx yy)).
  Proof.
    set (l := Tl_preserves_id _ _ yy xx).
    unfold Tr.
    cbn.

    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      exact l.
    }
    clear l.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite id_right_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite B_inv.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Context (Tl_preserves_comp
    : ∏ (x y1 y2 y3 : C) (g1 : C ⟦ y1, y2 ⟧) (g2 : C ⟦ y2, y3 ⟧) (xx : D x)
  (yy1 : D y1) (yy2 : D y2) (yy3 : D y3) (gg1 : yy1 -->[ g1] yy2) (gg2 : yy2 -->[ g2] yy3),
      T_mor x y1 y3 (g1 · g2) xx yy1 yy3 (gg1 ;; gg2)
      = transportb _ (bifunctor_leftcomp M x y1 y2 y3 g1 g2)
          (Tl _ gg1 ;; Tl _ gg2)).

  Lemma Tr_preserves_comp
    {x1 x2 x3 y : C} {f1 : C ⟦ x1, x2 ⟧} {f2 : C ⟦ x2, x3 ⟧} {xx1 : D x1}
    {xx2 : D x2} {xx3 : D x3} (yy : D y)
    (ff1 : xx1 -->[ f1] xx2) (ff2 : xx2 -->[ f2] xx3)
    : Tr yy (ff1 ;; ff2)
      = transportb _ (bifunctor_rightcomp M y x1 x2 x3 f1 f2) (Tr yy ff1 ;; Tr yy ff2).
  Proof.
    unfold Tr.
    cbn.
    rewrite (Tl_preserves_comp _ _ _ _ _ _ _ _ _ _ ff1 ff2).
    unfold transportb.
    rewrite ! mor_disp_transportf_prewhisker.
    unfold transportb.
    rewrite ! mor_disp_transportf_postwhisker.
    rewrite ! transport_f_f.
    etrans.
    2: {
      apply maponpaths.
      rewrite assoc_disp_var.
      do 2 apply maponpaths.
      rewrite assoc_disp.
      apply maponpaths.
      apply maponpaths_2.
      rewrite assoc_disp.
      apply maponpaths.
      apply maponpaths_2.
      apply pathsinv0, B_inv.
    }

    unfold transportb.
    rewrite ! transport_f_f.
    rewrite ! mor_disp_transportf_prewhisker.
    unfold transportb.
    rewrite ! transport_f_f.
    rewrite ! mor_disp_transportf_postwhisker.
    rewrite ! mor_disp_transportf_prewhisker.
    rewrite ! transport_f_f.
    rewrite id_left_disp.
    unfold transportb.
    rewrite ! mor_disp_transportf_postwhisker.
    rewrite ! mor_disp_transportf_prewhisker.
    rewrite ! transport_f_f.
    use transportf_transpose_right.
  Admitted.

  Definition TODO_JOKER (A : UU): A. Proof. Admitted.
  Definition make_symmetric_monoidal_disp_cat_tensor
    : disp_tensor D M.
  Proof.
    simple refine ((_,,(_,,_)),,(_,,_,,_,,_,,_)).
    - exact T_ob.
    - exact T_mor.
    - exact (λ _ _ _ _ _ _ yy gg, Tr yy gg).
    - exact Tl_preserves_id.
    - intro ; intros ; apply Tr_preserves_id.
    - exact Tl_preserves_comp.
    - intro ; intros ; apply Tr_preserves_comp.
    - cbn.
      unfold dispfunctoronmorphisms_are_equal.
      cbn.
      unfold dispfunctoronmorphisms1.
      unfold dispfunctoronmorphisms2.
      cbn.
      unfold Tr.
      cbn.

      intro ; intros.
      cbn in *.

      rewrite mor_disp_transportf_postwhisker.
      rewrite mor_disp_transportf_prewhisker.
      use transportf_transpose_left.
      rewrite transport_b_b.
      rewrite transport_b_f.
      apply TODO_JOKER. (*** **)
  Defined.

  Context (II : D I_{ M})
    (lulu : disp_leftunitor_data make_symmetric_monoidal_disp_cat_tensor II)
    (luluinv : disp_leftunitorinv_data make_symmetric_monoidal_disp_cat_tensor II).

  Lemma make_symmetric_monoidal_disp_cat_rightunitor
    {x : C} (xx : D x)
    : T xx II -->[ ru^{ M }_{ x}] xx.
  Proof.
    use (transportf _ _ (B _ _ xx II ;; lulu _ xx)).
    apply (sym_mon_braiding_lunitor ((C,,M),,S)).
  Defined.

  Definition make_symmetric_monoidal_disp_cat_rightunitor_inv
    {x : C} (xx : D x)
    : xx -->[ruinv^{ M }_{ x}] T xx II.
  Proof.
    use (transportf _ _ (luluinv _ xx ;; B _ _ _ _)).
    apply (sym_mon_braiding_linvunitor ((C,,M),,S)).
  Defined.

  Context (asas : disp_associator_data make_symmetric_monoidal_disp_cat_tensor).
  Definition make_symmetric_monoidal_disp_cat_associator_inv
    {x y z : C} (xx : D x) (yy : D y) (zz : D z)
    : T xx (T yy zz) -->[αinv^{ M }_{ x, y, z}] T (T xx yy) zz.
  Proof.
    Check (_ ;; asas _ _ _ _ _ _ ;; B _ _ _ _).
    refine (transportf _ _ (_ ;; asas _ _ _ _ _ _ ;; B _ _ _ _)) ; cbn.
    - admit.
    - admit.
  Admitted.

  Definition make_symmetric_monoidal_disp_cat_monoidal_data
    : disp_monoidal_data D M.
  Proof.
    exists make_symmetric_monoidal_disp_cat_tensor.
    exists II.
    exists lulu.
    exists luluinv.
    exists (λ _ xx, make_symmetric_monoidal_disp_cat_rightunitor xx).
    exists (λ _ xx, make_symmetric_monoidal_disp_cat_rightunitor_inv xx).
    exists asas.
    exact (λ _ _ _ xx yy zz, make_symmetric_monoidal_disp_cat_associator_inv xx yy zz).
  Defined.

  Definition make_symmetric_monoidal_disp_cat_monoidal_locally_prop
    (LP : locally_propositional D)
    : disp_monoidal D M.
  Proof.
    exists make_symmetric_monoidal_disp_cat_monoidal_data.
    repeat split ; try (intro ; intros) ; apply LP.
  Defined.

  Definition make_symmetric_monoidal_disp_cat_locally_prop'
    (LP : locally_propositional D)
    : ∑ DM : disp_monoidal D M, disp_symmetric DM S.
  Proof.
    exists (make_symmetric_monoidal_disp_cat_monoidal_locally_prop LP).
    use make_disp_symmetric_locally_propositional.
    { exact LP. }
    exact B.
  Defined.

End Construct_SymmetricMonoidal_On_LocallyProp_DisplayedCategories.

Definition make_symmetric_monoidal_disp_cat_locally_prop
  {C : category} {M : monoidal C} (S : symmetric M) (D : disp_cat C)
  (LP : locally_propositional D)
  (T : ∏ x y : C, D x → D y → D (x ⊗_{ M} y))
  (Tmor : ∏ (x y1 y2 : C) (g : C ⟦ y1, y2 ⟧) (xx : D x) (yy1 : D y1) (yy2 : D y2),
      yy1 -->[ g] yy2
      → T x y1 xx yy1 -->[ x ⊗^{ M}_{l} g] T x y2 xx yy2)
  (B :  ∏ (x y : C) (xx : D x) (yy : D y), T x y xx yy -->[ pr1 S x y] T y x yy xx)
  (II :  D I_{ M})
  (lulu : ∏ (x : C) (xx : D x), T I_{ M} x II xx -->[ lu^{ M }_{ x}] xx)
  (luluinv : ∏ (x : C) (xx : D x), xx -->[ luinv^{ M }_{ x}] T I_{ M} x II xx)
  (assass : ∏ (x y z : C) (xx : D x) (yy : D y) (zz : D z),
       (T _ _ (T _ _ xx yy) zz) -->[α^{ M }_{ x, y, z}] T _ _ xx (T _ _ yy zz))
  : ∑ DM : disp_monoidal D M, disp_symmetric DM S.
Proof.
  use make_symmetric_monoidal_disp_cat_locally_prop'.
  - exact T.
  - exact Tmor.
  - exact B.
  - intro ; intros ; apply LP.
  - intro ; intros ; apply LP.
  - intro ; intros ; apply LP.
  - exact II.
  - exact lulu.
  - exact luluinv.
  - exact assass.
  - exact LP.
Defined.
