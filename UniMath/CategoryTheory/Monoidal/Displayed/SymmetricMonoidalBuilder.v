(*
In this file, we provide a builder to construct a symmetric displayed monoidal category on a locally propositional displayed category [make_symmetric_monoidal_disp_cat_locally_prop].

This builder takes into account the symmetric aspects found in a monoidal category,
e.g., the (displayed) right unitor can be constructed from the left unitor (provided a braiding); the assumptions on the right unitor, follow from those on the left unitor.
*)

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

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section Construct_SymmetricMonoidal_On_LocallyProp_DisplayedCategories.

  Context (V : sym_monoidal_cat) (D : disp_cat V).

  Context (disp_tensor_ob : ∏ x y : V, D x → D y → D (x ⊗ y)).
  Let T {x y : V} (xx : D x) (yy : D y) : D (x ⊗ y) := disp_tensor_ob _ _ xx yy.

  Context (disp_lwhisker : ∏ (x y1 y2 : V) (g : V⟦ y1, y2 ⟧) (xx : D x) (yy1 : D y1) (yy2 : D y2),
              yy1 -->[ g] yy2 → T xx yy1 -->[ x ⊗^{V}_{l} g] T xx yy2).
  Let Tl
    {x y1 y2 : V} {g : V⟦ y1, y2 ⟧} (xx : D x) {yy1 : D y1} {yy2 : D y2}
    (gg : yy1 -->[ g] yy2)
    : T xx yy1 -->[ x ⊗^{V}_{l} g] T xx yy2
    := disp_lwhisker _ _ _ _ _ _ _ gg.

  Context (disp_braiding : ∏ (x y : V) (xx : D x) (yy : D y), T xx yy -->[sym_mon_braiding V x y] T yy xx).
  Let B {x y : V} (xx : D x) (yy : D y)
    : T xx yy -->[sym_mon_braiding V x y] T yy xx
    := disp_braiding x y xx yy.

  Let Tr
    {x1 x2 y : V} {f : V⟦ x1, x2 ⟧}
    {xx1 : D x1} {xx2 : D x2}
    (yy : D y) (ff : xx1 -->[ f] xx2)
    : T xx1 yy -->[ f ⊗^{V}_{r} y] T xx2 yy.
  Proof.
    set (t := B xx1 yy ;; Tl _ ff ;; B yy xx2).
    use (transportf _ _ t).
    etrans. {
      apply maponpaths_2.
      apply (monoidal_braiding_naturality_right V).
    }
    refine (assoc' _ _ _ @ _).
    etrans. {
      apply maponpaths.
      exact (pr1 ((pr122 (pr2 V)) x2 y)).
    }
    apply id_right.
  Defined.

  Context (disp_lwhisker_preserves_id :
            ∏ (x y : V) (xx : D x) (yy : D y),
              Tl xx (id_disp yy) =
                transportb _ (bifunctor_leftid V x y) (id_disp (T xx yy))).

  Context (B_inv : ∏ (x y : V) (xx : D x) (yy : D y),
              B xx yy ;; B yy xx = transportb _ (sym_mon_braiding_inv V x y) (id_disp _)).

  Local Lemma disp_rwhisker_preserves_id
    {x y : V} (xx : D x) (yy : D y)
    : Tr yy (id_disp xx) =
        transportb _ (bifunctor_rightid V y x) (id_disp (T xx yy)).
  Proof.
    unfold Tr.
    cbn.

    etrans. {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply disp_lwhisker_preserves_id.
    }
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

  Context (disp_lwhisker_preserves_comp
    : ∏ (x y1 y2 y3 : V) (g1 : V⟦ y1, y2 ⟧) (g2 : V⟦ y2, y3 ⟧) (xx : D x)
        (yy1 : D y1) (yy2 : D y2) (yy3 : D y3)
        (gg1 : yy1 -->[ g1] yy2) (gg2 : yy2 -->[ g2] yy3),
      Tl xx (gg1 ;; gg2)
      = transportb _ (bifunctor_leftcomp V x y1 y2 y3 g1 g2)
          (Tl _ gg1 ;; Tl _ gg2)).

  Local Lemma disp_rwhisker_preserves_comp
    {x1 x2 x3 y : V} {f1 : V⟦ x1, x2 ⟧} {f2 : V⟦ x2, x3 ⟧} {xx1 : D x1}
    {xx2 : D x2} {xx3 : D x3} (yy : D y)
    (ff1 : xx1 -->[ f1] xx2) (ff2 : xx2 -->[ f2] xx3)
    : Tr yy (ff1 ;; ff2)
      = transportb _ (bifunctor_rightcomp V y x1 x2 x3 f1 f2) (Tr yy ff1 ;; Tr yy ff2).
  Proof.
    unfold Tr.
    cbn.
    rewrite (disp_lwhisker_preserves_comp _ _ _ _ _ _ _ _ _ _ ff1 ff2).
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
    unfold transportb.
    rewrite transport_f_f.

    rewrite ! assoc_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    use transportf_transpose_right.
    unfold transportb.
    rewrite ! transport_f_f.
    use transportf_set.
    apply homset_property.
  Qed.

  (* Lemma B_naturality
    : B x1 y1 xx1 yy1 ;; Tl yy1 ff = Tl _ ff *)

  Context (disp_tensor_equalwhiskers
            : ∏ (x1 x2 y1 y2 : V) (f : V⟦ x1, x2 ⟧) (g : V⟦ y1, y2 ⟧)
                (xx1 : D x1) (xx2 : D x2) (yy1 : D y1) (yy2 : D y2)
                (ff : xx1 -->[ f] xx2) (gg : yy1 -->[ g] yy2),
              Tr yy1 ff ;; Tl xx2 gg
              = transportb _ (bifunctor_equalwhiskers V x1 x2 y1 y2 f g)
                  (Tl xx1 gg ;; Tr yy2 ff)).

  Definition make_symmetric_monoidal_disp_cat_tensor
    : disp_tensor D V.
  Proof.
    simple refine ((_,,(_,,_)),,(_,,_,,_,,_,,_)).
    - exact disp_tensor_ob.
    - exact disp_lwhisker.
    - exact (λ _ _ _ _ _ _ yy gg, Tr yy gg).
    - exact disp_lwhisker_preserves_id.
    - intro ; intros ; apply disp_rwhisker_preserves_id.
    - exact disp_lwhisker_preserves_comp.
    - intro ; intros ; apply disp_rwhisker_preserves_comp.
    - intro ; intros ; apply disp_tensor_equalwhiskers.
  Defined.

  Context (II : D (monoidal_unit V))
    (lu_lu : disp_leftunitor_data make_symmetric_monoidal_disp_cat_tensor II)
    (lu_lu_inv : disp_leftunitorinv_data make_symmetric_monoidal_disp_cat_tensor II).

  Lemma make_symmetric_monoidal_disp_cat_rightunitor
    {x : V} (xx : D x)
    : T xx II -->[mon_runitor x] xx.
  Proof.
    use (transportf _ _ (B xx II ;; lu_lu _ xx)).
    apply sym_mon_braiding_lunitor.
  Defined.

  Definition make_symmetric_monoidal_disp_cat_rightunitor_inv
    {x : V} (xx : D x)
    : xx -->[mon_rinvunitor x] T xx II.
  Proof.
    use (transportf _ _ (lu_lu_inv _ xx ;; B _ _)).
    apply sym_mon_braiding_linvunitor.
  Defined.

  Context (asas : disp_associator_data make_symmetric_monoidal_disp_cat_tensor).
  Context (asasinv : disp_associatorinv_data make_symmetric_monoidal_disp_cat_tensor).

  Definition make_symmetric_monoidal_disp_cat_monoidal_data
    : disp_monoidal_data D V.
  Proof.
    exists make_symmetric_monoidal_disp_cat_tensor.
    exists II.
    exists lu_lu.
    exists lu_lu_inv.
    exists (λ _ xx, make_symmetric_monoidal_disp_cat_rightunitor xx).
    exists (λ _ xx, make_symmetric_monoidal_disp_cat_rightunitor_inv xx).
    exists asas.
    exact asasinv.
  Defined.

  Definition make_symmetric_monoidal_disp_cat_monoidal_locally_prop
    (LP : locally_propositional D)
    : disp_monoidal D V.
  Proof.
    exists make_symmetric_monoidal_disp_cat_monoidal_data.
    repeat split ; try (intro ; intros) ; apply LP.
  Defined.

  Definition make_symmetric_monoidal_disp_cat_locally_prop'
    (LP : locally_propositional D)
    : ∑ DM : disp_monoidal D V, disp_symmetric DM V.
  Proof.
    exists (make_symmetric_monoidal_disp_cat_monoidal_locally_prop LP).
    use make_disp_symmetric_locally_propositional.
    { exact LP. }
    exact disp_braiding.
  Defined.

End Construct_SymmetricMonoidal_On_LocallyProp_DisplayedCategories.

Definition make_symmetric_monoidal_disp_cat_locally_prop
  (V : sym_monoidal_cat) (D : disp_cat V)
  (LP : locally_propositional D)
  (T : ∏ x y : V, D x → D y → D (x ⊗ y))
  (Tmor : ∏ (x y1 y2 : V) (g : V⟦ y1, y2 ⟧) (xx : D x) (yy1 : D y1) (yy2 : D y2),
      yy1 -->[g] yy2
      → T x y1 xx yy1 -->[ x ⊗^{V}_{l} g] T x y2 xx yy2)
  (B :  ∏ (x y : V) (xx : D x) (yy : D y), T x y xx yy -->[sym_mon_braiding V x y] T y x yy xx)
  (II :  D (monoidal_unit V))
  (lu_lu : ∏ (x : V) (xx : D x), T (monoidal_unit V) x II xx -->[mon_lunitor x] xx)
  (lu_lu_inv : ∏ (x : V) (xx : D x), xx -->[mon_linvunitor x] T (monoidal_unit V) x II xx)
  (assass : ∏ (x y z : V) (xx : D x) (yy : D y) (zz : D z),
      (T _ _ (T _ _ xx yy) zz) -->[mon_lassociator x y z] T _ _ xx (T _ _ yy zz))
  (assassinv : ∏ (x y z : V) (xx : D x) (yy : D y) (zz : D z),
      T _ _ xx (T _ _ yy zz) -->[mon_rassociator x y z] (T _ _ (T _ _ xx yy) zz))
  : ∑ DM : disp_monoidal D V, disp_symmetric DM V.
Proof.
  use make_symmetric_monoidal_disp_cat_locally_prop'.
  - exact T.
  - exact Tmor.
  - exact B.
  - intro ; intros ; apply LP.
  - intro ; intros ; apply LP.
  - intro ; intros ; apply LP.
  - intro ; intros ; apply LP.
  - exact II.
  - exact lu_lu.
  - exact lu_lu_inv.
  - exact assass.
  - exact assassinv.
  - exact LP.
Defined.
