Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.
Import MonoidalNotations.
Import DisplayedBifunctorNotations.
Import DisplayedMonoidalNotations.

Lemma disp_tensor_distributes_over_transportb_right
  {C : category}
  {D : disp_cat C}
  {M : monoidal C}
  (DM : disp_monoidal D M)
  {x y z : C}
  {f g : y --> z}
  (p : f = g)
  (xx : D x)
  {yy : D y}
  {zz : D z}
  (ff : yy -->[f] zz)
  (gg : yy -->[g] zz)
  : ff = transportb _ p gg
    -> xx ⊗⊗^{DM}_{l} transportb _ p ff
    = transportb _ (maponpaths  (leftwhiskering_on_morphisms M x y z) p) (xx ⊗⊗^{DM}_{l} gg).
Proof.
  induction p.
  intro q.
  cbn.
  apply maponpaths.
  exact q.
Qed.

Lemma disp_tensor_distributes_over_transportb_left
  {C : category}
  {D : disp_cat C}
  {M : monoidal C}
  (DM : disp_monoidal D M)
  {x y z : C}
  {f g : y --> z}
  (p : f = g)
  (xx : D x)
  {yy : D y}
  {zz : D z}
  (ff : yy -->[f] zz)
  (gg : yy -->[g] zz)
  : ff = transportb _ p gg
    -> transportb _ p ff ⊗⊗^{DM}_{r} xx
    = transportb _ (maponpaths  (rightwhiskering_on_morphisms M _ _ _) p) (gg ⊗⊗^{DM}_{r} xx).
Proof.
  induction p.
  intro q.
  cbn.
  apply maponpaths.
  exact q.
Qed.

Lemma disp_tensor_with_id_left
  {C : category}
  {D : disp_cat C}
  {M : monoidal C}
  (DM : disp_monoidal D M)
  {x y z : C}
  {f : z --> y}
  {g : y --> z}
  (p : g · f = identity y)
  (xx : D x)
  (yy : D y)
  : xx ⊗⊗^{DM}_{l} transportb (mor_disp _ _) p (id_disp yy)
    = transportb _ (maponpaths (λ i, x ⊗^{M}_{l} i) p @ bifunctor_leftid M x y) (id_disp (xx ⊗⊗_{DM} yy)).
Proof.
  set (pp := disp_tensor_distributes_over_transportb_right DM p xx (transportb _ p (id_disp yy)) (id_disp yy) (idpath _)).

  rewrite <- transport_b_b.
  etrans.
  2: {
    apply maponpaths.
    apply (disp_bifunctor_leftid DM _ _ xx yy).
  }
  refine (_ @ pp).
  apply maponpaths.
  now rewrite transportb_const.
Qed.

Lemma disp_tensor_with_id_right
  {C : category}
  {D : disp_cat C}
  {M : monoidal C}
  (DM : disp_monoidal D M)
  {x y z : C}
  {f : z --> y}
  {g : y --> z}
  (p : g · f = identity y)
  (xx : D x)
  (yy : D y)
  : transportb (mor_disp _ _) p (id_disp yy)  ⊗⊗^{DM}_{r} xx
    = transportb _ (maponpaths (λ i, i ⊗^{M}_{r} x) p @ bifunctor_rightid M x y) (id_disp (yy ⊗⊗_{DM} _)).
Proof.
  set (pp := disp_tensor_distributes_over_transportb_left DM p xx (transportb _ p (id_disp yy)) (id_disp yy) (idpath _)).

  rewrite <- transport_b_b.
  etrans.
  2: {
    apply maponpaths.
    apply (disp_bifunctor_rightid DM _ _ _ _).
  }
  refine (_ @ pp).
  apply maponpaths.
  now rewrite transportb_const.
Qed.

Lemma disp_tensor_with_id_on_right
  {C : category} {D : disp_cat C}
  {M : monoidal C} {DM : disp_monoidal D M}
  {x y z : C}
  {f : C⟦x, y⟧}
  {xx : D x} {yy : D y} {zz : D z}
  (ff : xx -->[f] yy)
  : ff ⊗⊗^{ DM} id_disp zz
    = transportb _ (when_bifunctor_becomes_rightwhiskering M z f) (ff ⊗⊗^{ DM}_{r} zz).
Proof.
  unfold dispfunctoronmorphisms1.
  etrans. {
    apply maponpaths.
    apply disp_bifunctor_leftid.
  }
  etrans. {
    apply mor_disp_transportf_prewhisker.
  }
  use transportf_transpose_left.
  rewrite transport_b_b.
  etrans. {
    apply id_right_disp.
  }
  apply maponpaths_2.
  apply homset_property.
Qed.

Lemma disp_tensor_with_id_on_left
  {C : category} {D : disp_cat C}
  {M : monoidal C} {DM : disp_monoidal D M}
  {x y z : C}
  {f : C⟦x, y⟧}
  {xx : D x} {yy : D y} {zz : D z}
  (ff : xx -->[f] yy)
  : id_disp zz ⊗⊗^{ DM} ff
    = transportb _ (when_bifunctor_becomes_leftwhiskering M z f) (zz ⊗⊗^{ DM}_{l} ff).
Proof.
  unfold dispfunctoronmorphisms1.
  etrans. {
    apply maponpaths_2.
    apply disp_bifunctor_rightid.
  }
  etrans. {
    apply mor_disp_transportf_postwhisker.
  }
  use transportf_transpose_left.
  rewrite transport_b_b.
  etrans. {
    apply id_left_disp.
  }
  apply maponpaths_2.
  apply homset_property.
Qed.
