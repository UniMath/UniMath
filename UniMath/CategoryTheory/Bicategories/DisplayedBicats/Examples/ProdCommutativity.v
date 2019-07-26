(* ******************************************************************************* *)
(** * Commutativity of direct product of displayed bicategories.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Initial.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Final.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Examples.Unitality.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(* MOVE??? *)
Definition transportf_make_dirprod
           (A : UU) (B B' : A → UU)
           (a1 a2 : A) (b : B a1) (b' : B' a1) (p : a1 = a2)
  : transportf (λ a : A, B a × B' a) p (make_dirprod b b') =
    make_dirprod (transportf B p b) (transportf B' p b').
Proof.
  induction p.
  apply idpath.
Defined.

Section DirProdCommutative.
  Context {B : bicat}.
  Variable (D1 D2 : disp_bicat B).

  Definition disp_swap_data
    : disp_psfunctor_data (disp_dirprod_bicat D1 D2) (disp_dirprod_bicat D2 D1) (ps_id_functor B).
  Proof.
    use make_disp_psfunctor_data.
    - intros a aa.
      exact (pr2 aa ,, pr1 aa).
    - intros a b f xx yy ff.
      exact (pr2 ff ,, pr1 ff).
    - intros a b f g α xx yy ff gg αα.
      exact (pr2 αα ,, pr1 αα).
    - intros a aa.
      exact (disp_id2_invertible_2cell _).
    - intros a b c f g aa bb cc ff gg.
      exact (disp_id2_invertible_2cell _).
  Defined.

  Definition disp_swap_laws : is_disp_psfunctor _ _ _ disp_swap_data.
  Proof.
    repeat use tpair.
    - intros a b f aa bb ff.
      cbn.
      unfold transportb.
      rewrite transportf_set.
      apply idpath.
      apply B.
    - intros a b f g h α β aa bb ff gg hh αα ββ.
      cbn.
      unfold transportb.
      rewrite transportf_set.
      apply idpath.
      apply B.
    - intros a b f aa bb ff.
      cbn.
      unfold transportb.
      rewrite transportf_make_dirprod.
      use pathsdirprod.
      + rewrite disp_id2_right.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_id2_rwhisker.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_id2_left.
        unfold transportb.
        rewrite !transport_f_f.
        rewrite transportf_set.
        apply idpath.
        apply B.
      + rewrite disp_id2_right.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_id2_rwhisker.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_id2_left.
        unfold transportb.
        rewrite !transport_f_f.
        rewrite transportf_set.
        apply idpath.
        apply B.
    - intros a b f aa bb ff.
      cbn.
      unfold transportb.
      rewrite transportf_make_dirprod.
      use pathsdirprod.
      + rewrite disp_id2_right.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_lwhisker_id2.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_id2_left.
        unfold transportb.
        rewrite !transport_f_f.
        rewrite transportf_set.
        apply idpath.
        apply B.
      + rewrite disp_id2_right.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_lwhisker_id2.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_id2_left.
        unfold transportb.
        rewrite! transport_f_f.
        rewrite transportf_set.
        apply idpath.
        apply B.
    - intros a b c d f g h aa bb cc dd ff gg hh.
      cbn.
      unfold transportb.
      rewrite transportf_make_dirprod.
      use pathsdirprod.
      + rewrite !disp_id2_right.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_id2_rwhisker.
        rewrite disp_lwhisker_id2.
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite disp_id2_left.
        rewrite disp_mor_transportf_prewhisker.
        rewrite disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        refine (transportf_paths (λ α, _ ==>[ α ] _) _ _).
        apply B.
      + rewrite !disp_id2_right.
        unfold transportb.
        rewrite disp_mor_transportf_postwhisker.
        rewrite disp_id2_rwhisker.
        rewrite disp_lwhisker_id2.
        unfold transportb.
        rewrite !disp_mor_transportf_postwhisker.
        rewrite disp_id2_left.
        rewrite disp_mor_transportf_prewhisker.
        rewrite disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        refine (transportf_paths (λ α, _ ==>[ α ] _) _ _).
        apply B.
    - intros a b c f g1 g2 α aa bb cc ff gg1 gg2 αα.
      cbn.
      unfold transportb.
      rewrite transportf_make_dirprod.
      use pathsdirprod.
      + rewrite disp_id2_left.
        rewrite disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        refine (transportf_paths (λ α, _ ==>[ α ] _) _ _).
        apply B.
      + rewrite disp_id2_left.
        rewrite disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        refine (transportf_paths (λ α, _ ==>[ α ] _) _ _).
        apply B.
    - intros a b c f1 f2 g α aa bb cc ff1 ff2 gg αα.
      cbn.
      unfold transportb.
      rewrite transportf_make_dirprod.
      use pathsdirprod.
      + rewrite disp_id2_left.
        rewrite disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        refine (transportf_paths (λ α, _ ==>[ α ] _) _ _).
        apply B.
      + rewrite disp_id2_left.
        rewrite disp_id2_right.
        unfold transportb.
        rewrite !transport_f_f.
        refine (transportf_paths (λ α, _ ==>[ α ] _) _ _).
        apply B.
  Qed.

  Definition disp_swap
    : disp_psfunctor (disp_dirprod_bicat D1 D2) (disp_dirprod_bicat D2 D1) (ps_id_functor B)
    := disp_swap_data ,, disp_swap_laws.
End DirProdCommutative.

Definition disp_swap_swap_data
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : disp_pstrans_data
      (disp_pseudo_comp _ _ _ _ _ (disp_swap D1 D2) (disp_swap D2 D1))
      (disp_pseudo_id (disp_dirprod_bicat D1 D2))
      (pstrans_lunitor (ps_id_functor B)).
Proof.
  use make_disp_pstrans_data.
  - exact (λ x xx, id_disp (pr1 xx) ,, id_disp (pr2 xx)).
  - intros x y f xx yy ff; cbn.
    exact (vcomp_disp_invertible (disp_invertible_2cell_lunitor ff) (disp_invertible_2cell_rinvunitor ff)).
Defined.

Definition disp_swap_swap_laws
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : is_disp_pstrans
      (disp_pseudo_comp _ _ _ _ _ (disp_swap D1 D2) (disp_swap D2 D1))
      (disp_pseudo_id (disp_dirprod_bicat D1 D2))
      (pstrans_lunitor (ps_id_functor B))
      (disp_swap_swap_data D1 D2).
Proof.
  repeat use tpair.
  - intros x y f g η xx yy ff gg ηη.
    cbn.
    unfold transportb.
    rewrite transportf_make_dirprod.
    apply dirprod_paths.
    + cbn.
      Admitted.

Definition disp_swap_swap
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : disp_pstrans
      (disp_pseudo_comp _ _ _ _ _ (disp_swap D1 D2) (disp_swap D2 D1))
      (disp_pseudo_id (disp_dirprod_bicat D1 D2))
      (pstrans_lunitor (ps_id_functor B))
  := _ ,, disp_swap_swap_laws D1 D2.

Definition disp_swap_swap_inv_data
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : disp_pstrans_data
      (disp_pseudo_id (disp_dirprod_bicat D1 D2))
      (disp_pseudo_comp _ _ _ _ _ (disp_swap D1 D2) (disp_swap D2 D1))
      (pstrans_linvunitor (ps_id_functor B)).
Proof.
  use make_disp_pstrans_data.
  - exact (λ x xx, id_disp (pr1 xx) ,, id_disp (pr2 xx)).
  - intros x y f xx yy ff; cbn.
    exact (vcomp_disp_invertible (disp_invertible_2cell_lunitor ff) (disp_invertible_2cell_rinvunitor ff)).
Defined.

Definition disp_swap_swap_inv_laws
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : is_disp_pstrans
      (disp_pseudo_id (disp_dirprod_bicat D1 D2))
      (disp_pseudo_comp _ _ _ _ _ (disp_swap D1 D2) (disp_swap D2 D1))
      (pstrans_linvunitor (ps_id_functor B))
      (disp_swap_swap_data D1 D2).
Proof.
  repeat use tpair.
  - intros x y f g η xx yy ff gg ηη.
    cbn.
    apply dirprod_paths.
    + cbn.
      Admitted.

Definition disp_swap_swap_inv
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : disp_pstrans
      (disp_pseudo_id (disp_dirprod_bicat D1 D2))
      (disp_pseudo_comp _ _ _ _ _ (disp_swap D1 D2) (disp_swap D2 D1))
      (pstrans_linvunitor (ps_id_functor B))
  := _ ,, disp_swap_swap_inv_laws D1 D2.


Definition is_disp_biequiv_unit_counit_path_pgroupoid
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : is_disp_biequivalence_unit_counit _ _
                                      (id_is_biequivalence B)
                                      (disp_swap D1 D2) (disp_swap D2 D1).
Proof.
  use tpair.
  - exact (disp_swap_swap D1 D2).
  - exact (disp_swap_swap D2 D1).
Defined.

Definition disp_swap_swap_swap_swap_data
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : disp_invmodification_data _ _ _ _
      (disp_ps_comp _ _ _ _ _ _ _ _ _ _  (disp_swap_swap_inv D1 D2) (disp_swap_swap D1 D2))
      (disp_id_trans _)
      (unitcounit_of_is_biequivalence (id_is_biequivalence B)).
Proof.
  intros x xx.
  simpl.
Admitted.
(*
  pose (invertible_modcomponent_of (unitcounit_of_is_biequivalence (id_is_biequivalence B)) x) as z.
  assert (pr1 z = runitor _).
  { cbn. apply idpath.
  cbn in z.
  Check disp_id2_invertible_2cell (id_disp xx).
  Print disp_idtoiso_2_1.
  Search disp_invertible_2cell id_disp.
 *)

Definition disp_swap_swap_swap_swap
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : disp_invmodification _ _ _ _
      (disp_ps_comp _ _ _ _ _ _ _ _ _ _  (disp_swap_swap_inv D1 D2) (disp_swap_swap D1 D2))
      (disp_id_trans _)
      (unitcounit_of_is_biequivalence (id_is_biequivalence B)).
Proof.
Admitted.


Definition disp_swap_swap_inv_swap_swap_inv
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : disp_invmodification _ _ _ _
      (disp_ps_comp _ _ _ _ _ _ _ _ _ _ (disp_swap_swap D1 D2) (disp_swap_swap_inv D1 D2))
      (disp_id_trans _)
      (unitunit_of_is_biequivalence (id_is_biequivalence B)).
Admitted.


Definition disp_swap_biequivalence
           {B : bicat}
           (D1 D2 : disp_bicat B)
  : disp_is_biequivalence_data _ _
                               (id_is_biequivalence B)
                               (is_disp_biequiv_unit_counit_path_pgroupoid D1 D2).
Proof.
  use tpair.
  - exact (disp_swap_swap_inv _ _).
  - use tpair.
    + exact (disp_swap_swap_inv _ _).
    + use tpair.
      * exact (disp_swap_swap_swap_swap _ _).
      * use tpair.
        -- exact (disp_swap_swap_inv_swap_swap_inv _ _).
         -- use tpair.
            ++ exact (disp_swap_swap_swap_swap _ _).
            ++ exact (disp_swap_swap_inv_swap_swap_inv _ _).
Defined.
