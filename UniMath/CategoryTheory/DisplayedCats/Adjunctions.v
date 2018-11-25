(**
  Contents:
  - Definition of homset correspondences for a displayed adjunction.
  - Homset correspondences are weak equivalences.
  - The right adjoint functor of a displayed adjunction preserves cartesian morphisms.

  Written by Tamara von Glehn and Noam Zeilberger at the School and Workshop on
  Univalent Mathematics, December 2017
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.

Section fix_disp_adjunction.

Context {C C' : category}
        (A : adjunction C C')
        {D : disp_cat C}
        {D': disp_cat C'}
        (X : disp_adjunction A D D').
Let F := left_functor A.
Let G := right_functor A.

Let FF : disp_functor F D D' := left_adj_over X.
Let GG : disp_functor G D' D := right_adj_over X.

Let η : functor_identity C ⟹ F ∙ G := adjunit A.
Let ε : G ∙ F ⟹ functor_identity C' := adjcounit A.
Let ηη : disp_nat_trans η (disp_functor_identity D) (disp_functor_composite FF GG)
    := unit_over X.
Let εε : disp_nat_trans ε (disp_functor_composite GG FF) (disp_functor_identity D')
    := counit_over X.

Local Open Scope hide_transport_scope.

Section DispHomSetIso_from_Adjunction.

  (* Naming: homset_conj_inv lies over φ_adj_inv and has inverse homset_conj,
     homset_conj' lies over φ_adj and has inverse homset_conj'_inv. *)

  Definition homset_conj_inv {c : C} {c' : C'} (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') -> (FF _ d -->[#F g ·  ε _] d') :=
    λ alpha, comp_disp (# FF alpha) (εε _ _).

  Definition homset_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c') :
     (FF _ d -->[f] d') -> (d -->[η _ · #G f] GG _ d') :=
    λ beta, comp_disp (ηη _ _) (# GG beta).

  Definition homset_conj'_inv {c : C} {c' : C'} (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c') :
    (d -->[η _ · #G f] GG _ d') -> (FF _ d -->[f] d').
  Proof.
    set (equiv := φ_adj_inv_after_φ_adj A f
                : # F (η c · # G f) · ε c' = f).
    exact (λ alpha, transportf _  equiv (homset_conj_inv _ _ _ alpha)).
  Defined.

  Definition homset_conj {c : C} {c' : C'} (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') :
    (FF _ d -->[#F g ·  ε _] d') -> (d -->[g] GG _ d').
  Proof.
    set (equiv := φ_adj_after_φ_adj_inv A g
                : η c · # G (# F g · ε c') = g).
    exact (λ beta, transportf _  equiv (homset_conj' _ _ _ beta)).
  Defined.

  (** * Naturality of homset bijections *)

  Open Scope mor_disp.

  Lemma homset_conj_inv_natural_precomp {c : C} {c' : C'} {g : C⟦c, G c'⟧} {c'' : C}
      {f : C⟦c'', c⟧} {d : D c} {d' : D' c'} {d'' : D c''}
      (gg : d -->[g] GG _ d') (ff : d'' -->[f] d) :
    homset_conj_inv _ _ _ (ff ;; gg)  =
    transportb _ (φ_adj_inv_natural_precomp A _ _ g _ f) (# FF ff ;; homset_conj_inv _ _ _ gg).
  Proof.
    unfold homset_conj_inv.
    rewrite disp_functor_comp.
    rewrite assoc_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply maponpaths_2, homset_property.
  Defined.

    Lemma homset_conj_inv_natural_postcomp {c : C} {c' : C'} {g : C⟦c, G c'⟧} {c'' : C'}
      {f : C'⟦c', c''⟧} {d : D c} {d' : D' c'} {d'' : D' c''}
      (gg : d -->[g] GG _ d') (ff : d' -->[f] d'') :
    homset_conj_inv _ _ _ (gg ;; # GG ff)  =
    transportb _ (φ_adj_inv_natural_postcomp A _ _ g _ f) (homset_conj_inv _ _ _ gg ;; ff).
  Proof.
    unfold homset_conj_inv.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite 2 assoc_disp_var.
    cbn.
    set (nat_εε := disp_nat_trans_ax εε ff).
    cbn in nat_εε. rewrite nat_εε.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite 3 transport_f_f.
    apply maponpaths_2, homset_property.
  Defined.

  Lemma homset_conj'_natural_precomp {c : C} {c' : C'} {f : C'⟦F c, c'⟧} {c'' : C}
        {k : C⟦c'', c⟧} {d : D c} {d' : D' c'} {d'' : D c''}
        (ff : FF _ d -->[f] d') (kk : d'' -->[k] d) :
    homset_conj' _ _ _ (# FF kk ;; ff) =
    transportb _ (φ_adj_natural_precomp A _ _ f _ k) (kk ;; homset_conj' _ _ _ ff).
  Proof.
    unfold homset_conj'.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite 2 assoc_disp.
    cbn.
    set (nat_ηη := disp_nat_trans_ax_var ηη kk).
    cbn in nat_ηη. rewrite nat_ηη.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite 3 transport_f_f.
    apply maponpaths_2, homset_property.
  Defined.

  Lemma homset_conj'_natural_postcomp {c : C} {c' : C'} {f : C'⟦F c, c'⟧} {c'' : C'}
        {k : C'⟦c', c''⟧} {d : D c} {d' : D' c'} {d'' : D' c''}
        (ff : FF _ d -->[f] d') (kk : d' -->[k] d'') :
    homset_conj' _ _ _ (ff ;; kk) =
    transportb _ (φ_adj_natural_postcomp A _ _ f _ k) (homset_conj' _ _ _ ff ;; # GG kk).
  Proof.
    unfold homset_conj'.
    rewrite disp_functor_comp.
    rewrite assoc_disp_var.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    apply maponpaths_2, homset_property.
  Defined.

  Lemma homset_conj_inv_after_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧)(d : D c) (d' : D' c')
        (beta : FF _ d -->[f] d') :
    transportf _ (φ_adj_inv_after_φ_adj A f)
     (homset_conj_inv _ _ _ (homset_conj' f d d' beta)) = beta.
  Proof.
    unfold homset_conj'.
    cbn.
    set (eq := homset_conj_inv_natural_postcomp (ηη c d) beta).
    cbn in eq. rewrite eq.
    unfold homset_conj_inv.
    cbn.
    rewrite transport_f_b.
    (* Note : there should probably be an accessor function for this *)
    assert (triangle1 : # FF (ηη c d);; εε (F c) (FF c d) =
                        transportb _ (triangle_id_left_ad A c ) (id_disp _))
      by (exact ((pr1 (pr2 X)) c d)).
    cbn in triangle1.
    rewrite triangle1.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    intermediate_path (transportf _ (idpath _) beta).
    - apply maponpaths_2, homset_property.
    - apply idpath.
  Defined.

  Lemma homset_conj'_after_conj_inv {c : C} {c' : C'} {g : C⟦c, G c'⟧} {d : D c} (d' : D' c')
        (alpha : d -->[g] GG _ d') :
    transportf _ (φ_adj_after_φ_adj_inv A g)
     (homset_conj' _ _ _ (homset_conj_inv g d d' alpha)) = alpha.
    unfold homset_conj_inv.
    cbn.
    set (eq := homset_conj'_natural_precomp (εε c' d') alpha).
    cbn in eq. rewrite eq.
    unfold homset_conj'.
    cbn.
    rewrite transport_f_b.
    assert (triangle2 : (ηη (G c') (GG c' d');; # GG (εε c' d')) =
       transportb _ (triangle_id_right_ad A c') (id_disp _)) by (exact (pr2 (pr2 X) c' d')).
    cbn in triangle2.
    rewrite triangle2.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite id_right_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    intermediate_path (transportf _ (idpath _ ) alpha).
    - apply maponpaths_2, homset_property.
    - apply idpath.
  Defined.

  Close Scope mor_disp.

  (** * homset_conj_inv and homset_conj' are weak equivalences. *)

  Lemma homset_conj_after_conj_inv {c : C} {c' : C'} {g : C⟦c, G c'⟧} {d : D c} (d' : D' c')
        (alpha : d -->[g] GG _ d') :
    homset_conj _ _ _ (homset_conj_inv _ _ _ alpha) = alpha.
  Proof.
    apply homset_conj'_after_conj_inv.
  Defined.

  Lemma homset_conj_inv_after_conj {c : C} {c' : C'} {g : C⟦c, G c'⟧} (d : D c) {d' : D' c'}
        (beta : FF _ d -->[#F g · ε _] d') :
    homset_conj_inv _ _ _ (homset_conj _ _ _ beta) = beta.
  Proof.
    unfold homset_conj.
    rewrite <- homset_conj_inv_after_conj'.
    unfold homset_conj_inv.
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_postwhisker.
    apply maponpaths_2, homset_property.
  Defined.

  Lemma homset_conj'_inv_after_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧)(d : D c) (d' : D' c')
        (beta : FF _ d -->[f] d') :
    homset_conj'_inv _ _ _ (homset_conj' _ _ _ beta) = beta.
  Proof.
    apply homset_conj_inv_after_conj'.
  Defined.

  Lemma homset_conj'_after_conj'_inv {c : C} {c' : C'} (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c')
        (alpha : d -->[η _ · #G f] GG _ d') :
    homset_conj' _ _ _ (homset_conj'_inv _ _ _ alpha) = alpha.
  Proof.
    unfold homset_conj', homset_conj'_inv.
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_prewhisker.
    rewrite <- homset_conj'_after_conj_inv.
    apply maponpaths_2, homset_property.
  Defined.

  Lemma dispadjunction_hom_weq (c : C) (c' : C') (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') ≃ (FF _ d -->[# F g · ε _] d').
  Proof.
    exists (homset_conj_inv _ _ _).
    apply (gradth _ (homset_conj _ _ _)).
    - apply homset_conj_after_conj_inv.
    - apply homset_conj_inv_after_conj.
  Defined.

  Lemma dispadjunction_hom_weq' (c : C) (c' : C') (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c') :
       (FF _ d -->[f] d') ≃ (d -->[η _ · # G f] GG _ d').
  Proof.
    exists (homset_conj' _ _ _).
    apply (gradth _ (homset_conj'_inv _ _ _)).
    - apply homset_conj'_inv_after_conj'.
    - apply homset_conj'_after_conj'_inv.
  Defined.

End DispHomSetIso_from_Adjunction.

(** * The right adjoint functor of a displayed adjunction preserves cartesian morphisms. *)

Lemma right_over_adj_preserves_cartesianness : is_cartesian_disp_functor GG.
Proof.
  unfold is_cartesian_disp_functor.
  intros c c' f d d' ff ff_cart.
  intros c'' g d'' h.
  set (eq := φ_adj_inv_natural_postcomp A _ _ g _ f
           : # F (g · # G f) · ε c = # F g · (ε c') · f).
  Open Scope mor_disp.
  apply (@iscontrweqb _ (∑ gg, (gg;; ff) = transportf _ eq (homset_conj_inv _ _ _ h))).
  - apply (weqbandf (dispadjunction_hom_weq _ _ g _ _)).
    intro gg.
    cbn.
    set (eq2 := homset_conj_inv_natural_postcomp gg ff).
    cbn in eq2.
    apply weqimplimpl.
    + intro p.
      rewrite <- p.
      rewrite eq2.
      rewrite transport_f_b.
      intermediate_path (transportf _ (idpath _ ) (# FF gg;; εε c' d';; ff)).
      * apply idpath.
      * apply maponpaths_2, homset_property.
    + intro p.
      set (equiv1 := homset_conj'_after_conj_inv _ h).
      set (equiv2 := homset_conj'_after_conj_inv _ (gg;; # GG ff)).
      unfold homset_conj' in equiv1, equiv2.
      rewrite <- equiv1.
      rewrite <- equiv2.
      rewrite eq2.
      rewrite p.
      rewrite transport_b_f.
      rewrite disp_functor_transportf.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      apply maponpaths_2, homset_property.
    + apply homsets_disp.
    + apply homsets_disp.
  - apply ff_cart.
Defined.

End fix_disp_adjunction.
