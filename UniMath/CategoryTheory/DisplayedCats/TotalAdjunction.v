(*
In this file, we show how any displayed adjunction (resp. equivalence) induces an adjunction (resp. equivalence) between the corresponding total categories.
Created by Kobe Wullaert at 06/12/2022.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Local Open Scope mor_disp_scope.
Local Open Scope type_scope.
Local Open Scope cat.


Section TotalFunctorCompositeIdentity.

  Definition total_functor_identity_inv
             {C : category} (D : disp_cat C)
    : nat_trans (total_functor (disp_functor_identity D))
                (functor_identity (total_category D)).
  Proof.
    apply nat_trans_id.
  Defined.

  Context {C1 C2 C3 : category}
          {F : functor C1 C2} {G : functor C2 C3}
          {D1 : disp_cat C1} {D2 : disp_cat C2} {D3 : disp_cat C3}
          (FF : disp_functor F D1 D2) (GG : disp_functor G D2 D3).

  Definition total_functor_comp_inv
    : nat_trans (total_functor (disp_functor_composite FF GG))
                (total_functor FF ∙ total_functor GG).
  Proof.
    apply nat_trans_id.
  Defined.

End TotalFunctorCompositeIdentity.

Section TotalAdjunction.

  Context {C1 C2 : category}
          {F : adjunction C1 C2}.

  Let L := left_functor F.
  Let R := right_functor F.
  Let η := adjunit F.
  Let ε := adjcounit F.

  Context {D1 : disp_cat C1} {D2 : disp_cat C2}
          (FF : disp_adjunction F D1 D2).

  Let LL := left_adj_over FF.
  Let RR := right_adj_over FF.
  Let ηη := unit_over FF.
  Let εε := counit_over FF.

  Definition total_adjunction_data
    : adjunction_data (total_category D1) (total_category D2).
  Proof.
    use make_adjunction_data.
    - exact (total_functor LL).
    - exact (total_functor RR).
    - use (nat_trans_comp _ _ _ (total_functor_identity D1)).
      use (nat_trans_comp _ _ _ _ (total_functor_comp_inv _ _)).
      use total_nat_trans.
      + exact η.
      + exact ηη.
    - use (nat_trans_comp _ _ _ (total_functor_comp _ _)).
      use (nat_trans_comp _ _ _ _ (total_functor_identity_inv _)).
      use total_nat_trans.
      + exact ε.
      + exact εε.
  Defined.

  Definition total_adjunction_triangle1
    : triangle_1_statement total_adjunction_data.
  Proof.
    intro x.
    use total2_paths_b.
    - cbn.
      etrans. {
        apply maponpaths.
        etrans. { apply id_left. }
        apply id_right.
      }
      etrans. {
        apply maponpaths_2.
        apply maponpaths.
        etrans. { apply id_left. }
        apply id_right.
      }
      exact (triangle_1_statement_from_adjunction F (pr1 x)).
    - cbn.
      set (t := triangle_1_over FF (pr1 x) (pr2 x)).
      unfold triangle_1_statement_over in t.
      cbn in t.

      set (a1_goal := (id_disp (pr2 x) ;; (ηη (pr1 x) (pr2 x) ;; id_disp
                                                                   (RR (left_functor F (pr1 x)) (LL (pr1 x) (pr2 x)))))).
      set (a1_t :=  (unit_over FF (pr1 x) (pr2 x))).

      assert (p : a1_goal = transportb _   (id_left (η (pr1 x) · identity (right_functor F (left_functor F (pr1 x)))) @ id_right (η (pr1 x))) a1_t).
      {
        unfold a1_goal.
        rewrite id_right_disp.
        rewrite id_left_disp.
        now rewrite transport_b_b.
      }

      etrans. {
        apply maponpaths_2, maponpaths.
        exact p.
      }
      clear p.

      set (a2_t :=  counit_over FF (left_functor F (pr1 x)) (left_adj_over FF (pr1 x) (pr2 x))).
      set (a2_goal := (id_disp (LL (right_functor F (left_functor F (pr1 x)))
                                   (RR (left_functor F (pr1 x)) (LL (pr1 x) (pr2 x)))) ;;
                       (εε (left_functor F (pr1 x)) (LL (pr1 x) (pr2 x)) ;; id_disp (LL (pr1 x) (pr2 x))))).

      assert (p : a2_goal = transportb _  (id_left (ε (left_functor F (pr1 x)) · identity (left_functor F (pr1 x))) @ id_right (ε (left_functor F (pr1 x)))) a2_t).
      {
        unfold a2_goal.
        rewrite id_right_disp.
        rewrite id_left_disp.
        now rewrite transport_b_b.
      }

      etrans. {
        apply maponpaths.
        exact p.
      }
      clear p.

      assert (q : (# (left_functor F))
   (identity (pr1 x) · (η (pr1 x) · identity (right_functor F (left_functor F (pr1 x)))))
 · (identity (left_functor F (right_functor F (left_functor F (pr1 x))))
    · (ε (left_functor F (pr1 x)) · identity (left_functor F (pr1 x)))) =
                    (# (left_functor F)) (adjunit F (pr1 x)) · adjcounit F (left_functor F (pr1 x))).
      {
        rewrite ! id_left.
        now rewrite ! id_right.
      }

      use pathscomp0.
      {
        exact (transportb _ q  (♯ (left_adj_over FF) (unit_over FF (pr1 x) (pr2 x)) ;; counit_over FF (left_functor F (pr1 x)) (left_adj_over FF (pr1 x) (pr2 x)))).
      }

      +  cbn.
         etrans. { apply mor_disp_transportf_prewhisker. }

         assert (hh : (# (left_functor F))
   (identity (pr1 x) · (η (pr1 x) · identity (right_functor F (left_functor F (pr1 x)))))
 · ε (left_functor F (pr1 x)) =
                        (# (left_functor F))%Cat (adjunit F (pr1 x)) · adjcounit F (left_functor F (pr1 x))).
         {
           apply maponpaths_2.
           apply maponpaths.
           refine (id_left _ @ _).
           apply id_right.
         }

         assert (h : (maponpaths
       (compose
          ((# (left_functor F))
             (identity (pr1 x) · (η (pr1 x) · identity (right_functor F (left_functor F (pr1 x)))))))
       (! (id_left (ε (left_functor F (pr1 x)) · identity (left_functor F (pr1 x))) @
                   id_right (ε (left_functor F (pr1 x)))))) = hh @ ! q).
         {
           apply homset_property.
         }

         etrans. {
           apply maponpaths_2.
           exact h.
         }
         unfold a2_t.
         unfold transportb.
         use transportf_transpose_left.
         unfold transportb.
         rewrite transport_f_f.
         do 2 rewrite pathscomp_inv.
         rewrite path_assoc.
         rewrite pathsinv0r.
         simpl.
         rewrite disp_functor_transportf.
         use transportf_transpose_right.
         unfold transportb.
         unfold a1_t.
         rewrite mor_disp_transportf_postwhisker.
         rewrite transport_f_f.
         use transportf_set.
         apply homset_property.
      + cbn.
        etrans. {
          apply maponpaths.
          exact t.
        }
        unfold transportb.
        rewrite transport_f_f.
        use transportf_paths.
        apply homset_property.
  Qed.

  Definition total_adjunction_triangle2
    : triangle_2_statement total_adjunction_data.
  Proof.
    intro x.
    use total2_paths_b.
    - cbn.
      etrans. {
        do 2 apply maponpaths.
        etrans. { apply id_left. }
        apply id_right.
      }

      etrans. {
        apply maponpaths_2.
        etrans. { apply id_left. }
        apply id_right.
      }
      exact (triangle_2_statement_from_adjunction F (pr1 x)).
    - cbn.
      set (t := triangle_2_over FF (pr1 x) (pr2 x)).
      unfold triangle_2_statement_over in t.
      cbn in t.

      set (q := (id_left (ε (pr1 x) · identity (pr1 x)) @ id_right (ε (pr1 x)))).

      assert (p : (id_disp (LL (right_functor F (pr1 x)) (RR (pr1 x) (pr2 x))) ;; (εε (pr1 x) (pr2 x) ;; id_disp (pr2 x))) = transportb _ q (counit_over FF (pr1 x) (pr2 x))).
      {
        rewrite id_right_disp.
        rewrite id_left_disp.
        now rewrite transport_b_b.
      }

      etrans. {
        do 2 apply maponpaths.
        exact p.
      }
      clear p.
      unfold q.
      clear q.

      assert (p : identity (right_functor F (pr1 x))
 · (η (right_functor F (pr1 x)) · identity (right_functor F (left_functor F (right_functor F (pr1 x)))))
 · (# (right_functor F))%Cat
     (identity (left_functor F (right_functor F (pr1 x))) · (ε (pr1 x) · identity (pr1 x))) =
 unit_from_are_adjoints F (right_functor F (pr1 x))
                        · (# (right_functor F))%Cat (counit_from_are_adjoints F (pr1 x))).
      {
        rewrite ! id_left.
        now rewrite ! id_right.
      }

      use pathscomp0.
      {
        exact (transportb _ p (transportb (mor_disp (right_adj_over FF (pr1 x) (pr2 x)) (right_adj_over FF (pr1 x) (pr2 x))) (triangle_id_right_ad F (pr1 x)) (id_disp (right_adj_over FF (pr1 x) (pr2 x))))).
      }

      2: {
        cbn.
        rewrite transport_b_b.
        apply maponpaths_2.
        apply homset_property.
      }
      cbn.
      rewrite transport_b_b.
      unfold transportb.
      rewrite disp_functor_transportf.
      rewrite mor_disp_transportf_prewhisker.
      use transportf_transpose_left.
      unfold transportb.
      rewrite transport_f_f.

      assert (qq : identity (right_functor F (pr1 x))
 · (adjunit F (right_functor F (pr1 x))
    · identity (right_functor F (left_functor F (right_functor F (pr1 x)))))
 · (# (right_functor F))%Cat (adjcounit F (pr1 x)) =
                    adjunit F (right_functor F (pr1 x)) · (# (right_functor F))%Cat (adjcounit F (pr1 x))).
      {
        rewrite ! id_left.
        now rewrite ! id_right.
      }


      assert (q :  id_disp (RR (pr1 x) (pr2 x)) ;; (ηη (right_functor F (pr1 x)) (RR (pr1 x) (pr2 x)) ;; id_disp (RR (left_functor F (right_functor F (pr1 x))) (LL (right_functor F (pr1 x)) (RR (pr1 x) (pr2 x))))) ;; ♯ RR (counit_over FF (pr1 x) (pr2 x)) = transportb _ qq ( unit_over FF (right_functor F (pr1 x)) (right_adj_over FF (pr1 x) (pr2 x)) ;; ♯ (right_adj_over FF) (counit_over FF (pr1 x) (pr2 x)))).
      {
        rewrite id_left_disp.
        rewrite id_right_disp.
        rewrite transport_b_b.
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        apply maponpaths_2.
        apply homset_property.
      }

      refine (q @ _).
      etrans. {
        apply maponpaths.
        exact t.
      }
      rewrite transport_b_b.
      unfold transportb.
      use maponpaths_2.
      apply homset_property.
  Qed.

  Definition total_adjunction
    : adjunction (total_category D1) (total_category D2).
  Proof.
    use make_adjunction.
    - exact total_adjunction_data.
    - split.
      + apply total_adjunction_triangle1.
      + apply total_adjunction_triangle2.
  Defined.

End TotalAdjunction.

Section TotalEquivalence.

  Context {C1 C2 : category}
          {F : adj_equiv C1 C2}.

  Let L := left_functor F.
  Let R := right_functor F.
  Let η := adjunit F.
  Let ε := adjcounit F.

  Context {D1 : disp_cat C1}
          {D2 : disp_cat C2}
          (FF : equiv_over F D1 D2).

  Let LL := left_adj_over FF.
  Let RR := right_adj_over FF.
  Let ηη := unit_over FF.
  Let εε := counit_over FF.

  Definition total_adjunction_forms_equivalence1_base
    : ∏ x : total_category D1, is_z_isomorphism (pr1 (adjunit (total_adjunction FF) x)).
  Proof.
    intro x.
    use is_z_iso_comp_of_is_z_isos.
    - apply Isos.identity_is_z_iso.
    - use Isos.is_z_iso_comp_of_is_z_isos.
      + apply (adj_equiv_of_cats_from_adj F).
      + apply Isos.identity_is_z_iso.
  Defined.

  Definition total_adjunction_forms_equivalence1_disp_inv
    : ∏ x : total_category D1,
        RR (F (pr1 x)) (LL (pr1 x) (pr2 x))
           -->[identity (R (F (pr1 x))) · is_z_isomorphism_mor ((pr122 F) (pr1 x)) · identity (pr1 x)]
           pr2 x.
  Proof.
    intro x.
    set (f := pr1 (pr12 FF (pr1 x) (pr2 x))).
    assert (p : identity (right_adjoint F (F (pr1 x))) · Isos.is_z_isomorphism_mor ((pr122 F) (pr1 x)) · identity (pr1 x) = Isos.is_z_isomorphism_mor ((pr122 F) (pr1 x))).
    {
      rewrite id_left.
      now apply id_right.
    }
    exact (transportf (mor_disp _ _) (! p) f).
  Defined.

  Lemma total_adjunction_forms_equivalence1_disp_inv_is_inv
    : ∏ x : total_category D1,
        is_disp_inverse
          (z_iso_is_inverse_in_precat
             (pr1 (adjunit (total_adjunction FF) x),, total_adjunction_forms_equivalence1_base x))
          (pr2 (adjunit (total_adjunction FF) x))
          (total_adjunction_forms_equivalence1_disp_inv x).
  Proof.
    unfold total_adjunction_forms_equivalence1_base.
    unfold total_adjunction_forms_equivalence1_disp_inv.
    split.
    - cbn.
      use transportf_transpose_right.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      cbn.

      set (ff := pr12 (pr12 FF (pr1 x) (pr2 x))).
      cbn in ff.
      set (fff := transportf_transpose_left ff).
      refine (_ @ fff).
      use transportf_transpose_right.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_right_disp.
      rewrite id_left_disp.
      rewrite transport_b_b.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      use transportf_set.
      apply homset_property.
    - cbn.
      use transportf_transpose_right.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      cbn.

      set (ff := pr22 (pr12 FF (pr1 x) (pr2 x))).
      cbn in ff.
      set (fff := transportf_transpose_left ff).
      refine (_ @ fff).
      use transportf_transpose_right.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_right_disp.
      rewrite id_left_disp.
      rewrite transport_b_b.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      use transportf_set.
      apply homset_property.
  Qed.

  Definition total_adjunction_forms_equivalence1
    : ∏ a : total_category D1, Isos.is_z_isomorphism (adjunit (total_adjunction FF) a).
  Proof.
    intro x.
    use is_z_iso_total.
    - exact (total_adjunction_forms_equivalence1_base x).
    - exists (total_adjunction_forms_equivalence1_disp_inv x).
      exact (total_adjunction_forms_equivalence1_disp_inv_is_inv x).
  Defined.

  Definition total_adjunction_forms_equivalence2_base
    :  ∏ b : total_category D2, Isos.is_z_isomorphism (pr1 (adjcounit (total_adjunction FF) b)).
  Proof.
    intro.
    use Isos.is_z_iso_comp_of_is_z_isos.
    - apply Isos.identity_is_z_iso.
    - use Isos.is_z_iso_comp_of_is_z_isos.
      + apply (adj_equiv_of_cats_from_adj F).
      + apply Isos.identity_is_z_iso.
  Defined.

  Definition total_adjunction_forms_equivalence2_disp_inv
    : ∏ x : total_category D2,
          pr2 (functor_identity (total_category D2) x) -->[
  inv_from_z_iso (pr1 (adjcounit (total_adjunction FF) x),, total_adjunction_forms_equivalence2_base x)]
              pr2 ((pr121 (total_adjunction FF) ∙ pr11 (total_adjunction FF)) x).
  Proof.
    intro x.
    set (f := pr1 (pr22 FF (pr1 x) (pr2 x))).
    cbn.
    assert (p :  identity (pr1 x) · Isos.is_z_isomorphism_mor ((pr222 F) (pr1 x))
                          · identity (F (right_adjoint F (pr1 x))) = Isos.is_z_isomorphism_mor ((pr222 F) (pr1 x))).
    {
      rewrite id_left.
      now apply id_right.
    }
    exact (transportf (mor_disp _ _) (! p) f).
  Defined.

  Lemma total_adjunction_forms_equivalence2_disp_inv_is_inv
    : ∏ x : total_category D2,
         is_disp_inverse
           (z_iso_is_inverse_in_precat
              (pr1 (adjcounit (total_adjunction FF) x),, total_adjunction_forms_equivalence2_base x))
           (pr2 (adjcounit (total_adjunction FF) x))
           (total_adjunction_forms_equivalence2_disp_inv x).
  Proof.
    unfold total_adjunction_forms_equivalence2_base.
    unfold total_adjunction_forms_equivalence2_disp_inv.
    split.
    - cbn.
      use transportf_transpose_right.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      cbn.

      set (ff := pr12 (pr22 FF (pr1 x) (pr2 x))).
      cbn in ff.
      set (fff := transportf_transpose_left ff).
      refine (_ @ fff).
      use transportf_transpose_right.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_right_disp.
      rewrite id_left_disp.
      rewrite transport_b_b.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      use transportf_set.
      apply homset_property.
    - cbn.
      use transportf_transpose_right.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      cbn.

      set (ff := pr22 (pr22 FF (pr1 x) (pr2 x))).
      cbn in ff.
      set (fff := transportf_transpose_left ff).
      refine (_ @ fff).
      use transportf_transpose_right.
      unfold transportb.
      rewrite transport_f_f.
      rewrite id_right_disp.
      rewrite id_left_disp.
      rewrite transport_b_b.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      use transportf_set.
      apply homset_property.
  Qed.

  Definition total_adjunction_forms_equivalence2
    :  ∏ b : total_category D2, Isos.is_z_isomorphism (adjcounit (total_adjunction FF) b).
  Proof.
    intro x.
    use is_z_iso_total.
    - exact (total_adjunction_forms_equivalence2_base x).
    - exists (total_adjunction_forms_equivalence2_disp_inv x).
      exact (total_adjunction_forms_equivalence2_disp_inv_is_inv x).
  Defined.

  Definition total_adjunction_forms_equivalence
    : forms_equivalence (total_adjunction FF).
  Proof.
    split.
    - exact total_adjunction_forms_equivalence1.
    - exact total_adjunction_forms_equivalence2.
  Defined.

  Definition total_adj_equivalence_of_cats
    : adj_equivalence_of_cats (total_functor LL).
  Proof.
    exists (total_adjunction FF).
    exact total_adjunction_forms_equivalence.
  Defined.

  Definition total_equivalence
    : adj_equiv (total_category D1) (total_category D2).
  Proof.
    exists (left_functor (total_adjunction FF)).
    exact total_adj_equivalence_of_cats.
  Defined.

End TotalEquivalence.
