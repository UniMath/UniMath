Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerCategories.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerFunctors.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.Transformations.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerIsos.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerUnivalence.

Local Open Scope cat.

Local Lemma equality_on_objects_from_functor_equality
      {C D : category}
      (F G : functor_data C D)
      (p : ∏ c: C, F c = G c)
      (q : transportf (λ F : C → D, ∏ a b : C, C ⟦ a, b ⟧ → D ⟦ F a, F b ⟧)
   (funextsec (λ _ : C, D) (pr1 F) (pr1 G) (λ x : C, p x)) (pr2 F) = pr2 G)
  : ∏ c : C,
      toforallpaths (λ _ : C, D) F G
    (base_paths F G
       (total2_paths_f ((funextsec (λ _ : C, D) (pr1 F) (pr1 G) (λ x : C, p x)))
                       q)) c = p c.
Proof.
  intro c.
  rewrite base_total2_paths.
  now rewrite toforallpaths_funextsec.
Qed.

Local Definition functor_eq_eq_from_functor_ob_eq'
             (C C': category)
             (F G : functor C C') (p q : pr1 F = pr1 G)
             (H : (base_paths _ _  p) =
                    (base_paths _ _ q)) :
    p = q.
Proof.
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )); simpl.
  use total2_paths_f.
  + exact H.
  + apply uip.
    do 2 (apply impred_isaset ; intro).
    apply funspace_isaset.
    apply C'.
Defined.

(* To be moved inside DaggerUnivalence *)
Local Lemma idtodaggeriso_is_idtoiso {C : category} (dagC : dagger C)
      {x y : C} (p : x = y)
  : pr1 (idtodaggeriso dagC x y p) = (* pr1 (Univalence.idtoiso p). *) dagC y x (pr1 (idtodaggeriso dagC y x (! p))).
Proof.
  induction p.
  apply pathsinv0, dagger_to_law_id.
Qed.

Local Lemma idtodaggeriso_is_idtoiso_idpath {C : category} (dagC : dagger C)
      (x : C)
  : pr1 (idtodaggeriso dagC x x (idpath x))
    = identity x.
Proof.
  apply idpath.
Qed.

Local Lemma idtoiso_of_pathsinv_is_dagger_of_idtoiso {C : category} (dagC : dagger C)
      {x y : C} (p : x = y)
  : pr1 (Univalence.idtoiso (! p)) = dagC x y (pr1 (Univalence.idtoiso p)).
Proof.
  induction p.
  apply pathsinv0, dagger_to_law_id.
Qed.

Local Lemma equality_of_composition
      {C : category} {x y z : C} (f1 f2 : C⟦x,y⟧) (g1 g2 : C⟦y,z⟧)
  : f1 = f2 -> g1 = g2 -> f1 · g1 = f2 · g2.
Proof.
  intros p q.
  induction p ; induction q.
  apply idpath.
Qed.

Section DaggerFunctorCategories.

  Context {C D : category}
          (dagC : dagger C) (dagD : dagger D).

  Definition dagger_functor_disp_cat
    : disp_cat (functor_category C D)
    := disp_full_sub [C,D] (λ F, is_dagger_functor dagC dagD F).

  Definition dagger_functor_cat
    : category
    := total_category dagger_functor_disp_cat.

  Definition make_dagger_functor
             {F : functor C D}
             (dagF : is_dagger_functor dagC dagD F)
    : dagger_functor_cat
    := F ,, dagF.

  Definition make_dagger_transformation
             (F G : dagger_functor_cat)
             (α : nat_trans (pr1 F : functor _ _) (pr1 G : functor _ _))
    : dagger_functor_cat⟦F,G⟧
    := α ,, tt.

  Definition dagger_functor_cat_structure
    : dagger_structure dagger_functor_cat
    := λ F G α, make_dagger_transformation _ _ (dagger_adjoint (pr2 F) (pr2 G) (pr1 α)).

  Lemma dagger_transformation_equality
        {F G : functor C D}
        {dagF : is_dagger_functor dagC dagD F}
        {dagG : is_dagger_functor dagC dagD G}
        (α β : dagger_functor_cat⟦make_dagger_functor dagF , make_dagger_functor dagG⟧)
    : (∏ x : C, pr11 α x = pr11 β x) -> α = β.
  Proof.
    intro p.
    use total2_paths_f.
    2: apply isapropunit.
    apply (nat_trans_eq D).
    exact p.
  Qed.

  Lemma dagger_functor_cat_laws
    : dagger_laws dagger_functor_cat_structure.
  Proof.
    (*use make_dagger_laws*) repeat split ;
      (intro ; intros ; apply dagger_transformation_equality ; intro).
    - apply dagger_to_law_id.
    - apply dagger_to_law_comp.
    - apply dagger_to_law_idemp.
  Qed.

  Definition dagger_on_functor_cat : dagger dagger_functor_cat
    := _ ,, dagger_functor_cat_laws.

End DaggerFunctorCategories.

Section Univalence.

  Context {C D : category}
          {dagC : dagger C} {dagD : dagger D}
          {F G : functor C D}
          (dagF : is_dagger_functor dagC dagD F)
          (dagG : is_dagger_functor dagC dagD G).

  Local Definition unitary_functors
    : UU
    := ∑ α : nat_trans F G,
        (∏ x : C, Isos.is_inverse_in_precat (α x) (dagD _ _ (α x))).

  Local Definition unitary_functors_eq
    : UU
    := ∑ p : (∏ x : pr11 C, unitary dagD (F x) (G x)),
        ∏ (x y : C) (f : C⟦x,y⟧),
        #G f = (dagD _ _ (pr1 (p x))) · #F f · (pr1 (p y)).

  Local Definition functors_eq_data
    : UU
    := ∑ p : (∏ x : C, (pr11 F x) = (pr11 G x)),
        ∏ (x y : pr11 C) (f : (pr11 C)⟦x,y⟧),
        #G f = pr1 (idtodaggeriso dagD _ _ (! p x)) · #F f · pr1 (idtodaggeriso dagD _ _ (p y)).

  Definition unitary_functors_equiv_unitary
    : unitary_functors ≃ unitary (dagger_functor_cat_structure dagC dagD) (F,,dagF) (G,,dagG).
  Proof.
    use weq_iso.
    - intro α.
      exists (make_dagger_transformation dagC dagD _ _ (pr1 α : nat_trans (pr1 (F,,dagF)) (pr1 (G,,dagG)))).
      split ; apply dagger_transformation_equality ; intro c ; apply (pr2 α c).
    - intro α.
      exists (pr11 α).
      intro c.
      split.
      + exact (toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ (pr12 α))) c).
      + exact (toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ (pr22 α))) c).
    - intro α.
      use total2_paths_f.
      + use (nat_trans_eq (pr2 D)).
        intro ; apply idpath.
      + use proofirrelevance.
        apply impred_isaprop ; intro.
        apply Isos.isaprop_is_inverse_in_precat.
    - intro α.
      use total2_paths_f.
      + apply dagger_transformation_equality.
        intro ; apply idpath.
      + apply isaprop_is_unitary.
  Defined.

  Definition unitary_functors_eq_equiv_unitary_functors
    : unitary_functors_eq ≃ unitary_functors.
  Proof.
    use weq_iso.
    - intros [p q].
      use tpair.
      + apply (make_nat_trans _ _ (λ c, pr1 (p c))).
        intros c1 c2 f.
        apply pathsinv0.
        etrans.
        1: apply maponpaths, q.
        etrans.
        1: apply assoc.
        apply maponpaths_2.
        etrans.
        1: apply assoc.
        refine (_ @ id_left _).
        apply maponpaths_2, p.
      + intro ; apply p.
    - intros [α p].
      use tpair.
      + intro c.
        exists (α c).
        apply p.
      + intros c1 c2 f.
        apply pathsinv0.
        etrans.
        1: apply assoc'.
        etrans.
        1: apply maponpaths, (pr2 α).
        etrans.
        1: apply assoc.
        refine (_ @ id_left _).
        apply maponpaths_2, p.
    - intro.
      use total2_paths_f.
      + apply idpath.
      + repeat (apply funextsec ; intro).
        apply homset_property.
    - intro.
      use total2_paths_f.
      + use (nat_trans_eq (pr2 D)).
        intro ; apply idpath.
      + apply funextsec ; intro.
        apply Isos.isaprop_is_inverse_in_precat.
  Defined.

  Definition functors_eq_data_equiv_unitary_functors_eq
             (u : is_univalent_dagger dagD)
    : functors_eq_data ≃ unitary_functors_eq.
  Proof.
    use weq_iso.
    - intro p.
      exists (λ c, idtodaggeriso dagD _ _ (pr1 p c)).
      intros x y f.
      refine (pr2 p x y f @ _).
      do 2 apply maponpaths_2.
      etrans.
      1: apply (idtodaggeriso_is_idtoiso dagD).
      do 3 apply maponpaths.
      apply pathsinv0inv0.
    - intros p.
      use tpair.
      + intro c ; apply u ; exact (pr1 p c).
      + intros x y f.
        refine (pr2 p x y f @ _).
        apply equality_of_composition.
        * apply maponpaths_2.
          cbn.
          etrans.
          2: apply pathsinv0, (idtodaggeriso_is_idtoiso dagD).
          do 2 apply maponpaths.
          etrans.
          1: apply pathsinv0, (idtodaggeriso_daggerisotoid u).
          apply maponpaths.
          apply pathsinv0, pathsinv0inv0.
        * cbn.
          apply maponpaths.
          apply pathsinv0, idtodaggeriso_daggerisotoid.
    - intro p.
      use total2_paths_f.
      + apply funextsec ; intro.
        apply daggerisotoid_idtodaggeriso.
      + repeat (apply funextsec ; intro).
        apply homset_property.
    - intro p.
      use total2_paths_f.
      + apply funextsec ; intro.
        use total2_paths_f.
        * apply maponpaths, idtodaggeriso_daggerisotoid.
        * apply isaprop_is_unitary.
      + repeat (apply funextsec ; intro).
        apply homset_property.
  Defined.

  Lemma transport_of_dagger_functor_map_is_pointwise
        (F0 G0 : pr11 C -> pr11 D)
        (F1 : ∏ a b : pr11 C, a --> b -> F0 a --> F0 b)
        (gamma : F0  = G0 )
        (a b : pr11 C) (f : a --> b) :
    transportf (fun x : pr11 C -> pr11 D =>
                  ∏ a0 b0 : pr11 C, a0 --> b0 -> x a0 --> x b0)
               gamma F1 a b f =
      Univalence.double_transport (toforallpaths (λ _ : pr11 C, pr11 D) F0 G0 gamma a)
                       (toforallpaths (λ _ : pr11 C, pr11 D) F0 G0 gamma b)
                       (F1 a b f).
  Proof.
    induction gamma.
    apply idpath.
  Qed.

  Lemma double_transport_idtodaggeriso (a a' b b' : pr111 D)
        (p : a = a') (q : b = b')  (f : a --> b) :
    Univalence.double_transport p q f = pr1 (idtodaggeriso dagD _ _ (! p)) · f · pr1 (idtodaggeriso dagD _ _ q).
  Proof.
    destruct p.
    destruct q.
    intermediate_path (identity _ · f).
    - apply pathsinv0; apply id_left.
    - apply pathsinv0; apply id_right.
  Defined.

    Definition equality_equiv_functors_eq_data
    : pr1 F = pr1 G ≃ functors_eq_data.
  Proof.
    use weq_iso.
    - intro p.
      exists (λ c, toforallpaths _ _ _ (base_paths _ _ p) c).
      abstract (
          intros x y f ;
          refine (! toforallpaths _ _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ (fiber_paths p) x) y) f @ _) ;
          etrans ; [
              apply transport_of_dagger_functor_map_is_pointwise
          | apply double_transport_idtodaggeriso]
        ).
    - intros [p q].
      use total2_paths_f.
      + apply funextsec ; intro ; apply p.
      + abstract(
            repeat (apply funextsec ; intro) ;
            rewrite transport_of_dagger_functor_map_is_pointwise ;
            rewrite double_transport_idtodaggeriso ;
            rewrite toforallpaths_funextsec ;
            exact (! q _ _ _)
          ).
    - intro.
      cbn.
      apply functor_eq_eq_from_functor_ob_eq'.
      etrans.
      1: apply base_total2_paths.
      apply (invmaponpathsweq (weqtoforallpaths _ _ _ )).
      simpl.
      rewrite toforallpaths_funextsec.
      apply funextsec; intro ; apply idpath.
    - intros [p q].
      use total2_paths_f.
      2: {
        apply proofirrelevance.
        do 3 (apply impred_isaprop ; intro).
        apply homset_property.
      }
      apply funextsec ; intro.
      apply equality_on_objects_from_functor_equality.
  Defined.

  Local Definition id_pr1_to_pr11_id
    : F = G ≃ pr1 F = pr1 G.
  Proof.
    use subtypeInjectivity.
    intro.
    apply isaprop_is_functor.
    apply (pr2 D).
  Defined.

  Local Definition id_to_pr1_id
    : (F,,dagF) = (G,,dagG) ≃ F = G.
  Proof.
    use subtypeInjectivity.
    intro.
    apply isaprop_is_dagger_functor.
  Defined.

  Local Definition univalence_iso
             (u : is_univalent_dagger dagD)
    : (F,,dagF) = (G,,dagG) ≃  unitary (dagger_functor_cat_structure dagC dagD) (F,, dagF) (G,, dagG).
  Proof.
    refine (_ ∘ id_to_pr1_id)%weq.
    refine (_ ∘ id_pr1_to_pr11_id)%weq.
    refine (_ ∘ equality_equiv_functors_eq_data)%weq.
    refine (_ ∘ functors_eq_data_equiv_unitary_functors_eq u)%weq.
    refine (_ ∘ unitary_functors_eq_equiv_unitary_functors)%weq.
    exact unitary_functors_equiv_unitary.
  Defined.

End Univalence.

Lemma dagger_functor_cat_is_dagger_univalent
      {C D : category}
      (dagC : dagger C) (dagD : dagger D)
      (u : is_univalent_dagger dagD)
  : is_univalent_dagger (dagger_on_functor_cat dagC dagD).
Proof.
  intros F G.
  use weqhomot.
  - exact (univalence_iso (pr2 F) (pr2 G) u).
  - intro p.
    induction p.
    use total2_paths_f.
    2: apply isaprop_is_unitary.
    use total2_paths_f.
    2: apply isapropunit.
    apply (nat_trans_eq (pr2 D)).
    intro ; apply idpath.
Qed.
