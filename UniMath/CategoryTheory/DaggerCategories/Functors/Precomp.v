Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalCategoryFacts.

Require Import UniMath.CategoryTheory.precomp_fully_faithful.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Transformations.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.
Require Import UniMath.CategoryTheory.DaggerCategories.FunctorCategory.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.FullyFaithful.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.WeakEquivalences.

Local Open Scope cat.

Definition dagger_functor_on_unitary
           {C D : category}
           {dagC : dagger C} {dagD : dagger D}
           {F : functor C D}
           (dagF : is_dagger_functor dagC dagD F)
  : ∏ c c' : C, unitary dagC c c' -> unitary dagD (F c) (F c').
Proof.
  intros c c' u.
  exists (#F (pr1 u)).
  split.
  - refine (_ @ functor_id F _).
    refine (_ @ maponpaths (#F) (pr12 u)).
    refine (_ @ ! functor_comp F _ _).
    apply maponpaths.
    apply pathsinv0, dagF.
  - refine (_ @ functor_id F _).
    refine (_ @ maponpaths (#F) (pr22 u)).
    refine (_ @ ! functor_comp F _ _).
    apply maponpaths_2.
    apply pathsinv0, dagF.
Defined.

Definition dagger_functor_on_unitary_inv
           {C D : category}
           {dagC : dagger C} {dagD : dagger D}
           {F : functor C D}
           (dagF : is_dagger_functor dagC dagD F)
  : ∏ c c' : C, ∏ u : unitary dagC c c',
        unitary_inv (dagger_functor_on_unitary dagF c c' u) = dagger_functor_on_unitary dagF _ _ (unitary_inv u).
Proof.
  intro ; intros.
  unfold unitary_inv.
  use subtypePath.
  { intro ; apply isaprop_is_unitary. }
  apply pathsinv0, dagF.
Defined.

Definition dagger_functor_on_unitary_inv_on_ob
           {C D : category}
           {dagC : dagger C} {dagD : dagger D}
           {F : functor C D}
           (dagF : is_dagger_functor dagC dagD F)
  : ∏ c c' : C, ∏ u : unitary dagC c c',
        pr1 (unitary_inv (dagger_functor_on_unitary dagF c c' u))
        = #F (dagC _ _ u).
Proof.
  intro ; intros.
  apply pathsinv0, dagF.
Qed.

Lemma dagger_of_idtodaggeriso
      {C : category} (dag : dagger C)
      {x y : C} (p : x = y)
  : pr1 dag _ _ (pr1 (idtodaggeriso dag _ _ p)) = pr1 (idtodaggeriso dag _ _ (! p)).
Proof.
  induction p.
  apply dagger_to_law_id.
Qed.

Section Precomp_dagger_functor.

  Context {C D E : category}
          {dagC : dagger C} {dagD : dagger D}
          {F : functor C D}
          (dagF : is_dagger_functor dagC dagD F)
          (dagE : dagger E).

  Definition disp_dagger_pre_composition_functor_data
    :  disp_functor_data
         (pre_composition_functor C D E F)
         (dagger_functor_disp_cat dagD dagE)
         (dagger_functor_disp_cat dagC dagE).
  Proof.
    exists (λ _ dagG, is_dagger_functor_comp dagF dagG).
    intro ; intros ; exact tt.
  Defined.

  Lemma disp_dagger_pre_composition_functor_laws
    : disp_functor_axioms disp_dagger_pre_composition_functor_data.
  Proof.
    repeat split ; intro ; intros ; apply isapropunit.
  Qed.

  Definition disp_dagger_pre_composition_functor
    :  disp_functor
         (pre_composition_functor C D E F)
         (dagger_functor_disp_cat dagD dagE)
         (dagger_functor_disp_cat dagC dagE)
    := _ ,, disp_dagger_pre_composition_functor_laws.

  Definition dagger_pre_composition_functor
    : functor (dagger_functor_cat dagD dagE) (dagger_functor_cat dagC dagE)
    := total_functor (F := pre_composition_functor C D E F)
                     disp_dagger_pre_composition_functor.

  Lemma dagger_pre_composition_functor_is_dagger_functor
    : is_dagger_functor (dagger_on_functor_cat dagD dagE)
                        (dagger_on_functor_cat dagC dagE)
                        dagger_pre_composition_functor.
  Proof.
    intro ; intros.
    use subtypePath.
    { intro ; apply isapropunit. }
    use (nat_trans_eq (pr2 E)).
    intro ; apply idpath.
  Qed.

End Precomp_dagger_functor.

Section Precomp_with_dagger_weak_equiv.

  Context {C D E : category}
          {dagC : dagger C} {dagD : dagger D}
          {H : functor C D}
          {dagH : is_dagger_functor dagC dagD H}
          (dagE : dagger E).

  Context (wH : is_weak_dagger_equiv dagH).

  Lemma disp_dagger_pre_composition_functor_ff
    : disp_functor_ff (disp_dagger_pre_composition_functor dagH dagE).
  Proof.
    intro ; intros ; exact (isweqcontrtounit iscontrunit).
  Qed.

  Lemma Precomp_is_ff
    : fully_faithful (dagger_pre_composition_functor dagH dagE).
  Proof.
    use (disp_functor_ff_to_total_ff _ disp_dagger_pre_composition_functor_ff).
    apply pre_composition_with_ess_surj_and_full_is_fully_faithful.
    - exact (is_unitarily_eso_is_eso _ (pr1 wH)).
    - exact (pr1 (fully_faithful_implies_full_and_faithful _ _ _ (pr2 wH))).
  Qed.

  Section IntermediateProp.

    Context {F : functor C E} (dagF : is_dagger_functor dagC dagE F).

  Local Definition X
        (d : D) : UU
    := ∑ (ck : ∑ e : E, ∏ c : C, unitary dagD (H c) d -> unitary dagE (F c) e),
    ∏ t t' : ∑ c : C, unitary dagD (H c) d,
          ∏ f : pr1 t --> pr1 t',
             (#H f · pr12 t' = pr12 t ->
                    #F f · pr1 (pr2 ck (pr1 t') (pr2 t')) = pr1 (pr2 ck (pr1 t) (pr2 t))).

  Local Definition kX
        (d : D)
        (t : X d) := (pr2 (pr1 t)).

  Local Notation "FF ^-1" := (fully_faithful_inv_hom FF _ _ ).
  Let fH := pr2 wH : fully_faithful H.

  Ltac inv_functor HF x y :=
   let H:=fresh in
   set (H:= homotweqinvweq (weq_from_fully_faithful HF x y));
     simpl in H;
     unfold fully_faithful_inv_hom; simpl;
     rewrite H; clear H.

  Lemma X_aux_type_center_of_contr_proof
        (b : D) (anot : C) (hnot : unitary dagD (H anot) b) :
    ∏ (t t' : ∑ a :  C, unitary dagD (H a) b)
      (f : pr1 t --> pr1 t'),
      #H f· pr12 t' = pr12 t ->
      #F f·
       #F (fH^-1 (pr12 t'· dagD _ _ (pr1 hnot))) =
        #F (fH^-1 (pr12 t· dagD _ _ (pr1 hnot))).
  Proof.
    intros t t' f.
    destruct t as [a h].
    destruct t' as [a' h'].
    simpl in *.
    intro star.
    rewrite <- functor_comp.
    apply maponpaths.
    apply (invmaponpathsweq
             (weq_from_fully_faithful fH a anot)).
    simpl.
    rewrite functor_comp.
    inv_functor fH a' anot.
    rewrite assoc.
    inv_functor fH a anot.
    rewrite <- star.
    apply idpath.
  Qed.

  Local Notation "F '^-i'" := (fully_faithful_reflects_unitary dagH F) (at level 20).

  Definition X_aux_type_center_of_contr (b : D)
             (anot : C)(hnot : unitary dagD (H anot) b) : X b.
  Proof.
    set (cnot := F anot).
    use tpair.
    - exists cnot.
      intros c u.
      unfold cnot.
      set (u' := fully_faithful_reflects_unitary dagH fH c anot (unitary_comp u (unitary_inv hnot))).
      exact (dagger_functor_on_unitary dagF _ _ u').
    - exact (λ t t' f p, X_aux_type_center_of_contr_proof b anot hnot t t' f p).
  Defined.

  (** Any inhabitant of [X b] is equal to the center of [X b]. *)

  Lemma X_aux_type_contr_eq
        (b : D) (anot : C) (hnot : unitary dagD (H anot) b) (Euniv : is_univalent_dagger dagE) :
    ∏ t : X b, t = X_aux_type_center_of_contr b anot hnot.
  Proof.
    intro t.
    assert (Hpr1 : pr1 (X_aux_type_center_of_contr b anot hnot) = pr1 t).
    {
      set (w := daggerisotoid Euniv ((pr2 (pr1 t)) anot hnot) :
             pr1 (pr1 (X_aux_type_center_of_contr b anot hnot)) = pr1 (pr1 t)).

      apply (total2_paths_f w).
      simpl.
      destruct t as [[c1 k1] q1].
      simpl in *.
      apply funextsec; intro a.
      apply funextsec; intro h.
      set (gah := fH^-i  _ _ (unitary_comp h (unitary_inv hnot))).
      set (qhelp := q1 (tpair _ a h)(tpair _ anot hnot) (pr1 gah)).
      simpl in *.

      assert (feedtoqhelp : #H (fH^-1 (pr1 h · pr1 (unitary_inv hnot)))· pr1 hnot = pr1 h).
      {
        inv_functor fH a anot.
        refine (assoc' _ _ _ @ _ @ id_right _).
        apply maponpaths.
        exact (pr22 hnot).
      }

      assert (quack := qhelp feedtoqhelp).

      simpl in *.

      intermediate_path (unitary_comp  (dagger_functor_on_unitary dagF _ _ (fH^-i _ _ (unitary_comp h (unitary_inv hnot)))) (idtodaggeriso _ _ _ w) ).
      - generalize w; intro w0.
        induction w0.
        apply unitary_eq.
        apply pathsinv0, id_right.
      - apply unitary_eq.
        simpl.
        unfold w.
        refine (_ @ quack).
        do 2 apply maponpaths.
        apply idtodaggeriso_daggerisotoid.
    }

    apply pathsinv0.
    apply (total2_paths_f Hpr1).
    apply proofirrelevance.
    repeat (apply impred; intro).
    apply homset_property.
  Qed.

  (** Putting everything together: [X b] is contractible. *)

  Definition iscontr_X (Euniv : is_univalent_dagger dagE) : ∏ b : D, iscontr (X b).
  Proof.
    intro b.
    assert (HH : isaprop (iscontr (X b))).
    apply isapropiscontr.
    apply (pr1 wH b (tpair (λ x, isaprop x) (iscontr (X b)) HH)).
    intro t.
    exists (X_aux_type_center_of_contr b (pr1 t) (pr2 t)).
    exact (X_aux_type_contr_eq b (pr1 t) (pr2 t) Euniv).
  Defined.

  (** The object part of [G], [Go b], is defined as the first component of
    the center of [X b]. *)

  (** *** [G] on objects *)

  Context (Euniv : is_univalent_dagger dagE).

  Local Definition Go : D -> E :=
    λ b : D, pr1 (pr1 (pr1 (iscontr_X Euniv b))).

  Local Definition k (b : D) :
    ∏ a : C, unitary _ (H a) b -> unitary _ (F a) (Go b) :=
    pr2 (pr1 (pr1 (iscontr_X Euniv b))).

  Local Definition q (b : D) := pr2 (pr1 (iscontr_X Euniv b)).

  (** Given any inhabitant of [X b], its first component is equal to [Go b]. *)

  Definition Xphi (b : D) (t : X b) : pr1 (pr1 t) = Go b.
  Proof.
    set (p1 := pr2 (iscontr_X Euniv b) t).
    exact (base_paths _ _ (base_paths _ _ p1)).
  Defined.

  (** Given any inhabitant [t : X b], its second component is equal to [k b],
       modulo transport along [Xphi b t]. *)

  Definition Xkphi_transp (b : D) (t : X b) :
    ∏ a : C, ∏ h : unitary _ (H a) b,
          transportf _ (Xphi b t) (kX _ t) a h =  k b a h.
  Proof.
    intro ; intro.
    set (p := fiber_paths (base_paths _ _ (pr2 (iscontr_X Euniv b) t))).
    exact (toforallpaths _ _ _ ((toforallpaths _ _ _ p) a) h).
  Qed.

  (** Similarly to the lemma before, the second component of [t] is the same
    as [k b], modulo postcomposition with an isomorphism. *)

  Definition Xkphi_idtoiso (b : D) (t : X b) :
    ∏ a : C, ∏ h : unitary _ (H a) b,
          k b a h · idtodaggeriso dagE _ _ (!Xphi b t) = kX _ t a h.
  Proof.
    intros a h.
    rewrite <- (Xkphi_transp _ t).
    generalize (Xphi b t).
    intro i; destruct i.
    apply id_right.
  Qed.

  (** *** Preparation for [G] on morphisms *)

(** [G f] will be defined as the first component of the center of
     contraction of [Y f]. *)

  Local Definition Y {b b' : D} (f : b --> b') :=
    ∑ g : Go b --> Go b',
              ∏ a : C,
                ∏ h : unitary _ (H a) b,
                  ∏ a' : C,
                    ∏ h' : unitary _ (H a') b',
                      ∏ l : a --> a',
                        #H l · h' = h · f -> #F l · k b' a' h' = k b a h · g.

  Lemma Y_inhab_proof (b b' : D) (f : b --> b') (a0 : C) (h0 : unitary _ (H a0) b)
        (a0' : C) (h0' : unitary _ (H a0') b') :
    ∏ (a : C) (h : unitary _ (H a) b) (a' : C) (h' : unitary _ (H a') b')
      (l : a --> a'),
      #H l· h' = h· f ->
      #F l· k b' a' h' =
        k b a h· ((unitary_inv (k b a0 h0)·
                                  #F (fH^-1 ((h0· f)· unitary_inv h0')))· k b' a0' h0').
  Proof.
    intros a h a' h' l alpha.
    set (m := fH^-i _ _ (unitary_comp h0 (unitary_inv h))).
    set (m' := fH^-i _ _ (unitary_comp h0' (unitary_inv h'))).
    assert (sss : unitary_comp (dagger_functor_on_unitary dagF _ _ m) (k b a h) =
                    k b a0 h0).
    {
      apply unitary_eq.
      apply (q b (tpair _ a0 h0) (tpair _ a h) m).
      simpl.
      inv_functor fH a0 a.
      rewrite <- assoc.
      refine (_ @ id_right _).
      apply maponpaths, (pr2 h).
    }
    assert (ssss : unitary_comp (dagger_functor_on_unitary dagF _ _ m') (k b' a' h') =
                     k b' a0' h0').
    {
      apply unitary_eq.
      apply (q b' (tpair _ a0' h0') (tpair _ a' h') m').
      simpl;
        inv_functor fH a0' a'.
      rewrite <- assoc.
      refine (_ @ id_right _).
      apply maponpaths, (pr22 h').
    }
    set (hfh := h0 · f · unitary_inv h0').
    set (l0 := fH^-1 hfh).
    set (g0 := unitary_inv (k b a0 h0) · #F l0  · k b' a0' h0').
    assert (sssss : #H (l0 · m') = #H (m · l)).
    { rewrite functor_comp .
      unfold m'. simpl.
      inv_functor fH a0' a'.
      unfold l0.
      inv_functor fH a0 a0'.
      unfold hfh.
      intermediate_path (h0 · f · (unitary_inv h0' · h0') · unitary_inv h').
      { repeat rewrite assoc; apply idpath. }
      etrans.
      {
        apply maponpaths_2, maponpaths.
        apply (pr22 h0').
      }
      rewrite id_right, functor_comp.
      inv_functor fH a0 a.
      repeat rewrite <- assoc.
      apply maponpaths, pathsinv0.
      apply unitary_inv_on_right.
      { apply h. }

      rewrite assoc.
      apply unitary_inv_on_left.
      { apply h'. }
      apply pathsinv0, alpha.
    }
    assert (star5 : unitary_inv m · l0 = l · unitary_inv m').
    {

      apply unitary_inv_on_right.
      { apply m. }
      rewrite assoc.
      apply unitary_inv_on_left.
      { apply m'. }
      apply (invmaponpathsweq (weq_from_fully_faithful fH a0 a')),
        pathsinv0, sssss.
    }
    clear sssss.
    unfold g0.
    assert (sss'' : k b a h · unitary_inv (k b a0 h0) =
                      unitary_inv (dagger_functor_on_unitary dagF _ _ m)).
    {
      apply pathsinv0.
      apply unitary_inv_on_left.
      { apply k. }
      apply pathsinv0.
      apply unitary_inv_on_right.
      { apply dagger_functor_on_unitary. }
      apply pathsinv0, (base_paths _ _ sss).
    }
    repeat rewrite assoc.
    rewrite sss''. clear sss'' sss.

    rewrite dagger_functor_on_unitary_inv.
    etrans.
    2: { apply maponpaths_2, functor_comp. }
    cbn.
    unfold m, m' in star5.
    cbn in star5.
    rewrite star5; clear star5.
    rewrite functor_comp.
    rewrite <- assoc.
    apply maponpaths.

    assert (star4 : unitary_inv (dagger_functor_on_unitary dagF _ _ m')
                                · k b' a0' h0' = k b' a' h').
    {
      apply unitary_inv_on_right.
      { apply dagger_functor_on_unitary. }
      apply pathsinv0, (base_paths _ _ ssss).
    }
    refine (! star4 @ _).
    apply maponpaths_2.
    apply pathsinv0, dagF.
  Qed.

  (** The center of [Y b b' f]. *)

  Definition Y_inhab (b b' : D) (f : b --> b')
             (a0 : C) (h0 : unitary dagD (H a0) b) (a0' : C) (h0' : unitary dagD (H a0') b') : Y f.
  Proof.
    set (hfh := h0 · f · unitary_inv h0').
    set (l0 := fH^-1 hfh).
    set (g0 := unitary_inv (k b a0 h0) · #F l0  · k b' a0' h0').
    exists g0.
    apply Y_inhab_proof.
  Defined.

  (** Any inhabitant of [Y b b' f] is equal to the center. *)

  Lemma Y_contr_eq (b b' : D) (f : b --> b')
        (a0 : C) (h0 : unitary _ (H a0) b)
        (a0' : C) (h0' : unitary _ (H a0') b') :
    ∏ t : Y f, t = Y_inhab b b' f a0 h0 a0' h0'.
  Proof.
    intro t.
    apply pathsinv0.
    assert (Hpr : pr1 (Y_inhab b b' f a0 h0 a0' h0') = pr1 t).
    {
      destruct t as [g1 r1]; simpl in *.
      rewrite <- assoc.
      use unitary_inv_on_right.
      { apply k. }

      set (hfh := h0 · f · unitary_inv h0').
      set (l0 := fH^-1 hfh).
      apply (r1 a0 h0 a0' h0' l0).
      unfold l0.
      inv_functor fH a0 a0' .
      unfold hfh.
      repeat rewrite <- assoc.
      apply maponpaths.
      refine (_ @ id_right _).
      apply maponpaths.
      apply h0'.
    }

    apply (total2_paths_f Hpr).
    apply proofirrelevance.
    repeat (apply impred; intro).
    apply homset_property.
  Qed.

  (** The type [Y b b' f] is contractible. *)

  Definition Y_iscontr  (b b' : D) (f : b --> b') :
    iscontr (Y f).
  Proof.
    assert (HH : isaprop (iscontr (Y f))).
    { apply isapropiscontr. }
    apply (pr1 wH b (tpair (λ x, isaprop x) (iscontr (Y f)) HH)).
    intros [a0 h0].
    apply (pr1 wH b' (tpair (λ x, isaprop x) (iscontr (Y f)) HH)).
    intros [a0' h0'].
    exists (Y_inhab b b' f a0 h0 a0' h0').
    apply Y_contr_eq.
  Defined.

  (** *** [G] on morphisms *)

  (** We now have the data necessary to define the functor [G]. *)

  Definition preimage_functor_data : functor_data D E.
  Proof.
    exists Go.
    intros b b' f.
    exact (pr11 (Y_iscontr b b' f)).
  Defined.

  Definition G {x y : D} (f : D⟦x,y⟧)
    := (pr11 (Y_iscontr _ _ f)).

  (** The above data is indeed functorial. *)

  Lemma is_functor_preimage_functor_data : is_functor preimage_functor_data.
  Proof.
    split.
    - unfold functor_idax. simpl.
      intro b.
      assert (PR2 : ∏ (a : C) (h : unitary _ (H a) b) (a' : C)
                      (h' : unitary _ (H a') b)
                      (l : a --> a'),
                 #H l· h' = h· identity b ->
                 #F l· k b a' h' = k b a h· identity (Go b)).
      {
        intros a h a' h' l LL.
        rewrite id_right.
        apply (q b (tpair _ a h) (tpair _ a' h') l).
        rewrite id_right in LL.
        apply LL.
      }
      set (Gbrtilde :=
             tpair _ (identity (Go b)) PR2 : Y (identity b)).
      set (H' := pr2 (Y_iscontr b b (identity b)) Gbrtilde).
      set (H'' := base_paths _ _ H').
      simpl in H'.
      rewrite <- H'.
      apply idpath.
    - (** composition *)
      intros b b' b'' f f'.
      assert (HHHH : isaprop (pr1 (pr1 (Y_iscontr b b'' (f· f'))) =
                                pr1 (pr1 (Y_iscontr b b' f))· pr1 (pr1 (Y_iscontr b' b'' f')))).
      { apply homset_property. }
      apply (pr1 wH b (tpair (λ x, isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f· f'))) =
                                            pr1 (pr1 (Y_iscontr b b' f))· pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
      intros [a0 h0]; simpl.
      apply (pr1 wH b' (tpair (λ x, isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f· f'))) =
                                             pr1 (pr1 (Y_iscontr b b' f))· pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
      intros [a0' h0']; simpl.
      apply (pr1 wH b'' (tpair (λ x, isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f· f'))) =
                                              pr1 (pr1 (Y_iscontr b b' f))· pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
      intros [a0'' h0''].
      simpl; clear HHHH.
      set (l0 := fH^-1 (h0 · f · unitary_inv h0')).
      set (l0' := fH^-1 (h0' · f' · unitary_inv h0'')).
      set (l0'' := fH^-1 (h0 · (f· f') · unitary_inv h0'')).
      assert (L : l0 · l0' = l0'').
      {
        apply (invmaponpathsweq (weq_from_fully_faithful fH a0 a0'')).
        simpl; rewrite functor_comp.
        unfold l0'.
        inv_functor fH a0' a0''.
        unfold l0.
        inv_functor fH a0 a0'.
        intermediate_path (h0 · f · (unitary_inv h0' · h0') · f' · unitary_inv h0'').
        { repeat rewrite assoc; apply idpath. }
        etrans.
        {
          do 2 apply maponpaths_2.
          apply maponpaths.
          apply h0'.
        }

        rewrite id_right.
        unfold l0''.
        inv_functor fH a0 a0''.
        repeat rewrite assoc; apply idpath.
      }
      assert (PR2 : ∏ (a : C) (h : unitary _ (H a) b)(a' : C)
                      (h' : unitary _ (H a') b') (l : a --> a'),
                 #H l· h' = h· f ->
                 #F l· k b' a' h' =
                   k b a h· ((unitary_inv (k b a0 h0)· #F l0)· k b' a0' h0') ).
      {
        intros a h a' h' l.
        intro alpha.
        set (m := fH^-i _ _ (unitary_comp h0 (unitary_inv h))).
        set (m' := fH^-i _ _ (unitary_comp h0' (unitary_inv h'))).
        assert (sss : unitary_comp (dagger_functor_on_unitary dagF _ _ m) (k b a h) =
                        k b a0 h0).
        { apply unitary_eq; simpl.
          apply (q b (tpair _ a0 h0) (tpair _ a h) m).
          simpl.
          inv_functor fH a0 a.
          rewrite <- assoc.
          refine (_ @ id_right _).
          apply maponpaths, h.
        }
        assert (ssss : unitary_comp (dagger_functor_on_unitary dagF _ _ m') (k b' a' h') = k b' a0' h0').
        {
          apply unitary_eq; simpl.
          apply (q b' (tpair _ a0' h0') (tpair _ a' h') m'); simpl.
          inv_functor fH a0' a'.
          rewrite <- assoc.
          refine (_ @ id_right _).
          apply maponpaths, h'.
        }
        assert (sssss : #H (l0 · m') = #H (m · l)).
        {
          rewrite functor_comp.
          unfold m'; simpl.
          inv_functor fH a0' a'.
          unfold l0.
          inv_functor fH a0 a0'.
          intermediate_path (h0 · f · (unitary_inv h0' · h0') · unitary_inv h').
          { repeat rewrite assoc; apply idpath. }
          etrans.
          { apply maponpaths_2, maponpaths , h0'. }
          rewrite id_right, functor_comp.
          inv_functor fH a0 a.
          repeat rewrite <- assoc.
          apply maponpaths.
          apply pathsinv0.
          apply unitary_inv_on_right.
          { apply h. }
          rewrite assoc.
          apply unitary_inv_on_left.
          { apply h'. }
          apply pathsinv0.
          apply alpha.
        }
        assert (star5 : unitary_inv m · l0 = l · unitary_inv m').
        {
          apply unitary_inv_on_right.
          { apply m. }
          rewrite assoc.
          apply unitary_inv_on_left.
          { apply m'. }
          apply (invmaponpathsweq (weq_from_fully_faithful fH a0 a' )).
          apply pathsinv0.
          apply sssss.
        }
        clear sssss.
        set (sss':= base_paths _ _ sss); simpl in sss'.
        assert (sss'' : k b a h · unitary_inv (k b a0 h0)
                        = unitary_inv (dagger_functor_on_unitary dagF _ _ m)).
        {
          apply pathsinv0.
          apply unitary_inv_on_left.
          { apply k. }
          apply pathsinv0.
          apply unitary_inv_on_right.
          { apply dagger_functor_on_unitary. }
          apply pathsinv0.
          apply sss'.
        }
        repeat rewrite assoc.
        rewrite sss''. clear sss'' sss' sss.
        etrans.
        2: {
          do 2 apply maponpaths_2.
          apply pathsinv0, dagger_functor_on_unitary_inv_on_ob.
        }

        rewrite <- functor_comp.
        etrans.
        2: {
          apply maponpaths_2, maponpaths.
          refine (! star5 @ _).
          apply maponpaths_2.
          apply (Isos.inverse_unique_precat _ _ m) ; apply m.
        }
        clear star5.

        rewrite functor_comp.
        etrans.
        2: {
          apply maponpaths_2, maponpaths.
          exact (dagger_functor_on_unitary_inv_on_ob dagF _ _ m').
        }

        assert (star4 : unitary_inv (dagger_functor_on_unitary dagF _ _ m') · k b' a0' h0'
                 = k b' a' h' ).
        {
          apply unitary_inv_on_right.
          { apply dagger_functor_on_unitary. }
          set (ssss' := base_paths _ _ ssss).
          apply pathsinv0.
          simpl in ssss'. simpl.
          apply ssss'; clear ssss'.
        }
        rewrite <- assoc.
        apply maponpaths.
        apply pathsinv0, star4.
      }
      assert (HGf : G f = unitary_inv (k b a0 h0) · #F l0 · k b' a0' h0').
      {
        set (Gbrtilde :=
               tpair _ (unitary_inv (k b a0 h0) · #F l0 · k b' a0' h0') PR2 : Y f).
        set (H' := pr2 (Y_iscontr b b' f) Gbrtilde).
        set (H'' := base_paths _ _ H').
        simpl in H'.
        unfold G.
        rewrite <- H'.
        apply idpath.
      }
      clear PR2.
      assert (PR2 : ∏ (a : C) (h : unitary _ (H a) b') (a' : C)
                      (h' : unitary _ (H a') b'') (l : a --> a'),
                 #H l· h' = h· f' ->
                 #F l· k b'' a' h' =
                   k b' a h· ((unitary_inv (k b' a0' h0')· #F l0')· k b'' a0'' h0'')).
      {
        intros a' h' a'' h'' l'.
        intro alpha.
        set (m := fH^-i _ _ (unitary_comp h0' (unitary_inv h'))).
        set (m' := fH^-i _ _ (unitary_comp h0'' (unitary_inv h''))).
        assert (sss : unitary_comp (dagger_functor_on_unitary dagF _ _ m) (k b' a' h') =
                        k b' a0' h0').
        {
          apply unitary_eq; simpl.
          apply (q b' (tpair _ a0' h0') (tpair _ a' h') m); simpl.
          inv_functor fH a0' a'.
          rewrite <- assoc.
          refine (_ @ id_right _).
          apply maponpaths.
          apply h'.
        }
        assert (ssss : unitary_comp (dagger_functor_on_unitary dagF _ _ m') (k b'' a'' h'') =
                         k b'' a0'' h0'').
        {
          apply unitary_eq; simpl.
          apply (q b'' (tpair _ a0'' h0'') (tpair _ a'' h'') m'); simpl.
          inv_functor fH a0'' a''.
          rewrite <- assoc.
          refine (_ @ id_right _).
          apply maponpaths.
          apply h''.
        }
        assert (sssss : #H (l0' · m') = #H (m · l')).
        {
          rewrite functor_comp.
          unfold m'. simpl.
          inv_functor fH a0'' a''.
          unfold l0'.
          inv_functor fH a0' a0''.
          intermediate_path (h0' · f' · (unitary_inv h0'' · h0'') · unitary_inv h'').
          { repeat rewrite assoc; apply idpath. }
          etrans.
          { apply maponpaths_2, maponpaths, h0''. }
          rewrite id_right, functor_comp.
          inv_functor fH a0' a'.
          repeat rewrite <- assoc.
          apply maponpaths, pathsinv0, unitary_inv_on_right.
          { apply h'. }
          rewrite assoc.
          apply unitary_inv_on_left.
          { apply h''. }
          apply pathsinv0, alpha.
        }
        assert (star5 : unitary_inv m · l0' = l' · unitary_inv m').
        {
          apply unitary_inv_on_right.
          { apply m. }
          rewrite assoc.
          apply unitary_inv_on_left.
          { apply m'. }
          apply (invmaponpathsweq (weq_from_fully_faithful fH a0' a'' )),
            pathsinv0, sssss.
        }
        set (sss':= base_paths _ _ sss); simpl in sss'.
        assert (sss'' : k b' a' h' · unitary_inv (k b' a0' h0') =
                          unitary_inv (dagger_functor_on_unitary dagF _ _ m)).
        {
          apply pathsinv0, unitary_inv_on_left, pathsinv0, unitary_inv_on_right.
          - apply k.
          - apply dagger_functor_on_unitary.
          - apply pathsinv0, sss'.
        }
        repeat rewrite assoc.
        rewrite sss''. clear sss'' sss' sss.
        etrans.
        2: {
          do 2 apply maponpaths_2.
          exact (! dagger_functor_on_unitary_inv_on_ob dagF _ _ m).
        }
        rewrite <- functor_comp.
        etrans.
        2: apply maponpaths_2, maponpaths, pathsinv0, star5.
        clear star5 sssss.
        rewrite functor_comp.
        etrans.
        2: {
          apply maponpaths_2, maponpaths.
          exact (dagger_functor_on_unitary_inv_on_ob dagF _ _ m').
        }

        assert (star4 : unitary_inv (dagger_functor_on_unitary dagF _ _ m') · k b'' a0'' h0''
                 = k b'' a'' h'' ).
        {
          apply unitary_inv_on_right.
          { apply dagger_functor_on_unitary. }
          set (ssss' := base_paths _ _ ssss).
          apply pathsinv0.
          simpl in *; apply ssss'.
        }
        rewrite <- assoc.
        apply maponpaths.
        exact (! star4).
      }
      assert (HGf' : G f' = unitary_inv (k b' a0' h0') · #F l0' · k b'' a0'' h0'').
      {
        set (Gbrtilde :=
               tpair _ (unitary_inv (k b' a0' h0') · #F l0' · k b'' a0'' h0'') PR2 :
               Y f').
        set (H' := pr2 (Y_iscontr b' b'' f') Gbrtilde).
        unfold G.
        rewrite <- (base_paths _ _ H').
        apply idpath.
      }
      clear PR2.
      assert (PR2 : ∏ (a : C) (h : unitary _ (H a) b) (a' : C)
                      (h' : unitary _ (H a') b'') (l : a --> a'),
                 #H l· h' = h· (f· f') ->
                 #F l· k b'' a' h' =
                   k b a h· ((unitary_inv (k b a0 h0)· #F l0'')· k b'' a0'' h0'')).
      {
        intros a h a'' h'' l.
        intro alpha.
        set (m := fH^-i _ _ (unitary_comp h0 (unitary_inv h))).
        set (m' := fH^-i _ _ (unitary_comp h0'' (unitary_inv h''))).
        assert (sss : unitary_comp (dagger_functor_on_unitary dagF _ _ m) (k b a h) = k b a0 h0).
        {
          apply unitary_eq.
          apply (q b (tpair _ a0 h0) (tpair _ a h) m); simpl.
          inv_functor fH a0 a.
          rewrite <- assoc.
          refine (_ @ id_right _).
          apply maponpaths.
          apply h.
        }
        assert (ssss : unitary_comp (dagger_functor_on_unitary dagF _ _ m') (k b'' a'' h'') =
                         k b'' a0'' h0'').
        { apply unitary_eq.
          apply (q b'' (tpair _ a0'' h0'') (tpair _ a'' h'') m').
          simpl; inv_functor fH a0'' a''.
          rewrite <- assoc.
          refine (_ @ id_right _).
          apply maponpaths.
          apply h''.
        }
        assert (sssss : #H (l0'' · m') = #H (m · l)).
        { rewrite functor_comp.
          unfold m'. simpl.
          inv_functor fH a0'' a''.
          unfold l0''.
          inv_functor fH a0 a0''.
          intermediate_path (h0 · (f · f') · (unitary_inv h0'' · h0'') · unitary_inv h'').
          { repeat rewrite assoc; apply idpath. }
          etrans.
          { apply maponpaths_2, maponpaths, h0''. }
          rewrite id_right, functor_comp.
          inv_functor fH a0 a.
          repeat rewrite <- assoc.
          apply maponpaths, pathsinv0, unitary_inv_on_right.
          { apply h. }
          repeat rewrite assoc.
          apply unitary_inv_on_left, pathsinv0.
          { apply h''. }
          repeat rewrite <- assoc.
          apply alpha.
        }
        assert (star5 : unitary_inv m · l0'' = l · unitary_inv m').
        {
          apply unitary_inv_on_right.
          { apply m. }
          rewrite assoc.
          apply unitary_inv_on_left.
          { apply m'. }
          apply (invmaponpathsweq (weq_from_fully_faithful fH a0 a'' )).
          apply pathsinv0, sssss.
        }


        set (sss':= base_paths _ _ sss); simpl in sss'.
        assert (sss'' : k b a h · unitary_inv (k b a0 h0) =
                          unitary_inv (dagger_functor_on_unitary dagF _ _  m)).
        {
          apply pathsinv0, unitary_inv_on_left, pathsinv0, unitary_inv_on_right.
          - apply k.
          - apply dagger_functor_on_unitary.
          - apply pathsinv0, sss'.
        }

        repeat rewrite assoc.
        rewrite sss''. clear sss'' sss' sss.
        etrans.
        2: {
          do 2 apply maponpaths_2.
          exact (! dagger_functor_on_unitary_inv_on_ob dagF _ _ m).
        }
        rewrite <- functor_comp.
        etrans.
        2: apply maponpaths_2, maponpaths, (! star5).
        clear star5 sssss.
        rewrite functor_comp.
        etrans.
        2: {
          apply maponpaths_2, maponpaths.
          exact (dagger_functor_on_unitary_inv_on_ob dagF _ _ m').
        }
        assert (star4 : unitary_inv (dagger_functor_on_unitary dagF _ _ m') · k b'' a0'' h0'' = k b'' a'' h'').
        {
          apply unitary_inv_on_right, pathsinv0, (base_paths _ _ ssss).
          apply dagger_functor_on_unitary.
        }
        rewrite <- assoc.
        apply maponpaths.
        exact (! star4).
      }
      assert (HGff' : G (f · f') = unitary_inv (k b a0 h0) · #F l0'' · k b'' a0'' h0'').
      {
        set (Gbrtilde :=
               tpair _ (unitary_inv (k b a0 h0) · #F l0'' · k b'' a0'' h0'') PR2 :
               Y (f · f')).
        unfold G.
        rewrite <- (pr2 (Y_iscontr b b'' (f · f')) Gbrtilde).
        apply idpath.
      }
      clear PR2.
      fold (G (f · f')).
      fold (G (f)) (G f').
      rewrite HGf, HGf'.
      intermediate_path (unitary_inv (k b a0 h0)· #F l0· (k b' a0' h0'·
                                                            unitary_inv (k b' a0' h0'))· #F l0'· k b'' a0'' h0'').
      {
        etrans.
        2: {
          do 2 apply maponpaths_2.
          apply maponpaths, pathsinv0, k.
        }

        rewrite id_right, HGff'.
        repeat rewrite <- assoc.
        apply maponpaths.
        rewrite <- L.
        rewrite functor_comp.
        repeat rewrite <- assoc.
        apply idpath.
      }
      now repeat rewrite <- assoc.
  Qed.


  (** We call the functor [GG] ... *)

  Definition GG : functor D E := tpair _ preimage_functor_data
                                       is_functor_preimage_functor_data.

  (** ** [G] is the preimage of [F] under [ _ O H] *)

  (** Given any [a : A], we produce an element in [X (H a)], whose
     first component is [F a].
   This allows to prove [G (H a) = F a]. *)

  Lemma qF (a0 : C) :
    ∏ (t t' : ∑ a :  C, unitary dagD (H a) (H a0))
      (f : pr1 t --> pr1 t'),
      #H f· pr2 t' = pr2 t ->
      #F f· #F (fH^-1 (pr2 t')) =
        #F (fH^-1  (pr2 t)).
  Proof.
    simpl.
    intros [a h] [a' h'] f L.
    simpl in L; simpl.
    rewrite <- functor_comp.
    apply maponpaths.
    apply (invmaponpathsweq (weq_from_fully_faithful fH a a0)
                            (f· fH^-1 h') (fH^-1 h)  ).
    inv_functor fH a a0.
    rewrite functor_comp.
    inv_functor fH a' a0.
    apply L.
  Qed.


  Definition kFa (a0 : C)
    : ∏ a : C, unitary _ (H a) (H a0) -> unitary _ (F a) (F a0)
    := fun (a : C) (h : unitary _ (H a) (H a0)) =>
      dagger_functor_on_unitary dagF _ _ (fully_faithful_reflects_unitary dagH fH _ _ h).

  Definition XtripleF (a0 : C) : X (H a0)
    := tpair _ (tpair _ (F a0) (kFa a0)) (qF a0).


  Lemma phi (a0 : C)
    : pr1 (pr1 (functor_composite H GG)) a0 = pr1 (pr1 F) a0.
  Proof.
    exact (!Xphi _ (XtripleF a0)).
  Defined.

  Lemma extphi : pr1 (pr1 (functor_composite H GG)) = pr1 (pr1 F).
  Proof.
    apply funextsec.
    unfold homot.
    apply phi.
  Defined.

  (** Now for the functor as a whole. It remains to prove
      equality on morphisms, modulo transport. *)

  Lemma is_preimage_for_pre_composition : functor_composite H GG = F.
  Proof.
    apply (functor_eq _ _  E (functor_composite H GG) F).
    apply (total2_paths_f extphi).
    apply funextsec; intro a0;
      apply funextsec; intro a0';
      apply funextsec; intro f.
    rewrite FunctorCategory.transport_of_functor_map_is_pointwise.
    unfold extphi.
    unfold Univalence.double_transport.
    rewrite toforallpaths_funextsec.
    rewrite <- Univalence.idtoiso_postcompose.
    rewrite <- Univalence.idtoiso_precompose.
    rewrite Univalence.idtoiso_inv.
    rewrite <- assoc.
    assert (PSIf : ∏ (a : C) (h : unitary _ (H a) (H a0)) (a' : C)
                     (h' : unitary _ (H a') (H a0')) (l : a --> a'),
               #H l· h' = h· #H f ->
               #F l· k (H a0') a' h' =
                 k (H a0) a h·
                   ((pr1 (idtodaggeriso dagE _ _ (phi a0)) · #F f)
                      · unitary_inv (idtodaggeriso dagE _ _ (phi a0')))).
    {
      intros a h a' h' l alpha.
      rewrite assoc.
      apply unitary_inv_on_left.
      { apply idtodaggeriso. }
      unfold phi.
      repeat rewrite assoc.
      rewrite (Xkphi_idtoiso (H a0) (XtripleF a0)).
      repeat rewrite <- assoc.
      rewrite (Xkphi_idtoiso (H a0') (XtripleF a0')).
      simpl.
      assert (HH4 : fH^-1 h · f = l · fH^-1 h').
      {
        apply (invmaponpathsweq (weq_from_fully_faithful fH a a0')).
        simpl; repeat rewrite functor_comp.
        inv_functor fH a a0.
        inv_functor fH a' a0'.
        apply pathsinv0, alpha.
      }
      intermediate_path (#F (fH^-1 h· f)).
      { now rewrite functor_comp. }
      rewrite HH4.
      now rewrite functor_comp.
    }

    set (Ybla := tpair _ (idtodaggeriso _ _ _ (phi a0) · #F f · unitary_inv (idtodaggeriso _ _ _ (phi a0')))
                    PSIf : Y (#H f)).
    set (Ycontr := pr2 (Y_iscontr _ _ (#(pr1 H) f)) Ybla).
    set (Ycontr2 := base_paths _ _ Ycontr); simpl in *.
    change (H a0) with (pr1 H a0).
    change (H a0') with (pr1 H a0').
    change (G (#H f)) with (G (#(pr1 H) f)).
    change (#H f) with (# (pr1 H) f).
    rewrite <- Ycontr2.
    repeat rewrite assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      refine (_ @ idpath (identity _)).
      generalize (phi a0).
      intro p ; induction p ; apply id_right.
    }

    rewrite id_left.
    repeat rewrite <- assoc.
    etrans.
    {
      apply maponpaths.
      refine (_ @ idpath (identity _)).
      rewrite dagger_of_idtodaggeriso.
      etrans.
      { apply maponpaths_2, idtodaggeriso_is_dagger_of_idtodaggeriso. }
      refine (_ @ pr22 (idtodaggeriso dagE _ _ (phi a0'))).
      rewrite pathsinv0inv0.
      apply maponpaths.
      generalize (phi a0').
      intro p ; induction p ; apply idpath.
    }
    apply id_right.
  Qed.

  Lemma GG_is_dagger_functor
    : is_dagger_functor dagD dagE GG.
  Proof.
    intros x y f.

    transparent assert (rhs : (Y (dagD x y f))).
    {
      exists (dagE (Go x) (Go y) (G f)).
      intros c h c' h' l p.

      apply (dagger_injective dagE).
      do 2 rewrite dagger_to_law_comp.
      rewrite dagger_to_law_idemp.
      rewrite <- dagF.
      apply unitary_inv_on_left.
      { apply k. }

      unfold G.

      set (p0 := pr21 (Y_iscontr _ _ (dagD _ _ f)) _ h _ h' l p).
      rewrite assoc'.

      assert (pf : # H (dagC c c' l) · h = h' · f).
      {
        rewrite dagH.
        apply (dagger_injective dagD).
        do 2 rewrite dagger_to_law_comp.
        rewrite dagger_to_law_idemp.
        use unitary_inv_on_left.
        { apply h'. }
        rewrite assoc'.
        rewrite p.
        rewrite assoc.
        etrans.
        2: apply maponpaths_2, pathsinv0, (pr22 h).
        apply pathsinv0, id_left.
      }

      etrans.
      2: {
        apply maponpaths, pathsinv0.
        exact (pr21 (Y_iscontr _ _ f) _ h' _ h (dagC _ _ l) pf).
      }
      rewrite assoc.
      etrans.
      2: apply maponpaths_2, pathsinv0, k.
      apply pathsinv0, id_left.
    }
    exact (base_paths _ _ (! pr2 (Y_iscontr _ _ (dagD x y f)) rhs)).
  Qed.

  End IntermediateProp.

  Lemma Precomp_is_unitarily_eso
        (Euniv : is_univalent_dagger dagE)
    : is_unitarily_eso (dagger_pre_composition_functor_is_dagger_functor dagH dagE).
  Proof.
    intros [F dagF] p' f.
    apply f.
    exists (_ ,, GG_is_dagger_functor dagF Euniv).
    apply idtodaggeriso.
    use subtypePath.
    { intro ; apply isaprop_is_dagger_functor. }
    apply is_preimage_for_pre_composition.
  Qed.

End Precomp_with_dagger_weak_equiv.

Lemma Precomp_of_dagger_weak_equiv_is_dagger_weak_equiv
      {C D E : category}
      {dagC : dagger C} {dagD : dagger D}
      {H : functor C D}
      {dagH : is_dagger_functor dagC dagD H}
      (wH : is_weak_dagger_equiv dagH)
      {dagE : dagger E}
      (univE : is_univalent_dagger dagE)
  : is_weak_dagger_equiv (dagger_pre_composition_functor_is_dagger_functor dagH dagE).
Proof.
  split.
  - exact (Precomp_is_unitarily_eso _ wH univE).
  - exact (Precomp_is_ff _ wH).
Qed.
