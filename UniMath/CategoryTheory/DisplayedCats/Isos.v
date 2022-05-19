
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** ** Isomorphisms (and lemmas) *)

Section Isos.

  Definition is_z_iso_disp {C : precategory} {D : disp_cat_data C}
             {x y : C} (f : z_iso x y) {xx : D x} {yy} (ff : xx -->[f] yy)
    : UU
    := ∑ (gg : yy -->[inv_from_z_iso f] xx),
      gg ;; ff = transportb _ (z_iso_after_z_iso_inv _) (id_disp _)
                            × ff ;; gg = transportb _ (z_iso_inv_after_z_iso _) (id_disp _).

  Definition z_iso_disp {C : precategory} {D : disp_cat_data C}
             {x y : C} (f : z_iso x y) (xx : D x) (yy : D y)
    := ∑ ff : xx -->[f] yy, is_z_iso_disp f ff.

  Definition make_z_iso_disp {C : precategory} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y} {xx : D x} {yy : D y}
             (ff : xx -->[f] yy) (is : is_z_iso_disp f ff)
    : z_iso_disp _ _ _
    := (ff,, is).

  Definition mor_disp_from_z_iso {C : precategory} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y}{xx : D x} {yy : D y}
             (i : z_iso_disp f xx yy) : _ -->[ _ ] _ := pr1 i.
  Coercion mor_disp_from_z_iso : z_iso_disp >-> mor_disp.

  Definition is_z_iso_disp_from_z_iso {C : precategory} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y}{xx : D x} {yy : D y}
             (i : z_iso_disp f xx yy) : is_z_iso_disp f i := pr2 i.
  Coercion is_z_iso_disp_from_z_iso : z_iso_disp >-> is_z_iso_disp.

  Definition inv_mor_disp_from_z_iso {C : precategory} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y}{xx : D x} {yy : D y}
             {ff : xx -->[f] yy} (i : is_z_iso_disp f ff)
    : _ -->[ _ ] _ := pr1 i.

  Definition z_iso_disp_after_inv_mor {C : precategory} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y}{xx : D x} {yy : D y}
             {ff : xx -->[f] yy} (i : is_z_iso_disp f ff)
    : inv_mor_disp_from_z_iso i ;; ff
      = transportb _ (z_iso_after_z_iso_inv _) (id_disp _).
  Proof.
    apply (pr2 i).
  Qed.

  Definition inv_mor_after_z_iso_disp {C : precategory} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y}{xx : D x} {yy : D y}
             {ff : xx -->[f] yy} (i : is_z_iso_disp f ff)
    : ff ;; inv_mor_disp_from_z_iso i
      = transportb _ (z_iso_inv_after_z_iso _) (id_disp _).
  Proof.
    apply (pr2 (pr2 i)).
  Qed.

  Lemma isaprop_is_z_iso_disp {C : category} {D : disp_cat C}
        {x y : C} (f : z_iso x y) {xx : D x} {yy} (ff : xx -->[f] yy)
    : isaprop (is_z_iso_disp f ff).
  Proof.
    apply invproofirrelevance; intros i i'.
    apply subtypePath.
    - intros gg. apply isapropdirprod; apply homsets_disp.
    (* uniqueness of inverses *)
    (* TODO: think about better lemmas for this sort of calculation?
  e.g. all that repeated application of [transport_f_f], etc. *)
    - destruct i as [gg [gf fg]], i' as [gg' [gf' fg']]; simpl.
      etrans. eapply pathsinv0, transportfbinv.
      etrans. apply maponpaths, @pathsinv0, id_right_disp.
      etrans. apply maponpaths, maponpaths.
      etrans. eapply pathsinv0, transportfbinv.
      apply maponpaths, @pathsinv0, fg'.
      etrans. apply maponpaths, mor_disp_transportf_prewhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths, assoc_disp.
      etrans. apply transport_f_f.
      etrans. apply maponpaths, maponpaths_2, gf.
      etrans. apply maponpaths, mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths, id_left_disp.
      etrans. apply transport_f_f.
      use (@maponpaths_2 _ _ _ (transportf _) _ (idpath _)).
      apply homset_property.
  Qed.

  Lemma isaset_z_iso_disp {C : category} {D : disp_cat C}
        {x y} (f : z_iso x y) (xx : D x) (yy : D y)
    : isaset (z_iso_disp f xx yy).
  Proof.
    apply isaset_total2.
    - apply homsets_disp.
    - intros. apply isasetaprop, isaprop_is_z_iso_disp.
  Qed.

  Lemma eq_z_iso_disp {C : category} {D : disp_cat C}
        {x y : C} (f : z_iso x y)
        {xx : D x} {yy} (ff ff' : z_iso_disp f xx yy)
    : pr1 ff = pr1 ff' -> ff = ff'.
  Proof.
    apply subtypePath; intro; apply isaprop_is_z_iso_disp.
  Qed.

  Lemma is_z_iso_disp_transportf {C : category} {D : disp_cat C}
        {x y : C} {f f' : z_iso x y} (e : f = f')
        {xx : D x} {yy} {ff : xx -->[f] yy}
        (is : is_z_iso_disp _ ff)
    : is_z_iso_disp f' (transportf _ (maponpaths _ e) ff).
  Proof.
    induction e.
    apply is.
  Qed.

  Lemma transportf_z_iso_disp {C : category} {D : disp_cat C}
        {x y : C} {xx : D x} {yy}
        {f f' : z_iso x y} (e : f = f')
        (ff : z_iso_disp f xx yy)
    : pr1 (transportf (λ g, z_iso_disp g _ _) e ff)
      = transportf _ (maponpaths pr1 e) (pr1 ff).
  Proof.
    destruct e; apply idpath.
  Qed.

  Definition is_z_iso_inv_from_z_iso_disp {C : category} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y}{xx : D x} {yy : D y}
             (i : z_iso_disp f xx yy)
    :
    is_z_iso_disp (z_iso_inv_from_z_iso f) (inv_mor_disp_from_z_iso i).
  Proof.
    use tpair.
    - change ( xx -->[ z_iso_inv_from_z_iso (z_iso_inv_from_z_iso f)] yy).
      set (XR := transportb (mor_disp xx yy )
                            (maponpaths pr1 (z_iso_inv_z_iso_inv _ _ f))).
      apply XR. apply i.
    - cbn.
      split.
      + abstract (
            etrans ;[ apply mor_disp_transportf_postwhisker |];
            etrans ; [ apply maponpaths; apply (inv_mor_after_z_iso_disp i)  | ];
            etrans ;[ apply transport_f_f |];
            apply transportf_comp_lemma; apply transportf_comp_lemma_hset;
            try apply homset_property; apply idpath ).
      + abstract (
            etrans ;[ apply mor_disp_transportf_prewhisker |];
            etrans ;[ apply maponpaths; apply (z_iso_disp_after_inv_mor i) |];
            etrans ;[ apply transport_f_f |];
            apply transportf_comp_lemma; apply transportf_comp_lemma_hset;
            try apply homset_property; apply idpath ).
  Defined.

  Definition is_z_iso_inv_from_is_z_iso_disp {C : category} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y}{xx : D x} {yy : D y}
             (ff : xx -->[f] yy)
             (i : is_z_iso_disp f ff)
    :
    is_z_iso_disp (z_iso_inv_from_z_iso f) (inv_mor_disp_from_z_iso i).
  Proof.
    apply (is_z_iso_inv_from_z_iso_disp (ff ,, i)).
  Defined.

  Definition z_iso_inv_from_z_iso_disp {C : category} {D : disp_cat_data C}
             {x y : C} {f : z_iso x y}{xx : D x} {yy : D y}
             (i : z_iso_disp f xx yy)
    :
    z_iso_disp (z_iso_inv_from_z_iso f) yy xx.
  Proof.
    exists (inv_mor_disp_from_z_iso i).
    apply is_z_iso_inv_from_z_iso_disp.
  Defined.

  Definition z_iso_disp_comp {C : category} {D : disp_cat C}
             {x y z : C} {f : z_iso x y} {g : z_iso y z} {xx : D x} {yy : D y} {zz : D z}
             (ff : z_iso_disp f xx yy) (gg : z_iso_disp g yy zz)
    :
    z_iso_disp (z_iso_comp f g) xx zz.
  Proof.
    use tpair.
    - apply (ff ;; gg).
    - use tpair.
      + apply (transportb (mor_disp zz xx) (maponpaths pr1 (z_iso_inv_of_z_iso_comp _ _ _ f g))).
        cbn.
        apply (inv_mor_disp_from_z_iso gg ;; inv_mor_disp_from_z_iso ff).
      + split.
        * etrans. apply mor_disp_transportf_postwhisker.
          etrans. apply maponpaths. apply assoc_disp_var.
          etrans. apply maponpaths, maponpaths, maponpaths.
          apply assoc_disp.
          etrans. apply maponpaths, maponpaths, maponpaths, maponpaths.
          eapply (maponpaths (λ x, x ;; gg)).
          apply z_iso_disp_after_inv_mor.
          etrans. apply transport_f_f.
          etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
          etrans.  apply transport_f_f.
          etrans. apply maponpaths, maponpaths.
          apply mor_disp_transportf_postwhisker.
          etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
          etrans. apply transport_f_f.
          etrans. apply maponpaths, maponpaths. apply id_left_disp.
          etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
          etrans. apply transport_f_f.
          etrans. apply maponpaths. apply z_iso_disp_after_inv_mor.
          etrans. apply transport_f_f.
          apply transportf_comp_lemma; apply transportf_comp_lemma_hset;
            try apply homset_property; apply idpath.
        * cbn. simpl.
          etrans. apply assoc_disp_var.
          etrans. apply maponpaths, maponpaths.
          apply mor_disp_transportf_prewhisker.
          etrans. apply maponpaths, maponpaths, maponpaths.
          apply assoc_disp.
          etrans. apply maponpaths, maponpaths, maponpaths, maponpaths.
          eapply (maponpaths (λ x, x ;; inv_mor_disp_from_z_iso ff )).
          apply inv_mor_after_z_iso_disp.
          etrans. apply maponpaths, maponpaths, maponpaths, maponpaths.
          apply mor_disp_transportf_postwhisker.
          etrans. apply maponpaths, maponpaths, maponpaths, maponpaths, maponpaths.
          apply id_left_disp.
          etrans. apply maponpaths, maponpaths. apply transport_f_f.
          etrans. apply maponpaths, maponpaths. apply transport_f_f.
          etrans.  apply maponpaths, maponpaths. apply transport_f_f.
          etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
          etrans. apply transport_f_f.
          etrans. apply maponpaths.
          apply inv_mor_after_z_iso_disp.
          etrans. apply transport_f_f.
          apply transportf_comp_lemma; apply transportf_comp_lemma_hset;
            try apply homset_property; apply idpath.
  Defined.

  Definition id_is_z_iso_disp {C} {D : disp_cat C} {x : C} (xx : D x)
    : is_z_iso_disp (identity_z_iso x) (id_disp xx).
  Proof.
    exists (id_disp _); split.
    - etrans. apply id_left_disp.
      apply maponpaths_2, homset_property.
    - etrans. apply id_left_disp.
      apply maponpaths_2, homset_property.
  Defined.

  Definition identity_z_iso_disp {C} {D : disp_cat C} {x : C} (xx : D x)
    : z_iso_disp (identity_z_iso x) xx xx
    := (_ ,, id_is_z_iso_disp _).

  Lemma idtoiso_disp {C} {D : disp_cat C}
        {x x' : C} (e : x = x')
        {xx : D x} {xx' : D x'} (ee : transportf _ e xx = xx')
    : z_iso_disp (idtoiso e) xx xx'.
  Proof.
    destruct e, ee; apply identity_z_iso_disp.
  Defined.

  Lemma idtoiso_fiber_disp {C} {D : disp_cat C} {x : C}
        {xx xx' : D x} (ee : xx = xx')
    : z_iso_disp (identity_z_iso x) xx xx'.
  Proof.
    exact (idtoiso_disp (idpath _) ee).
  Defined.


  Lemma z_iso_disp_precomp {C : category} {D : disp_cat C}
        {x y : C} (f : z_iso x y)
        {xx : D x} {yy} (ff : z_iso_disp f xx yy)
    : forall (y' : C) (f' : y --> y') (yy' : D y'),
      isweq (fun ff' : yy -->[ f' ] yy' => pr1 ff ;; ff').
  Proof.
    intros y' f' yy'.
    use isweq_iso.
    + intro X.
      set (XR := (pr1 (pr2 ff)) ;; X).
      set (XR' := transportf _ (assoc _ _ _   ) XR).
      set (XRRT := transportf _
                              (maponpaths (λ xyz, xyz · f') (z_iso_after_z_iso_inv f))
                              XR').
      set (XRRT' := transportf _ (id_left _ )
                               XRRT).
      apply XRRT'.
    + intros. simpl.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply assoc_disp.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply maponpaths_2. apply (pr2 (pr2 ff)).
      etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply id_left_disp.
      etrans. apply transport_f_f.
      apply transportf_comp_lemma_hset.
      apply C. apply idpath.
    + intros; simpl.
      etrans. apply maponpaths. apply transport_f_f.
      etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply assoc_disp.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply maponpaths_2.
      assert (XR := pr2 (pr2 (pr2 ff))). simpl in XR. apply XR.
      etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply id_left_disp.
      etrans. apply transport_f_f.
      apply transportf_comp_lemma_hset.
      apply C. apply idpath.
  Defined.

  Lemma z_iso_disp_postcomp {C : category} {D : disp_cat C}
        {x y : C} (i : z_iso x y)
        {xx : D x} {yy} (ii : z_iso_disp i xx yy)
    : forall (x' : C) (f' : x' --> x) (xx' : D x'),
      isweq (fun ff : xx' -->[ f' ] xx => ff ;; ii)%mor_disp.
  Proof.
    intros y' f' yy'.
    use isweq_iso.
    + intro X.
      set (XR := X ;; (pr1 (pr2 ii))).
      set (XR' := transportf (λ x, _ -->[ x ] _) (!assoc _ _ _   ) XR).
      set (XRRT := transportf (λ x, _ -->[ x ] _ )
                              (maponpaths (λ xyz, _ · xyz) (z_iso_inv_after_z_iso _ ))
                              XR').
      set (XRRT' := transportf _ (id_right _ )
                               XRRT).
      apply XRRT'.
    + intros. simpl.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply assoc_disp_var.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply maponpaths. apply (pr2 (pr2 (pr2 ii))).
      etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply id_right_disp.
      etrans. apply transport_f_f.
      apply transportf_comp_lemma_hset.
      apply C. apply idpath.
    + intros; simpl.
      etrans. apply maponpaths_2. apply transport_f_f.
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply assoc_disp_var.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply maponpaths.
      assert (XR := pr1 (pr2 (pr2 ii))). simpl in XR. apply XR.
      etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply id_right_disp.
      etrans. apply transport_f_f.
      apply transportf_comp_lemma_hset.
      apply C. apply idpath.
  Defined.


  (* Useful when you want to prove [is_z_iso_disp], and you have some lemma [awesome_lemma] which gives that, but over a different (or just opaque) proof of [is_z_isomorphism] in the base.  Then you can use [eapply is_z_iso_disp_independent_of_is_z_iso; apply awesome_lemma.]. *)
  Lemma is_z_iso_disp_independent_of_is_z_iso
        {C : category} {D : disp_cat_data C}
        {x y : C} (f : z_iso x y) {xx : D x} {yy} (ff : xx -->[f] yy)
        {H'f : is_z_isomorphism f} (Hff : is_z_iso_disp ((f : _ --> _),,H'f) ff)
    : is_z_iso_disp f ff.
  Proof.
    destruct f as [F Hf].
    assert (E : Hf = H'f). apply isaprop_is_z_isomorphism.
    destruct E. exact Hff.
  Qed.

End Isos.

(** ** More utility lemmas *)

(** A few more general lemmas for displayed-cat algebra, that require isomorphisms to state. *)
Section Utilities.

  (** Note: closely analogous to [idtoiso_precompose].  We name it differently to fit the convention of naming equalities according to their LHS, for reference during calculation. *)
  Lemma transportf_precompose_disp {C} {D : disp_cat C}
        {c d : C} (f : c --> d )
        {cc cc' : D c} (e : cc = cc') {dd} (ff : cc -->[f] dd)
    : transportf (λ xx : D c, xx -->[f] dd) e ff
      = transportf _ (id_left _)
                   (z_iso_inv_from_z_iso_disp (idtoiso_disp (idpath _) (e)) ;; ff).
  Proof.
    destruct e; cbn.
    rewrite (@id_left_disp _ _ _ _ _ cc).
    apply pathsinv0, transportfbinv.
  Qed.

  (* TODO: add dual [transportf_postcompose_disp]. *)

  Definition precomp_with_z_iso_disp_is_inj
             {C : category} {D : disp_cat C}
             {a b c : C} {i : z_iso a b} {f : b --> c}
             {aa : D a} {bb} {cc} (ii : z_iso_disp i aa bb) {ff ff' : bb -->[f] cc}
    : (ii ;; ff = ii ;; ff') -> ff = ff'.
  Proof.
    intros e.
    use pathscomp0.
    - use (transportf _ _ ((z_iso_inv_from_z_iso_disp ii ;; ii) ;; ff)).
      etrans; [ apply maponpaths_2, z_iso_after_z_iso_inv | apply id_left ].
    - apply pathsinv0.
      etrans. eapply transportf_bind.
      eapply cancel_postcomposition_disp, (z_iso_disp_after_inv_mor ii).
      rewrite (@id_left_disp _ _ _ _ _ bb).
      etrans. apply transport_f_f.
      use (@maponpaths_2 _ _ _ _ _ (idpath _)).
      apply homset_property.
    - etrans. eapply transportf_bind, assoc_disp_var.
      rewrite e.
      etrans. eapply transportf_bind, assoc_disp.
      etrans. eapply transportf_bind.
      eapply cancel_postcomposition_disp, (z_iso_disp_after_inv_mor ii).
      rewrite id_left_disp.
      etrans. apply transport_f_f.
      use (@maponpaths_2 _ _ _ _ _ (idpath _)).
      apply homset_property.
  Qed.

  (* TODO: add dual [postcomp_with_iso_disp_is_inj]. *)

  Definition postcomp_with_z_iso_disp_is_inj
             {C : category}
             {D : disp_cat C}
             {x y z : C}
             {f : x --> y}
             {g : x --> y}
             {h : y --> z}
             (Hh : is_z_isomorphism h)
             (p : f = g)
             {xx : D x}
             {yy : D y}
             {zz : D z}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             {hh : yy -->[ h ] zz}
             (Hhh : is_z_iso_disp (h ,, Hh) hh)
             (pp : (ff ;; hh
                    =
                      transportb
                        (λ z, _ -->[ z ] _)
                        (maponpaths (λ z, _ · h) p)
                        (gg ;; hh))%mor_disp)
    : ff = transportb _ p gg.
  Proof.
    refine (id_right_disp_var _ @ _).
    pose (transportb_transpose_left (inv_mor_after_z_iso_disp Hhh)) as q.
    etrans.
    {
      do 2 apply maponpaths.
      exact (!q).
    }
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact pp.
    }
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      exact (inv_mor_after_z_iso_disp Hhh).
    }
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite id_right_disp.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.
End Utilities.
