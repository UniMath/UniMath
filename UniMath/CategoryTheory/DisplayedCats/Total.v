
(** * Total Categories and Total Functors *)

Require Import UniMath.Foundations.Sets.

(* Needed for pr1_issurjective *)
Require Import UniMath.MoreFoundations.AxiomOfChoice.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp.

(** ** Definition and forgetful functor *)

(* Any displayed category has a total category, with a forgetful functor to the base category. *)
Section Total_Category.

  Section Total_Category_data.

    Context {C : precategory_data} (D : disp_cat_data C).

    Definition total_category_ob_mor : precategory_ob_mor.
    Proof.
      exists (∑ x:C, D x).
      intros xx yy.
      (* note: we use projections rather than destructing, so that [ xx --> yy ]
         can β-reduce without [xx] and [yy] needing to be in whnf *)
      exact (∑ (f : pr1 xx --> pr1 yy), pr2 xx -->[f] pr2 yy).
    Defined.

    Definition total_category_id_comp : precategory_id_comp (total_category_ob_mor).
    Proof.
      apply tpair; simpl.
      - intros. exists (identity _). apply id_disp.
      - intros xx yy zz ff gg.
        exists (pr1 ff · pr1 gg).
        exact (pr2 ff ;; pr2 gg).
    Defined.

    Definition total_category_data : precategory_data
      := (total_category_ob_mor ,, total_category_id_comp).

  End Total_Category_data.

  (* TODO: make notations [( ,, )] and [ ;; ] different levels?  ;; should bind tighter, perhaps, and ,, looser? *)
  Lemma total_category_is_precat {C : category} (D : disp_cat C) :
    is_precategory (total_category_data D).
  Proof.
    apply is_precategory_one_assoc_to_two.
    repeat apply tpair; simpl.
    - intros xx yy ff; cbn.
      use total2_paths_f; simpl.
      apply id_left.
      eapply pathscomp0.
      apply maponpaths, id_left_disp.
      apply transportfbinv.
    - intros xx yy ff; cbn.
      use total2_paths_f; simpl.
      apply id_right.
      eapply pathscomp0.
      apply maponpaths, id_right_disp.
      apply transportfbinv.
    - intros xx yy zz ww ff gg hh.
      use total2_paths_f; simpl.
      apply assoc.
      eapply pathscomp0.
      apply maponpaths, assoc_disp.
      apply transportfbinv.
  Qed.

  (* The “pre-category” version, without homsets *)
  Definition total_precategory {C : category} (D : disp_cat C) : precategory :=
    (total_category_data D ,, total_category_is_precat D).

  Lemma total_category_has_homsets {C : category} (D : disp_cat C) :
    has_homsets (total_category_data D).
  Proof.
    intros ? ?; simpl. apply isaset_total2. apply homset_property.
    intros; apply homsets_disp.
  Qed.

  Definition total_category {C : category} (D : disp_cat C) : category :=
    (total_precategory D,, total_category_has_homsets D).

  Definition pr1_category_data {C : category} (D : disp_cat C) :
    functor_data (total_category D) C.
  Proof.
    exists pr1.
    intros a b; exact pr1.
  Defined.

  Lemma pr1_category_is_functor {C : category} (D : disp_cat C) :
    is_functor (pr1_category_data D).
  Proof.
    apply tpair.
    - intros x; apply idpath.
    - intros x y z f g; apply idpath.
  Qed.

  Definition pr1_category {C : category} (D : disp_cat C) :
    functor (total_category D) C :=
    make_functor (pr1_category_data D) (pr1_category_is_functor D).

  Lemma full_pr1_category {C : category} (D : disp_cat C)
        (H : ∏ (a b : total_category D) (x : C ⟦ pr1 a, pr1 b ⟧), (∥ pr2 a -->[ x] pr2 b ∥))
    : full (pr1_category D).
  Proof.
    intros ? ?.
    use pr1_issurjective.
    apply H.
  Defined.

  Lemma faithful_pr1_category {C : category} (D : disp_cat C)
        (H : ∏ (a b : total_precategory D) (x : C ⟦ pr1 a, pr1 b ⟧), isaprop (pr2 a -->[ x] pr2 b))
    : faithful (pr1_category D).
  Proof.
    intros ? ?.
    apply isinclpr1, H.
  Defined.

  Definition fully_faithful_pr1_category {C : category} (D : disp_cat C)
             (H : ∏ (a b : total_precategory D) (x : C ⟦ pr1 a, pr1 b ⟧), iscontr (pr2 a -->[ x] pr2 b))
    : fully_faithful (pr1_category D).
  Proof.
    intros ? ?.
    apply isweqpr1, H.
  Defined.

  (** ** Isomorphisms and saturation *)

  Definition is_iso_total {C : category} {D : disp_cat C}
             {xx yy : total_category D} (ff : xx --> yy)
             (i : is_iso (pr1 ff))
             (fi := make_iso (pr1 ff) i)
             (ii : is_iso_disp fi (pr2 ff))
    : is_iso ff.
  Proof.
    apply is_iso_from_is_z_iso.
    exists (inv_from_iso fi,, pr1 ii).
    split.
    - use total2_paths_f.
      apply (iso_inv_after_iso fi).
      etrans. apply maponpaths. apply (inv_mor_after_iso_disp ii).
      apply transportfbinv.
    - use total2_paths_f.
      apply (iso_after_iso_inv fi).
      etrans. apply maponpaths. apply (iso_disp_after_inv_mor ii).
      apply transportfbinv.
  Qed.

  Definition inv_from_iso_in_total
             {C : category}
             {D : disp_cat C}
             {x y : C}
             {f : x --> y}
             (Hf : is_iso f)
             {xx : D x}
             {yy : D y}
             {ff : xx -->[ f ] yy}
             (Hff : is_iso_disp (make_iso f Hf) ff)
    : pr1 (inv_from_iso
             (make_iso
                _
                (@is_iso_total
                   C D
                   (x ,, xx) (y ,, yy)
                   (f ,, ff)
                   Hf
                   Hff)))
      =
        inv_from_iso (make_iso _ Hf).
  Proof.
    use inv_iso_unique'.
    unfold precomp_with ; cbn.
    exact (maponpaths
             pr1
             (iso_inv_after_iso
                (make_iso
                   _
                   (@is_iso_total
                      C D
                      (x ,, xx) (y ,, yy)
                      (f ,, ff)
                      Hf
                      Hff)))).
  Qed.

  Definition is_iso_base_from_total {C : category} {D : disp_cat C}
             {xx yy : total_category D} {ff : xx --> yy} (i : is_iso ff)
    : is_iso (pr1 ff).
  Proof.
    set (ffi := make_iso ff i).
    apply (is_iso_qinv _ (pr1 (inv_from_iso ffi))).
    split.
    - exact (maponpaths pr1 (iso_inv_after_iso ffi)).
    - exact (maponpaths pr1 (iso_after_iso_inv ffi)).
  Qed.

  Definition iso_base_from_total {C : category} {D : disp_cat C}
             {xx yy : total_category D} (ffi : iso xx yy) : iso (pr1 xx) (pr1 yy) :=
    make_iso _ (is_iso_base_from_total (pr2 ffi)).

  Definition inv_iso_base_from_total {C : category} {D : disp_cat C}
             {xx yy : total_precategory D} (ffi : iso xx yy) :
    inv_from_iso (iso_base_from_total ffi) = pr1 (inv_from_iso ffi).
  Proof.
    apply pathsinv0, inv_iso_unique'. unfold precomp_with.
    exact (maponpaths pr1 (iso_inv_after_iso ffi)).
  Qed.

  Definition is_iso_disp_from_total {C : category} {D : disp_cat C}
             {xx yy : total_precategory D} {ff : xx --> yy} (i : is_iso ff) (ffi := make_iso ff i) :
    is_iso_disp (iso_base_from_total (ff,,i)) (pr2 ff).
  Proof.
    use tpair; [ | split].
    - eapply transportb. apply inv_iso_base_from_total.
      exact (pr2 (inv_from_iso ffi)).
    - etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths, @pathsinv0.
      exact (fiber_paths (!iso_after_iso_inv ffi)).
      etrans. apply transport_f_f.
      use (toforallpaths _ _ _ _ (id_disp _)).
      unfold transportb; apply maponpaths, homset_property.
    - etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths, @pathsinv0.
      exact (fiber_paths (!iso_inv_after_iso ffi)).
      etrans. apply transport_f_f.
      use (toforallpaths _ _ _ _ (id_disp _)).
      unfold transportb; apply maponpaths, homset_property.
  Qed.

  Definition iso_disp_from_total {C : category} {D : disp_cat C}
             {xx yy : total_precategory D} (ff : iso xx yy) :
    iso_disp (iso_base_from_total ff) (pr2 xx) (pr2 yy).
  Proof.
    exact (_,, is_iso_disp_from_total (pr2 ff)).
  Defined.

  Definition total_iso {C : category} {D : disp_cat C} {xx yy : total_category D}
             (f : iso (pr1 xx) (pr1 yy)) (ff : iso_disp f (pr2 xx) (pr2 yy))
    : iso xx yy.
  Proof.
    exists (pr1 f,, pr1 ff).
    apply (is_iso_total (pr1 f,, pr1 ff) (pr2 f) (pr2 ff)).
  Defined.

  Lemma inv_mor_total_iso {C : category} {D : disp_cat C} {xx yy : total_category D}
        (f : iso (pr1 xx) (pr1 yy)) (ff : iso_disp f (pr2 xx) (pr2 yy))
    : inv_from_iso (total_iso f ff)
      = (inv_from_iso f,, inv_mor_disp_from_iso ff).
  Proof.
    (* Could de-opacify [is_iso_total] and then use [inv_from_iso_from_is_z_iso].  If de-opacfying [is_iso_total] would make its inverse compute definitionally, that’d be wonderful, but for the sake of just this one lemma, it’s probably not worth it.  So we prove this the hard way. *)
    apply cancel_precomposition_iso with (total_iso f ff).
    etrans. apply iso_inv_after_iso. apply pathsinv0.
    use total2_paths_f; cbn.
    - apply iso_inv_after_iso.
    - etrans. apply maponpaths, inv_mor_after_iso_disp.
      apply transportfbinv.
  Qed.

  Definition total_iso_equiv_map {C : category} {D : disp_cat C} {xx yy : total_category D}
    : (∑ f : iso (pr1 xx) (pr1 yy), iso_disp f (pr2 xx) (pr2 yy))
      -> iso xx yy
    := λ ff, total_iso (pr1 ff) (pr2 ff).

  Definition total_isweq_iso {C : category} {D : disp_cat C} (xx yy : total_category D)
    : isweq (@total_iso_equiv_map _ _ xx yy).
  Proof.
    use isweq_iso.
    - intros ff. exists (iso_base_from_total ff). apply iso_disp_from_total.
    - intros [f ff]. use total2_paths_f.
      + apply eq_iso, idpath.
      + apply eq_iso_disp.
        etrans. apply transportf_iso_disp.
        simpl pr2. simpl (pr1 (iso_disp_from_total _)).
        use (@maponpaths_2 _ _ _ (transportf _) _ (idpath _)).
        apply homset_property.
    - intros f. apply eq_iso; simpl.
      destruct f as [[f ff] w]; apply idpath.
  Qed.

  Definition total_iso_equiv {C : category} {D : disp_cat C} (xx yy : total_category D)
    : (∑ f : iso (pr1 xx) (pr1 yy), iso_disp f (pr2 xx) (pr2 yy))
        ≃ iso xx yy
    := make_weq _ (total_isweq_iso xx yy).

  Lemma is_univalent_total_category {C : category} {D : disp_cat C}
        (CC : is_univalent C) (DD : is_univalent_disp D) :
    is_univalent (total_category D).
  Proof.
    intros xs ys.
    set (x := pr1 xs). set (xx := pr2 xs).
    set (y := pr1 ys). set (yy := pr2 ys).
    use weqhomot.
    apply (@weqcomp _ (∑ e : x = y, transportf _ e xx = yy) _).
    apply total2_paths_equiv.
    apply (@weqcomp _ (∑ e : x = y, iso_disp (idtoiso e) xx yy) _).
    apply weqfibtototal.
    intros e. exists (λ ee, idtoiso_disp e ee).
    apply DD.
    apply (@weqcomp _ (∑ f : iso x y, iso_disp f xx yy) _).
    use (weqfp (make_weq _ _)). apply CC.
    apply total_iso_equiv.
    intros e; destruct e; apply eq_iso; cbn.
    apply idpath.
  Qed.

End Total_Category.

Arguments pr1_category [C] D.

Section TotalUnivalent.
  Definition total_univalent_category
             {C : univalent_category}
             (D : disp_univalent_category C)
    : univalent_category.
  Proof.
    use make_univalent_category.
    - exact (total_category D).
    - exact (is_univalent_total_category (pr2 C) (pr2 D)).
  Defined.
End TotalUnivalent.

(** ** Total functors of displayed functors*)
Section Total_Functors.

  Definition total_functor_data {C' C} {F}
             {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D' D)
    : functor_data (total_category D') (total_category D).
  Proof.
    use tpair.
    - intros xx. exists (F (pr1 xx)). exact (FF _ (pr2 xx)).
    - intros xx yy ff. exists (# F (pr1 ff))%cat. exact (# FF (pr2 ff)).
  Defined.

  Definition total_functor_axioms {C' C} {F}
             {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D' D)
    : is_functor (total_functor_data FF).
  Proof.
    split.
    - intros xx; use total2_paths_f.
      apply functor_id.
      etrans. apply maponpaths, disp_functor_id.
      apply transportfbinv.
    - intros xx yy zz ff gg; use total2_paths_f; simpl.
      apply functor_comp.
      etrans. apply maponpaths, disp_functor_comp.
      apply transportfbinv.
  Qed.

  Definition total_functor {C' C} {F}
             {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D' D)
    : functor (total_category D') (total_category D)
    := (total_functor_data FF,, total_functor_axioms FF).


  (** Laws for total fucntors *)
  Definition total_functor_commute
             {C₁ C₂ : category}
             {F : C₁ ⟶ C₂}
             {D₁ : disp_cat C₁}
             {D₂ : disp_cat C₂}
             (FF : disp_functor F D₁ D₂)
    : pr1_category D₁ ∙ F ⟹ total_functor FF ∙ pr1_category D₂.
  Proof.
    use make_nat_trans.
    - exact (λ _, identity _).
    - abstract
        (intros ? ? ? ;
         cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition total_functor_commute_iso
             {C₁ C₂ : category}
             {F : C₁ ⟶ C₂}
             {D₁ : disp_cat C₁}
             {D₂ : disp_cat C₂}
             (FF : disp_functor F D₁ D₂)
    : nat_iso
        (pr1_category D₁ ∙ F)
        (total_functor FF ∙ pr1_category D₂).
  Proof.
    use make_nat_iso.
    * exact (total_functor_commute FF).
    * intro.
      apply identity_is_iso.
  Defined.

  Definition total_functor_identity
             {C : category}
             (D : disp_cat C)
    : functor_identity (total_category D)
                       ⟹
                       total_functor (disp_functor_identity D).
  Proof.
    use make_nat_trans.
    - exact (λ _, identity _).
    - abstract
        (intros ? ? ? ; simpl ;
         refine (@id_right (total_category _) _ _ _ @ _) ;
         exact (!(@id_left (total_category _) _ _ _))).
  Defined.

  Definition total_functor_comp
             {C₁ C₂ C₃ : category}
             {F : C₁ ⟶ C₂}
             {G : C₂ ⟶ C₃}
             {D₁ : disp_cat C₁}
             {D₂ : disp_cat C₂}
             {D₃ : disp_cat C₃}
             (FF : disp_functor F D₁ D₂)
             (GG : disp_functor G D₂ D₃)
    : total_functor FF ∙ total_functor GG
                    ⟹
                    total_functor (disp_functor_composite FF GG).
  Proof.
    use make_nat_trans.
    - exact (λ _, identity _).
    - abstract
        (intros x y f ;
         refine (@id_right (total_category _) _ _ _ @ _) ;
         exact (!(@id_left (total_category _) _ _ _))).
  Defined.

End Total_Functors.

Section Total_Nat_Trans.
  (** Total natural transformation *)
  Definition total_nat_trans
             {C₁ C₂ : category}
             {F G : C₁ ⟶ C₂}
             {τ : F ⟹ G}
             {D₁ : disp_cat C₁}
             {D₂ : disp_cat C₂}
             {FF : disp_functor F D₁ D₂}
             {GG : disp_functor G D₁ D₂}
             (ττ : disp_nat_trans τ FF GG)
    : nat_trans (total_functor FF) (total_functor GG).
  Proof.
    use make_nat_trans.
    - exact (λ x, τ (pr1 x) ,, ττ (pr1 x) (pr2 x)).
    - abstract
        (intros x y f ; cbn ;
         use total2_paths_b ;
         [ exact (nat_trans_ax τ _ _ (pr1 f))
         | exact (disp_nat_trans_ax ττ (pr2 f))]).
  Defined.

End Total_Nat_Trans.
