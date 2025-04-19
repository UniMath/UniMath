(***********************************************************************************************

 What is the plan?
 - The displayed bicategory of univalent categories with finite limits and a universe object
   must be constructed in two steps
 - The first step: just add an object
 - Second step: add the `El` map
 - After that, we take the `Sigma`

 What do the desired bicats look like?
 - FinLim with universe: add universe, add type formers
 - LCCC: product of universe and LCCC, add type formers
 - everything with local property and LCCC: same idea

 The equivalence with the usual definition of universe can also be proven.
 This missing ingredient was one of the coherences that should be added

 Main steps:
 - Make a file with the important basic definitions of universes
 - Make a file with the displayed bicategory over FinLim
 - Make a file with the equivalent with the map

 Dealing with type formers:
 - Type formers should be written similarly for compcats and for cats with finlim
 - Make a file with the basic definitions of the type formers,
   e.g., when is the universe in a cat with ∏-types closed under ∏-types
   and similar for the other type formers

 For the displayed bicategory: each of the 2-cell operations should be a separate proposition
 with the simplified statement. This improves compilation time, and it gives nicer goals. In
 addition, the coercions will work better.

 Ultimately, the file structure will be

 ComprehensionCat -> Universes -> InCategory    -> CatWithOb
                                                -> CatWithElMap
                                                -> UniverseAsMorphism
                                                -> BicatOfCatWithUniv
                                                -> CatWithUnivTypeFormers
                               -> InCompCat     -> CompCatWithOb
                                                -> CompCatWithElMap
                                                -> BicatOfCompCatWithUniv
                                                -> CompCatWithUnivTypeFormers
                               -> Biequivalence -> TO BE DETERMINED

 Necessary type formers:
 1. ∑-types
 2. Extensional identity types
 3. Unit types
 4. ∏-types
 5. Quotient types
 6. Empty type
 7. Coproduct types
 8. Natural numbers type
 9. Subobject classifier type

 For product biequivalence:
     Needed: all 2-cells are equal and invertible
     satisfied in this example



 adding the el map must also come with stability
 this is needed to express the coherence condition for 2-cells


 Content
 1. The map assigning types to terms of the universe
 2. Stability

 2. Preservation by functors and examples of such functors

 ***********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithOb.

Local Open Scope cat.

(** * 1. The map assigning types to terms of the universe *)
Definition cat_el_map
           (C : univ_cat_with_finlim_ob)
  : UU
  := ∏ (Γ : C),
     Γ --> univ_cat_universe C
     →
     ∑ (e : C), e --> Γ.

Definition cat_el_map_el
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
           {Γ : C}
           (t : Γ --> univ_cat_universe C)
  : C
  := pr1 (el Γ t).

Definition cat_el_map_mor
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
           {Γ : C}
           (t : Γ --> univ_cat_universe C)
  : cat_el_map_el el t --> Γ
  := pr2 (el Γ t).

Definition cat_el_map_el_eq
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
           {Γ : C}
           {t t' : Γ --> univ_cat_universe C}
           (p : t = t')
  : z_iso (cat_el_map_el el t) (cat_el_map_el el t').
Proof.
  induction p.
  apply identity_z_iso.
Defined.

Proposition cat_el_map_el_eq_eq
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map C)
            {Γ : C}
            {t t' : Γ --> univ_cat_universe C}
            (p p' : t = t')
  : pr1 (cat_el_map_el_eq el p) = cat_el_map_el_eq el p'.
Proof.
  assert (p = p') as ->.
  {
    apply homset_property.
  }
  apply idpath.
Qed.

Notation "'el_eq'" := (cat_el_map_el_eq _ _) (only printing).

Proposition cat_el_map_el_eq_id
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map C)
            {Γ : C}
            {t : Γ --> univ_cat_universe C}
            (p : t = t)
  : pr1 (cat_el_map_el_eq el p)
    =
    identity _.
Proof.
  assert (p = idpath _) as ->.
  {
    apply homset_property.
  }
  apply idpath.
Qed.

Proposition cat_el_map_el_eq_comp
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map C)
            {Γ : C}
            {t t' t'' : Γ --> univ_cat_universe C}
            (p : t = t')
            (q : t' = t'')
  : cat_el_map_el_eq el p · cat_el_map_el_eq el q
    =
    cat_el_map_el_eq el (p @ q).
Proof.
  induction p, q ; cbn.
  apply id_left.
Qed.

Proposition cat_el_map_mor_eq
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map C)
            {Γ : C}
            {t t' : Γ --> univ_cat_universe C}
            (p : t = t')
  : cat_el_map_el_eq el p · cat_el_map_mor el t'
    =
    cat_el_map_mor el t.
Proof.
  induction p ; cbn.
  apply id_left.
Qed.

Proposition cat_el_map_el_eq_postcomp
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map C)
            {Γ : C}
            {t t' : Γ --> univ_cat_universe C}
            (p₁ p₂ : t = t')
            {x : C}
            {f g : x --> cat_el_map_el el t}
            (q : f = g)
  : f · cat_el_map_el_eq el p₁ = g · cat_el_map_el_eq el p₂.
Proof.
  induction q.
  apply maponpaths.
  apply cat_el_map_el_eq_eq.
Qed.

Proposition cat_el_map_el_eq_precomp
            {C : univ_cat_with_finlim_ob}
            (el : cat_el_map C)
            {Γ : C}
            {t t' : Γ --> univ_cat_universe C}
            (p₁ p₂ : t = t')
            {x : C}
            {f g : cat_el_map_el el t' --> x}
            (q : f = g)
  : cat_el_map_el_eq el p₁ · f
    =
    cat_el_map_el_eq el p₂ · g.
Proof.
  induction q.
  apply maponpaths_2.
  apply cat_el_map_el_eq_eq.
Qed.

(** * 2. Stability *)
Definition cat_el_map_stable
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
  : UU
  := ∏ (Γ Δ : C)
       (s : Γ --> Δ)
       (t : Δ --> univ_cat_universe C),
     ∑ (f : cat_el_map_el el (s · t) --> cat_el_map_el el t)
       (p : f · cat_el_map_mor el t
            =
            cat_el_map_mor el (s · t) · s),
     isPullback p.

Definition cat_stable_el_map
           (C : univ_cat_with_finlim_ob)
  : UU
  := ∑ (el : cat_el_map C),
     cat_el_map_stable el.

Definition make_cat_stable_el_map
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
           (H_el : cat_el_map_stable el)
  : cat_stable_el_map C
  := el ,, H_el.

Coercion cat_stable_el_map_to_el_map
         {C : univ_cat_with_finlim_ob}
         (el : cat_stable_el_map C)
  : cat_el_map C
  := pr1 el.

Definition cat_el_map_pb_mor
           {C : univ_cat_with_finlim_ob}
           (el : cat_stable_el_map C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (t : Δ --> univ_cat_universe C)
  : cat_el_map_el el (s · t) --> cat_el_map_el el t
  := pr1 (pr2 el Γ Δ s t).

Proposition cat_el_map_pb_mor_eq
            {C : univ_cat_with_finlim_ob}
            (el : cat_stable_el_map C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t t' : Δ --> univ_cat_universe C}
            (p : t' = t)
            (q : s · t' = s · t)
  : cat_el_map_el_eq el q · cat_el_map_pb_mor el s t
    =
    cat_el_map_pb_mor el s t' · cat_el_map_el_eq el p.
Proof.
  induction p.
  assert (q = idpath _) as ->.
  {
    apply homset_property.
  }
  cbn.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition cat_stable_el_map_pb
           {C : univ_cat_with_finlim_ob}
           (el : cat_stable_el_map C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (t : Δ --> univ_cat_universe C)
  : Pullback (cat_el_map_mor el t) s.
Proof.
  use make_Pullback.
  - exact (cat_el_map_el el (s · t)).
  - exact (cat_el_map_pb_mor el s t).
  - exact (cat_el_map_mor el (s · t)).
  - exact (pr12 (pr2 el Γ Δ s t)).
  - exact (pr22 (pr2 el Γ Δ s t)).
Defined.

(** * 3. Coherence *)
Definition is_coherent_cat_stable_el_map
           {C : univ_cat_with_finlim_ob}
           (el : cat_stable_el_map C)
  : UU
  := (∏ (Γ : C)
        (t : Γ --> univ_cat_universe C),
      cat_el_map_pb_mor el (identity _) t
      =
      cat_el_map_el_eq el (id_left _))
     ×
     (∏ (Γ₁ Γ₂ Γ₃ : C)
        (s₁ : Γ₁ --> Γ₂)
        (s₂ : Γ₂ --> Γ₃)
        (t : Γ₃ --> univ_cat_universe C),
       cat_el_map_pb_mor el (s₁ · s₂) t
       =
       cat_el_map_el_eq el (assoc' _ _ _)
       · cat_el_map_pb_mor el s₁ (s₂ · t)
       · cat_el_map_pb_mor el s₂ t).

Proposition isaprop_is_coherent_cat_stable_el_map
            {C : univ_cat_with_finlim_ob}
            (el : cat_stable_el_map C)
  : isaprop (is_coherent_cat_stable_el_map el).
Proof.
  use isapropdirprod.
  - repeat (use impred ; intro).
    apply homset_property.
  - repeat (use impred ; intro).
    apply homset_property.
Qed.

Definition cat_stable_el_map_coherent
           (C : univ_cat_with_finlim_ob)
  : UU
  := ∑ (el : cat_stable_el_map C),
     is_coherent_cat_stable_el_map el.

Definition make_cat_stable_el_map_coherent
           {C : univ_cat_with_finlim_ob}
           (el : cat_stable_el_map C)
           (H : is_coherent_cat_stable_el_map el)
  : cat_stable_el_map_coherent C
  := el ,, H.

Coercion cat_stable_el_map_coherent_to_el_map
         {C : univ_cat_with_finlim_ob}
         (el : cat_stable_el_map_coherent C)
  : cat_stable_el_map C
  := pr1 el.

Proposition cat_el_map_pb_mor_id
            {C : univ_cat_with_finlim_ob}
            (el : cat_stable_el_map_coherent C)
            {Γ : C}
            (t : Γ --> univ_cat_universe C)
  : cat_el_map_pb_mor el (identity _) t
    =
    cat_el_map_el_eq el (id_left _).
Proof.
  exact (pr12 el Γ t).
Defined.

Definition cat_el_map_pb_mor_comp
           {C : univ_cat_with_finlim_ob}
           (el : cat_stable_el_map_coherent C)
           {Γ₁ Γ₂ Γ₃ : C}
           (s₁ : Γ₁ --> Γ₂)
           (s₂ : Γ₂ --> Γ₃)
           (t : Γ₃ --> univ_cat_universe C)
  : cat_el_map_pb_mor el (s₁ · s₂) t
    =
    cat_el_map_el_eq el (assoc' _ _ _)
    · cat_el_map_pb_mor el s₁ (s₂ · t)
    · cat_el_map_pb_mor el s₂ t.
Proof.
  exact (pr22 el Γ₁ Γ₂ Γ₃ s₁ s₂ t).
Defined.


Proposition koe
            {C : univ_cat_with_finlim_ob}
            {Γ₁ Γ₂ : C}
            {el₁ el₂ : cat_el_map C}
            (p : el₁ = el₂)
            (t : Γ₂ --> univ_cat_universe C)
            (s : Γ₁ --> Γ₂)
            (f : cat_el_map_el el₁ (s · t) --> cat_el_map_el el₁ t)
  : transportf
      (λ (el : cat_el_map C), cat_el_map_el el (s · t) --> cat_el_map_el el t)
      p
      f
    =
    idtoiso (!base_paths _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ p _) (s · t))) · f · idtoiso (base_paths _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ p _) t)).
Proof.
  induction p ; cbn.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Proposition cat_el_map_eq
            {C : univ_cat_with_finlim_ob}
            {el₁ el₂ : cat_stable_el_map C}
            (p : ∏ (Γ : C)
                   (t : Γ --> univ_cat_universe C),
                 z_iso (cat_el_map_el el₁ t) (cat_el_map_el el₂ t))
            (q : ∏ (Γ : C)
                   (t : Γ --> univ_cat_universe C),
                 p Γ t · cat_el_map_mor el₂ t
                 =
                 cat_el_map_mor el₁ t)
             (r : ∏ (Γ Δ : C)
                    (s : Γ --> Δ)
                    (t : Δ --> univ_cat_universe C),
                  cat_el_map_pb_mor el₁ s t · p _ _
                  =
                  p _ _ · cat_el_map_pb_mor el₂ s t)
  : el₁ = el₂.
Proof.
  induction el₁ as [ el₁ H₁ ].
  induction el₂ as [ el₂ H₂ ].
  use total2_paths_f.
  {
    use funextsec ; intro Γ.
    use funextsec ; intro t.
    use total2_paths_f.
    {
      use isotoid.
      {
        apply univalent_category_is_univalent.
      }
      apply p.
    }
    rewrite transportf_isotoid.
    use z_iso_inv_on_right.
    refine (!_).
    apply q.
  }
  cbn.
  unfold cat_el_map_stable.
  use funextsec ; intro Γ.
  rewrite transportf_sec_constant.
  use funextsec ; intro Δ.
  rewrite transportf_sec_constant.
  use funextsec ; intro s.
  rewrite transportf_sec_constant.
  use funextsec ; intro t.
  rewrite transportf_sec_constant.
  use subtypePath.
  {
    intro.
    use isaproptotal2.
    {
      intro.
      apply isaprop_isPullback.
    }
    intros.
    apply homset_property.
  }
  rewrite pr1_transportf.
  rewrite koe.
  rewrite !toforallpaths_funextsec.
  rewrite !base_total2_paths.
  rewrite idtoiso_inv.
  cbn.
  rewrite !idtoiso_isotoid.
  rewrite !assoc'.
  use z_iso_inv_on_right.
  apply r.
Qed.


(** * 4. Preservation by functors and examples of such functors *)
Definition functor_el_map
           {C₁ C₂ : univ_cat_with_finlim_ob}
           (el₁ : cat_el_map C₁)
           (el₂ : cat_el_map C₂)
           (F : functor_finlim_ob C₁ C₂)
  : UU
  := ∏ (Γ : C₁)
       (t : Γ --> univ_cat_universe C₁),
     ∑ (f : z_iso
              (F (cat_el_map_el el₁ t))
              (cat_el_map_el el₂ (#F t · functor_on_universe F))),
     #F (cat_el_map_mor el₁ t)
     =
     f
     · cat_el_map_mor el₂ (#F t · functor_on_universe F).

Definition functor_el_map_iso
           {C₁ C₂ : univ_cat_with_finlim_ob}
           {el₁ : cat_el_map C₁}
           {el₂ : cat_el_map C₂}
           {F : functor_finlim_ob C₁ C₂}
           (Fel : functor_el_map el₁ el₂ F)
           {Γ : C₁}
           (t : Γ --> univ_cat_universe C₁)
  : z_iso
      (F (cat_el_map_el el₁ t))
      (cat_el_map_el el₂ (#F t · functor_on_universe F))
  := pr1 (Fel Γ t).

Proposition functor_el_map_iso_eq_path
            {C₁ C₂ : univ_cat_with_finlim_ob}
            (F : functor_finlim_ob C₁ C₂)
            {Γ : C₁}
            {t₁ t₂ : Γ --> univ_cat_universe C₁}
            (p : t₁ = t₂)
  : #F t₁ · functor_on_universe F
    =
    #F t₂ · functor_on_universe F.
Proof.
  induction p.
  apply idpath.
Defined.

Proposition functor_el_map_iso_eq
            {C₁ C₂ : univ_cat_with_finlim_ob}
            {el₁ : cat_el_map C₁}
            {el₂ : cat_el_map C₂}
            {F : functor_finlim_ob C₁ C₂}
            (Fel : functor_el_map el₁ el₂ F)
            {Γ : C₁}
            {t₁ t₂ : Γ --> univ_cat_universe C₁}
            (p : t₁ = t₂)
  : pr1 (functor_el_map_iso Fel t₂)
    =
    #F (cat_el_map_el_eq el₁ (!p))
    · functor_el_map_iso Fel t₁
    · (cat_el_map_el_eq el₂ (functor_el_map_iso_eq_path F p)).
Proof.
  induction p ; cbn.
  rewrite functor_id.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Proposition functor_on_cat_el_map_el_eq
            {C₁ C₂ : univ_cat_with_finlim_ob}
            {el₁ : cat_el_map C₁}
            {el₂ : cat_el_map C₂}
            {F : functor_finlim_ob C₁ C₂}
            (Fel : functor_el_map el₁ el₂ F)
            {Γ : C₁}
            {t₁ t₂ : Γ --> univ_cat_universe C₁}
            (p : t₁ = t₂)
  : #F (cat_el_map_el_eq el₁ p)
    =
    functor_el_map_iso Fel t₁
    · cat_el_map_el_eq el₂ (functor_el_map_iso_eq_path F p)
    · inv_from_z_iso (functor_el_map_iso Fel t₂).
Proof.
  induction p ; cbn.
  rewrite functor_id.
  rewrite id_right.
  rewrite z_iso_inv_after_z_iso.
  apply idpath.
Qed.

Proposition functor_el_map_comm
            {C₁ C₂ : univ_cat_with_finlim_ob}
            {el₁ : cat_el_map C₁}
            {el₂ : cat_el_map C₂}
            {F : functor_finlim_ob C₁ C₂}
            (Fel : functor_el_map el₁ el₂ F)
            {Γ : C₁}
            (t : Γ --> univ_cat_universe C₁)
  : #F (cat_el_map_mor el₁ t)
    =
    functor_el_map_iso Fel t
    · cat_el_map_mor el₂ (#F t · functor_on_universe F).
Proof.
  exact (pr2 (Fel Γ t)).
Qed.

Definition make_functor_el_map
           {C₁ C₂ : univ_cat_with_finlim_ob}
           {el₁ : cat_el_map C₁}
           {el₂ : cat_el_map C₂}
           {F : functor_finlim_ob C₁ C₂}
           (f : ∏ (Γ : C₁) (t : Γ --> univ_cat_universe C₁),
                z_iso
                  (F (cat_el_map_el el₁ t))
                  (cat_el_map_el el₂ (#F t · functor_on_universe F)))
           (p : ∏ (Γ : C₁) (t : Γ --> univ_cat_universe C₁),
                #F (cat_el_map_mor el₁ t)
                =
                f Γ t
                · cat_el_map_mor el₂ (#F t · functor_on_universe F))
  : functor_el_map el₁ el₂ F
  := λ Γ t, f Γ t ,, p Γ t.

Definition id_functor_el_map
           {C : univ_cat_with_finlim_ob}
           (el : cat_el_map C)
  : functor_el_map el el (id₁ C).
Proof.
  use make_functor_el_map.
  - intros Γ t.
    use make_z_iso.
    + exact (cat_el_map_el_eq el (!(id_right _))).
    + exact (cat_el_map_el_eq el (id_right _)).
    + abstract
        (split ;
         cbn ;
         rewrite cat_el_map_el_eq_comp ;
         [ rewrite pathsinv0l | rewrite pathsinv0r ] ;
         apply idpath).
  - abstract
      (intros Γ t ;
       cbn ;
       rewrite cat_el_map_mor_eq ;
       apply idpath).
Defined.

Definition comp_functor_el_map
           {C₁ C₂ C₃ : univ_cat_with_finlim_ob}
           {F : functor_finlim_ob C₁ C₂}
           {G : functor_finlim_ob C₂ C₃}
           {el₁ : cat_el_map C₁}
           {el₂ : cat_el_map C₂}
           {el₃ : cat_el_map C₃}
           (Fel : functor_el_map el₁ el₂ F)
           (Gel : functor_el_map el₂ el₃ G)
  : functor_el_map el₁ el₃ (F · G).
Proof.
  use make_functor_el_map.
  - intros Γ t.
    cbn.
    refine (z_iso_comp
              (functor_on_z_iso G (functor_el_map_iso Fel t))
              _).
    refine (z_iso_comp
              (functor_el_map_iso Gel _)
              (cat_el_map_el_eq el₃ _)).
    abstract
      (rewrite functor_comp ;
       rewrite !assoc' ;
       apply idpath).
  - abstract
      (intros Γ t ; cbn ;
       refine (maponpaths (λ z, #G z) (functor_el_map_comm Fel t) @ _) ;
       rewrite functor_comp ;
       rewrite !assoc' ;
       apply maponpaths ;
       refine (functor_el_map_comm Gel _ @ _) ;
       apply maponpaths ;
       refine (!_) ;
       apply cat_el_map_mor_eq).
Defined.

(** * 5.  *)
Proposition functor_stable_el_map_path
            {C₁ C₂ : univ_cat_with_finlim_ob}
            (F : functor_finlim_ob C₁ C₂)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : Δ --> univ_cat_universe C₁)
  : # F (s · t) · functor_on_universe F
    =
    # F s · (# F t · functor_on_universe F).
Proof.
  rewrite functor_comp, assoc'.
  apply idpath.
Qed.

Definition functor_stable_el_map
           {C₁ C₂ : univ_cat_with_finlim_ob}
           {el₁ : cat_stable_el_map C₁}
           {el₂ : cat_stable_el_map C₂}
           {F : functor_finlim_ob C₁ C₂}
           (Fel : functor_el_map el₁ el₂ F)
  : UU
  := ∏ (Γ Δ : C₁)
       (s : Γ --> Δ)
       (t : Δ --> univ_cat_universe C₁),
     #F (cat_el_map_pb_mor el₁ s t)
     · functor_el_map_iso Fel t
     =
     functor_el_map_iso Fel _
     · cat_el_map_el_eq el₂ (functor_stable_el_map_path F s t)
     · cat_el_map_pb_mor el₂ (#F s) (# F t · functor_on_universe F).

Definition functor_preserves_el
           {C₁ C₂ : univ_cat_with_finlim_ob}
           (el₁ : cat_stable_el_map C₁)
           (el₂ : cat_stable_el_map C₂)
           (F : functor_finlim_ob C₁ C₂)
  : UU
  := ∑ (Fel : functor_el_map el₁ el₂ F),
     functor_stable_el_map Fel.

Coercion functor_preserves_el_to_el_map
         {C₁ C₂ : univ_cat_with_finlim_ob}
         {el₁ : cat_stable_el_map C₁}
         {el₂ : cat_stable_el_map C₂}
         {F : functor_finlim_ob C₁ C₂}
         (Fel : functor_preserves_el el₁ el₂ F)
  : functor_el_map el₁ el₂ F
  := pr1 Fel.

Proposition functor_preserves_el_path
            {C₁ C₂ : univ_cat_with_finlim_ob}
            {el₁ : cat_stable_el_map C₁}
            {el₂ : cat_stable_el_map C₂}
            {F : functor_finlim_ob C₁ C₂}
            (Fel : functor_preserves_el el₁ el₂ F)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : Δ --> univ_cat_universe C₁)
  : #F (cat_el_map_pb_mor el₁ s t)
    · functor_el_map_iso Fel t
    =
    functor_el_map_iso Fel _
    · cat_el_map_el_eq el₂ (functor_stable_el_map_path F s t)
    · cat_el_map_pb_mor el₂ (#F s) (# F t · functor_on_universe F).
Proof.
  exact (pr2 Fel Γ Δ s t).
Qed.

Definition make_functor_preserves_el
           {C₁ C₂ : univ_cat_with_finlim_ob}
           {el₁ : cat_stable_el_map C₁}
           {el₂ : cat_stable_el_map C₂}
           {F : functor_finlim_ob C₁ C₂}
           (Fel : functor_el_map el₁ el₂ F)
           (Fp : functor_stable_el_map Fel)
  : functor_preserves_el el₁ el₂ F
  := Fel ,, Fp.

Definition id_functor_stable_el_map
           {C : univ_cat_with_finlim_ob}
           (el : cat_stable_el_map C)
  : functor_stable_el_map (id_functor_el_map el).
Proof.
  intros Γ Δ s t.
  etrans.
  {
    refine (!_).
    use cat_el_map_pb_mor_eq.
    abstract
      (rewrite id_right ;
       apply idpath).
  }
  apply maponpaths_2.
  refine (_ @ !(cat_el_map_el_eq_comp _ _ _)).
  apply cat_el_map_el_eq_eq.
Qed.

Definition id_functor_preserves_el
           {C : univ_cat_with_finlim_ob}
           (el : cat_stable_el_map C)
  : functor_preserves_el el el (id₁ _).
Proof.
  use make_functor_preserves_el.
  - apply id_functor_el_map.
  - apply id_functor_stable_el_map.
Defined.

Proposition comp_functor_stable_el_map
            {C₁ C₂ C₃ : univ_cat_with_finlim_ob}
            {F : functor_finlim_ob C₁ C₂}
            {G : functor_finlim_ob C₂ C₃}
            {el₁ : cat_stable_el_map C₁}
            {el₂ : cat_stable_el_map C₂}
            {el₃ : cat_stable_el_map C₃}
            (Fel : functor_preserves_el el₁ el₂ F)
            (Gel : functor_preserves_el el₂ el₃ G)
  : functor_stable_el_map (comp_functor_el_map Fel Gel).
Proof.
  intros Γ Δ s t.
  cbn.
  do 2 refine (assoc _ _ _ @ _).
  rewrite <- functor_comp.
  rewrite (functor_preserves_el_path Fel).
  etrans.
  {
    do 2 apply maponpaths_2.
    do 2 rewrite (functor_comp G).
    apply idpath.
  }
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    rewrite (functor_preserves_el_path Gel).
    apply idpath.
  }
  rewrite !assoc'.
  etrans.
  {
    do 3 apply maponpaths.
    refine (!_).
    use cat_el_map_pb_mor_eq.
    {
      apply maponpaths.
      rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    }
  }
  do 3 refine (assoc _ _ _ @ _).
  do 2 refine (_ @ assoc' _ _ _).
  apply maponpaths_2.
  do 2 refine (assoc' _ _ _ @ _).
  refine (_ @ assoc _ _ _).
  rewrite !cat_el_map_el_eq_comp.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    use functor_el_map_iso_eq.
    {
      exact (# F s · (# F t · functor_on_universe F)).
    }
    rewrite !assoc.
    rewrite functor_comp.
    apply idpath.
  }
  do 2 refine (assoc' _ _ _ @ _).
  rewrite cat_el_map_el_eq_comp.
  refine (assoc _ _ _ @ _ @ assoc' _ _ _).
  use cat_el_map_el_eq_postcomp.
  apply maponpaths_2.
  apply maponpaths.
  apply cat_el_map_el_eq_eq.
Qed.

Definition comp_functor_preserves_el
           {C₁ C₂ C₃ : univ_cat_with_finlim_ob}
           {F : functor_finlim_ob C₁ C₂}
           {G : functor_finlim_ob C₂ C₃}
           {el₁ : cat_stable_el_map C₁}
           {el₂ : cat_stable_el_map C₂}
           {el₃ : cat_stable_el_map C₃}
           (Fel : functor_preserves_el el₁ el₂ F)
           (Gel : functor_preserves_el el₂ el₃ G)
  : functor_preserves_el el₁ el₃ (F · G).
Proof.
  use make_functor_preserves_el.
  - exact (comp_functor_el_map Fel Gel).
  - exact (comp_functor_stable_el_map Fel Gel).
Defined.



Proposition nat_trans_preserves_el_path
            {C₁ C₂ : univ_cat_with_finlim_ob}
            {F G : functor_finlim_ob C₁ C₂}
            (τ : nat_trans_finlim_ob F G)
            {Γ : C₁}
            (t : Γ --> univ_cat_universe C₁)
  : # F t · functor_on_universe F = τ Γ · (# G t · functor_on_universe G).
Proof.
  rewrite <- (nat_trans_universe_eq τ).
  rewrite assoc.
  rewrite (nat_trans_ax τ _ _ t).
  rewrite assoc'.
  apply idpath.
Qed.

Definition nat_trans_preserves_el
           {C₁ C₂ : univ_cat_with_finlim_ob}
           {F G : functor_finlim_ob C₁ C₂}
           (τ : nat_trans_finlim_ob F G)
           {el₁ : cat_stable_el_map C₁}
           {el₂ : cat_stable_el_map C₂}
           (Fe : functor_preserves_el el₁ el₂ F)
           (Ge : functor_preserves_el el₁ el₂ G)
  : UU
  := ∏ (Γ : C₁)
       (t : Γ --> univ_cat_universe C₁),
     τ _ · functor_el_map_iso Ge t
     =
     functor_el_map_iso Fe t
     · cat_el_map_el_eq el₂ (nat_trans_preserves_el_path τ t)
     · cat_el_map_pb_mor _ (τ Γ) _.

Proposition isaprop_nat_trans_preserves_el
            {C₁ C₂ : univ_cat_with_finlim_ob}
            {F G : functor_finlim_ob C₁ C₂}
            (τ : nat_trans_finlim_ob F G)
            {el₁ : cat_stable_el_map C₁}
            {el₂ : cat_stable_el_map C₂}
            (Fe : functor_preserves_el el₁ el₂ F)
            (Ge : functor_preserves_el el₁ el₂ G)
  : isaprop (nat_trans_preserves_el τ Fe Ge).
Proof.
  do 2 (use impred ; intro).
  apply homset_property.
Qed.

Definition disp_cat_ob_mor_finlim_el
  : disp_cat_ob_mor bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact cat_stable_el_map_coherent.
  - exact (λ (C₁ C₂ : univ_cat_with_finlim_ob)
             (el₁ : cat_stable_el_map_coherent C₁)
             (el₂ : cat_stable_el_map_coherent C₂)
             (F : functor_finlim_ob C₁ C₂),
           functor_preserves_el el₁ el₂ F).
Defined.

Definition disp_cat_id_comp_finlim_el
  : disp_cat_id_comp bicat_of_univ_cat_with_finlim_ob disp_cat_ob_mor_finlim_el.
Proof.
  simple refine (_ ,, _).
  - intros C el.
    exact (id_functor_preserves_el (pr1 el)).
  - intros C₁ C₂ C₃ F G el₁ el₂ el₃ Fel Gel.
    exact (comp_functor_preserves_el Fel Gel).
Defined.

Definition disp_cat_data_finlim_el
  : disp_cat_data bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_finlim_el.
  - exact disp_cat_id_comp_finlim_el.
Defined.

Definition disp_prebicat_1_id_comp_cells_finlim_el
  : disp_prebicat_1_id_comp_cells bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_finlim_el.
  - exact (λ (C₁ C₂ : univ_cat_with_finlim_ob)
             (F G : functor_finlim_ob C₁ C₂)
             (τ : nat_trans_finlim_ob F G)
             (el₁ : cat_stable_el_map_coherent C₁)
             (el₂ : cat_stable_el_map_coherent C₂)
             (Fe : functor_preserves_el el₁ el₂ F)
             (Ge : functor_preserves_el el₁ el₂ G),
           nat_trans_preserves_el τ Fe Ge).
Defined.

Proposition disp_prebicat_ops_finlim_el
  : disp_prebicat_ops
      disp_prebicat_1_id_comp_cells_finlim_el.
Proof.
  repeat split.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    refine (!(id_right _) @ _).
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_id.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !assoc'.
    rewrite !cat_el_map_el_eq_comp.
    refine (!_).
    etrans.
    {
      exact (functor_el_map_iso_eq _ (id_right _)).
    }
    rewrite !assoc.
    use cat_el_map_el_eq_postcomp.
    apply maponpaths_2.
    apply maponpaths.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    rewrite !assoc'.
    refine (!(id_right _) @ _).
    apply maponpaths.
    rewrite !assoc.
    rewrite !cat_el_map_el_eq_comp.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_id.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths_2.
      exact (functor_el_map_iso_eq _ (id_right _)).
    }
    rewrite !assoc'.
    rewrite !cat_el_map_el_eq_comp.
    rewrite !assoc.
    refine (assoc _ _ _ @ _).
    use cat_el_map_el_eq_postcomp.
    apply maponpaths_2.
    apply maponpaths.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    rewrite cat_el_map_el_eq_comp.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ C₃ C₄ F G H el₁ el₂ el₃ el₄ Fel Gel Hel Γ t.
    simpl.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths_2.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply (functor_on_cat_el_map_el_eq (pr1 Hel)).
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      rewrite z_iso_after_z_iso_inv.
      rewrite id_left.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ C₃ C₄ F G H el₁ el₂ el₃ el₄ Fel Gel Hel Γ t.
    simpl.
    rewrite id_left.
    etrans.
    {
      apply maponpaths_2.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply (functor_on_cat_el_map_el_eq (pr1 Hel)).
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc _ _ _ @ _).
      rewrite z_iso_after_z_iso_inv.
      rewrite id_left.
      apply idpath.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ F G H τ θ el₁ el₂ Fel Gel Hel p q Γ t.
    simpl.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply q.
    }
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply p.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      rewrite assoc'.
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply nat_trans_ax.
      }
      rewrite !assoc'.
      apply maponpaths.
      apply θ.
    }
    refine (assoc _ _ _ @ _).
    refine (_ @ assoc' _ _ _).
    apply maponpaths_2.
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ C₃ F G₁ G₂ τ el₁ el₂ el₃ Fel Gel₁ Gel₂ p Γ t.
    simpl.
    etrans.
    {
      do 2 refine (assoc _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply nat_trans_ax.
      }
      do 2 refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply p.
    }
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite cat_el_map_el_eq_comp.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ C₃ F₁ F₂ G τ el₁ el₂ el₃ Fel₁ Fel₂ Gel p Γ t.
    simpl.
    etrans.
    {
      do 2 refine (assoc _ _ _ @ _).
      do 2 apply maponpaths_2.
      refine (!(functor_comp _ _ _) @ _).
      apply maponpaths.
      apply p.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply functor_comp.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply (functor_on_cat_el_map_el_eq (pr1 Gel)).
    }
    rewrite !assoc'.
    apply maponpaths.

    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply functor_preserves_el_path.
    }
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply z_iso_after_z_iso_inv.
    }
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    }
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
Qed.

Definition disp_prebicat_data_finlim_el
  : disp_prebicat_data bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_finlim_el.
  - exact disp_prebicat_ops_finlim_el.
Defined.


Definition disp_prebicat_finlim_el
  : disp_prebicat bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_finlim_el.
  - abstract
      (repeat split ;
       intro ;
       intros ;
       apply isaprop_nat_trans_preserves_el).
Defined.

Definition disp_bicat_finlim_el
  : disp_bicat bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_finlim_el.
  - abstract
      (intro ; intros ;
       apply isasetaprop ;
       apply isaprop_nat_trans_preserves_el).
Defined.



(** * 3. Universes as morphisms *)
Section UniverseAsMorphism.
  Context (C : univ_cat_with_finlim_ob).

  Definition cat_stable_el_map_coherent_to_mor
             (el : cat_stable_el_map_coherent C)
    : ∑ (e : C), e --> univ_cat_universe C.
  Proof.
    simple refine (_ ,, _).
    - exact (cat_el_map_el el (identity _)).
    - exact (cat_el_map_mor el (identity _)).
  Defined.

  Section MorphismsToUniverse.
    Context {e : C}
            (p : e --> univ_cat_universe C).

    Definition cat_el_map_from_mor
      : cat_el_map C.
    Proof.
      intros Γ t.
      pose (P := pullbacks_univ_cat_with_finlim C _ _ _ p t).
      exact (PullbackObject P ,, PullbackPr2 P).
    Defined.

    Definition morphism_to_pb_mor_univ
               {Γ Δ : C}
               (s : Γ --> Δ)
               (t : Δ --> univ_cat_universe C)
      : pullbacks_univ_cat_with_finlim C (univ_cat_universe C) e Γ p (s · t)
        -->
        pullbacks_univ_cat_with_finlim C (univ_cat_universe C) e Δ p t.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _).
      - exact (PullbackPr2 _ · s).
      - abstract
          (rewrite !assoc' ;
           rewrite <- PullbackSqrCommutes ;
           apply idpath).
    Defined.

    Proposition morphism_to_pb_mor_univ_comm
                {Γ Δ : C}
                (s : Γ --> Δ)
                (t : Δ --> univ_cat_universe C)
      : morphism_to_pb_mor_univ s t
        · PullbackPr2
            (pullbacks_univ_cat_with_finlim
               C
               (univ_cat_universe C)
               e Δ p t)
        =
        PullbackPr2
          (pullbacks_univ_cat_with_finlim
             C
             (univ_cat_universe C)
             e Γ p (s · t))
        · s.
    Proof.
      apply PullbackArrow_PullbackPr2.
    Qed.

    Section UMP.
      Context {Γ Δ : C}
              (s : Γ --> Δ)
              (t : Δ --> univ_cat_universe C)
              {A : C}
              (h : A
                   -->
                   pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_universe C)
                     e Δ p t)
              (k : A --> Γ)
              (q : h
                   · PullbackPr2
                       (pullbacks_univ_cat_with_finlim
                          C
                          (univ_cat_universe C) e Δ p t)
                   =
                   k · s).

      Definition is_pb_morphism_to_pb_mor_univ_mor
        : A
          -->
          pullbacks_univ_cat_with_finlim C (univ_cat_universe C) e Γ p (s · t).
      Proof.
        use PullbackArrow.
        - exact (h · PullbackPr1 _).
        - exact k.
        - abstract
            (rewrite !assoc ;
             rewrite <- q ;
             rewrite !assoc' ;
             rewrite <- PullbackSqrCommutes ;
             apply idpath).
      Defined.

      Proposition is_pb_morphism_to_pb_mor_univ_pr1
        : is_pb_morphism_to_pb_mor_univ_mor · morphism_to_pb_mor_univ s t
          =
          h.
      Proof.
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_universe C)
                     e Δ p t))).
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          apply PullbackArrow_PullbackPr1.
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          rewrite !assoc.
          unfold is_pb_morphism_to_pb_mor_univ_mor.
          rewrite PullbackArrow_PullbackPr2.
          rewrite q.
          apply idpath.
      Qed.

      Proposition is_pb_morphism_to_pb_mor_univ_unique
        : isaprop
            (∑ hk,
             (hk · morphism_to_pb_mor_univ s t = h)
             ×
             (hk
              · PullbackPr2
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_universe C)
                     e Γ p (s · t))
              =
              k)).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual
               (isPullback_Pullback
                  (pullbacks_univ_cat_with_finlim
                     C
                     (univ_cat_universe C)
                     e Γ p (s · t)))).
        - pose proof (maponpaths
                        (λ z, z · PullbackPr1 _)
                        (pr12 ζ₁ @ !(pr12 ζ₂)))
            as r.
          cbn in r.
          unfold morphism_to_pb_mor_univ in r.
          rewrite !assoc' in r.
          rewrite PullbackArrow_PullbackPr1 in r.
          exact r.
        - refine (pr22 ζ₁ @ _).
          refine (_ @ !(pr22 ζ₂)).
          apply idpath.
      Qed.
    End UMP.

    Definition is_pb_morphism_to_pb_mor_univ
               {Γ Δ : C}
               (s : Γ --> Δ)
               (t : Δ --> univ_cat_universe C)
      : isPullback (morphism_to_pb_mor_univ_comm s t).
    Proof.
      intros A h k q ; cbn in q.
      use iscontraprop1.
      - apply is_pb_morphism_to_pb_mor_univ_unique.
      - simple refine (_ ,, _ ,, _).
        + exact (is_pb_morphism_to_pb_mor_univ_mor s t h k q).
        + exact (is_pb_morphism_to_pb_mor_univ_pr1 s t h k q).
        + abstract
            (cbn ;
             apply PullbackArrow_PullbackPr2).
    Defined.

    Definition cat_el_map_stable_from_mor
      : cat_el_map_stable cat_el_map_from_mor.
    Proof.
      intros Γ Δ s t.
      simple refine (_ ,, _ ,, _).
      - exact (morphism_to_pb_mor_univ s t).
      - exact (morphism_to_pb_mor_univ_comm s t).
      - exact (is_pb_morphism_to_pb_mor_univ s t).
    Defined.

    Definition cat_stable_el_map_from_mor
      : cat_stable_el_map C.
    Proof.
      use make_cat_stable_el_map.
      - exact cat_el_map_from_mor.
      - exact cat_el_map_stable_from_mor.
    Defined.

    Definition cat_el_map_el_eq_mor_from_mor
               {Γ : C}
               {t₁ t₂ : Γ --> univ_cat_universe C}
               (r : t₁ = t₂)
      : cat_el_map_el cat_stable_el_map_from_mor t₁
        -->
        cat_el_map_el cat_stable_el_map_from_mor t₂.
    Proof.
      use PullbackArrow.
      - exact (PullbackPr1 _).
      - exact (PullbackPr2 _).
      - abstract
          (rewrite r ;
           apply PullbackSqrCommutes).
    Defined.

    Proposition cat_el_map_el_eq_from_mor
                {Γ : C}
                {t₁ t₂ : Γ --> univ_cat_universe C}
                (r : t₁ = t₂)
      : pr1 (cat_el_map_el_eq cat_stable_el_map_from_mor r)
        =
        cat_el_map_el_eq_mor_from_mor r.
    Proof.
      induction r ; cbn ; unfold cat_el_map_el_eq_mor_from_mor.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      - rewrite id_left.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      - rewrite id_left.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
    Qed.

    Proposition is_coherent_cat_stable_el_map_from_mor
      : is_coherent_cat_stable_el_map cat_stable_el_map_from_mor.
    Proof.
      split.
      - intros Γ t.
        refine (_ @ !(cat_el_map_el_eq_from_mor _)).
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
          exact (!(PullbackArrow_PullbackPr1 _ _ _ _ _)).
        + refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
          refine (_ @ !(PullbackArrow_PullbackPr2 _ _ _ _ _)).
          apply id_right.
      - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths_2.
          apply cat_el_map_el_eq_from_mor.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + do 2 refine (assoc' _ _ _ @ _).
          etrans.
          {
            do 2 apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          etrans.
          {
            apply maponpaths.
            apply PullbackArrow_PullbackPr1.
          }
          refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
          exact (!(PullbackArrow_PullbackPr1 _ _ _ _ _)).
        + do 2 refine (assoc' _ _ _ @ _).
          etrans.
          {
            do 2 apply maponpaths.
            apply PullbackArrow_PullbackPr2.
          }
          etrans.
          {
            apply maponpaths.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            apply PullbackArrow_PullbackPr2.
          }
          etrans.
          {
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            apply PullbackArrow_PullbackPr2.
          }
          refine (_ @ !(PullbackArrow_PullbackPr2 _ _ _ _ _)).
          apply assoc'.
    Qed.

    Definition cat_stable_el_map_coherent_from_mor
      : cat_stable_el_map_coherent C.
    Proof.
      use make_cat_stable_el_map_coherent.
      - exact cat_stable_el_map_from_mor.
      - exact is_coherent_cat_stable_el_map_from_mor.
    Defined.
  End MorphismsToUniverse.

  Section UniverseToMorphismToUniverse.
    Context (el : cat_stable_el_map_coherent C).

    Section Isomorphism.
      Context {Γ : C}
              (t : Γ --> univ_cat_universe C).

      Let P : Pullback (cat_el_map_mor el (id₁ (univ_cat_universe C))) t
        := cat_stable_el_map_pb el t (identity _).

      Definition mor_to_cat_el_map_to_mor_z_iso_mor
        : cat_el_map_el
            (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
            t
          -->
          cat_el_map_el el (t · identity _).
      Proof.
        use (PullbackArrow P _ _ _ _) ; cbn.
        - exact (PullbackPr1 _).
        - exact (PullbackPr2 _).
        - apply PullbackSqrCommutes.
      Defined.

      Definition mor_to_cat_el_map_to_mor_z_iso_inv
        : cat_el_map_el el (t · identity _)
          -->
          cat_el_map_el
            (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
            t.
      Proof.
        use PullbackArrow.
        - exact (cat_el_map_pb_mor el t (identity _)).
        - exact (cat_el_map_mor el _).
        - apply (PullbackSqrCommutes P).
      Defined.

      Proposition mor_to_cat_el_map_to_mor_z_iso_eqs
        : is_inverse_in_precat
            mor_to_cat_el_map_to_mor_z_iso_mor
            mor_to_cat_el_map_to_mor_z_iso_inv.
      Proof.
        split.
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply PullbackArrow_PullbackPr1.
            }
            refine (PullbackArrow_PullbackPr1 P _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply PullbackArrow_PullbackPr2.
            }
            refine (PullbackArrow_PullbackPr2 P _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply (PullbackArrow_PullbackPr1 P).
            }
            refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
          + rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply (PullbackArrow_PullbackPr2 P).
            }
            refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
            rewrite id_left.
            apply idpath.
      Qed.

      Definition mor_to_cat_el_map_to_mor_z_iso
        : z_iso
            (cat_el_map_el
               (cat_el_map_from_mor (cat_el_map_mor el (identity _)))
               t)
            (cat_el_map_el el (t · identity _)).
      Proof.
        use make_z_iso.
        - exact mor_to_cat_el_map_to_mor_z_iso_mor.
        - exact mor_to_cat_el_map_to_mor_z_iso_inv.
        - exact mor_to_cat_el_map_to_mor_z_iso_eqs.
      Defined.
    End Isomorphism.

    Arguments mor_to_cat_el_map_to_mor_z_iso_mor /.

    Lemma mor_to_cat_el_map_to_mor_eq1
          {Γ : C}
          (t : Γ --> univ_cat_universe C)
      : mor_to_cat_el_map_to_mor_z_iso_mor t
        · cat_el_map_el_eq el (id_right t)
        · cat_el_map_mor el t
        =
        PullbackPr2 _.
    Proof.
      cbn.
      rewrite !assoc'.
      rewrite cat_el_map_mor_eq.
      exact (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el t (identity _)) _ _ _ _).
    Qed.

    Lemma mor_to_cat_el_map_to_mor_eq2
          {Γ Δ : C}
          (s : Γ --> Δ)
          (t : Δ --> univ_cat_universe C)
      : morphism_to_pb_mor_univ (cat_el_map_mor el (identity _)) s t
        · mor_to_cat_el_map_to_mor_z_iso_mor t
        · cat_el_map_el_eq el (id_right t)
        =
        mor_to_cat_el_map_to_mor_z_iso_mor (s · t)
        · cat_el_map_el_eq el (id_right (s · t))
        · cat_el_map_pb_mor el s t.
    Proof.
      rewrite !assoc'.
      assert (cat_el_map_el_eq el (id_right (s · t))
              · cat_el_map_pb_mor el s t
              =
              cat_el_map_el_eq el (assoc' _ _ _)
              · cat_el_map_pb_mor el s (t · identity _)
              · cat_el_map_el_eq el (id_right t))
        as ->.
      {
        refine (_ @ assoc _ _ _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          use cat_el_map_pb_mor_eq.
          refine (assoc _ _ _ @ id_right _).
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (cat_el_map_el_eq_comp _ _ _ @ _).
        do 2 apply maponpaths.
        apply homset_property.
      }
      pose (P := cat_stable_el_map_pb el (s · t) (identity _)).
      rewrite !assoc.
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (cat_stable_el_map_pb el t _))).
      - refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb el t _)).
        }
        unfold morphism_to_pb_mor_univ.
        rewrite PullbackArrow_PullbackPr1.
        cbn.
        refine (!_).
        etrans.
        {
          do 2 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          refine (!_).
          apply cat_el_map_pb_mor_comp.
        }
        apply (PullbackArrow_PullbackPr1 P).
      - refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el t _)).
        }
        unfold morphism_to_pb_mor_univ.
        rewrite PullbackArrow_PullbackPr2.
        cbn.
        refine (!_).
        assert (PullbackPr2 (cat_stable_el_map_pb el (s · t) (identity _)) · s
                =
                cat_el_map_el_eq el (assoc' s t (identity _))
                · cat_el_map_pb_mor el s (t · identity _)
                · cat_el_map_mor el (t · identity _))
          as p.
        {
          cbn.
          refine (!_).
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            exact (PullbackSqrCommutes (cat_stable_el_map_pb el s _)).
          }
          cbn.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply cat_el_map_mor_eq.
        }        etrans.
        {
          do 2 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          exact (!p).
        }
        rewrite !assoc.
        apply maponpaths_2.
        apply (PullbackArrow_PullbackPr2 P).
    Qed.

    Definition cat_el_map_coherent_to_mor_to_el_map
      : cat_stable_el_map_coherent_from_mor (cat_el_map_mor el (identity _)) = el.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_is_coherent_cat_stable_el_map.
      }
      use cat_el_map_eq.
      - intros Γ t.
        exact (z_iso_comp
                 (mor_to_cat_el_map_to_mor_z_iso t)
                 (cat_el_map_el_eq el (id_right _))).
      - intros Γ t.
        exact (mor_to_cat_el_map_to_mor_eq1 t).
      - intros Γ Δ s t.
        refine (_ @ mor_to_cat_el_map_to_mor_eq2 s t).
        apply assoc.
    Qed.

  End UniverseToMorphismToUniverse.

  Section MorphismToUniverseToMorphism.
    Context {e : C}
            (p : e --> univ_cat_universe C).

    Definition cat_el_map_to_mor_to_map_z_iso_inv
      : e --> pullbacks_univ_cat_with_finlim C _ _ _ p (identity _).
    Proof.
      use PullbackArrow.
      - apply identity.
      - exact p.
      - abstract
          (rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Proposition cat_el_map_to_mor_to_map_z_iso_invs
      : is_inverse_in_precat
          (PullbackPr1 _)
          cat_el_map_to_mor_to_map_z_iso_inv.
    Proof.
      unfold cat_el_map_to_mor_to_map_z_iso_inv.
      split.
      - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr1.
          rewrite id_left, id_right.
          apply idpath.
        + rewrite !assoc'.
          rewrite PullbackArrow_PullbackPr2.
          rewrite id_left.
          refine (PullbackSqrCommutes _ @ _).
          apply id_right.
      - apply PullbackArrow_PullbackPr1.
    Qed.

    Definition cat_el_map_to_mor_to_map_z_iso
      : z_iso
          (pullbacks_univ_cat_with_finlim
             C
             _ _ _
             p
             (identity _))
          e.
    Proof.
      use make_z_iso.
      - exact (PullbackPr1 _).
      - exact cat_el_map_to_mor_to_map_z_iso_inv.
      - exact cat_el_map_to_mor_to_map_z_iso_invs.
    Defined.
  End MorphismToUniverseToMorphism.

  Proposition mor_to_cat_el_map_to_mor
              (ep : ∑ (e : C), e --> univ_cat_universe C)
    : cat_stable_el_map_coherent_to_mor (cat_stable_el_map_coherent_from_mor (pr2 ep)) = ep.
  Proof.
    induction ep as [ e p ].
    use total2_paths_f.
    - use isotoid.
      {
        apply univalent_category_is_univalent.
      }
      exact (cat_el_map_to_mor_to_map_z_iso p).
    - abstract
        (cbn ;
         rewrite transportf_isotoid ;
         cbn ;
         unfold cat_el_map_to_mor_to_map_z_iso_inv ;
         apply PullbackArrow_PullbackPr2).
  Qed.

  Definition cat_stable_el_map_coherent_mor_weq
    : cat_stable_el_map_coherent C
      ≃
      ∑ (e : C), e --> univ_cat_universe C.
  Proof.
    use weq_iso.
    - exact cat_stable_el_map_coherent_to_mor.
    - exact (λ ep, cat_stable_el_map_coherent_from_mor (pr2 ep)).
    - intros el.
      exact (cat_el_map_coherent_to_mor_to_el_map el).
    - intros ep.
      exact (mor_to_cat_el_map_to_mor ep).
  Defined.
End UniverseAsMorphism.
