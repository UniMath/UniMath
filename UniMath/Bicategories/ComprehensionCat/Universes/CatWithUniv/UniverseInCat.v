(**

 Universes in categories

 In this file, we define the notion of universe within a category. These are Tarski-style
 universes, meaning that we have a map assigned to each term of the universe an actual type
 (instead of Russel style universes whose inhabitants are actual types). To define such
 universes, we first give their core ingredients. These are an object `U` and an map that
 assigns to each morphism into `U` a type. Concretely, this entails to
 - an object `U`
 - for all morphisms `t : Γ --> U`, a morphism `⌜ t ⌝ : El t --> Γ`
 This data is given in [cat_el_map].

 Next we express stability under substitution of the map `El`. To state that, we use that
 substitution is interpreted using pullback. More specifically, we express that certain
 squares are pullbacks. Suppose that we have morphisms `s : Δ --> Γ` and `t : Γ --> U`. Then
 we have the following

<<
 El (s · t)         El t
     |                |
     |                |
     V                V
     Δ      ------>   Γ   -----> U
               s            t
>>

 To say that `El (s · t)` is the substitution of `El t` along `s`, we say that we have a morphism
 `sub_U s t : El (s · t) --> El t`, which makes the resulting square a pullback square. This
 is expressed in [cat_el_map_stable].

 The final requirement is coherence of substitution. Specifically, we say how the morphism
 `sub_U s t` acts on the identity and composition of substitutions. The precise definition is
 given in [is_coherent_cat_stable_el_map]. All in all, we get a notion of universe in a category
 with finite limits, which is given in [cat_stable_el_map_coherent].

 To construct a bicategory of categories with universes, we also define when functors and natural
 transformations preserve them. Suppose that we have a functor `F : C ⟶ D` and that `C` has a
 universe `U_1` and that `D` has as universe `U_2`. Then we say that `F` preserves the universe
 if we have
 - an isomorphism `i : F U_1 ≅ U_2`
 - for each `t : Γ --> U` in `C` we have an isomorphism `j : F (El_1 t) ≅ El_2 (F t · i)` such
   that the morphisms `F (El_1 t)` and `j · El_2 (F t · i)` are equal.
 We also require that the functor `F` preserves the morphisms `sub_U s t : El (s · t) --> El t`.
 These requirements are expressed in the file `CatWithOb` (i.e., the morphism `i : F U_1 ≅ U_2`),
 and in the definitions [functor_el_map] and [functor_stable_el_map]. Finally, we define when a
 natural transformation preserves universes (see [nat_trans_preserves_el]). In this definition,
 we require that a certain diagram commutes.

 Content
 1. The map assigning types to terms of the universe
 2. Stability
 3. Coherence
 4. Preservation by functors
 5. Identity and compositions preserve universes
 6. Functors that preserve stable universes
 7. The identity and composition
 8. Preservation by natural transformations

                                                                                               *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.

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

(** This lemma calculates the necessary transport for an equality principle *)
Proposition transportf_cat_el_map
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
    idtoiso (!base_paths _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ p _) (s · t)))
    · f
    · idtoiso (base_paths _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ p _) t)).
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
  rewrite transportf_cat_el_map.
  rewrite !toforallpaths_funextsec.
  rewrite !base_total2_paths.
  rewrite idtoiso_inv.
  cbn.
  rewrite !idtoiso_isotoid.
  rewrite !assoc'.
  use z_iso_inv_on_right.
  apply r.
Qed.

(** * 4. Preservation by functors *)
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

(** * 5. Identity and compositions preserve universes *)
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

(** * 6. Functors that preserve stable universes *)
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

(** * 7. The identity and composition *)
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

(** * 8. Preservation by natural transformations *)
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
