
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Local Open Scope cat.

(** ** Functors over functors between bases *)

(** One could define these in terms of functor-liftings, as:

[[
Definition disp_functor {C C' : category} (F : functor C C')
    (D : disp_cat C) (D' : disp_cat C')
  := functor_lifting D' (functor_composite (pr1_category D) F).
]]

However, it seems like it may probably be cleaner to define these independently.

TODO: reassess this design decision after some experience using it! *)

Section Disp_Functor.

  Definition disp_functor_data {C' C : precategory_data} (F : functor_data C' C)
             (D' : disp_cat_data C') (D : disp_cat_data C)
    := ∑ (Fob : ∏ x, D' x -> D (F x)),
      ∏ x y (xx : D' x) (yy : D' y) (f : x --> y),
      (xx -->[f] yy) -> (Fob _ xx -->[ # F f ] Fob _ yy).

  Definition disp_functor_on_objects {C' C : precategory_data} {F : functor_data C' C}
             {D' : disp_cat_data C'} {D : disp_cat_data C}
             (FF : disp_functor_data F D' D) {x : C'} (xx : D' x)
    : D (F x)
    := pr1 FF x xx.

  Coercion disp_functor_on_objects : disp_functor_data >-> Funclass.

  (** Unfortunately, the coercion loses implicitness of the {x:C'} argument:
  we have to write [ FF _ xx ] instead of just [ FF xx ].

  If anyone knows a way to avoid this, we would be happy to hear it! *)

  Definition disp_functor_on_morphisms {C' C : precategory_data} {F : functor_data C' C}
             {D' : disp_cat_data C'} {D : disp_cat_data C}
             (FF : disp_functor_data F D' D)
             {x y : C'} {xx : D' x} {yy} {f : x --> y} (ff : xx -->[f] yy)
    : (FF _ xx) -->[ # F f ] (FF _ yy)
    := pr2 FF x y xx yy f ff.

  Local Open Scope mor_disp_scope.
  Notation "# F" := (disp_functor_on_morphisms F)
                      (at level 3) : mor_disp_scope.

  Definition disp_functor_axioms {C' C : category} {F : functor C' C}
             {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor_data F D' D)
    :=  (∏ x (xx : D' x),
          # FF (id_disp xx) = transportb _ (functor_id F x) (id_disp (FF _ xx)))
          × (∏ x y z (xx : D' x) yy zz (f : x --> y) (g : y --> z)
               (ff : xx -->[f] yy) (gg : yy -->[g] zz),
              # FF (ff ;; gg)
              = transportb _ (functor_comp F f g) (# FF ff ;; # FF gg)).

  Lemma isaprop_disp_functor_axioms {C' C : category} {F : functor C' C}
        {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor_data F D' D)
    : isaprop (disp_functor_axioms FF).
  Proof.
    apply isapropdirprod;
      repeat (apply impred; intros);
      apply homsets_disp.
  Qed.

  Definition disp_functor {C' C : category} (F : functor C' C)
             (D' : disp_cat C') (D : disp_cat C)
    := ∑ FF : disp_functor_data F D' D, disp_functor_axioms FF.

  Definition disp_functor_data_from_disp_functor
             {C' C} {F} {D' : disp_cat C'} {D : disp_cat C}
             (FF : disp_functor F D' D)
    : disp_functor_data F D' D
    := pr1 FF.

  Coercion disp_functor_data_from_disp_functor
    : disp_functor >-> disp_functor_data.

  Definition disp_functor_id {C' C} {F} {D' : disp_cat C'} {D : disp_cat C}
             (FF : disp_functor F D' D)
             {x} (xx : D' x)
    : # FF (id_disp xx) = transportb _ (functor_id F x) (id_disp (FF _ xx))
    := pr1 (pr2 FF) x xx.

  Definition disp_functor_comp {C' C} {F} {D' : disp_cat C'} {D : disp_cat C}
             (FF : disp_functor F D' D)
             {x y z} {xx : D' x} {yy} {zz} {f : x --> y} {g : y --> z}
             (ff : xx -->[f] yy) (gg : yy -->[g] zz)
    : # FF (ff ;; gg)
      = transportb _ (functor_comp F f g) (# FF ff ;; # FF gg)
    := pr2 (pr2 FF) _ _ _ _ _ _ _ _ ff gg.

  (** variant access function *)
  Definition disp_functor_comp_var {C' C} {F} {D' : disp_cat C'} {D : disp_cat C}
             (FF : disp_functor F D' D)
             {x y z} {xx : D' x} {yy} {zz} {f : x --> y} {g : y --> z}
             (ff : xx -->[f] yy) (gg : yy -->[g] zz)
    : transportf _ (functor_comp F f g) (# FF (ff ;; gg))
      = # FF ff ;; # FF gg.
  Proof.
    apply transportf_pathsinv0.
    apply pathsinv0, disp_functor_comp.
  Defined.

  (** Useful transport lemma for [disp_functor]. *)
  Lemma disp_functor_transportf {C' C : category}
        {D' : disp_cat C'} {D : disp_cat C}
        (F : functor C' C) (FF : disp_functor F D' D)
        (x' x : C') (f' f : x' --> x) (p : f' = f)
        (xx' : D' x') (xx : D' x)
        (ff : xx' -->[ f' ] xx)
    :
    # FF (transportf _ p ff)
    =
      transportf _ (maponpaths (#F)%cat p) (#FF ff) .
  Proof.
    induction p.
    apply idpath.
  Defined.

  (** ** Composite and identity functors. *)

  Definition disp_functor_composite_data
             {C C' C'' : category} {D} {D'} {D''}
             {F : functor C C'} {F' : functor C' C''}
             (FF : disp_functor F D D')
             (FF' : disp_functor F' D' D'')
    : disp_functor_data (functor_composite F F') D D''.
  Proof.
    use tpair.
    + intros x xx. exact (FF' _ (FF _ xx)).
    + intros x y xx yy f ff. exact (# FF' (# FF ff)).
  Defined.

  Lemma disp_functor_composite_axioms
        {C C' C'' : category} {D} {D'} {D''}
        {F : functor C C'} {F' : functor C' C''}
        (FF : disp_functor F D D')
        (FF' : disp_functor F' D' D'')
    : disp_functor_axioms (disp_functor_composite_data FF FF').
  Proof.
    split; simpl.
    + intros x xx.
      etrans. apply maponpaths. apply disp_functor_id.
      etrans. apply disp_functor_transportf.
      etrans. apply maponpaths. apply disp_functor_id.
      etrans. apply transport_f_f.
      unfold transportb.
      apply maponpaths_2, homset_property.
    + intros.
      etrans. apply maponpaths. apply disp_functor_comp.
      etrans. apply disp_functor_transportf.
      etrans. apply maponpaths. apply disp_functor_comp.
      etrans. apply transport_f_f.
      unfold transportb.
      apply maponpaths_2, homset_property.
  Qed.

  Definition disp_functor_composite
             {C C' C'' : category} {D} {D'} {D''}
             {F : functor C C'} {F' : functor C' C''}
             (FF : disp_functor F D D')
             (FF' : disp_functor F' D' D'')
    : disp_functor (functor_composite F F') D D''.
  Proof.
    use tpair.
    - apply (disp_functor_composite_data FF FF').
    - apply disp_functor_composite_axioms.
  Defined.

  Definition disp_functor_identity
             {C : category} (D : disp_cat C)
    : disp_functor (functor_identity _ ) D D.
  Proof.
    use tpair.
    - use tpair.
      + intros; assumption.
      + cbn. intros. assumption.
    - split; simpl.
      + intros; apply idpath.
      + intros; apply idpath.
  Defined.

  (** ** Action of functors on isos. *)
  Section Functors_on_isos.

    (* TODO: functor_on_inv_from_iso should have implicit arguments *)

    Lemma disp_functor_on_iso_disp_aux1 {C C'} {F}
          {D : disp_cat C} {D' : disp_cat C'}
          (FF : disp_functor F D D')
          {x y} {xx : D x} {yy} {f : iso x y}
          (ff : xx -->[f] yy)
          (Hff : is_iso_disp f ff)
      : transportf _ (functor_on_inv_from_iso F f)
                   (# FF (inv_mor_disp_from_iso Hff))
        ;; # FF ff
        = transportb _ (iso_after_iso_inv _) (id_disp _).
    Proof.
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths, @pathsinv0, disp_functor_comp_var.
      etrans. apply transport_f_f.
      etrans. apply maponpaths, maponpaths, iso_disp_after_inv_mor.
      etrans. apply maponpaths, disp_functor_transportf.
      etrans. apply transport_f_f.
      etrans. apply maponpaths, disp_functor_id.
      etrans. apply transport_f_b.
      unfold transportb. apply maponpaths_2, homset_property.
    Qed.

    Lemma disp_functor_on_iso_disp_aux2 {C C'} {F}
          {D : disp_cat C} {D' : disp_cat C'}
          (FF : disp_functor F D D')
          {x y} {xx : D x} {yy} {f : iso x y}
          (ff : xx -->[f] yy)
          (Hff : is_iso_disp f ff)
      : # FF ff
        ;; transportf _ (functor_on_inv_from_iso F f)
                      (# FF (inv_mor_disp_from_iso Hff))
        =
          transportb _ (iso_inv_after_iso (functor_on_iso _ _)) (id_disp (FF x xx)).
    Proof.
      etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths, @pathsinv0, disp_functor_comp_var.
      etrans. apply transport_f_f.
      etrans. apply maponpaths, maponpaths, inv_mor_after_iso_disp.
      etrans. apply maponpaths, disp_functor_transportf.
      etrans. apply transport_f_f.
      etrans. apply maponpaths, disp_functor_id.
      etrans. apply transport_f_f.
      unfold transportb. apply maponpaths_2, homset_property.
    Qed.

    (** Let's see how [disp_functor]s behave on [iso_disp]s *)
    (** TODO: consider naming *)
    (* Undelimit Scope transport. *)
    Definition disp_functor_on_is_iso_disp {C C'} {F}
               {D : disp_cat C} {D' : disp_cat C'}
               (FF : disp_functor F D D')
               {x y} {xx : D x} {yy} {f : iso x y}
               {ff : xx -->[f] yy} (Hff : is_iso_disp f ff)
      : is_iso_disp (functor_on_iso F f) (# FF ff).
    Proof.
      exists (transportf _ (functor_on_inv_from_iso F f)
                    (# FF (inv_mor_disp_from_iso Hff))); split.
      - apply disp_functor_on_iso_disp_aux1.
      - apply disp_functor_on_iso_disp_aux2.
    Defined.

    Definition disp_functor_on_iso_disp {C C'} {F}
               {D : disp_cat C} {D' : disp_cat C'}
               (FF : disp_functor F D D')
               {x y} {xx : D x} {yy} {f : iso x y}
               (ff : iso_disp f xx yy)
      : iso_disp (functor_on_iso F f) (FF _ xx) (FF _ yy)
      := (_ ,, disp_functor_on_is_iso_disp _ ff).

  End Functors_on_isos.


  (** ** Properties of functors *)

  Section Functor_Properties.

    Definition disp_functor_ff {C C'} {F}
               {D : disp_cat C} {D' : disp_cat C'} (FF : disp_functor F D D')
      :=
      ∏ x y (xx : D x) (yy : D y) (f : x --> y),
        isweq (fun ff : xx -->[f] yy => # FF ff).

    Section ff_reflects_isos.

      (* TODO: Try making FF implicit, since it can be inferred from [FF_ff]. *)
      Context {C C' : category}
              {F : functor C C'}
              {D : disp_cat C}
              {D' : disp_cat C'}
              (FF : disp_functor F D D')
              (FF_ff : disp_functor_ff FF).

      Definition disp_functor_ff_weq {x y} xx yy f
        := make_weq _ (FF_ff x y xx yy f).
      Definition disp_functor_ff_inv {x y} {xx} {yy} {f : x --> y}
        := invmap (disp_functor_ff_weq xx yy f).

      (* TODO: add a general version [disp_functor_ff_inv_transportf], where the transportf on the LHS is arbitrary. *)
      Lemma disp_functor_ff_inv_transportf
            {x y : C} {f f' : x --> y} (e : f = f')
            {xx : D x} {yy : D y} (ff : FF _ xx -->[(#F)%cat f] FF _ yy)
        : disp_functor_ff_inv (transportf _ (maponpaths (# F )%cat e) ff)
          =
            transportf _ e (disp_functor_ff_inv ff).
      Proof.
        induction e.
        apply idpath.
      Qed.

      (* TODO: move the transport to the RHS. *)
      Lemma disp_functor_ff_inv_identity {x : C} (xx : D x)
        : disp_functor_ff_inv (transportb _ (functor_id F _ ) (id_disp (FF _ xx)))
          = id_disp xx.
      Proof.
        apply invmap_eq.
        apply pathsinv0.
        apply (disp_functor_id FF).
      Qed.

      (* TODO: move the transport to the RHS. *)
      Lemma disp_functor_ff_inv_compose {x y z : C} {f : x --> y} {g : y --> z}
            {xx} {yy} {zz}
            (ff : FF _ xx -->[(#F)%cat f] FF _ yy) (gg : FF _ yy -->[(#F)%cat g] FF _ zz)
        : disp_functor_ff_inv (transportb _ (functor_comp F _ _ ) (ff ;; gg))
          = disp_functor_ff_inv ff ;; disp_functor_ff_inv gg.
      Proof.
        apply invmap_eq. cbn.
        apply pathsinv0.
        etrans. apply (disp_functor_comp FF).
        apply maponpaths.
        etrans. apply maponpaths. exact (homotweqinvweq _ _).
        apply maponpaths_2. exact (homotweqinvweq _ _).
      Qed.

      Definition disp_functor_ff_reflects_isos
                 {x y} {xx : D x} {yy : D y} {f : iso x y}
                 (ff : xx -->[f] yy) (isiso: is_iso_disp (functor_on_iso F f) (# FF ff))
        : is_iso_disp _ ff.
      Proof.
        set (FFffinv := inv_mor_disp_from_iso isiso).
        set (FFffinv' := transportb _ (functor_on_inv_from_iso _ _ ) FFffinv).
        set (ffinv := disp_functor_ff_inv FFffinv').
        exists ffinv.
        split.
        - unfold ffinv. unfold FFffinv'.
          admit.
        - admit.
      Abort.

    End ff_reflects_isos.

    (** Given a base functor [F : C —> C'] and a displayed functor [FF : D' -> D] over it, there are two different “essential surjectivity” conditions one can put on [FF].

Given [c : C] and [d : D' (F c)], one can ask for a lift of [d] either in [D c] itself, or more generally in some fiber [D c'] with [c'] isomorphic to [c].

The second version is better-behaved in general; but the stricter first version is equivalent when [D] is an isofibration, and is simpler to work with.  So we call the second version “essentially split surjective”, [disp_functor_ess_split_surj], and the first “displayed ess. split surj.”, [disp_functor_disp_ess_split_surj].
     *)

    Definition disp_functor_ess_split_surj {C' C} {F}
               {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D D')
      : UU
      :=
      ∏ x (xx : D' (F x)),
        ∑ y : C,
          ∑ i : iso y x,
            ∑ yy : D y,
              iso_disp (functor_on_iso F i) (FF _ yy) xx.

    Definition disp_functor_disp_ess_split_surj {C' C} {F}
               {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D D')
      : UU
      :=
      ∏ x (xx : D' (F x)),
        ∑ (yy : D x),
        iso_disp (identity_iso _) (FF _ yy) xx.

    (* TODO: add access functions for these. *)

  End Functor_Properties.
End Disp_Functor.

(* Redeclare notations globally: *)

Notation "# F" := (disp_functor_on_morphisms F)
                    (at level 3) : mor_disp_scope.

(** Operations on displayed functors/transformations over the identity *)
Section CompDispFunctorOverIdentity.
  Context {C : category}
          {D₁ D₂ D₃ : disp_cat C}
          (FF : disp_functor (functor_identity C) D₁ D₂)
          (GG : disp_functor (functor_identity C) D₂ D₃).

  Definition disp_functor_over_id_composite_data
    : disp_functor_data (functor_identity C) D₁ D₃.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, GG x (FF x xx)).
    - exact (λ x y xx yy f ff, (#GG (#FF ff))%mor_disp).
  Defined.

  Definition disp_functor_over_id_composite_axioms
    : disp_functor_axioms disp_functor_over_id_composite_data.
  Proof.
    split.
    - intros x xx ; cbn.
      rewrite (disp_functor_id FF) ; cbn.
      rewrite (disp_functor_id GG) ; cbn.
      apply idpath.
    - intros x y z xx yy zz f g ff gg ; cbn.
      etrans.
      {
        apply maponpaths.
        exact (disp_functor_comp FF ff gg).
      }
      cbn.
      exact (disp_functor_comp GG (#FF ff) (#FF gg)).
  Qed.

  Definition disp_functor_over_id_composite
    : disp_functor (functor_identity C) D₁ D₃.
  Proof.
    simple refine (_ ,, _).
    - exact disp_functor_over_id_composite_data.
    - exact disp_functor_over_id_composite_axioms.
  Defined.
End CompDispFunctorOverIdentity.

(** ** A functor of displayed categories from reindexing *)

Section reindexing_disp_functor.

  Context {C C' : category} (F : functor C C') (D' : disp_cat C').

  Definition reindex_disp_functor : disp_functor F (reindex_disp_cat F D') D'.
  Proof.
    use tpair.
    - use tpair.
      + cbn. intro x. exact (idfun _ ).
      + cbn. intros x x' d d' f.  exact (idfun _ ).
    - abstract (
          split;
          [intros; apply idpath |];
          intros; apply idpath
        ).
  Defined.

End reindexing_disp_functor.
