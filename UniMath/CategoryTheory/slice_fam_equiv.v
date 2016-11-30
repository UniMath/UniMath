Require Import UniMath.Foundations.Basics.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.equivalences
        UniMath.CategoryTheory.DiscretePrecategory
        UniMath.CategoryTheory.UnicodeNotations.

(** Proof that Set / X and Set ^ X are equivalent as categories *)
Section slice_fam_equiv.

  Definition hfiber_hSet {X : hSet} {Y : hSet} (f : X → Y) (y : Y) : hSet :=
    hSetpair (hfiber f y) (isaset_hfiber f y (pr2 X) (pr2 Y)).

  Variable X : hSet.

  Local Definition slice (A : hSet) := slice_precat HSET A has_homsets_HSET.
  Local Definition discrete (A : hSet) := discrete_precategory (pr1 A).
  Local Definition discrete_has_homsets (A : hSet) :=
    has_homsets_discrete_precategory (pr1 A) (hlevelntosn 2 (pr1 A) (isofhlevelssnset 0 (pr1 A) (pr2 A))).
  Local Definition fam (A : hSet) := functor_precategory (discrete A) HSET has_homsets_HSET.
  Local Definition mkfam (f : X → hSet) := functor_discrete_precategory (pr1 X) HSET f.

  Definition slice_to_fam_fun (a : slice X) : fam X :=
    mkfam (fun x : X => hfiber_hSet (pr2 a) x).

  Local Notation s_to_f := slice_to_fam_fun.

  (* don't use transportf! or maybe do, but w/ destruct or induction *)
  Definition slice_to_fam_mor_fun {a b : slice X} (f : a --> b) (x : X) :
    (s_to_f a : functor (discrete X) HSET) x --> (s_to_f b : functor (discrete X) HSET) x :=
    fun p => hfibersgftog (pr1 f) (pr2 b) _ (transportf (fun p => hfiber p x) (pr2 f) p).

  (* Look for stuff about discrete cats in new commits/PRs *)
  (* Email when done!! *)
  Definition slice_to_fam_mor_is_nat_trans {a b : slice X} (f : a --> b) :
    is_nat_trans (s_to_f a : functor (discrete X) HSET) (s_to_f b : functor (discrete X) HSET) (slice_to_fam_mor_fun f)
    := discrete_fun_is_nat_trans X has_homsets_HSET (slice_to_fam_mor_fun f).

  Definition slice_to_fam_mor {a b : slice X} (f : a --> b) : s_to_f a --> s_to_f b :=
    (slice_to_fam_mor_fun f) ,, (slice_to_fam_mor_is_nat_trans f).

  Definition slice_to_fam_data : functor_data (slice X) (fam X) :=
    functor_data_constr _ _ slice_to_fam_fun (@slice_to_fam_mor).

  (* maybe (later) look at when base category isn't an hSet (h1, h2, h3 stuff) *)
  Lemma slice_to_fam_is_functor : is_functor slice_to_fam_data.
  Proof.
    split; [ intro a | intros a b c f g];
      apply (nat_trans_eq has_homsets_HSET);
      intro x;
      apply funextsec; intro p;
        apply (invmaponpathsincl pr1); simpl;
          try (apply isofhlevelfpr1;
               intros ?; apply (pr2 (eqset _ _))).
    + unfold identity. simpl.
      unfold hfiber. rewrite transportf_total2.
      simpl. rewrite transportf_const.
      reflexivity.
    +  repeat (unfold hfiber; rewrite transportf_total2; simpl).
       repeat (rewrite transportf_const).
       reflexivity.
  Defined.

  Definition slice_to_fam_functor : functor (slice X) (fam X) :=
    slice_to_fam_data ,, slice_to_fam_is_functor.

  Definition fam_to_slice_fun (f : fam X) : slice X :=
    (total2_hSet (pr1 f)) ,, pr1.

  Local Notation f_to_s := fam_to_slice_fun.

  Definition fam_to_slice_mor {a b : fam X} (f : a --> b) : f_to_s a --> f_to_s b :=
  (fun h => pr1 h ,, (pr1 f) (pr1 h) (pr2 h)) ,, (idpath (pr2 (f_to_s a))).

  Definition fam_to_slice_data : functor_data (fam X) (slice X) :=
    functor_data_constr _ _ fam_to_slice_fun (@fam_to_slice_mor).

  Theorem fam_to_slice_is_functor : is_functor fam_to_slice_data.
  Proof.
    split; [intro f | intros f f' f'' F F'];
      apply (invmaponpathsincl pr1);
      try (apply isofhlevelfpr1;
           intros ?; apply (pr2 (eqset _ _))).
    + apply funextsec. intro p.
      exact (!tppr p).
    + reflexivity.
  Defined.

  Definition fam_to_slice_functor : functor (fam X) (slice X) :=
    fam_to_slice_data ,, fam_to_slice_is_functor.

  Definition slice_counit_fun (f : slice X) : (functor_composite_data slice_to_fam_data fam_to_slice_data) f --> (functor_identity_data _) f.
  Proof.
    exists (fun h : (Σ x : X, hfiber (pr2 f) x) => pr1 (pr2 h)).
    simpl.
    apply funextsec.
    intro p.
    exact (!pr2 (pr2 p)).
  Defined.

  Definition slice_counit_is_nat_trans : is_nat_trans _ _ slice_counit_fun.
  Proof.
    intros f f' F.
    apply (invmaponpathsincl pr1).
    + apply isofhlevelfpr1.
      intros ?.
      exact (pr2 (eqset _ _)).
    + unfold slice_counit_fun. simpl.
      unfold compose. simpl.
      apply funextsec. intro p.
      unfold hfiber. rewrite transportf_total2.
      simpl. rewrite transportf_const.
      reflexivity.
  Defined.

  Definition slice_counit : nat_trans (functor_composite slice_to_fam_functor fam_to_slice_functor) (functor_identity (slice X)) :=
    slice_counit_fun ,, slice_counit_is_nat_trans.

  Definition slice_all_iso : forall x : slice X, is_isomorphism (slice_counit x).
  Proof.
    intro x.
    apply iso_to_slice_precat_iso.
    simpl.
    assert (H : fromcoconusf (pr2 x) =
                (fun h : @total2 (pr1hSet X)
                                (fun x0 : pr1hSet X =>
                                   @hfiber (pr1hSet (@pr1 hSet (fun a : hSet => forall _ : pr1hSet a, pr1hSet X) x))
                                           (pr1hSet X)
                                           (@pr2 hSet (fun a : hSet => forall _ : pr1hSet a, pr1hSet X) x) x0)
                  => pr1 (pr2 h))).
    + reflexivity.
    + rewrite <- H.
      assert (coconus_isaset : isaset ((coconusf (pr2 x)))).
    - exact (isaset_total2_hSet X (fun y => (hfiber_hSet (pr2 x) y))).
    - exact (hset_equiv_is_iso (hSetpair (coconusf (pr2 x)) coconus_isaset) _ (weqfromcoconusf (pr2 x))).
  Defined.

  Definition slice_unit := nat_trans_inv_from_pointwise_inv _ _ (has_homsets_slice_precat _ has_homsets_HSET X) _ _ slice_counit slice_all_iso.

  Definition fam_unit_fun_fun (f : fam X) (x : X) :
    (pr1 ((functor_identity_data _) f)) x --> (pr1 ((functor_composite_data fam_to_slice_data slice_to_fam_data) f)) x :=
    fun a => ((x ,, a) ,, idpath x).

  Definition fam_unit_fun_is_nat_trans (f : fam X) :
    is_nat_trans (pr1 ((functor_identity_data _) f)) (pr1 ((functor_composite_data fam_to_slice_data slice_to_fam_data) f)) (fam_unit_fun_fun f).
  Proof.
    intros x x' g.
    rewrite g.
    apply funextsec. simpl. intro p.
    apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros ?.
      exact (pr2 (eqset _ _)).
    -  apply pair_path_in2.
       exact (transportb (fun f' => f' p = (identity ((pr1 f) x')) p) ((pr1 (pr2 f)) x') (idpath _)).
  Defined.

  Definition fam_unit_fun (f : fam X) : (functor_identity_data _) f --> (functor_composite_data fam_to_slice_data slice_to_fam_data) f :=
    (fam_unit_fun_fun f) ,, (fam_unit_fun_is_nat_trans f).

  Definition fam_unit_is_nat_trans : is_nat_trans _ _ fam_unit_fun.
  Proof.
    intros f f' F.
    apply (nat_trans_eq has_homsets_HSET).
    intro x.
    apply funextsec. intro a.
    apply (invmaponpathsincl pr1).
    + apply isofhlevelfpr1.
      intros ?.
      exact (pr2 (eqset _ _)).
    + reflexivity.
  Defined.

  Definition fam_unit : nat_trans (functor_identity (fam X)) (functor_composite fam_to_slice_functor slice_to_fam_functor) :=
    fam_unit_fun ,, fam_unit_is_nat_trans.

  Lemma fam_iso (F : fam X) : iso ((functor_identity (fam X)) F) ((functor_composite fam_to_slice_functor slice_to_fam_functor) F).
  Proof.
    apply (functor_iso_from_pointwise_iso _ _ has_homsets_HSET _ _ ((pr1 fam_unit) F)).
    intro x.
    unfold is_isomorphism. simpl.
    unfold fam_unit_fun_fun. simpl.
    assert (isaset_total2_F : isaset (Σ x ,  pr1 ((pr1 F) x))).
    - apply isaset_total2_hSet.
    - assert (isaset_hfiber_pr1 : isaset (hfiber (@pr1 (discrete X) (funcomp (pr1 (pr1 F)) pr1)) x)).
      + exact (@isaset_hfiber (hSetpair (Σ x ,  pr1 ((pr1 F) x)) isaset_total2_F) _ (@pr1 (discrete X) (funcomp (pr1 (pr1 F)) pr1)) x isaset_total2_F (pr2 X)).
      + assert (H : (λ a : (pr1 ((pr1 F) x)), (x,, a),, idpath x) = ezmappr1 (funcomp (pr1 (pr1 F)) pr1) x).
        * apply funextsec.
          intro a.
          reflexivity.
        * exact (hset_equiv_is_iso ((pr1 F) x) (hSetpair (hfiber pr1 x) isaset_hfiber_pr1) (ezweqpr1 (funcomp (pr1 (pr1 F)) pr1) x)).
  Defined.

  Definition fam_all_iso (F : fam X) : is_isomorphism (fam_unit F) := pr2 (fam_iso F).

  Definition fam_counit := nat_trans_inv_from_pointwise_inv _ _ (functor_category_has_homsets _ _ has_homsets_HSET) _ _ fam_unit fam_all_iso.

  Lemma slice_fam_form_adj : form_adjunction fam_to_slice_functor slice_to_fam_functor fam_unit slice_counit.
  Proof.
    unfold form_adjunction.
    split.
    + intro f.
      apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros ?.
      exact (pr2 (eqset _ _)).
    - apply funextsec. intro x.
      exact (!tppr _).
    + intro F.
      apply (nat_trans_eq has_homsets_HSET).
      intro x.
      apply funextsec.
      intro f.
      apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros ?.
      exact (pr2 (eqset _ _)).
    - simpl.
      unfold hfiber. rewrite transportf_total2.
      simpl. rewrite transportf_const.
      reflexivity.
  Defined.

  Definition slice_fam_are_adjoints : are_adjoints _ _ :=
    (fam_unit ,, slice_counit) ,, slice_fam_form_adj.

  Definition slice_fam_equiv : adj_equivalence_of_precats fam_to_slice_functor :=
    (slice_to_fam_functor ,, slice_fam_are_adjoints) ,, (fam_all_iso ,, slice_all_iso) .

End slice_fam_equiv.