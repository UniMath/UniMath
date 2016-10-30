Require Import UniMath.Foundations.Basics.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.CommaCategories
        UniMath.CategoryTheory.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.equivalences.

Section hfiber_hSet.

  Lemma isaset_hfiber {X : hSet} {Y : UU} (p : Π y1 y2 : Y, isaprop (y1 = y2)) (f : X -> Y) (y : Y) : isaset (hfiber f y).
  Proof.
    unfold hfiber.
    apply isaset_total2.
    apply (pr2 X).
    intro x.
    apply isasetaprop.
    apply p.
  Defined.

  Definition hfiber_hSet {X : hSet} {Y : UU} (p : Π y1 y2 : Y, isaprop (y1 = y2)) (f : X -> Y) (y : Y) : hSet :=
    hSetpair (hfiber f y) (isaset_hfiber p f y).

End hfiber_hSet.

(** * Discrete precategories FROM Anders' multisorted.v *)
Section DiscreteCategory.

Variable (A : UU).

Definition discrete_precategory_data : precategory_data.
Proof.
mkpair.
- apply (A,,paths).
- mkpair; [ apply idpath | apply @pathscomp0 ].
Defined.

Definition is_precategory_discrete_precategory_data : is_precategory discrete_precategory_data.
Proof.
split; [split|]; trivial; intros.
+ apply pathscomp0rid.
+ apply path_assoc.
Qed.

Definition discrete_precategory : precategory :=
  (discrete_precategory_data,,is_precategory_discrete_precategory_data).

Lemma has_homsets_discrete_precategory (H : isofhlevel 3 A) : has_homsets discrete_precategory.
Proof.
intros ? ? ? ? ? ?; apply H.
Qed.

(** To define a functor out of a discrete category it suffices to give a function *)
Lemma functor_discrete_precategory (D : precategory) (f : A → D) :
  functor discrete_precategory D.
Proof.
mkpair.
+ mkpair.
  - apply f.
  - intros s t []; apply identity.
+ abstract (now split; [intro|intros a b c [] []; simpl; rewrite id_left]).
Defined.

End DiscreteCategory.

(** Proof that Set / X is equivalent as categories to Set ^ X *)
Section slice_fam_equiv.

  Variable X : hSet.

  Local Definition slice (A : hSet) := slice_precat HSET A has_homsets_HSET.
  Local Definition discrete (A : hSet) := discrete_precategory (pr1 A).
  Local Definition discrete_has_homsets (A : hSet) :=
    has_homsets_discrete_precategory (pr1 A) (hlevelntosn 2 (pr1 A) (isofhlevelssnset 0 (pr1 A) (pr2 A))).
  Local Definition fam (A : hSet) := functor_precategory (discrete A) HSET has_homsets_HSET.
  Local Definition mkfam (f : (pr1 X) → hSet) := functor_discrete_precategory (pr1 X) HSET f.
  Local Definition mkhfiberhset {A B : hSet} (f : (pr1 A) → (pr1 B)) := hfiber_hSet (fun x x' => pr2 (eqset x x')) f.
  Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

  Definition slice_to_fam_fun (a : ob (slice X)) : ob (fam X) :=
    mkfam (fun x : X => mkhfiberhset (pr2 a) x).

  Local Notation s_to_f := slice_to_fam_fun.

  Definition slice_to_fam_mor_fun (a b : slice X) (f : a --> b) (x : X) : (pr1 (s_to_f a)) x --> (pr1 (s_to_f b)) x.
  Proof.
    intro p.
    exists ((pr1 f) (pr1 p)).
    rewrite <- (pr2 p).
    apply (transportb (fun f' => f' (pr1 p) = (pr2 a) (pr1 p)) (pr2 f) (idpath _)).
  Defined.

  Definition slice_to_fam_mor_is_nat_trans (a b : slice X) (f : a --> b) :
    is_nat_trans (pr1 (s_to_f a)) (pr1 (s_to_f b)) (slice_to_fam_mor_fun a b f).
  Proof.
    unfold is_nat_trans.
    intros x x' g.
    rewrite g.
    apply funextsec. intro p.
    apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros ?.
      apply (pr2 (eqset _ _)).
    - reflexivity.
  Defined.

  Definition slice_to_fam_mor (a b : slice X) (f : a --> b) : s_to_f a --> s_to_f b :=
    (slice_to_fam_mor_fun a b f) ,, (slice_to_fam_mor_is_nat_trans a b f).

  Definition slice_to_fam_data : functor_data (slice X) (fam X) :=
    functor_data_constr _ _ slice_to_fam_fun slice_to_fam_mor.

  Lemma slice_to_fam_is_functor : is_functor slice_to_fam_data.
  Proof.
    split; [ intro a | intros a b c f g];
      apply (nat_trans_eq has_homsets_HSET);
      intro x;
      apply funextsec; intro p;
      apply (invmaponpathsincl pr1).
      + apply isofhlevelfpr1.
        intros ?.
        apply (pr2 (eqset _ _)).
      + reflexivity.
      + apply isofhlevelfpr1.
        intros ?.
        apply (pr2 (eqset _ _)).
      + reflexivity.
  Defined.

  Definition slice_to_fam_functor : functor (slice X) (fam X) :=
    slice_to_fam_data ,, slice_to_fam_is_functor.

  Definition fam_to_slice_fun (f : ob (fam X)) : ob (slice X) :=
    (total2_hSet (pr1 f)) ,, pr1.

  Local Notation f_to_s := fam_to_slice_fun.

  Definition fam_to_slice_mor (a b : fam X) (f : a --> b) : f_to_s a --> f_to_s b :=
  (fun h => pr1 h ,, (pr1 f) (pr1 h) (pr2 h)) ,, (idpath (pr2 (f_to_s a))).

  Definition fam_to_slice_data : functor_data (fam X) (slice X) :=
    functor_data_constr _ _ fam_to_slice_fun fam_to_slice_mor.

  Theorem fam_to_slice_is_functor : is_functor fam_to_slice_data.
  Proof.
    split.
    + intro f.
      apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros ?.
      apply (pr2 (eqset _ _)).
    - apply funextsec.
      intro p. symmetry. apply tppr.
      + intros f f' f'' F F'.
        apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros ?.
      apply (pr2 (eqset _ _)).
    - reflexivity.
  Defined.

  Definition fam_to_slice_functor : functor (fam X) (slice X) :=
    fam_to_slice_data ,, fam_to_slice_is_functor.

  Definition slice_counit_fun (f : slice X) : (functor_composite_data slice_to_fam_data fam_to_slice_data) f --> (functor_identity_data _) f.
  Proof.
    exists (fun h : (Σ x : X, hfiber (pr2 f) x) => pr1 (pr2 h)).
    simpl.
    apply funextsec.
    intro p. apply(pr2 (pr2 p)).
  Defined.

  Definition slice_counit_is_nat_trans : is_nat_trans _ _ slice_counit_fun.
  Proof.
    intros f f' F.
    apply (invmaponpathsincl pr1).
    + apply isofhlevelfpr1.
      intros ?.
      apply (pr2 (eqset _ _)).
    + reflexivity.
  Defined.

  Definition slice_counit : nat_trans (functor_composite slice_to_fam_functor fam_to_slice_functor) (functor_identity (slice X)) :=
    slice_counit_fun ,, slice_counit_is_nat_trans.

  Definition slice_all_iso : forall x : slice X, is_isomorphism ((pr1 slice_counit) x).
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
    + rewrite <- H.      assert (coconus_isaset : isaset ((coconusf (pr2 x)))).
    - apply (isaset_total2_hSet X (fun y => (hfiber_hSet (fun z z' => pr2 (eqset z z')) (pr2 x) y))).
    - apply (hset_equiv_is_iso (hSetpair (coconusf (pr2 x)) coconus_isaset) _ (weqfromcoconusf (pr2 x))).
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
      apply (pr2 (eqset _ _)).
    -  apply pair_path_in2.
       apply (transportb (fun f' => f' p = (identity ((pr1 f) x')) p) ((pr1 (pr2 f)) x') (idpath _)).
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
      apply (pr2 (eqset _ _)).
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
      + apply (@isaset_hfiber (hSetpair (Σ x ,  pr1 ((pr1 F) x)) isaset_total2_F) _ (fun z z' : X => pr2 (eqset z z')) (@pr1 (discrete X) (funcomp (pr1 (pr1 F)) pr1)) x).
      + assert (H : (λ a : (pr1 ((pr1 F) x)), (x,, a),, idpath x) = ezmappr1 (funcomp (pr1 (pr1 F)) pr1) x).
        * apply funextsec.
          intro a.
          reflexivity.
        * apply (hset_equiv_is_iso ((pr1 F) x) (hSetpair (hfiber pr1 x) isaset_hfiber_pr1) (ezweqpr1 (funcomp (pr1 (pr1 F)) pr1) x)).
  Defined.

  Definition fam_all_iso (F : fam X) : is_isomorphism ((pr1 fam_unit) F) := pr2 (fam_iso F).

  Definition fam_counit := nat_trans_inv_from_pointwise_inv _ _ (functor_category_has_homsets _ _ has_homsets_HSET) _ _ fam_unit fam_all_iso.

  Lemma slice_fam_form_adj : form_adjunction fam_to_slice_functor slice_to_fam_functor fam_unit slice_counit.
  Proof.
    unfold form_adjunction.
    split.
    + intro f.
      apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros ?.
      apply (pr2 (eqset _ _)).
    - apply funextsec. intro x.
      symmetry. apply tppr.
    + intro F.
      apply (nat_trans_eq has_homsets_HSET).
      intro x.
      apply funextsec.
      intro f.
      apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros ?.
      apply (pr2 (eqset _ _)).
    - reflexivity.
  Defined.

  Definition slice_fam_are_adjoints : are_adjoints _ _ :=
    (fam_unit ,, slice_counit) ,, slice_fam_form_adj.

  Theorem slice_fam_equiv : adj_equivalence_of_precats fam_to_slice_functor.
  Proof.
    exists (slice_to_fam_functor ,, slice_fam_are_adjoints).
    split.
    + apply fam_all_iso.
    + apply slice_all_iso.
  Defined.

End slice_fam_equiv.