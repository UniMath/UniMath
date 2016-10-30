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

Section family_precategory. (* TODO: find in std lib *)

  Variable X : hSet.

  Definition family_precategory_ob_mor : precategory_ob_mor :=
    tpair (fun ob : UU => ob -> ob -> UU) (X -> hSet)
          (fun f g => Π x, hset_fun_space (f x) (g x)).

  Definition family_precategory_data : precategory_data :=
    precategory_data_pair
      family_precategory_ob_mor
      (fun (f : X -> hSet) (x : X) (z : f x) => z)
      (fun (f g h : pr1 X -> hSet)
           (F : Π x , hset_fun_space (f x) (g x))
           (G : Π x , hset_fun_space (g x) (h x))
           (x : X) (z : f x) => (G x) ((F x) z)).


  Lemma is_precategory_family_precategory_data :
    is_precategory family_precategory_data.
  Proof.
    repeat split; simpl.
  Defined.

  Definition family_precategory : precategory :=
    tpair _ _ is_precategory_family_precategory_data.

End family_precategory.

Section slice_fam_equiv.

  Variable X : hSet.

  Local Notation "hSet / X" := (slice_precat HSET X has_homsets_HSET). (* maybe redo where eq is homotopy *)
  Local Notation "hSet ^ X" := (family_precategory X).
  Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

  Local Lemma helper {A B : UU} (f g : A -> B) (p : f = g) (a : A) : f a = g a.
  Proof.
    intros.
    apply (transportb (fun f => f a = g a) p (idpath _)).
  Defined.

  Definition slice_to_fam_fun (A : ob (hSet / X)) : ob (hSet ^ X) :=
    fun x : X => hfiber_hSet (fun x x' => pr2 (eqset x x')) (pr2 A) x.

  Local Notation F := slice_to_fam_fun.

  Definition slice_to_fam_mor (a b : hSet / X) (f : a --> b) : F a --> F b.
  Proof.
    intros x p.
    unfold F. unfold hfiber_hSet. unfold hSetpair.
    exists ((pr1 f) (pr1 p)).
    Check (helper (fun x => pr2 b (pr1 f x)) (pr2 a) (pr2 f) (pr1 p)).
    (* apply (transportb (fun z => pr2 b (pr1 f z) = pr2 a z) (pr2 f) (idpath _)). *)
    rewrite (helper (fun x => pr2 b (pr1 f x)) (pr2 a) (pr2 f) (pr1 p)).
    apply (pr2 p).
  Defined.

  Definition slice_to_fam_data : functor_data (hSet / X) (hSet ^ X) :=
    functor_data_constr _ _ slice_to_fam_fun slice_to_fam_mor.

  Theorem slice_to_fam_is_functor : is_functor slice_to_fam_data.
  Proof.
    split.
    + unfold functor_idax.
      intros A.
      apply funextsec. intros x.
      apply funextsec. intros a.
      apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intro a'.
      apply (pr2 (eqset _ _)).
    - simpl. unfold identity. simpl.
      reflexivity.
      + unfold functor_compax.
        intros A B C f g.
        apply funextsec. intros x.
        apply funextsec. intros a.
        apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intro a'.
      apply (pr2 (eqset _ _)).
    - simpl. unfold compose. simpl.
      reflexivity.
  Defined.

  Definition slice_to_fam_functor : functor (hSet / X) (hSet ^ X) :=
    slice_to_fam_data ,, slice_to_fam_is_functor.

  Definition fam_to_slice_fun (f : ob (hSet ^ X)) : ob (hSet / X) :=
    (total2_hSet f) ,, pr1.

  Local Notation G := fam_to_slice_fun.

  Definition fam_to_slice_mor (a b : (hSet ^ X)) (f : a --> b) : G a --> G b.
  Proof.
    exists (fun h => pr1 h ,, f (pr1 h) (pr2 h)).
    reflexivity.
  Defined.

  Definition fam_to_slice_data : functor_data (hSet ^ X) (hSet / X) :=
    functor_data_constr _ _ fam_to_slice_fun fam_to_slice_mor.

  Theorem fam_to_slice_is_functor : is_functor fam_to_slice_data.
  Proof.
    split.
    + unfold functor_idax.
      intro f.
      apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intro f'.
      apply (pr2 (eqset _ _)).
    - simpl. unfold identity. simpl.
      apply funextsec.
      intro p. symmetry. apply tppr.
      + unfold functor_compax.
        intros f f' f'' F F'.
        apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intro f'''.
      apply (pr2 (eqset _ _)).
    - reflexivity.
  Defined.

  Definition fam_to_slice_functor : functor (hSet ^ X) (hSet / X) :=
    fam_to_slice_data ,, fam_to_slice_is_functor.

  Definition slice_counit_fun (f : (hSet / X)) : (functor_composite_data slice_to_fam_data fam_to_slice_data) f --> (functor_identity_data _) f.
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
      intro F'.
      apply (pr2 (eqset _ _)).
    + reflexivity.
  Defined.

  Definition slice_counit : nat_trans (functor_composite slice_to_fam_functor fam_to_slice_functor) (functor_identity (hSet / X)) :=
    slice_counit_fun ,, slice_counit_is_nat_trans.

  Definition slice_all_iso : forall x : (hSet / X), is_isomorphism ((pr1 slice_counit) x).
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
    - apply (isaset_total2_hSet X (fun y => (hfiber_hSet (fun z z' => pr2 (eqset z z')) (pr2 x) y))).
    - apply (hset_equiv_is_iso (hSetpair (coconusf (pr2 x)) coconus_isaset) _ (weqfromcoconusf (pr2 x))).
  Defined.

  Definition fam_unit_fun (f : hSet ^ X) : (functor_identity_data _) f --> (functor_composite_data fam_to_slice_data slice_to_fam_data) f :=
    fun x a => ((x ,, a) ,, idpath x).

  Definition fam_unit_is_nat_trans : is_nat_trans _ _ fam_unit_fun.
  Proof.
    intros f f' F.
    apply funextsec. intro x.
    apply funextsec. intro a.
    apply (invmaponpathsincl pr1).
    + apply isofhlevelfpr1.
      intro F'.
      apply (pr2 (eqset _ _)).
    + reflexivity.
  Defined.

  Definition fam_unit : nat_trans (functor_identity (family_precategory X)) (functor_composite fam_to_slice_functor slice_to_fam_functor) :=
    fam_unit_fun ,, fam_unit_is_nat_trans.

  Lemma iso_to_fam_precat_iso (F F' : hSet ^ X) (f : F --> F') : (Π (x : X) , @is_isomorphism HSET (F x) (F' x) (f x)) -> is_isomorphism f.
  Proof.
    simpl in F. simpl in F'.
    unfold is_isomorphism.
    unfold is_iso.
    unfold precomp_with. simpl.
    intros P F''. Check hfibertoforall.

    unfold isweq. intro g.

  Admitted.

  Definition fam_all_iso : forall x : (hSet ^ X), is_isomorphism ((pr1 fam_unit) x).
  Proof.
    simpl. intro F.
    unfold is_isomorphism.
    unfold fam_unit_fun. simpl.
    assert (H : (λ (x : X) (a : F x), (x,, a),, idpath x) = (λ (x : X) , ezmappr1 F x)).
    + reflexivity.
    + rewrite H.
      apply iso_to_fam_precat_iso.
      intro x.
      unfold is_isomorphism. simpl.
      Check (ezmappr1 (λ x0 : X, F x0) x). Print hfiber_hSet.
      assert (isaset_total2_F : isaset (Σ x , F x)).
      * apply isaset_total2_hSet.
      * assert (isaset_hfiber_pr1 : isaset (hfiber (@pr1 X F) x)).
    - apply (@isaset_hfiber (hSetpair (Σ x : X, F x) isaset_total2_F) _ (fun z z' : X => pr2 (eqset z z')) (@pr1 X F) x).
    - apply (hset_equiv_is_iso (F x) (hSetpair (hfiber (@pr1 X F) x) isaset_hfiber_pr1) (ezweqpr1 F x)).
  Defined.

  Definition F_G_form_adjunction : form_adjunction _ _ fam_unit slice_counit.
  Proof.
    unfold form_adjunction.
    split.
    + intro f.
      apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intro f'.
      apply (pr2 (eqset _ _)).
    - unfold compose.
      apply funextsec. intro x.
      symmetry. apply tppr.
      + intro F.
        apply funextsec.
        intro x.
        unfold identity; simpl.
        apply funextsec.
        intro f.
        apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intro a.
      apply (pr2 (eqset _ _)).
    - reflexivity.
  Defined.

  Definition F_G_are_adjoints : are_adjoints _ _ :=
    (fam_unit ,, slice_counit) ,, F_G_form_adjunction.

  Theorem slice_fam_equiv : Σ (G : functor (hSet ^ X) (hSet / X)), adj_equivalence_of_precats G.
  Proof.
    exists fam_to_slice_functor.
    unfold adj_equivalence_of_precats.
    unfold is_left_adjoint.
    exists (slice_to_fam_functor ,, F_G_are_adjoints).
    split.
    + intros f f'.
      unfold precomp_with. simpl.
      unfold compose. simpl.
      unfold fam_unit_fun.
      simpl.

      intro F.
      unfold iscontr.
      assert (H : Π (x : X) (p : hfiber (X:=(Σ (x' : X), f x')) pr1 x), pr1 (pr1 p) = x).
    - intros x p.
      rewrite (pr2 p). reflexivity.
    - pose (g' := fun (x : X) (p : hfiber (X:=(Σ (x' : X), f x')) pr1 x) => F (pr1 (pr1 p)) (pr2 (pr1 p))).
      c      assert (K' : (fun (x : X) (z : f x) => g' x ((x ,, z) ,, idpath x)) = F).
      -- unfold g'. simpl.
         apply funextsec. intro x.
         apply funextsec. intro z.
         reflexivity.
      -- pose (g := fun (x : X) (p : hfiber pr1 x) => (transportf (fun x' => f' x') (H x p) (g' x p))).
         simpl in g.
         assert (K : (fun (x : X) (z : f x) => g x ((x ,, z) ,, idpath x)) = F).
         ++ rewrite <- K'.
            apply funextsec; intro x.
            apply funextsec; intro z.
            unfold g. unfold g'. simpl.
            simpl. unfold transportf. simpl.


            exists
              intros t.
            apply (invmaponpathsincl pr1).
    - apply isofhlevelfpr1.
      intros g.
      simpl.
      intros p p'.
      admit.
    - simpl. reflexivity.

  Admitted.


(*

  Definition slice_unit_fun (f : (hSet / X)) : (functor_identity_data _) f --> (functor_composite_data slice_to_fam_data fam_to_slice_data) f :=
    (fun x => ((pr2 f) x ,, ( x ,, idpath _))) ,, (idpath _).

  Open Scope transport.

  Definition slice_unit_is_nat_trans : is_nat_trans _ _ slice_unit_fun.
  Proof.
    intros f f' F.
    apply (invmaponpathsincl pr1).
    + apply isofhlevelfpr1.
      intro F'.
      apply (pr2 (eqset _ _)).
    + simpl. unfold compose. simpl.
      apply funextsec. intro x.
      assert (H : (compose (pr1 F) (pr2 f')) x = pr2 f x).
    - rewrite (pr2 F). reflexivity.
    - unfold compose in H. simpl in H.
      apply total2_paths2 with (p := H).
      unfold slice_to_fam_mor. simpl.
      apply (invmaponpathsincl pr1).
      * apply isofhlevelfpr1.
         intro F'.
         apply (pr2 (eqset _ _)).
      * simpl.
   Admitted.

  Definition slice_unit : nat_trans (functor_identity (slice_precat HSET X has_homsets_HSET)) (functor_composite slice_to_fam_functor fam_to_slice_functor) :=
    slice_unit_fun ,, slice_unit_is_nat_trans.
 *)


(*
  Definition fam_counit_fun (f : hSet ^ X) : (functor_composite_data fam_to_slice_data slice_to_fam_data) f -->(functor_identity_data _) f.
  Proof.
    intros x a.
    assert (H : pr1 (pr1 a) = x).
    + apply (pr2 a).
    + rewrite <- H.
      apply (pr2 (pr1 a)).
  Defined.

  Definition fam_counit_is_nat_trans : is_nat_trans _ _ fam_counit_fun.
  Proof.
    intros f f' F.
    apply funextsec. intro x.
    apply funextsec. intro a.
    simpl. unfold compose. simpl.
    Admitted.

  Definition fam_counit : nat_trans (functor_composite fam_to_slice_functor slice_to_fam_functor) (functor_identity (family_precategory X)) :=
    fam_counit_fun ,, fam_counit_is_nat_trans.
 *)

(*
  Definition G_F_form_adjunction : form_adjunction _ _ slice_unit fam_counit.
  Proof.
  Admitted.

  Definition G_F_are_adjoints : are_adjoints _ _ :=
    (slice_unit ,, fam_counit) ,, G_F_form_adjunction.
 *)

End slice_fam_equiv.