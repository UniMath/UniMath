(** **********************************************************
Matthew Weaver, 2017
************************************************************)


(** **********************************************************
Contents : Equivalence of the categories pshf ∫P and
           pshf C / P for any P in pshf C
************************************************************)

Require Import UniMath.MoreFoundations.Tactics
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.Categories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.equivalences
        UniMath.CategoryTheory.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.opp_precat
        UniMath.CategoryTheory.ElementsOp.

(** * Proof that pshf ∫P ≃ pshf C / P *)
Section elems_slice_equiv.

  Local Open Scope cat.

  Local Definition pshf (C : precategory) : category := [C^op, SET].
  Local Notation "C / X" := (slice_precat C X (pr2 C)).
  Local Definition ap_pshf {X : precategory} := fun (P : pshf X) (x : X) => pr1hSet ((pr1 P) x).
  Local Notation "##" := ap_pshf.

  (* BEGIN: Stuff from Anders *)
  Lemma transportb_to_transportf (X : UU) (P : X -> UU) (x y : X) (e : x = y) (px : P x) (py : P y) :
    transportf P e px = py -> px = transportb P e py.
  Proof.
    intros H.
    now rewrite <- H, transportbfinv.
  Qed.

  Lemma transportf_pshf (C : precategory) (F : pshf C) (x y z : C)
        (e : x = y) (f : C⟦x,z⟧) (u : ##F z) :
    transportf (λ x, ##F x) e (# (pr1 F) f u) =
    # (pr1 F) (transportf (@precategory_morphisms C^op z) e f) u.
  Proof.
    now induction e.
  Qed.

  Lemma pr1_pair_path_in2 (X : UU) (P : X → UU) (x : X) (p q : P x) (e : p = q) :
    maponpaths pr1 (pair_path_in2 P e) = idpath x.
  Proof.
    now induction e.
  Qed.
  (* END: Stuff From Anders *)

  Variable (C : precategory).
  Variable (P : pshf C).

  (* BEGIN: Stuff from Anders *)
  (* Any f : J → I and ρ : P I defines a morphism from (J,,# P ρ) to (I,,ρ) in ∫P *)
  Definition mor_to_el_mor {I J : C} (f : J --> I) (ρ : pr1 P I : hSet) :
    ∫P ⟦ make_ob J (# (pr1 P) f ρ), make_ob I ρ ⟧ :=
    make_mor (J,,# (pr1 P) f ρ) (I,,ρ) f (idpath (# (pr1 P) f ρ)).

  Lemma make_ob_eq {I : C} {x y} (e : x = y) :
    make_ob I x = @make_ob C P I y.
  Proof.
    apply pair_path_in2, e.
  Defined.

  Lemma transportf_make_ob {A : pshf ∫P} {I : C} {x y} (e : x = y)
        (u : pr1 (pr1 A (make_ob I x))) :
    transportf (λ x, pr1 (pr1 A (make_ob I x))) e u =
    transportf (λ x, pr1 (pr1 A x)) (make_ob_eq e) u.
  Proof.
    now induction e.
  Qed.

  Lemma make_ob_identity_eq {I : C} (ρ : pr1 (pr1 P I)) :
    make_ob I (# (pr1 P) (identity I) ρ) = make_ob I ρ.
  Proof.
    exact (make_ob_eq (eqtohomot (functor_id P I) ρ)).
  Defined.

  Lemma mor_to_el_mor_id {I : C} (ρ : pr1 (pr1 P I)) :
    mor_to_el_mor (identity I) ρ =
    transportb (λ X, ∫P⟦X, make_ob I ρ⟧) (make_ob_eq (eqtohomot (functor_id P I) ρ)) (identity _).
  Proof.
    apply (transportb_to_transportf _ (λ X : ∫P, ∫P ⟦X,_⟧)), cat_of_elems_mor_eq; simpl.
    rewrite transportf_total2; simpl.
    etrans; [apply (functtransportf pr1 (λ x, C⟦x,I⟧) (make_ob_identity_eq _))|].
    assert (H : maponpaths pr1 (make_ob_identity_eq ρ) = idpath _).
    { apply pr1_pair_path_in2. }
    now rewrite H, idpath_transportf.
  Qed.

  Lemma mor_to_el_mor_comp_eq {I J K} (ρ : pr1 (pr1 P I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
    make_ob _ (# (pr1 P) (f · g) ρ) = make_ob _ (# (pr1 P) g (# (pr1 P) f ρ)).
  Proof.
    exact (make_ob_eq (eqtohomot (functor_comp P f g) ρ)).
  Defined.

  Lemma mor_to_el_mor_comp {I J K} (ρ : pr1 (pr1 P I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
    mor_to_el_mor (f · g) ρ =
    transportb (λ X, ∫P⟦X,_⟧) (mor_to_el_mor_comp_eq ρ f g)
               (mor_to_el_mor g (# (pr1 P) f ρ) · mor_to_el_mor f ρ).
  Proof.
    apply (transportb_to_transportf _ (λ X : ∫P, ∫P ⟦X,_⟧)), cat_of_elems_mor_eq; simpl.
    rewrite transportf_total2; simpl.
    etrans; [apply (functtransportf pr1 (λ x, C⟦x,I⟧) (mor_to_el_mor_comp_eq ρ f g))|].
    assert (H : maponpaths pr1 (mor_to_el_mor_comp_eq ρ f g) = idpath _).
    { apply pr1_pair_path_in2. }
    now rewrite H, idpath_transportf.
  Qed.
  (* END: Stuff from Anders *)

  (** ** Construction of the functor from pshf ∫P to pshf C / P *)
  Local Definition mk_ob := @make_ob C P.
  Local Definition mk_mor := @make_mor C P.

  Definition pshf_to_slice_ob_funct_fun (F : pshf ∫P) : C^op → SET :=
    fun X => total2_hSet (fun p : ##P X => (pr1 F) (mk_ob X p)).

  Definition pshf_to_slice_ob_funct_mor (F : pshf ∫P) {X Y : C^op} (f : X --> Y) :
    pshf_to_slice_ob_funct_fun F X --> pshf_to_slice_ob_funct_fun F Y :=
    fun p => # (pr1 P) f (pr1 p) ,, # (pr1 F) (mor_to_el_mor f (pr1 p)) (pr2 p).

  Definition pshf_to_slice_ob_funct_data (F : pshf ∫P) : functor_data C^op SET :=
    pshf_to_slice_ob_funct_fun F ,, @pshf_to_slice_ob_funct_mor F.

  (* Proof from Anders:
     see [ctx_ext] in https://github.com/mortberg/TypeTheory/blob/cube0/TypeTheory/Cubical/cubical.v *)
  Definition pshf_to_slice_ob_is_funct (F : pshf ∫P) : is_functor (pshf_to_slice_ob_funct_data F).
  Proof.
    split.
    + intros I; apply funextfun; intros [ρ u].
      use total2_paths_f.
      * exact (eqtohomot (functor_id P I) ρ).
      * etrans; [use transportf_make_ob|].
        etrans; [apply (transportf_pshf (∫P) F)|]; cbn.
        now rewrite (mor_to_el_mor_id ρ), transportfbinv, (functor_id F).
    + intros I J K f g; apply funextfun; intros [ρ u].
      use total2_paths_f.
      * exact (eqtohomot (functor_comp P f g) ρ).
      * etrans; [use transportf_make_ob|].
        etrans; [apply (transportf_pshf (∫P) F)|].
        rewrite (mor_to_el_mor_comp _ f g), transportfbinv.
        generalize u; simpl in *.
        apply eqtohomot, (functor_comp F (mor_to_el_mor f ρ) (mor_to_el_mor g (# (pr1 P) f ρ))).
  Qed.

  (* Version of proof worked out by Vladimir and me *)
  Definition pshf_to_slice_ob_is_funct' (F : pshf ∫P) : is_functor (pshf_to_slice_ob_funct_data F).
  Proof.
    split;
      [intros X | intros X Y Z f g];
      apply funextsec; intros [p q].

    + set (T := ∑ p' : ## P X, p' = # (pr1 P) (identity X) p : UU).
      set (T' := ∑ p' : ## P X, (pr1 F) (X ,, p) --> (pr1 F) (X ,, p') : UU).
      set (phi := fun (x : T) => mk_mor (X ,, pr1 x) (X ,, p) (identity X) (pr2 x)).
      set (G := fun (x : T) => pr1 x ,, # (pr1 F) (phi x) : T').
      set (e := fun (x : ∫P) => eqtohomot (!((functor_id P) (pr1 x))) (pr2 x)).
      set (h := fun (x : T') => pr1 x ,, (pr2 x) q : pr1hSet (pshf_to_slice_ob_funct_fun F X)).

      refine (maponpaths (funcomp G h)
                         (connectedcoconustot ((# (pr1 P) (identity X) p) ,, idpath _) (p ,, e (X ,, p))) @ _).
      refine (@pair_path_in2 _ (fun x => pr1hSet ((pr1 F) (X ,, x))) p _ _ _).
      refine (eqtohomot _ q @ eqtohomot (functor_id F (X ,, p)) q).
      refine (maponpaths (# (pr1 F)) _).
      use total2_paths_f.
      * reflexivity.
      * rewrite idpath_transportf;
        now apply eqset.

    + set (T := ∑ p' : ## P Z, p' = # (pr1 P) (g ∘ f) p : UU).
      set (T' := ∑ p' : ## P Z, (pr1 F) (X ,, p) --> (pr1 F) (Z ,, p') : UU).
      set (phi := fun (x : T) => mk_mor (Z ,, pr1 x) (X ,, p) (g ∘ f) (pr2 x)).
      set (G := fun (x : T) => (pr1 x ,, # (pr1 F) (phi x)) : T').
      set (e := fun (z y x : ∫P) (f : z --> y) (g : y --> x) =>
                  ((pr2 f) @ maponpaths (# (pr1 P) (pr1 f)) (pr2 g)
                    @ (eqtohomot (!(functor_comp P) (pr1 g) (pr1 f)) (pr2 x)))).
      set (h := fun (x : T') => pr1 x ,, (pr2 x) q : pr1hSet (pshf_to_slice_ob_funct_fun F Z)).

      refine (maponpaths (funcomp G h)
                         (connectedcoconustot (# (pr1 P) (g ∘ f) p ,, idpath _)
                                              (# (pr1 P) g (# (pr1 P) f p) ,,
                                                 e (mk_ob Z (# (pr1 P) g (# (pr1 P) f p)))
                                                 (mk_ob Y (# (pr1 P) f p)) (mk_ob X p)
                                                 (g ,, idpath _) (f ,, idpath _))) @ _).
      refine (@pair_path_in2 _ (fun x => pr1hSet ((pr1 F) (Z ,, x))) (# (pr1 P) g (# (pr1 P) f p)) _ _ _).
      refine (eqtohomot _ q @ eqtohomot (@functor_comp _ _ F (mk_ob X p)
                                                       (mk_ob Y (# (pr1 P) f p))
                                                       (mk_ob Z (# (pr1 P) g (# (pr1 P) f p)))
                                                       (f ,, idpath _) (g,, idpath _)) q).
      refine (maponpaths (# (pr1 F)) _).
      use total2_paths_f.
      * reflexivity.
      * rewrite idpath_transportf;
        now apply eqset.
  Qed.

  Definition pshf_to_slice_ob_funct (F : pshf ∫P) : pshf C :=
    pshf_to_slice_ob_funct_data F ,, pshf_to_slice_ob_is_funct F.

  Definition pshf_to_slice_ob_nat_fun (F : pshf ∫P) (x : C) : (∑ (Px :##P x), ##F (x,, Px)) → ##P x := pr1.

  Definition pshf_to_slice_ob : pshf ∫P → pshf C / P.
  Proof.
    intro F.
    exists (pshf_to_slice_ob_funct F).
    now exists (pshf_to_slice_ob_nat_fun F).
  Defined.

  Definition pshf_to_slice_ob_nat {X Y : pshf ∫P} (f : X --> Y) (c : C)
    : (∑ Px : ## P c, ## X (c,, Px)) → (∑ Px : ## P c, ## Y (c,, Px)) :=
    fun p => pr1 p ,, (pr1 f) (c ,, (pr1 p)) (pr2 p).

  Definition pshf_to_slice_ob_isnat {X Y : pshf ∫P} (f : X --> Y) :
    is_nat_trans (pshf_to_slice_ob_funct_data X) (pshf_to_slice_ob_funct_data Y) (pshf_to_slice_ob_nat f).
    simpl.
    intros c c' g.
    apply funextsec; intro p.
    apply pair_path_in2.
    exact (eqtohomot ((pr2 f) (c ,, pr1 p) (c',, # (pr1 P) g (pr1 p)) (g,, idpath (# (pr1 P) g (pr1 p)))) (pr2 p)).
  Qed.

  Definition pshf_to_slice_mor {X Y : pshf ∫P} (f : X --> Y) :
    pshf_to_slice_ob X --> pshf_to_slice_ob Y.
    exists (pshf_to_slice_ob_nat f ,, pshf_to_slice_ob_isnat f).
    now apply (nat_trans_eq has_homsets_HSET).
  Defined.

  Definition pshf_to_slice_data : functor_data (pshf ∫P) (pshf C / P) :=
    pshf_to_slice_ob ,, @pshf_to_slice_mor.

  Definition pshf_to_slice_is_funct : is_functor pshf_to_slice_data.
  Proof.
    split; [intros X | intros X Y Z f g];
      apply eq_mor_slicecat;
      apply (nat_trans_eq has_homsets_HSET);
      unfold pshf_to_slice_ob_nat , pshf_to_slice_ob_funct_fun;
      intro c;
      apply funextsec; intro p;
      now rewrite tppr.
  Defined.

  Definition pshf_to_slice : functor (pshf ∫P) (pshf C / P) :=
    pshf_to_slice_data ,, pshf_to_slice_is_funct.

  (** ** Construction of the functor from pshf C / P to pshf ∫P *)
  Definition slice_to_pshf_ob_ob (Q : pshf C / P) : (∫P)^op → SET :=
    fun p =>
      hfiber ((pr1 (pr2 Q)) (pr1 p)) (pr2 p) ,,
             isaset_hfiber ((pr1 (pr2 Q)) (pr1 p)) (pr2 p) (pr2 (((pr1 (pr1 Q)) (pr1 p)))) (pr2 ((pr1 P) (pr1 p))).

  Definition slice_to_pshf_ob_mor (Q : pshf C / P) {F G : (∫P)^op} (f : F --> G) :
    slice_to_pshf_ob_ob Q F --> slice_to_pshf_ob_ob Q G.
    intros s.
    destruct Q as [[[Q Qmor] Qisfunct] [Qnat Qisnat]].
    destruct F as [x Px]. destruct G as [y Py].
    destruct f as [f feq].
    apply (hfibersgftog (Qmor _ _ f) (Qnat y)).
    exists (pr1 s).
    rewrite feq.
    refine (eqtohomot (Qisnat _ _ f) (pr1 s) @ _).
    exact (maponpaths (# (pr1 P) f) (pr2 s)).
  Defined.

  Definition slice_to_pshf_ob_funct_data (Q : pshf C / P) : functor_data ((∫P)^op) SET :=
    slice_to_pshf_ob_ob Q ,, @slice_to_pshf_ob_mor Q.

  Definition slice_to_pshf_ob_is_funct (Q : pshf C / P) : is_functor (slice_to_pshf_ob_funct_data Q).
  Proof.
    split;
      [intros [x Px] | intros [x Px] [y Py] [z Pz] [f feq] [g geq]];
      destruct Q as [[[Q Qmor] Qisfunct] [Qnat Qisnat]];
      apply funextsec; intro p;
        apply (invmaponpathsincl pr1);
        try (apply isofhlevelfpr1;
             intros ?; exact (pr2 (eqset _ _))).
    + exact (eqtohomot ((pr1 Qisfunct) x) (pr1 p)).
    + exact (eqtohomot ((pr2 Qisfunct) x y z f g) (pr1 p)).
  Qed.

  Definition slice_to_pshf_ob : pshf C / P → pshf ∫P :=
    fun Q =>  slice_to_pshf_ob_funct_data Q ,,  slice_to_pshf_ob_is_funct Q.

  Definition slice_to_pshf_ob_nat {X Y : pshf C / P} (F : X --> Y) (e : ∫P^op) :
    (slice_to_pshf_ob_ob X) e --> (slice_to_pshf_ob_ob Y) e.
  Proof.
    induction e as [e Pe].
    exact (fun p => hfibersgftog ((pr1 (pr1 F)) e)
                                 ((pr1 (pr2 Y)) e) Pe
                                 (transportf (fun x => hfiber (x e) Pe) (base_paths _ _ (pr2 F)) p)).
  Defined.

  Definition slice_to_pshf_ob_is_nat {X Y : pshf C / P} (F : X --> Y) :
    is_nat_trans (slice_to_pshf_ob X : functor _ _) (slice_to_pshf_ob Y : functor _ _) (slice_to_pshf_ob_nat F).
  Proof.
    intros [e Pe] [e' Pe'] [f feq].
    destruct X as [[[X Xmor] Xisfunct] [Xnat Xisnat]].
    destruct Y as [[[Y Ymor] Yisfunct] [Ynat Yisnat]].
    destruct F as [[F Fisnat] Feq].
    simpl in *.
    apply funextsec; intros [p peq].
    apply (invmaponpathsincl pr1).
    + apply isofhlevelfpr1.
      intros ?.
      exact (pr2 (eqset _ _)).
    + simpl.
      destruct peq.
      unfold hfiber.
      repeat rewrite transportf_total2.
      simpl.
      repeat rewrite transportf_const.
      exact (eqtohomot (Fisnat e e' f) p).
  Qed.

  Definition slice_to_pshf_mor {X Y : pshf C / P} (F : X --> Y) :
    slice_to_pshf_ob X --> slice_to_pshf_ob Y :=
    slice_to_pshf_ob_nat F ,, slice_to_pshf_ob_is_nat F.

  Definition slice_to_pshf_data : functor_data (pshf C / P) (pshf ∫P) :=
    slice_to_pshf_ob ,, @slice_to_pshf_mor.

  Definition slice_to_pshf_is_funct : is_functor slice_to_pshf_data.
  Proof.
    split; [ intros X | intros X Y Z F G];
      apply (nat_trans_eq has_homsets_HSET);
      intros [c Pc];
      apply funextsec; intros [p peq];
      apply (invmaponpathsincl pr1);
      try (apply isofhlevelfpr1;
           intros ?;
                  exact (pr2 (eqset _ _)));
      simpl;
      unfold hfiber;
      unfold hfibersgftog; unfold hfiberpair;
      repeat (rewrite transportf_total2;
              simpl; unfold hfiber);
      now repeat rewrite transportf_const.
  Qed.

  Definition slice_to_pshf : functor (pshf C / P) (pshf ∫P) :=
    slice_to_pshf_data ,, slice_to_pshf_is_funct.

  (** ** Construction of the natural isomorphism from (slice_to_pshf ∙ pshf_to_slice) to the identity functor *)
  Definition slice_counit_fun (X : pshf C / P) :
    (slice_to_pshf ∙ pshf_to_slice) X --> (functor_identity _) X.
  Proof.
    destruct X as [[[X Xmor] Xisfunct] [Xnat Xisnat]].
    simpl in *.
    repeat (mkpair; simpl).
    + intros x [p q].
      exact (pr1 q).
    + intros A B f.
      apply funextsec; intros [p peq].
      reflexivity.
    + apply (nat_trans_eq has_homsets_HSET).
      intros A.
      apply funextsec; intros [p [q e]].
      exact (!e).
  Defined.

  Definition is_nat_trans_slice_counit : is_nat_trans _ _ slice_counit_fun.
  Proof.
    intros X Y f.
    apply eq_mor_slicecat , (nat_trans_eq has_homsets_HSET).
    intros A.
    apply funextsec; intros [p [q e]].
    simpl. unfold compose. simpl.
    destruct X as [[[X Xmor] Xisfunct] [Xnat Xisnat]].
    destruct Y as [[[Y Ymor] Yisfunct] [Ynat Yisnat]].
    destruct f as [[f fisnat] feq]. simpl in *.
    apply maponpaths. unfold hfiber.
    rewrite transportf_total2. simpl.
    rewrite transportf_const.
    now unfold idfun.
  Qed.

  Definition slice_counit : nat_trans (slice_to_pshf ∙ pshf_to_slice) (functor_identity (pshf C / P)) :=
    slice_counit_fun ,, is_nat_trans_slice_counit.

  Definition slice_all_iso : forall F : pshf C / P, is_iso (slice_counit F).
  Proof.
    intros [[[F Fmor] Fisfunct] [Fnat Fisnat]].
    apply iso_to_slice_precat_iso.
    apply functor_iso_if_pointwise_iso.
    intros X; simpl.
    match goal with
    | |- is_iso ?t => assert (eq : t =
                                   (fun X0 => pr1 (pr2 X0)))
    end.
    { apply funextsec. intros [p q]. simpl. reflexivity. }
    rewrite eq.
    change (fun X0 => pr1 (pr2 X0)) with (fromcoconusf (Fnat X)).
    exact (hset_equiv_is_iso (hSetpair (coconusf (Fnat X))
                                         (isaset_total2_hSet _ (fun y => (hfiber_hSet (Fnat X) y)))) _
                               (weqfromcoconusf (Fnat X))).
  Qed.

  Definition slice_unit : nat_trans (functor_identity (pshf C / P)) (slice_to_pshf ∙ pshf_to_slice) :=
    nat_trans_inv_from_pointwise_inv _ _
                                     (has_homsets_slice_precat (pr2 (pshf C)) P)
                                     (slice_to_pshf ∙ pshf_to_slice) (functor_identity (pshf C / P))
                                     slice_counit slice_all_iso.

  (** ** Construction of the natural isomorphism from the identity functor to (pshf_to_slice ∙ slice_to_pshf) *)
  Definition pshf_unit_fun (F : pshf ∫P) :
    (functor_identity _) F --> (pshf_to_slice ∙ slice_to_pshf) F.
  Proof.
    mkpair.
    + intros [X p] x.
      exact ((p ,, x) ,, idpath p).
    + intros [X p] [X' p'] [f feq].
      simpl in *.
      apply funextsec; intros x.
      apply (invmaponpathsincl pr1).
      apply isofhlevelfpr1;
        intros ?;
               exact (pr2 (eqset _ _)).
      induction (!feq).
      apply (total2_paths2_f (idpath _)).
      rewrite idpath_transportf.
      assert (set_eq : idpath _ = feq).
      { apply (pr2 (P X')). }
      now induction set_eq.
  Defined.

  Definition is_nat_trans_pshf_unit : is_nat_trans _ _ pshf_unit_fun.
  Proof.
    intros [[F Fmor] Fisfunct] [[G Gmor] Gisfunct] [f fisnat].
    apply (nat_trans_eq has_homsets_HSET).
    intros [X p].
    apply funextsec; intros q.
    apply (invmaponpathsincl pr1).
    apply isofhlevelfpr1;
      intros ?;
             exact (pr2 (eqset _ _)).
    simpl. unfold hfiber.
    rewrite transportf_total2; simpl.
    now rewrite transportf_const.
  Qed.

  Definition pshf_unit : nat_trans (functor_identity (pshf ∫P)) (pshf_to_slice ∙ slice_to_pshf) :=
    pshf_unit_fun ,, is_nat_trans_pshf_unit.

  Definition pshf_all_iso : forall F : pshf ∫P, is_iso (pshf_unit F).
  Proof.
    intros [[F Fmor] Fisfunct].
    apply functor_iso_if_pointwise_iso.
    intros [X p]; simpl.
    assert (H : isweq (λ x : pr1hSet (F (X,, p)) , (p,, x) ,, idpath p : pr1hSet (slice_to_pshf_ob_ob (pshf_to_slice_ob ((F,, Fmor),, Fisfunct)) (X,, p)))).
    { unfold isweq. intros [[p' x'] e'].
      simpl in *. induction e'.
      refine ((x',, idpath _),, _).
      intros [x'' t].
      apply (invmaponpathsincl pr1).
      apply isofhlevelfpr1;
        intros ?;
               exact (pr2 (@eqset
                             ((slice_to_pshf_ob_ob (pshf_to_slice_ob ((F,, Fmor),, Fisfunct)) (X,, p'))) _ _)).
      assert (eq_id : base_paths (p',, x'') (p',, x') (maponpaths pr1 t) = idpath p').
      { set (c := iscontraprop1 (pr2 (@eqset ((pr1 P) X) p' p')) (idpath p')).
        exact ((pr2 c) _ @ !((pr2 c) _)).
      }
      set (eq := fiber_paths (maponpaths pr1 t)).
      refine (_ @ eq).
      rewrite (transportf_paths _ eq_id).
      now rewrite idpath_transportf.
    }
    exact (hset_equiv_is_iso (F (X ,, p)) _ (_ ,, H)).
  Qed.

  Definition pshf_counit : nat_trans (pshf_to_slice ∙ slice_to_pshf) (functor_identity (pshf ∫P))  :=
    nat_trans_inv_from_pointwise_inv _ _ (pr2 (pshf ∫P)) _ _ pshf_unit pshf_all_iso.

  (** ** The equivalence of the categories pshf ∫P and pshf C / P *)
  Definition pshf_of_elems_slice_of_pshf_equiv : equivalence_of_precats (pshf ∫P) (pshf C / P) :=
    (pshf_to_slice ,,  slice_to_pshf ,, pshf_unit ,, slice_counit) ,, (pshf_all_iso ,, slice_all_iso).

  Definition pshf_of_elems_slice_of_pshf_adj_equiv : adj_equivalence_of_precats pshf_to_slice :=
    @adjointificiation (pshf ∫P) (pshf C / P ,, has_homsets_slice_precat (pr2 (pshf C)) P) pshf_of_elems_slice_of_pshf_equiv.

End elems_slice_equiv.