(** **********************************************************
Matthew Weaver, 2017
************************************************************)


(** **********************************************************
Contents : Equivalence of the categories PreShv ∫P and
           PreShv C / P for any P in PreShv C
************************************************************)

Require Import UniMath.MoreFoundations.Tactics
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.Categories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.equivalences
        UniMath.CategoryTheory.categories.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.opp_precat
        UniMath.CategoryTheory.Presheaf
        UniMath.CategoryTheory.ElementsOp.

(** * Proof that PreShv ∫P ≃ PreShv C / P *)
Section elems_slice_equiv.

  Local Open Scope cat.

  Local Notation "C / X" := (slice_precat C X (pr2 C)).
  Local Definition ap_PreShv {X : precategory} := fun (P : PreShv X) (x : X) => pr1hSet ((pr1 P) x).
  Local Notation "##" := ap_PreShv.

  Variable (C : precategory) (P : PreShv C).

  (** ** Construction of the functor from PreShv ∫P to PreShv C / P *)
  Local Definition mk_ob := @make_ob C P.
  Local Definition mk_mor := @make_mor C P.

  Definition PreShv_to_slice_ob_funct_fun (F : PreShv ∫P) : C^op → SET :=
    λ X, total2_hSet (fun p : ##P X => (pr1 F) (mk_ob X p)).

  Definition PreShv_to_slice_ob_funct_mor (F : PreShv ∫P) {X Y : C^op} (f : X --> Y) :
    PreShv_to_slice_ob_funct_fun F X --> PreShv_to_slice_ob_funct_fun F Y :=
    λ p, # (pr1 P) f (pr1 p) ,, # (pr1 F) (mor_to_el_mor (C:=C) f (pr1 p)) (pr2 p).


  Definition PreShv_to_slice_ob_funct_data (F : PreShv ∫P) : functor_data C^op SET :=
    PreShv_to_slice_ob_funct_fun F ,, @PreShv_to_slice_ob_funct_mor F.

  (* Proof from Anders:
     see [ctx_ext] in https://github.com/mortberg/TypeTheory/blob/cube0/TypeTheory/Cubical/cubical.v *)
  Definition PreShv_to_slice_ob_is_funct (F : PreShv ∫P) : is_functor (PreShv_to_slice_ob_funct_data F).
  Proof.
    split.
    + intros I; apply funextfun; intros [ρ u].
      use total2_paths_f.
      * exact (eqtohomot (functor_id P I) ρ).
      * etrans; [use transportf_make_ob|].
        etrans; [apply transportf_PreShv|]; cbn.
        now rewrite (mor_to_el_mor_id ρ), transportfbinv, (functor_id F).
    + intros I J K f g; apply funextfun; intros [ρ u].
      use total2_paths_f.
      * exact (eqtohomot (functor_comp P f g) ρ).
      * etrans; [use transportf_make_ob|].
        etrans; [apply transportf_PreShv|].
        rewrite (mor_to_el_mor_comp _ f g), transportfbinv.
        generalize u; simpl in *.
        apply eqtohomot, (functor_comp F (mor_to_el_mor f ρ) (mor_to_el_mor g (# (pr1 P) f ρ))).
  Qed.

  (* Version of proof worked out by Vladimir and me *)
  Definition PreShv_to_slice_ob_is_funct' (F : PreShv ∫P) : is_functor (PreShv_to_slice_ob_funct_data F).
  Proof.
    split;
      [intros X | intros X Y Z f g];
      apply funextsec; intros [p q].

    + set (T := ∑ p' : ## P X, p' = # (pr1 P) (identity X) p : UU).
      set (T' := ∑ p' : ## P X, (pr1 F) (X ,, p) --> (pr1 F) (X ,, p') : UU).
      set (phi := λ (x : T), mk_mor (X ,, pr1 x) (X ,, p) (identity X) (pr2 x)).
      set (G := λ (x : T), pr1 x ,, # (pr1 F) (phi x) : T').
      set (e := fun (x : ∫P) => eqtohomot (!((functor_id P) (pr1 x))) (pr2 x)).
      set (h := λ (x : T'), pr1 x ,, (pr2 x) q : pr1hSet (PreShv_to_slice_ob_funct_fun F X)).

      refine (maponpaths (funcomp G h)
                         (connectedcoconustot ((# (pr1 P) (identity X) p) ,, idpath _) (p ,, e (X ,, p))) @ _).
      refine (@pair_path_in2 _ (λ x, pr1hSet ((pr1 F) (X ,, x))) p _ _ _).
      refine (eqtohomot _ q @ eqtohomot (functor_id F (X ,, p)) q).
      refine (maponpaths (# (pr1 F)) _).
      use total2_paths_f.
      * reflexivity.
      * rewrite idpath_transportf;
        now apply eqset.

    + set (T := ∑ p' : ## P Z, p' = # (pr1 P) (g ∘ f) p : UU).
      set (T' := ∑ p' : ## P Z, (pr1 F) (X ,, p) --> (pr1 F) (Z ,, p') : UU).
      set (phi := λ (x : T), mk_mor (Z ,, pr1 x) (X ,, p) (g ∘ f) (pr2 x)).
      set (G := λ (x : T), (pr1 x ,, # (pr1 F) (phi x)) : T').
      set (e := fun (z y x : ∫P) (f : z --> y) (g : y --> x) =>
                  ((pr2 f) @ maponpaths (# (pr1 P) (pr1 f)) (pr2 g)
                    @ (eqtohomot (!(functor_comp P) (pr1 g) (pr1 f)) (pr2 x)))).
      set (h := λ (x : T'), pr1 x ,, (pr2 x) q : pr1hSet (PreShv_to_slice_ob_funct_fun F Z)).

      refine (maponpaths (funcomp G h)
                         (connectedcoconustot (# (pr1 P) (g ∘ f) p ,, idpath _)
                                              (# (pr1 P) g (# (pr1 P) f p) ,,
                                                 e (mk_ob Z (# (pr1 P) g (# (pr1 P) f p)))
                                                 (mk_ob Y (# (pr1 P) f p)) (mk_ob X p)
                                                 (g ,, idpath _) (f ,, idpath _))) @ _).
      refine (@pair_path_in2 _ (λ x, pr1hSet ((pr1 F) (Z ,, x))) (# (pr1 P) g (# (pr1 P) f p)) _ _ _).
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

  Definition PreShv_to_slice_ob_funct (F : PreShv ∫P) : PreShv C :=
    PreShv_to_slice_ob_funct_data F ,, PreShv_to_slice_ob_is_funct F.

  Definition PreShv_to_slice_ob_nat_fun (F : PreShv ∫P) (x : C) : (∑ (Px :##P x), ##F (x,, Px)) → ##P x := pr1.

  Definition PreShv_to_slice_ob : PreShv ∫P → PreShv C / P.
  Proof.
    intro F.
    exists (PreShv_to_slice_ob_funct F).
    now exists (PreShv_to_slice_ob_nat_fun F).
  Defined.

  Definition PreShv_to_slice_ob_nat {X Y : PreShv ∫P} (f : X --> Y) (c : C)
    : (∑ Px : ## P c, ## X (c,, Px)) → (∑ Px : ## P c, ## Y (c,, Px)) :=
    λ p, pr1 p ,, (pr1 f) (c ,, (pr1 p)) (pr2 p).

  Definition PreShv_to_slice_ob_isnat {X Y : PreShv ∫P} (f : X --> Y) :
    is_nat_trans (PreShv_to_slice_ob_funct_data X) (PreShv_to_slice_ob_funct_data Y) (PreShv_to_slice_ob_nat f).
    simpl.
    intros c c' g.
    apply funextsec; intro p.
    apply pair_path_in2.
    exact (eqtohomot ((pr2 f) (c ,, pr1 p) (c',, # (pr1 P) g (pr1 p)) (g,, idpath (# (pr1 P) g (pr1 p)))) (pr2 p)).
  Qed.

  Definition PreShv_to_slice_mor {X Y : PreShv ∫P} (f : X --> Y) :
    PreShv_to_slice_ob X --> PreShv_to_slice_ob Y.
    exists (PreShv_to_slice_ob_nat f ,, PreShv_to_slice_ob_isnat f).
    now apply (nat_trans_eq has_homsets_HSET).
  Defined.

  Definition PreShv_to_slice_data : functor_data (PreShv ∫P) (PreShv C / P) :=
    PreShv_to_slice_ob ,, @PreShv_to_slice_mor.

  Definition PreShv_to_slice_is_funct : is_functor PreShv_to_slice_data.
  Proof.
    split; [intros X | intros X Y Z f g];
      apply eq_mor_slicecat;
      apply (nat_trans_eq has_homsets_HSET);
      unfold PreShv_to_slice_ob_nat , PreShv_to_slice_ob_funct_fun;
      intro c;
      apply funextsec; intro p;
      reflexivity.
  Defined.

  Definition PreShv_to_slice : functor (PreShv ∫P) (PreShv C / P) :=
    PreShv_to_slice_data ,, PreShv_to_slice_is_funct.

  (** ** Construction of the functor from PreShv C / P to PreShv ∫P *)
  Definition slice_to_PreShv_ob_ob (Q : PreShv C / P) : (∫P)^op → SET :=
    λ p,
      hfiber ((pr1 (pr2 Q)) (pr1 p)) (pr2 p) ,,
             isaset_hfiber ((pr1 (pr2 Q)) (pr1 p)) (pr2 p) (pr2 (((pr1 (pr1 Q)) (pr1 p)))) (pr2 ((pr1 P) (pr1 p))).

  Definition slice_to_PreShv_ob_mor (Q : PreShv C / P) {F G : (∫P)^op} (f : F --> G) :
    slice_to_PreShv_ob_ob Q F --> slice_to_PreShv_ob_ob Q G.
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

  Definition slice_to_PreShv_ob_funct_data (Q : PreShv C / P) : functor_data ((∫P)^op) SET :=
    slice_to_PreShv_ob_ob Q ,, @slice_to_PreShv_ob_mor Q.

  Definition slice_to_PreShv_ob_is_funct (Q : PreShv C / P) : is_functor (slice_to_PreShv_ob_funct_data Q).
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

  Definition slice_to_PreShv_ob : PreShv C / P → PreShv ∫P :=
    λ Q,  slice_to_PreShv_ob_funct_data Q ,,  slice_to_PreShv_ob_is_funct Q.

  Definition slice_to_PreShv_ob_nat {X Y : PreShv C / P} (F : X --> Y) (e : ∫P^op) :
    (slice_to_PreShv_ob_ob X) e --> (slice_to_PreShv_ob_ob Y) e.
  Proof.
    induction e as [e Pe].
    exact (λ p, hfibersgftog ((pr1 (pr1 F)) e)
                                 ((pr1 (pr2 Y)) e) Pe
                                 (transportf (λ x, hfiber (x e) Pe) (base_paths _ _ (pr2 F)) p)).
  Defined.

  Definition slice_to_PreShv_ob_is_nat {X Y : PreShv C / P} (F : X --> Y) :
    is_nat_trans (slice_to_PreShv_ob X : functor _ _) (slice_to_PreShv_ob Y : functor _ _) (slice_to_PreShv_ob_nat F).
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

  Definition slice_to_PreShv_mor {X Y : PreShv C / P} (F : X --> Y) :
    slice_to_PreShv_ob X --> slice_to_PreShv_ob Y :=
    slice_to_PreShv_ob_nat F ,, slice_to_PreShv_ob_is_nat F.

  Definition slice_to_PreShv_data : functor_data (PreShv C / P) (PreShv ∫P) :=
    slice_to_PreShv_ob ,, @slice_to_PreShv_mor.

  Definition slice_to_PreShv_is_funct : is_functor slice_to_PreShv_data.
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

  Definition slice_to_PreShv : functor (PreShv C / P) (PreShv ∫P) :=
    slice_to_PreShv_data ,, slice_to_PreShv_is_funct.

  (** ** Construction of the natural isomorphism from (slice_to_PreShv ∙ PreShv_to_slice) to the identity functor *)
  Definition slice_counit_fun (X : PreShv C / P) :
    (slice_to_PreShv ∙ PreShv_to_slice) X --> (functor_identity _) X.
  Proof.
    destruct X as [[[X Xmor] Xisfunct] [Xnat Xisnat]].
    simpl in *.
    repeat (use tpair; simpl).
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

  Definition slice_counit : slice_to_PreShv ∙ PreShv_to_slice ⟹ functor_identity (PreShv C / P) :=
    slice_counit_fun ,, is_nat_trans_slice_counit.

  Definition slice_all_iso : forall F : PreShv C / P, is_iso (slice_counit F).
  Proof.
    intros [[[F Fmor] Fisfunct] [Fnat Fisnat]].
    apply iso_to_slice_precat_iso.
    apply functor_iso_if_pointwise_iso.
    intros X; simpl.
    match goal with
    | |- is_iso ?t => assert (eq : t =
                                   (λ X0, pr1 (pr2 X0)))
    end.
    { apply funextsec. intros [p q]. simpl. reflexivity. }
    rewrite eq.
    change (λ X0, pr1 (pr2 X0)) with (fromcoconusf (Fnat X)).
    exact (hset_equiv_is_iso (hSetpair (coconusf (Fnat X))
                                         (isaset_total2_hSet _ (λ y, (hfiber_hSet (Fnat X) y)))) _
                               (weqfromcoconusf (Fnat X))).
  Qed.

  Definition slice_unit : functor_identity (PreShv C / P) ⟹ slice_to_PreShv ∙ PreShv_to_slice :=
    nat_trans_inv_from_pointwise_inv _ _
                                     (has_homsets_slice_precat (pr2 (PreShv C)) P)
                                     (slice_to_PreShv ∙ PreShv_to_slice) (functor_identity (PreShv C / P))
                                     slice_counit slice_all_iso.

  (** ** Construction of the natural isomorphism from the identity functor to (PreShv_to_slice ∙ slice_to_PreShv) *)
  Definition PreShv_unit_fun (F : PreShv ∫P) :
    (functor_identity _) F --> (PreShv_to_slice ∙ slice_to_PreShv) F.
  Proof.
    use tpair.
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

  Definition is_nat_trans_PreShv_unit : is_nat_trans _ _ PreShv_unit_fun.
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

  Definition PreShv_unit : functor_identity (PreShv ∫P) ⟹ PreShv_to_slice ∙ slice_to_PreShv :=
    PreShv_unit_fun ,, is_nat_trans_PreShv_unit.

  Definition PreShv_all_iso : forall F : PreShv ∫P, is_iso (PreShv_unit F).
  Proof.
    intros [[F Fmor] Fisfunct].
    apply functor_iso_if_pointwise_iso.
    intros [X p]; simpl.
    assert (H : isweq (λ x : pr1hSet (F (X,, p)) , (p,, x) ,, idpath p : pr1hSet (slice_to_PreShv_ob_ob (PreShv_to_slice_ob ((F,, Fmor),, Fisfunct)) (X,, p)))).
    { unfold isweq. intros [[p' x'] e'].
      simpl in *. induction e'.
      refine ((x',, idpath _),, _).
      intros [x'' t].
      apply (invmaponpathsincl pr1).
      apply isofhlevelfpr1;
        intros ?;
               exact (pr2 (@eqset
                             ((slice_to_PreShv_ob_ob (PreShv_to_slice_ob ((F,, Fmor),, Fisfunct)) (X,, p'))) _ _)).
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

  Definition PreShv_counit : PreShv_to_slice ∙ slice_to_PreShv ⟹ functor_identity (PreShv ∫P) :=
    nat_trans_inv_from_pointwise_inv _ _ (pr2 (PreShv ∫P)) _ _ PreShv_unit PreShv_all_iso.

  (** ** The equivalence of the categories PreShv ∫P and PreShv C / P *)
  Definition PreShv_of_elems_slice_of_PreShv_equiv : equivalence_of_precats (PreShv ∫P) (PreShv C / P) :=
    (PreShv_to_slice ,,  slice_to_PreShv ,, PreShv_unit ,, slice_counit) ,, (PreShv_all_iso ,, slice_all_iso).

  Definition PreShv_of_elems_slice_of_PreShv_adj_equiv : adj_equivalence_of_precats PreShv_to_slice :=
    @adjointificiation (PreShv ∫P) (PreShv C / P ,, has_homsets_slice_precat (pr2 (PreShv C)) P) PreShv_of_elems_slice_of_PreShv_equiv.

End elems_slice_equiv.