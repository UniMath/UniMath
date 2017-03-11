Require Import UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.opp_precat
        UniMath.CategoryTheory.yoneda
        UniMath.CategoryTheory.ElementsOp.

(* Proof that pshf (el P) ≃ (pshf C) / P *)
Section elems_slice_equiv.

  Local Open Scope cat.

  Local Definition pshf (C : Precategory) : Precategory := [C^op, SET].
  Local Definition el {C : Precategory} (P : pshf C) : Precategory := (cat_of_elems P ,, has_homsets_cat_of_elems P (pr2 C)).
  Local Definition slice (C : Precategory) (X : C) : Precategory :=
    ((slice_precat C X (pr2 C)) ,, (has_homsets_slice_precat (pr2 C) X)).

  Variable (C : Precategory).
  Variable (P : pshf C).

  Local Definition ap_pshf {X : Precategory} := fun (P : pshf X) (x : X) => pr1hSet ((pr1 P) x).
  Local Notation "##" := ap_pshf.

  Definition pshf_to_slice_ob_funct_fun (F : pshf (el P)) : C^op → SET :=
    fun X => total2_hSet (fun (p : pr1 ((pr1 P) X)) => ((pr1 F) (X ,, p))).

  Definition pshf_to_slice_ob_funct_mor (F : pshf (el P)) {X Y : C^op} (f : X --> Y) :
    pshf_to_slice_ob_funct_fun F X --> pshf_to_slice_ob_funct_fun F Y :=
    fun p => # (pr1 P) f (pr1 p) ,,
               pr2 (pr1 F) (X ,, (pr1 p)) (Y,, # (pr1 P) f (pr1 p)) (f ,, idpath (# (pr1 P) f (pr1 p))) (pr2 p).

  Definition pshf_to_slice_ob_funct_data (F : pshf (el P)) : functor_data C^op SET :=
    pshf_to_slice_ob_funct_fun F ,, @pshf_to_slice_ob_funct_mor F.

  Definition pshf_to_slice_ob_is_funct (F : pshf (el P)) : is_functor (pshf_to_slice_ob_funct_data F).
  Proof.
    split;
      [intros X | intros X Y Z f g];  
      apply funextsec; intros [p q].
    
    + set (T := ∑ p' : ## P X, p' = # (pr1 P) (identity X) p : UU).
      set (T' := ∑ p' : ## P X, (pr1 F) (X ,, p) --> (pr1 F) (X ,, p') : UU).
      set (phi := fun (x : T) => identity X ,, (pr2 x) : ((X ,, pr1 x) : el P) --> ((X ,, p) : el P)).
      set (G := fun (x : T) => pr1 x ,, # (pr1 F) (phi x) : T').
      set (e := fun (x : el P) => eqtohomot (!((functor_id P) (pr1 x))) (pr2 x)).
      set (h := fun (x : T') => pr1 x ,, (pr2 x) q : pr1hSet (pshf_to_slice_ob_funct_fun F X)).
      
      refine (maponpaths (funcomp G h)
                         (connectedcoconustot ((# (pr1 P) (identity X) p) ,, idpath _) (p ,, e (X ,, p))) @ _).
      refine (@pair_path_in2 _ (fun x => pr1hSet ((pr1 F) (X ,, x))) p _ _ _).
      exact (eqtohomot (functor_id F (X ,, p)) q).
      
    + set (T := ∑ p' : ## P Z, p' = # (pr1 P) (g ∘ f) p : UU).      
      set (T' := ∑ p' : ## P Z, (pr1 F) (X ,, p) --> (pr1 F) (Z ,, p') : UU).
      set (phi := fun (x : T) => (g ∘ f) ,, (pr2 x) : ((Z ,, pr1 x) : el P) --> ((X ,, p) : el P)).
      set (G := fun (x : T) => (pr1 x ,, # (pr1 F) (phi x)) : T').
      set (e := fun (z y x : el P) (f : z --> y) (g : y --> x) =>
                  ((pr2 f) @ maponpaths (# (pr1 P) (pr1 f)) (pr2 g)
                    @ (eqtohomot (!(functor_comp P) (pr1 g) (pr1 f)) (pr2 x)))).
      set (h := fun (x : T') => pr1 x ,, (pr2 x) q : pr1hSet (pshf_to_slice_ob_funct_fun F Z)).
      
      refine (maponpaths (funcomp G h)
                         (connectedcoconustot (# (pr1 P) (g ∘ f) p ,, idpath _)
                                              (# (pr1 P) g (# (pr1 P) f p) ,,
                                                 e (Z ,, # (pr1 P) g (# (pr1 P) f p) : el P)
                                                 (Y ,, # (pr1 P) f p : el P) (X ,, p : el P)
                                                 (g ,, idpath _) (f ,, idpath _))) @ _).
      
      refine (@pair_path_in2 _ (fun x => pr1hSet ((pr1 F) (Z ,, x))) (# (pr1 P) g (# (pr1 P) f p)) _ _ _).
      exact (eqtohomot (@functor_comp _ _ F (X ,, p : el P)
                                      (Y ,, # (pr1 P) f p : el P)
                                      (Z ,, # (pr1 P) g (# (pr1 P) f p) : el P)
                                      (f ,, idpath _) (g,, idpath _)) q).
  Qed.

  Definition pshf_to_slice_ob_funct (F : pshf (el P)) : pshf C :=
    pshf_to_slice_ob_funct_data F ,, pshf_to_slice_ob_is_funct F.

  Definition pshf_to_slice_ob_nat_fun (F : pshf (el P)) (x : C) : (∑ (Px : pr1 ((pr1 P) x)), pr1 ((pr1 F) (x,, Px))) → pr1 ((pr1 P) x) := pr1.

  Definition pshf_to_slice_ob : pshf (el P) → slice (pshf C) P.
  Proof.
    intro F.
    exists (pshf_to_slice_ob_funct F).
    exists (pshf_to_slice_ob_nat_fun F).
    intros x x' f.
    reflexivity.
  Defined.

  Definition pshf_to_slice_ob_nat {X Y : pshf (el P)} (f : X --> Y) (c : C)
    : (∑ Px : ## P c, ## X (c,, Px)) → (∑ Px : ## P c, ## Y (c,, Px)) :=
    fun p => pr1 p ,, (pr1 f) (c ,, (pr1 p)) (pr2 p).

  Definition pshf_to_slice_ob_isnat {X Y : pshf (el P)} (f : X --> Y) :
    is_nat_trans (pshf_to_slice_ob_funct_data X) (pshf_to_slice_ob_funct_data Y) (pshf_to_slice_ob_nat f).
    simpl.
    intros c c' g.
    apply funextsec; intro p.
    apply pair_path_in2.
    exact (eqtohomot ((pr2 f) (c ,, pr1 p) (c',, # (pr1 P) g (pr1 p)) (g,, idpath (# (pr1 P) g (pr1 p)))) (pr2 p)).
  Qed.

  Definition pshf_to_slice_mor {X Y : pshf (el P)} (f : X --> Y) :
    pshf_to_slice_ob X --> pshf_to_slice_ob Y.
    exists (pshf_to_slice_ob_nat f ,, pshf_to_slice_ob_isnat f).
    apply (nat_trans_eq has_homsets_HSET).
    reflexivity.
  Defined.

  Definition pshf_to_slice_data : functor_data (pshf (el P)) (slice (pshf C) P) :=
    pshf_to_slice_ob ,, @pshf_to_slice_mor.

  Definition pshf_to_slice_is_funct : is_functor pshf_to_slice_data.
  Proof.
    split; [intros X | intros X Y Z f g];
      apply slice_precat_morphisms_pr1_eq;
      apply (nat_trans_eq has_homsets_HSET);
      unfold pshf_to_slice_ob_nat , pshf_to_slice_ob_funct_fun;
      intro c;
      apply funextsec; intro p;
      rewrite tppr;
      reflexivity.
  Defined.

  Definition pshf_to_slice : functor (pshf (el P)) (slice (pshf C) P) :=
    pshf_to_slice_data ,, pshf_to_slice_is_funct.

  Definition slice_to_pshf_ob_ob (Q : slice (pshf C) P) : (el P)^op → SET :=
    fun p =>
      hfiber ((pr1 (pr2 Q)) (pr1 p)) (pr2 p) ,,
             isaset_hfiber ((pr1 (pr2 Q))  (pr1 p)) (pr2 p) (pr2 (((pr1 (pr1 Q)) (pr1 p)))) (pr2 ((pr1 P) (pr1 p))).

  Definition slice_to_pshf_ob_mor (Q : slice (pshf C) P) {F G : (el P)^op} (f : F --> G) :
    slice_to_pshf_ob_ob Q F --> slice_to_pshf_ob_ob Q G.
    intros s.
    destruct Q as [[[Q Qmor] [Qid Qcomp]] [Qnat Qisnat]].
    destruct F as [x Px]. destruct G as [y Py].
    destruct f as [f feq].
    apply (hfibersgftog (Qmor _ _ f) (Qnat y)).
    exists (pr1 s).
    rewrite feq.
    refine (eqtohomot (Qisnat _ _ f) (pr1 s) @ _). 
    exact (maponpaths (# (pr1 P) f) (pr2 s)).
  Defined.

  Definition slice_to_pshf_ob_funct_data (Q : slice (pshf C) P) : functor_data ((el P)^op) SET :=
    slice_to_pshf_ob_ob Q ,, @slice_to_pshf_ob_mor Q.

  Definition slice_to_pshf_ob_is_funct (Q : slice (pshf C) P) : is_functor (slice_to_pshf_ob_funct_data Q).
  Proof.
    split;
      [intros [x Px] | intros [x Px] [y Py] [z Pz] [f feq] [g geq]];
      destruct Q as [[[Q Qmor] [Qid Qcomp]] [Qnat Qisnat]];
      apply funextsec; intro p;
        apply (invmaponpathsincl pr1);
        try (apply isofhlevelfpr1;
             intros ?; exact (pr2 (eqset _ _))).
    + exact (eqtohomot (Qid x) (pr1 p)).
    + exact (eqtohomot (Qcomp x y z f g) (pr1 p)).
  Defined.

  Definition slice_to_pshf_ob : slice (pshf C) P → pshf (el P) :=
    fun Q =>  slice_to_pshf_ob_funct_data Q ,,  slice_to_pshf_ob_is_funct Q.

  Definition slice_to_pshf_ob_nat {X Y : slice (pshf C) P} (F : X --> Y) (e : (el P)^op) :
    (slice_to_pshf_ob_ob X) e --> (slice_to_pshf_ob_ob Y) e :=
    match e with
    | (e ,, Pe) =>
      fun p => hfibersgftog ((pr1 (pr1 F)) e) ((pr1 (pr2 Y)) e) Pe (transportf (fun x => hfiber (x e) Pe) (base_paths _ _ (pr2 F)) p)
    end.

  Definition slice_to_pshf_ob_is_nat {X Y : slice (pshf C) P} (F : X --> Y) :
    is_nat_trans (slice_to_pshf_ob X : functor _ _) (slice_to_pshf_ob Y : functor _ _) (slice_to_pshf_ob_nat F).
  Proof.
    intros [e Pe] [e' Pe'] [f feq].
    destruct X as [[[X Xmor] [Xid Xcomp]] [Xnat Xisnat]].
    destruct Y as [[[Y Ymor] [Yid Ycomp]] [Ynat Yisnat]].
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

  Definition slice_to_pshf_mor {X Y : slice (pshf C) P} (F : X --> Y) :
    slice_to_pshf_ob X --> slice_to_pshf_ob Y :=
    slice_to_pshf_ob_nat F ,, slice_to_pshf_ob_is_nat F.

  Definition slice_to_pshf_data : functor_data (slice (pshf C) P) (pshf (el P)) :=
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
      repeat rewrite transportf_total2;
      simpl;
      repeat rewrite transportf_const;
      reflexivity.
  Qed.

  Definition slice_to_pshf : functor (slice (pshf C) P) (pshf (el P)) :=
    slice_to_pshf_data ,, slice_to_pshf_is_funct.

  Definition slice_counit_fun (X : slice (pshf C) P) :
    (functor_composite_data slice_to_pshf pshf_to_slice) X --> (functor_identity_data _) X.
  Proof.
    destruct X as [[[X Xmor] [Xid Xcomp]] [Xnat Xisnat]].
    simpl in *.
    unfold pshf_to_slice_ob ,  slice_to_pshf_ob.
    unfold slice_to_pshf_ob_funct_data , pshf_to_slice_ob_funct_data.
  Admitted.

End elems_slice_equiv.