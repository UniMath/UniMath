Require Import UniMath.Foundations.Basics.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.opp_precat
        UniMath.Ktheory.ElementsOp
        UniMath.CategoryTheory.UnicodeNotations.



(* Proof that pshf (el P) ≃ (pshf C) / P *)
Section elems_slice_equiv.

  Local Open Scope cat.

  Local Definition el {C : Precategory} (P : C^op ==> SET) : Precategory := @cat C P.
  Local Definition pshf (C : Precategory) : Precategory := [C^op, SET].
  Local Definition slice (C : Precategory) (X : C) : Precategory :=
    ((slice_precat C X (pr2 C)) ,, (has_homsets_slice_precat C (pr2 C) X)).

  Variable (C : Precategory).
  Variable (P : pshf C).

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
    intros [[Ffun Fmor] [Fid Fcomp]].
    split.
    + intro a. simpl.
      unfold identity.
      unfold pshf_to_slice_ob_funct_mor. simpl.
      induction P as [[Pfun Pmor] [Pid Pcomp]]; simpl.
      apply funextsec; intro p.
      induction p as [p Fp]; simpl.
      apply (total2_paths2 (apevalat p (Pid a))).
      induction ((Pid a)).
      unfold transportf.
      unfold constr1. simpl.
      unfold idfun.
      admit.
    + intros a b c f g.
      unfold pshf_to_slice_ob_funct_data; simpl.
      unfold pshf_to_slice_ob_funct_mor; simpl.
      (* apply funextsec; intro p.
      induction p as [p Fp]; simpl.
      apply (total2_paths2 (apevalat p ((pr2 (pr2 P)) a b c f g))).
      induction P as [[Pfun Pmor] [Pid Pcomp]]; simpl. *)
      admit.
  Admitted.

  Definition pshf_to_slice_ob_funct (F : pshf (el P)) : pshf C :=
    pshf_to_slice_ob_funct_data F ,, pshf_to_slice_ob_is_funct F.

  Definition pshf_to_slice_ob_nat_fun (F : pshf (el P)) (x : C) : (Σ (Px : pr1 ((pr1 P) x)), pr1 ((pr1 F) (x,, Px))) → pr1 ((pr1 P) x) := pr1.

  Definition pshf_to_slice_ob : pshf (el P) → slice (pshf C) P.
  Proof.
    intro F.
    exists (pshf_to_slice_ob_funct F).
    exists (pshf_to_slice_ob_nat_fun F).
    intros x x' f.
    reflexivity.
  Defined.

  Definition pshf_to_slice_ob_nat {X Y : pshf (el P)} (f : X --> Y) (c : C)
    : (Σ (Px : pr1 ((pr1 P) c)), pr1 ((pr1 X) (c,, Px))) → (Σ (Px : pr1 ((pr1 P) c)), pr1 ((pr1 Y) (c,, Px))) := (* rewrite w/ defn*)
    fun p => pr1 p ,, (pr1 f) (c ,, (pr1 p)) (pr2 p).

  Definition pshf_to_slice_ob_isnat {X Y : pshf (el P)} (f : X --> Y) :
    is_nat_trans (pshf_to_slice_ob_funct_data X) (pshf_to_slice_ob_funct_data Y) (pshf_to_slice_ob_nat f).
    simpl.
    intros X Y f c c' g.
    apply funextsec; intro p.
    apply pair_path_in2.
    exact (apevalat (pr2 p) ((pr2 f) (c ,, pr1 p) (c',, # (pr1 P) g (pr1 p)) (g,, idpath (# (pr1 P) g (pr1 p))))).
  Defined.

  Definition pshf_to_slice_mor {X Y : pshf (el P)} (f : X --> Y) :
    pshf_to_slice_ob X --> pshf_to_slice_ob Y.
    simpl.
    intros X Y f.
    exists (pshf_to_slice_ob_nat f ,, pshf_to_slice_ob_isnat f).
    apply (invmaponpathsincl pr1).
    + apply isofhlevelfpr1.
      intros ?.
      apply (isaprop_is_nat_trans _ _ has_homsets_HSET).
    + reflexivity.
  Defined.

  Definition pshf_to_slice_data : functor_data (pshf (el P)) (slice (pshf C) P) :=
    pshf_to_slice_ob ,, @pshf_to_slice_mor.

  Definition pshf_to_slice_is_funct : is_functor pshf_to_slice_data.
  Proof.
    split; [intros X | intros X Y Z f g];
      apply slice_precat_morphisms_pr1_eq;
      apply (invmaponpathsincl pr1);
      try (apply isofhlevelfpr1;
           intros ?;
                  apply (isaprop_is_nat_trans _ _ has_homsets_HSET));
      simpl.
    + unfold pshf_to_slice_ob_nat , pshf_to_slice_ob_funct_fun.
      apply funextsec; intro c.
      apply funextsec; intro p.
      rewrite tppr.
      reflexivity.
    + unfold pshf_to_slice_ob_nat.
      apply funextsec; intro c.
      apply funextsec; intro p.
      rewrite tppr. reflexivity.
  Defined.

  Definition pshf_to_slice : (pshf (el P)) ==> (slice (pshf C) P) :=
    pshf_to_slice_data ,, pshf_to_slice_is_funct.

  Definition slice_to_pshf_ob_ob (Q : slice (pshf C) P) : (el P)^op → SET :=
    fun p =>
      hfiber ((pr1 (pr2 Q)) (pr1 p)) (pr2 p) ,,
             isaset_hfiber ((pr1 (pr2 Q))  (pr1 p)) (pr2 p) (pr2 (((pr1 (pr1 Q)) (pr1 p)))) (pr2 ((pr1 P) (pr1 p))).

  Definition slice_to_pshf_ob_mor (Q : slice (pshf C) P) {F G : (el P)^op} (f : F --> G) :
    slice_to_pshf_ob_ob Q F --> slice_to_pshf_ob_ob Q G.
    intros [[[Q Qmor] [Qid Qcomp]] [Qnat Qisnat]] [x Px] [y Py] [f feq] s.
    apply (hfibersgftog (Qmor _ _ f) (Qnat y)).
    exists (pr1 s).
    rewrite feq.
    destruct (pr2 s).
    exact (apevalat (pr1 s) (Qisnat _ _ f)).
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
    + exact (apevalat (pr1 p) (Qid x)).
    + exact (apevalat (pr1 p) (Qcomp x y z f g)).
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
    intros [[[X Xmor] [Xid Xcomp]] [Xnat Xisnat]] [[[Y Ymor] [Yid Ycomp]] [Ynat Yisnat]] [[F Fisnat] Feq] [e Pe] [e' Pe'] [f feq].
    simpl in *.
    apply funextsec; intros [p peq].
    apply (invmaponpathsincl pr1).
    + apply isofhlevelfpr1.
      intros ?.
      exact (pr2 (eqset _ _)).
    + simpl.
      destruct peq.
      unfold hfiber.
      unfold hfibersgftog. unfold hfiberpair.
      repeat rewrite transportf_pair.
      simpl.
      repeat rewrite transportf_const.
      unfold idfun.
      exact (apevalat p (Fisnat e e' f)).
  Defined.

  Definition slice_to_pshf_mor {X Y : slice (pshf C) P} (F : X --> Y) :
    slice_to_pshf_ob X --> slice_to_pshf_ob Y :=
    slice_to_pshf_ob_nat F ,, slice_to_pshf_ob_is_nat F.

  Definition slice_to_pshf_data : functor_data (slice (pshf C) P) (pshf (el P)) :=
    slice_to_pshf_ob ,, @slice_to_pshf_mor.

  Definition slice_to_pshf_is_funct : is_functor slice_to_pshf_data.
  Proof.
    split; [ intros X | intros X Y Z F G];
      apply (invmaponpathsincl pr1);
      try (apply isofhlevelfpr1;
           intros ?;
                  apply (isaprop_is_nat_trans _ _ has_homsets_HSET));
      apply funextsec; intros [c Pc];
      apply funextsec; intros [p peq];
      apply (invmaponpathsincl pr1);
      try (apply isofhlevelfpr1;
           intros ?;
                  exact (pr2 (eqset _ _)));
      simpl;
      unfold hfiber;
      unfold hfibersgftog; unfold hfiberpair;
      repeat rewrite transportf_pair;
      simpl;
      repeat rewrite transportf_const;
      reflexivity.
  Defined.

  Definition slice_to_pshf : functor (slice (pshf C) P) (pshf (el P)) :=
    slice_to_pshf_data ,, slice_to_pshf_is_funct.

End elems_slice_equiv.