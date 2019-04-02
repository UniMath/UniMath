Require Export UniMath.Inductives.addresses.
Require Export UniMath.MoreFoundations.All.
Require Export UniMath.Inductives.containers.
Require Import UniMath.Inductives.M_from_nat.
Require Import UniMath.Inductives.auxiliary_lemmas.


Open Scope transport.


(* Lemmas that should be elsewhere *)

Definition impred_iscontr_computational :
  ∏ (T : UU) (P : T → UU), (∏ t : T, iscontr (P t)) ->
    iscontr (∏ t : T, P t).
Proof.
  intros T P sc.
  exists (fun t => iscontrpr1 (sc t)).
  intros sec.
  use funextsec.
  intros t.
  apply proofirrelevancecontr.
  exact (sc t).
Defined.

Lemma funextfun_id (X Y : UU) (f : X -> Y) :
  funextfun _ _ (fun x : X => idpath (f x) ) = idpath _ .
Proof.
  intros.
  apply (invmaponpathsweq ( (weqtoforallpaths _ _ _ ))).
  cbn.
  etrans.
  apply (homotweqinvweq (weqtoforallpaths _ _ _)).
  apply idpath.
Defined.


Definition moveR_Mp {X : UU} {a b c : X} (p : a = b) (q : a = c) (r : b = c) :
  q = p @ r -> !p @ q = r.
Proof.
  intros.
  induction p. induction q. exact X0.
Defined.




Section Wtypes.

  (* Assuming M-types construct W-types *)

  Context {I : UU} {A : Fam I} {B : ∏ i, A i -> Fam I}.

  Definition M := m_type A B.

  Definition isWf {i} (m : M i) : UU :=
    ∏ (P : ∏ i, M i -> hProp),
    (∏ i a f, (∏ j b, P j (f j b)) -> P i (m_sup a f)) ->
    P i m.

  Definition isprop_isWf {i} (m : M i) : isaprop (isWf m).
  Proof.
    apply impred; intros P.
    apply impred; intro step.
    apply propproperty.
  Defined.

  Definition W : Fam I :=
    λ i, ∑ m : M i, isWf m.

  Definition subtr_wf_then_wf {i} (m : M i) :
    (∏ j (b : B i (m_label m) j), isWf (m_arg m b)) ->
    isWf m.
  Proof.
    intros subtrees_wf P step.
    rewrite <- (m_sup_m_out m).
    apply step. intros j b.
    apply subtrees_wf. exact step.
  Defined.

  Definition sup {i} (a : A i) (f : B i a ->__i W) : W i.
  Proof.
    exists (m_sup a (λ j, pr1 ∘ f j)).
    intros P step.
    apply step. intros j b.
    apply (f j b).2. exact step.
  Defined.

  Definition label {i} (w : W i) : A i :=
    m_label w.1.


  Definition P {i} (m : M i) : UU :=
    ∏ j (b : B i (m_label m) j), isWf (m_arg m b).

  Definition ispropP {i} (m : M i) : isaprop (P m).
  Proof.
    apply impred; intro.
    apply impred; intro.
    apply isprop_isWf.
  Qed.

  Definition Pp {i} (m : M i) : hProp.
  Proof.
    exists (P m).
    apply ispropP.
  Defined.

  Definition wf_then_subtr_wf {i} (m : M i) (p : isWf m) : Pp m.
  Proof.
    apply p; clear i m p; intros i a f IH.
    unfold Pp, P in *; cbn in *. intros j b.
    apply subtr_wf_then_wf.
    change ((λ a_f : ∑ a, B i a ->__i M,
                     ∏ j (b : B i a_f.1 j),
                     ∏ j' (b' : B j (m_label (a_f.2 j b)) j'),
                     isWf (m_arg (a_f.2 j b) b'))
              (a,, f)) in IH.
    apply (transportb _ (m_out_m_sup a f) IH).
  Defined.

  Definition arg {i} (w : W i) {j} (b : B i (label w) j) : W j.
  Proof.
    exists (m_arg w.1 b).
    apply wf_then_subtr_wf. exact w.2.
  Defined.

  Variable (C : Fam I) (sC : algebra_structure (⟦ A ◁ B ⟧) C).
  Definition step {i} (a : A i) (f : B i a ->__i C) : C i :=
    sC i (a,, f).

  Lemma index_at_extend_addr {i} {w : W i} (addr : Addr w)
        {j} (b : B (index_at addr) (label_at addr) j) :
    index_at (arg := @arg) (extend_addr _ addr b) = j.
  Proof.
    revert i w addr j b; use addresses_induction; hnf.
    - cbn. reflexivity.
    - intros i w j b addr' IH j' b'.
      change (index_at (subtree_addr w b (extend_addr (arg w b) addr' b')) = j').
      change (index_at (extend_addr (arg w b) addr' b') = j').
      apply IH.
  Defined.

  Definition fun_step {i} {w : W i}
             (h : ∏ addr : Addr w, C (index_at addr))
             (addr : Addr w) :
    C (index_at addr) :=
    step (label_at addr)
         (λ j b, transportf C
                            (index_at_extend_addr addr b)
                            (h (extend_addr w addr b))).

  Definition LHom {i} (w : W i) :=
    ∑ h : ∏ addr : Addr w, C (index_at addr),
          ∏ addr : Addr w, fun_step h addr = h addr.

  Definition equiv_addr_match {i} (w : W i) (P : Addr (arg:=@arg) w -> UU) :
               (∏ addr : Addr w, P addr) ≃
               (P (root_addr _)) ×
                 (∏ j (b : B i (label w) j) addr, P (subtree_addr w b addr)).
  Proof.
    use weq_iso.
      - exact (fun f => (f (root_addr _),,
                        fun j b addr' => f (subtree_addr _ b addr'))).
      - intros [root_case subtree_case] addr.
        revert i w addr P root_case subtree_case. use addresses_induction.
          + intros. intros ? ? ?.
            exact root_case.
          + intros. intros ? ? ? .
            apply subtree_case.
      - intro f.
        apply funextsec.
        intro addr.
        revert i w addr P f; use addresses_induction.
          + intros. intros ? ?. reflexivity.
          + intros. intros ? ?. reflexivity.
      - intros pair. destruct pair. simpl. reflexivity.
  Defined.

  Definition equiv_arg_recursor {i} (w : W i) :
               LHom w ≃ ∏ j (b : B i (label w) j), LHom (arg w b).
  Proof.
    intermediate_weq
      (∑ h,
        (fun_step h (root_addr w) = h (root_addr w)) ×
        (∏ j (b : B i (label w) j) addr,
          fun_step h (subtree_addr w b addr) = h (subtree_addr w b addr))).
      { use weqfibtototal.
        intro h.
        apply (equiv_addr_match w (fun addr => fun_step h addr = h addr)). }
      (* *)
      - intermediate_weq
       (∑ ch : C i × (∏ j (b : B i (label w) j)
                      (addr : Addr (label:=@label) (arg:=@arg) (arg w b)),
                      C (index_at addr)),
         (step (label w) (fun j b => (pr2 ch) j b (root_addr _)) = pr1 ch) ×
         (∏ j (b : B i (label w) j) (addr : Addr (arg w b)),
           step (label_at addr)
                (fun j' b' => index_at_extend_addr addr b' #
                              (pr2 ch) j b (extend_addr _ addr b')) =
           (pr2 ch) j b addr)).
        + use weqbandf.
          * apply equiv_addr_match.
          * intro h. cbn.
            apply weqdirprodf.
            -- exact (idweq _).
            -- exact (idweq _).
        (* *)
        + intermediate_weq
            (∑ h : (∏ j (b : B i (label w) j) (addr : Addr (arg w b)),
                    C (index_at addr)),
              (∏ j (b : B i (label w) j) (addr : Addr (arg w b)),
                step (label_at addr)
                     (fun j' b' => index_at_extend_addr addr b' #
                                   h j b (extend_addr _ addr b')) =
                h j b addr)).
          use weq_iso.
            * exact (fun chP => (pr2 (pr1 chP) ,, pr2 (pr2 chP))).
            * intros. destruct X as [h P2].
              exists (step (label w) (fun j b => h j b (root_addr _)) ,, h).
              simpl.
              exact ((idpath _) ,, P2).
            * intros chP. destruct chP as [ch P]. destruct ch as [c h].
              destruct P as [P1 P2].
              simpl. use total2_paths_f.
                -- simpl. use total2_paths2.
                     ++ exact P1.
                     ++ reflexivity.
                -- rewrite transportf_dirprod.
                   use total2_paths2.
                     ++ simpl in *. induction P1. reflexivity.
                     ++ simpl in *. induction P1. reflexivity.
            * intros. reflexivity.
            (* *)
            * unfold LHom.
              use weq_iso.
                -- intros h j b.
                   exists ((pr1 h) j b).
                   exact ((pr2 h) j b).
                -- intro h.
                   exists (fun j b => pr1 (h j b)).
                   exact (fun j b => pr2 (h j b)).
                -- intros. reflexivity.
                -- intros. reflexivity.
  Defined.

  Definition iscontr_LHom {i} (w : W i) : iscontr (LHom w).
  Proof.
    destruct w as [m wf].
    transparent assert (iscontrforanywf : (∏ j, M j -> hProp)).
      { intros j0 m0. exists (∏ wf, iscontr (LHom (m0,, wf))).
        apply impred. intro t. apply isapropiscontr. }
    apply (wf iscontrforanywf).
    intros i0 a0 f0 IH.
    intro wf'.
    apply (iscontrweqb (equiv_arg_recursor _)).
    apply impred_iscontr_computational; intros j.
    apply impred_iscontr_computational; intros b.
    change ((λ a_f : ⟦ A ◁ B ⟧ M i0,
                     ∏ j (b : B i0 a_f.1 j), iscontrforanywf j (a_f.2 j b))
              (a0,, f0)) in IH.
    apply (transportb _ (m_out_m_sup a0 f0) IH).
  Defined.


  Definition local_recursor {i} (w : W i) :=
    iscontrpr1 (iscontr_LHom w).

  Definition WHom' :=
    ∑ f : W ->__i C,
      ∏ i w, f i w = step (label w) (f ∘__i (@arg i w)).

  Definition uncurry {X : UU} {Y : X -> UU} {Z : ∏ x, Y x -> UU}
             (f : ∏ x y, Z x y) (x_y : ∑ x, Y x) :
    Z x_y.1 x_y.2 :=
    f x_y.1 x_y.2.

  Definition WHom'_to_LHom (h : WHom') i (w : W i) : LHom w.
  Proof.
    induction h as [h1 h2].
    exists (λ addr : Addr w, h1 _ (subtree_at addr)).
    intros addr.
    refine (_ @ !(h2 _ (subtree_at addr))).
    unfold fun_step.
    apply maponpaths. unfold comp__i.
    revert i w addr; use addresses_induction; hnf.
    - reflexivity.
    - intros i w j b addr' IH. exact IH.
  Defined.

  Goal ∏ '(h,, β) i w, pr2 (WHom'_to_LHom (h,, β) i w) (root_addr w) = !β i w.
  Proof. reflexivity. Qed.

  Definition arg_recursor {i} {w : W i}
             (h : LHom w) {j} (b : B i (label w) j) :
    LHom (arg w b) :=
    h.1 ∘ subtree_addr w b,,
    h.2 ∘ subtree_addr w b.


  Definition κ (h : ∏ i (w : W i), LHom w) {i} (w : W i) :
    (∏ j b, arg_recursor (h i w) b = h j (arg w b)) ->
    step (label w) (λ j b, (pr1 (arg_recursor (h i w) b)) (root_addr _)) =
    step (label w) (λ j b, (pr1 (h j (arg w b))) (root_addr _)).
  Proof.
    intros p.
    apply maponpaths.
    apply funextsec; intros j. apply funextsec; intros b.
    apply (maponpaths (λ h : LHom (arg w b), h.1 (root_addr (arg w b)))).
    apply p.
  Defined.

  Definition LHom_to_WHom' (h : ∏ i (w : W i), LHom w) :
    WHom'.
  Proof.
    exists (fun i w => pr1 (h i w) (root_addr w)).
    intros i w.
    refine (!((pr2 (h i w)) (root_addr _)) @ _).
    apply κ; intros j b.
    use proofirrelevancecontr.
    apply iscontr_LHom.
  Defined.

  Lemma funextsec_idpath {X} {Y : X -> UU} (f : ∏ x, Y x) :
    funextsec Y f f (λ x, idpath (f x)) = idpath f.
  Proof.
    change (invmap (weqtoforallpaths Y f f)
                   (weqtoforallpaths Y f f (idpath f)) =
            idpath f).
    apply homotinvweqweq.
  Qed.

  Definition WHom'_to_LHoml_is_sect (h : WHom') :
    LHom_to_WHom' (WHom'_to_LHom h) = h.
  Proof.
    use total2_paths_f.
    - reflexivity.
    - apply funextsec; intros i. apply funextsec; intros w.
      rewrite idpath_transportf.
      apply moveR_Mp.
      transitivity (κ (WHom'_to_LHom h) w (λ j b, idpath _)). {
        apply maponpaths. apply funextsec; intros j. apply funextsec; intros b.
        assert (isset_LHom : isaset (LHom (arg w b))).
            + apply hlevelntosn. apply hlevelntosn. apply iscontr_LHom.
            + apply isset_LHom.
      }
      transitivity (idpath (step (label w) (λ j b, h.1 j (arg w b)))). {
        unfold κ.
        change (idpath (step (label w) _)) with
            (maponpaths (step (label w)) (idpath (λ j b, h.1 j (arg w b)))).
        apply maponpaths.
        rewrite <- funextsec_idpath. apply maponpaths. apply funextsec; intros j.
        rewrite <- funextsec_idpath. apply maponpaths. apply funextsec; intros b.
        reflexivity.
      }
      symmetry. apply pathsinv0l.
  Defined.


  Definition iscontr_WHom' : iscontr WHom'.
  Proof.
    use (iscontrretract LHom_to_WHom' WHom'_to_LHom).
    exact WHom'_to_LHoml_is_sect.
    use impred_iscontr_computational. intro i.
    use impred_iscontr_computational. intro w.
    apply iscontr_LHom.
  Defined.

  (* comment since it does not yet compile
  Definition label_and_arg_on_sup {i} (a : A i) (f : B i a ->__i W) :
    tpair (λ a, B i a ->__i W)
          (label (sup a f))
          (@arg i (sup a f)) =
    tpair (λ a, B i a ->__i W) a f.
  Proof.
    change (let '(m,, wf) := sup a f in
            let '(a',, f') := m_out A B i m in
            tpair (λ a, B i a ->__i W)
                  a
                  (λ j b, m_arg m b,, wf_then_subtr_wf m wf j b) =
            tpair (λ a, B i a ->__i W)
                  a
                  f).
  Qed.

  Definition arg_sup {i} (a : A i) (f : B i a ->__i W) :
    @arg i (sup a f) = f.
  Proof.
    intros.
    apply funextsec.
    intro.
    simpl.
    apply subtypeEquality.
      - intro. apply isprop_isWf.
      - simpl. reflexivity.
  Defined.

  Definition m_and_sup i m : m_sup (m_label m) (@m_arg I A B i m) = m.
  Proof.
    destruct m.
    simpl. reflexivity.
  Defined.

  Definition W_is_algebra : algebra_structure ⟦ A ◁ B ⟧ W :=
    fun i a_f => sup a_f.1 a_f.2.

  Definition W_as_algebra : algebra ⟦ A ◁ B ⟧ :=
    (W ,, W_is_algebra).


  Definition FW_equiv_W : ⟦ A ◁ B ⟧ W ≃__i W.
  Proof.
    intros i.
    use weq_iso.
    - exact (W_is_algebra i).
    - exact (fun w => (label w,, @arg i w)).
    - intro af. use total2_paths_f.
      + unfold W_is_algebra. cbn.
  Admitted.
  (*       reflexivity. *)
  (*         + rewrite idpath_transportf. apply sup_and_arg. *)
  (*     - simpl. intro w. unfold W_is_algebra. simpl. *)
  (*       apply subtypeEquality. intro. apply isprop_isWf. *)
  (*       destruct w. simpl. destruct pr1. reflexivity. *)
  (* Defined. *)


  Definition WHom_equiv_to_WHom' :
    WHom' ≃ algebra_morphism W_as_algebra (C ,, sC).
  Proof.
    unfold WHom', algebra_morphism, algebra_str_morphism. cbn.
    use weqfibtototal; intros h. cbn.
    change ((∏ i w, h i w = step (label w) (h ∘__i @arg i w)) ≃
           (∏ i a_f, h i (sup a_f.1 a_f.2) = sC i (⟦ A ◁ B ⟧.map h i a_f))).
    apply weq_functor_sec_id; intros i.
    apply (weqcomp (weqonsecbase _ (FW_equiv_W i))).
    apply weqonsecfibers; intros af; induction af as [a f]. simpl.
    unfold step.
    change (
        h i (W_is_algebra i (a,, f)) =
        sC i (tpair (λ a, B i a ->__i C)
                    (label (sup a f))
                    (h ∘__i @arg i (sup a f)))
           ≃
        h i (W_is_algebra i (a,, f)) =
        sC i (a,, h ∘__i f)).
    rewrite sup_and_arg.
    apply idweq.
  Defined.

  Definition iscontr_WHom : iscontr (algebra_morphism W_as_algebra (C ,, sC)).
  Proof.
    apply (iscontrweqf WHom_equiv_to_WHom').
    exact iscontr_WHom'.
  Defined.

End Wtypes.


Definition W_is_initial_algebra (A : UU) (B : A -> UU) :
             is_initial (@W_as_algebra A B).
Proof.
  intros.
  intro C.
  exact (iscontr_WHom (pr1 C) (pr2 C)).
Defined.



(* Testig computability *)

  (*
Definition B : bool -> UU.
Proof.
  intro tf.
  induction tf.
  exact unit.
  exact empty.
Defined.

Definition nat' := @W bool B.
Definition zero' : nat' := sup false fromempty.

Definition computes_zero : ((pr1 (iscontrpr1 (iscontr_WHom' nat' (@W_is_algebra bool B)))) zero') = zero'.
Proof.
  unfold iscontr_WHom'.
  unfold iscontrretract.
  unfold iscontrpr1.
  unfold pr1.
  unfold impred_iscontr_computational.
  unfold LHom_to_WHom'.
  unfold iscontrpr1.
  unfold pr1.
  unfold zero'.
  unfold sup.
  unfold iscontr_LHom.
  unfold iscontrweqb.
  unfold iscontrretract.
  unfold impred_iscontr_computational.
  unfold iscontrpr1.
  unfold invmap.
  unfold hfiberpr1.
  unfold weqccontrhfiber.
  unfold weqproperty.
  unfold pr1.
  unfold pr2.
  unfold iscontrpr1.
  unfold equiv_arg_recursor.
  Print iscontrweqb.

Definition nat_is_algebra :
             algebra_structure (polynomial_functor bool B) nat.
Proof.
  intro.

  Variable (a : A) (f : B a -> W).

  Definition XX : ((pr1 (iscontrpr1 (iscontr_WHom'))) (sup a f)) = ((pr1 (iscontrpr1 (iscontr_WHom'))) (sup a f)).
  Proof.
    cbn.
    destruct w as [m iswf].
    destruct m.
    destruct t as [a f].
    unfold impred_iscontr_computational. unfold iscontrpr1. simpl. unfold funcontr.
    unfold iscontr_LHom. simpl.
*)

   *)
End Wtypes.
