(** The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Inductives.addresses.
Require Export UniMath.MoreFoundations.All.

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

  Context {A : UU} {B : A -> UU}.

  CoInductive M : Type :=
    supM : total2 (fun a : A => B a -> M) -> M.

  Definition labelM (m : M) : A.
  Proof.
    intros.
    destruct m.
    exact (pr1 t).
  Defined.

  Definition argM (m : M) : B (labelM m) -> M.
  Proof.
    intros m.
    destruct m.
    exact (pr2 t).
  Defined.

  Definition isWf (m : M) : UU :=
    ∏ P : M -> hProp,
      (∏ a : A, ∏ f : B a -> M, (∏ b : B a, P (f b)) -> P (supM (a ,, f)))
        -> P m.

  Definition isprop_isWf (m : M) : isaprop (isWf m).
  Proof.
    intros. apply impred.
    intro. apply impred.
    intro. exact (pr2 (t m)).
  Defined.

  Definition W : UU := total2 isWf.

  Definition sup (a : A) (f : B a -> W) : W.
  Proof.
    intros.
    exists (supM (a ,, pr1 ∘ f)).
    intros P step.
    apply step.
    intro b.
    apply (pr2 (f b)).
    exact step.
  Defined.

  Definition W_is_algebra : algebra_structure (polynomial_functor A B) W :=
    fun t => sup (pr1 t) (pr2 t).

  Definition W_as_algebra : algebra (polynomial_functor A B) :=
    (W ,, W_is_algebra).

  Definition label : W -> A.
  Proof.
    intro w. destruct w as [m p].
    destruct m.
    exact (pr1 t).
  Defined.

  Definition subtr_wf_then_wf (m : M) (stwf : ∏ b : B (labelM m), isWf (argM m b) ) : isWf m.
  Proof.
    intros.
    intros P step.
    destruct m.
    destruct t as [a f].
    simpl in *.
    apply step.
    intro b.
    apply (stwf b).
    exact step.
  Defined.

  Definition P (m : M) : UU := ∏ b : B (labelM m), isWf (argM m b).


  Definition ispropP (m : M) : isaprop (P m).
  Proof.
    intros.
    apply impred.
    intro.
    apply isprop_isWf.
  Qed.

  Definition Pp (m : M) : hProp.
  Proof.
    intros.
    exists (P m).
    apply ispropP.
  Defined.

  Definition wf_then_subtr_wf (m : M) (p : isWf m) : Pp m.
  Proof.
    intros.
    apply p.
    intros. clear p m.
    simpl in *.
    unfold P in *.
    simpl.
    intro b.
    apply subtr_wf_then_wf.
    apply (X b).
  Defined.

  Definition arg (w : W) (b : B (label w)) : W.
  Proof.
    intros w. destruct w as [m p].
    destruct m. destruct t as [a f].
    intro b.
    exists (f b).
    simpl in b.
    exact (wf_then_subtr_wf (supM (a,, f)) p b).
  Defined.

  Variable (C : Type) (sC : algebra_structure (polynomial_functor A B) C).
  Definition step a f := sC (a ,, f).

  Definition LHom (w : W) :=
    ∑ h : Addr w -> C, ∏ addr : Addr w,
      step (label_at w addr)
        (h ∘ (extend_addr (label:=label) (arg:=arg) w addr)) =
      h addr.

  Definition equiv_addr_match (w : W) (P : Addr (arg:=arg) w -> UU) :
               (∏ addr : Addr w, P addr) ≃
               (P (root_addr _)) ×
                 (∏ b : B (label w), ∏ addr , P (subtree_addr w b addr)).
  Proof.
    intros w P.
    use weqgradth.
      - exact (fun f => (f (root_addr _) ,, fun b addr' => f (subtree_addr _ b addr'))).
      - intros [root_case subtree_case] addr. revert w addr P root_case subtree_case.
        use addresses_induction.
          + intros. intros ? ? ?.
            exact root_case.
          + intros. intros ? ? ? .
            apply subtree_case.
      - intro f.
        apply funextsec.
        intro addr. revert w addr P f.
        use addresses_induction.
          + intros. intros ? ?. reflexivity.
          + intros. intros ? ?. reflexivity.
      - intros pair. destruct pair. simpl. reflexivity.
  Defined.

  Definition equiv_arg_recursor (w : W) :
               LHom w ≃ ∏ b : B (label w), LHom (arg w b).
  Proof.
    intros.
    (* *)
    intermediate_weq
      (∑ h,
        (step (label_at w (root_addr _)) (h ∘ extend_addr w (root_addr _)) = h (root_addr _)) ×
        (∏ b : B (label w), ∏ addr : Addr (arg w b),
          step (label_at w (subtree_addr w b addr))
               (h ∘ extend_addr w (subtree_addr w b addr)) =
          h (subtree_addr w b addr))).
      { use weqfibtototal.
        intro h.
        apply (equiv_addr_match w (fun addr => step (label_at w addr) (h ∘ extend_addr w addr) = h addr)). }
      (* *)
      - intermediate_weq
       (∑ ch : C × (∏ b : B (label w), Addr (label:=label) (arg:=arg) (arg w b) -> C),
         (step (label w) (fun b => (pr2 ch) b (root_addr _)) = pr1 ch) ×
         (∏ b : B (label w), ∏ addr : Addr (arg w b),
           step (label_at (arg w b) addr) (fun b' => (pr2 ch) b (extend_addr _ addr b')) = (pr2 ch) b addr)).
        + use weqbandf.
          use equiv_addr_match.
          intro h.
          apply weqdirprodf.
            * simpl. apply idweq.
            * simpl. apply idweq.
        (* *)
        + intermediate_weq
            (∑ h : (∏ b : B (label w), Addr (label:=label) (arg:=arg) (arg w b) -> C),
              (∏ b : B (label w), ∏ addr : Addr (arg w b),
                step (label_at (arg w b) addr)
                     (fun b' => h b (extend_addr _ addr b')) = h b addr)).
          use weqgradth.
            * exact (fun chP => (pr2 (pr1 chP) ,, pr2 (pr2 chP))).
            * intros. destruct X as [h P2].
              exists (step (label w) (fun b => h b (root_addr _)) ,, h).
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
              use weqgradth.
                -- intros h b.
                   exists ((pr1 h) b).
                   exact ((pr2 h) b).
                -- intro h.
                   exists (fun b => pr1 (h b)).
                   exact (fun b => pr2 (h b)).
                -- intros. reflexivity.
                -- intros. reflexivity.
  Defined.

  Definition iscontr_LHom (w : W) : iscontr (LHom w).
  Proof.
    intros.
    destruct w as [m wf].
    destruct m. destruct t as [a f].
    transparent assert (iscontrforanywf : (M -> hProp)).
      { intros m0. exists (∏ wf, iscontr (LHom (m0 ,, wf))).
        apply impred. intro t. apply isapropiscontr. }
    apply (wf iscontrforanywf).
    intros a0 f0 IH.
    intro wf'.
    apply (iscontrweqb (equiv_arg_recursor _)). apply impred_iscontr_computational.
    intros b. apply IH.
  Defined.


  Definition local_recursor (w : W) :=
    iscontrpr1 (iscontr_LHom w).

  Definition WHom' :=
    ∑ f : W -> C,
      ∏ w, f w = step (label w) (f ∘ (arg w)).


  Definition WHom'_to_LHom (h : WHom') (w : W) : LHom w.
  Proof.
    intros.
    destruct h as [h1 h2].
    exists (h1 ∘ (subtree_at w)).
    intros addr.
    refine (_ @ !(h2 ((subtree_at w) addr))).
    apply (maponpaths (fun f => step ((label_at w) addr) (h1 ∘ f))).
    use subtree_at_extend_addr.
  Defined.

  Definition arg_recursor {w : W}
            (h : LHom w) (b : B (label w)) : LHom ((arg w) b) :=
    ((pr1 h) ∘ subtree_addr w b ,, (pr2 h) ∘ subtree_addr w b).


  Definition LHom_to_WHom' (h : forall w, LHom w) :
    WHom'.
  Proof.
    intro h.
    exists (fun w => (pr1 (h w)) (root_addr w)).
    intros w.
    refine (!((pr2 (h w)) (root_addr _)) @ _).
    apply (maponpaths (step (label w))).
    apply funextfun. intros b.
    change ((pr1 (arg_recursor (h w) b)) (root_addr _) =
            (pr1 (h (arg w b))) (root_addr _)).
    apply (maponpaths (fun h' : LHom _ => (pr1 h') (root_addr _))).
    use proofirrelevancecontr.
    apply iscontr_LHom.
  Defined.

  Definition WHom'_to_LHoml_is_sect (h : WHom') :
    LHom_to_WHom' (WHom'_to_LHom h) = h.
  Proof.
    intros h.
    use total2_paths_f.
    - reflexivity.
    - apply funextsec. intros w'.
      rewrite idpath_transportf.
      apply moveR_Mp.
      simpl. rewrite pathsinv0l.
      transitivity (maponpaths (step (label w'))
                       (funextfun _ _
                             (fun b =>
                                maponpaths (fun h' => (pr1 h') (root_addr _))
                                           (idpath (WHom'_to_LHom h (arg w' b)))))).
        * repeat apply maponpaths.
          apply funextsec. intro. repeat apply maponpaths.
          destruct h.
          assert (isset_LHom : isaset (LHom (arg w' x))).
            + apply hlevelntosn. apply hlevelntosn. apply iscontr_LHom.
            + apply isset_LHom.
        * destruct h. simpl.

          set (test := (funextfun
                (λ b : B (label w'),
                  (pr1 ∘ subtree_at (arg w' b))
                    (root_addr (arg w' b)))
                 (λ b : B (label w'),
                  (pr1 ∘ subtree_at (arg w' b))
                    (root_addr (arg w' b)))
                 (λ b : B (label w'),
                  idpath
                    ((pr1 ∘ subtree_at (arg w' b))
                       (root_addr (arg w' b)))))).
          assert (test = idpath _).
            -- apply funextfun_id.
            -- rewrite X. simpl. reflexivity.
  Defined.


  Definition iscontr_WHom' : iscontr WHom'.
  Proof.
    use (@iscontrretract (∏ w, LHom w)).
    exact LHom_to_WHom'.
    exact WHom'_to_LHom.
    exact WHom'_to_LHoml_is_sect.
    use impred_iscontr_computational.
    intro t. apply iscontr_LHom.
  Defined.

  Definition sup_and_arg a f : arg (sup a f) = f.
  Proof.
    intros.
    apply funextsec.
    intro.
    simpl.
    apply subtypeEquality.
      - intro. apply isprop_isWf.
      - simpl. reflexivity.
  Defined.

  Definition m_and_sup m : supM (labelM m ,, argM m) = m.
  Proof.
    intro.
    destruct m.
    simpl. reflexivity.
  Defined.

  Definition FW_equiv_W : (polynomial_functor A B).0 W ≃ W.
  Proof.
    use weqgradth.
      - exact W_is_algebra.
      - exact (fun w => (label w ,, arg w)).
      - intro af. use total2_paths_f.
          + reflexivity.
          + rewrite idpath_transportf. apply sup_and_arg.
      - simpl. intro w. unfold W_is_algebra. simpl.
        apply subtypeEquality. intro. apply isprop_isWf.
        destruct w. simpl. destruct pr1. reflexivity.
  Defined.

  Definition WHom_equiv_to_WHom' : WHom' ≃ algebra_morphism W_as_algebra (C ,, sC).
  Proof.
    unfold WHom'.
    use weqfibtototal.
    simpl. unfold polynomial_functor_on_types.
    intro.
    eapply weqcomp.
    exact (weqonsecbase _ FW_equiv_W).
    apply weqonsecfibers.
    intros af.
    destruct af as [a f].
    simpl.
    unfold polynomial_functor_on_maps.
    unfold step.
    change (
    x (W_is_algebra (a,, f)) = sC (a,, x ∘ arg (sup a f))
  ≃ x (W_is_algebra (a,, f)) = sC (a,, x ∘ f)).
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


End Wtypes.