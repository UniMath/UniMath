
Require Export UniMath.Inductives.M_from_nat.
Require Import UniMath.Inductives.auxiliary_lemmas.
Open Scope type_scope.
Open Scope transport.


Check m_out.
Arguments m_out {_ _ _ _} _.
Arguments m_arg {_ _ _ _} _ {_} _.

Lemma transport_fun_to_const {A B C} {a1 a2}
      (p : a1 = a2) (f : B a1 -> C) (b : B a2) :
  transportf (λ a : A, B a -> C) p f b =
  f (transportb B p b).
Proof. induction p. reflexivity. Defined.

Lemma pr1_on_paths {A B} {x1 x2 : ∑ a : A, B a} (p : x1 = x2) :
  pr1 x1 = pr1 x2.
Proof. induction p. reflexivity. Defined.

Lemma pr2_on_paths {A B} {x1 x2 : ∑ a : A, B a} (p : x1 = x2) :
  pr1_on_paths p # pr2 x1 = pr2 x2.
Proof. induction p. reflexivity. Defined.




(* Definition m_out' {I A B} {i : I} (m : m_type A B i) : *)
(*   ∑ a, B i a ->ⁱ m_type A B := *)
(*   (m_label m,, @m_arg _ _ _ _ m). *)
(* Lemma isweq_m_out A B : *)
(*   isweq (@m_out' A B). *)
(* Admitted. *)
(* Definition weq_m_out {A B} : *)
(*   M A B ≃ ∑ a, B a -> M A B := *)
(*   weqpair (λ m, m_label m,, m_arg m) (isweq_m_out A B). *)
(* Definition sup {A B} label arg : M A B := *)
(*   invmap weq_m_out (label,, arg). *)

Definition corec {I A B} (C : Fam I)
           (c_label : C ->ⁱ A) (c_arg : ∏ i c, B i (c_label i c) ->ⁱ C) :
  C ->ⁱ m_type A B :=
  @m_corec _ _ _
           (tpair (λ carrier, carrier ->ⁱ ⟦ A ◁ B ⟧ carrier)
                  C
                  (fun i c => (c_label i c,, @c_arg i c))).

Inductive Addr {I A B} {i : I} (m : m_type A B i) : UU :=
| root_addr : Addr m
| subtree_addr : ∏ j (b : B i (m_label m) j),
                 Addr (m_arg m b) -> Addr m.

Fixpoint label_at {A B} {m : M A B}
         (addr : Addr m) {struct addr} :
  A :=
  match addr with
  | root_addr _ => m_label m
  | subtree_addr _ b addr' => label_at addr'
  end.


Variable (A1 A2 : Type) (B : A1 -> Type).


Definition dec_step_label : (∑ m : M A1 B, Addr m -> A2) ->
                            A1 × A2 :=
  λ mf, (m_label (pr1 mf),, (pr2 mf) (root_addr _)).

Definition dec_step_arg : ∏ mf : (∑ m : M A1 B, Addr m -> A2),
                                 B (pr1 (dec_step_label mf)) ->
                                 ∑ m : M A1 B, Addr m -> A2 :=
  λ '(m,, f) b, (m_arg m b,, f ∘ subtree_addr _ b).

Definition dec : (∑ m : M A1 B, Addr m -> A2) ->
                 M (A1 × A2) (B ∘ pr1) :=
  corec _ dec_step_label dec_step_arg.


Definition undec1_step_label : M (A1 × A2) (B ∘ pr1) -> A1 :=
  λ m, pr1 (m_label m).

Definition undec1_step_arg : forall m, B (undec1_step_label m) ->
                                  M (A1 × A2) (B ∘ pr1) :=
  m_arg.

Definition undec1 : M (A1 × A2) (B ∘ pr1) ->
                    M A1 B :=
  corec _ undec1_step_label undec1_step_arg.

Fixpoint undec2 m (addr : Addr (undec1 m)) {struct addr} : A2 :=
  match addr with
  | root_addr _ => pr2 (m_label m)
  | subtree_addr _ b addr' => undec2 (m_arg m b) addr'
  end.

Definition undec : M (A1 × A2) (B ∘ pr1) ->
                   ∑ m : M A1 B, Addr m -> A2 :=
  fun m => undec1 m,, undec2 m.

Definition m_path_label {A B} {m1 m2 : M A B} (p : m1 = m2) :
  m_label m1 = m_label m2.
Proof. induction p; reflexivity. Defined.

Definition m_path_arg {A B} {m1 m2 : M A B} (p : m1 = m2) :
  ∏ b, @m_arg _ _ _ _ tt m1 b = m_arg m2 (m_path_label p # b).
Proof. induction p; reflexivity. Defined.

Definition destruct_total2_path {A B} {x1 x2 : ∑ a : A, B a} (p : x1 = x2) :
  ∑ q : pr1 x1 = pr1 x2,
        q # pr2 x1 = pr2 x2 :=
  pr1_on_paths p,, pr2_on_paths p.

Definition destruct_m_path {A B} {m1 m2 : M A B} (p : m1 = m2) :
  ∑ q : m_label m1 = m_label m2,
        ∏ b, @m_arg _ _ _ _ tt m1 b = m_arg m2 (q # b) :=
  (m_path_label p,, m_path_arg p).


Section Eta.

  Context {I A B C}
          (f g : C ->ⁱ m_type A B)
          (c_arg : ∏ i c, B i (m_label (f i c)) ->ⁱ C)
          (p : ∏ (i : I) (c : C i), m_label (f i c) = m_label (g i c))
          (q_f : ∏ i c j b, m_arg (f i c) b = f j (c_arg i c j b))
          (q_g : ∏ (i : I) (c : C i) (j : I) (b : B i (m_label (f i c)) j),
                 m_arg (g i c) (transportf (λ a, B i a j) (p i c) b) =
                 g j (c_arg i c j b)).

  Local Definition F := ⟦ A ◁ B ⟧.

  Local Definition c_coalg : coalgebra F :=
    tpair (coalgebra_structure F)
          C
          (λ i c, tpair (λ a, ∏ j, B i a j -> C j)
                        (m_label (f i c))
                        (c_arg i c)).

  Definition f_hom : coalgebra_morphism c_coalg (m_coalgebra _ _).
  Proof.
    exists f.
    apply funextsec; intros i; apply funextfun; intros c.
    use total2_paths_f.
    - reflexivity.
    - cbn -[m_out]; unfold idfun.
      apply funextsec; intros j; apply funextsec; intros b.
      apply q_f.
  Defined.

  Definition g_hom : coalgebra_morphism c_coalg (m_coalgebra _ _).
  Proof.
    exists g.
    apply funextsec; intros i; apply funextfun; intros c.
    use total2_paths_f.
    - exact (!p i c).
    - apply funextsec; intros j; apply funextsec; intros b.
      cbn -[m_out].
      exact ((toforallpaths _ _ _ (transportf_sec_constant
                                     (λ a j, B i a j -> m_type A B j) _ _ _) b) @
               !transportb_fun' _ _ _ @
               q_g i c j b).
  Defined.


  Lemma eta i c : f i c = g i c.
  Proof.
    change (f_hom.f i c = g_hom.f i c).
    apply (maponpaths (λ h : coalgebra_morphism c_coalg (m_coalgebra A B),
                             h.f i c)).
    apply uniqueness_morphism_coalgebra; apply m_coalgebra_is_final.
  Defined.



  (* Lemma def (f' g' : coalgebra_morphism c_coalg (m_coalgebra A B)) (p' : f' = g') *)
  (*   i c : *)
  (*   maponpaths (λ h : coalgebra_morphism c_coalg (m_coalgebra A B), *)
  (*                     m_out (h.f i c)) p' = *)
  (*   total2_paths_f (pr1_on_paths (toforallpaths _ _ _ *)
  (*                      (toforallpaths _ _ _ (pr2 f') i) c) @ *)
  (*                    !pr1_on_paths (toforallpaths _ _ _ *)
  (*                      (toforallpaths _ _ _ (pr2 g') i) c)) *)
  (*                  (pr2_on_paths (toforallpaths _ _ _ *)
  (*                      (toforallpaths _ _ _ (pr2 f') i) c) @ *)
  (*                    _ @ *)
  (*                    !(transportb_fun' _ _ _ @ *)
  (*                      !(toforallpaths _ _ _ (transportf_sec_constant *)
  (*                                              (λ a j, B i a j -> m_type A B j) _ _ _) b) @ *)
  (*                      pr2_on_paths (toforallpaths _ _ _ *)
  (*                      (toforallpaths _ _ _ (pr2 g') i) c))). *)

  (*   pr2 f' @ maponpaths (λ h, ⟦ A ◁ B ⟧.1 (h.f) ∘ⁱ pr2 c_coalg) p' @ !pr2 g'. *)
  (* Proof. *)
  (*   induction p'; cbn -[m_out]. *)
  (*   symmetry; apply pathsinv0r. *)
  (* Qed. *)

  (* Goal ∏ c, maponpaths (m_out A' B' tt) (eta c) = *)
  (*           maponpaths (m_out A' B' tt) (eta c). *)
  (* Proof. *)
  (*   intros c. *)
  (*   unfold eta. *)
  (*   intermediate_path (toforallpaths _ _ _ (toforallpaths _ _ _ *)
  (*       (maponpaths (λ h : coalgebra_morphism c_coalg (m_coalgebra A' B'), *)
  (*                           m_out A' B' ∘ⁱ h.f) *)
  (*       (uniqueness_morphism_coalgebra _ (m_coalgebra_is_final _ _) _ f_hom g_hom)) tt) c). { *)
  (*     admit. *)
  (*   } *)
  (*   rewrite def. *)
  (* Abort. *)



  (* Lemma destruct_eta c : *)
  (*   destruct_m_path (eta c) = *)
  (*   tpair (λ q, ∏ b, m_arg (f c) b = m_arg (g c) (q # b)) *)
  (*         (p c) *)
  (*         (λ b, q_f c b @ eta (c_arg c b) @ !q_g c b). *)
  (* Proof. *)
  (*   unfold eta. *)
  (*   Check def. *)
  (*   Check (maponpaths (λ h : coalgebra_morphism c_coalg (m_coalgebra A' B'), m_out A' B' ∘ⁱ h .f) *)
  (*        (uniqueness_morphism_coalgebra _ (m_coalgebra_is_final _ _) _ f_hom g_hom)). *)
  (* Admitted. *)

End Eta.

Definition moveL_transportb_p {A : UU} (P : A -> UU) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : p # u = v -> u = p #' v.
Proof. intros H; induction p; exact H. Defined.


Lemma from_transported_addr :
  ∏ C (f g : coalgebra_morphism C (m_coalgebra _ _)) (p : f = g)
     (c : pr1 C tt) (b : B (m_label (f.f tt c))) (addr : Addr (m_arg (f.f tt c) b)),
Addr (g.f tt c).
Proof.
  intros C f g p c b addr.
  transparent assert (uf : (m_label (f.f tt c) = pr1 (pr2 C tt c))). {
    exact (pr1_on_paths (toforallpaths _ _ _ (toforallpaths _ _ _ (pr2 f) tt) c)).
  }
  transparent assert (ug : (m_label (g.f tt c) = pr1 (pr2 C tt c))). {
    exact (pr1_on_paths (toforallpaths _ _ _ (toforallpaths _ _ _ (pr2 g) tt) c)).
  }
  set (b' := uf @ !ug # b).
  use subtree_addr.
  - exact b'.
  - cbn.
    assert (q : @m_arg _ _ _ tt tt (f.f tt c) b = m_arg (g.f tt c) b'). {
      transitivity (f.f tt (pr2 (pr2 C tt c) tt (uf # b))). {
        change (pr2 ((@m_out _ _ _ ∘ⁱ f.f) tt c) tt b =
                pr2 ((F.1 (f.f) ∘ⁱ pr2 C) tt c) tt (uf # b)).
        rewrite transportb_fun'; apply (maponpaths (λ f, f b)).
        set (P a := ∏ u, B a -> pr1 (m_coalgebra (λ _ : unit, A1) (λ _ a _, B a)) u).
        refine (_ @ transportb_sec_constant (λ a i, B a -> pr1 (m_coalgebra _ _) i)
                                       uf
                                       (pr2 ((F.1 (f.f) ∘ⁱ pr2 C) tt c))
                                       tt).
        fold P.
        apply (maponpaths (λ f, f tt)).
        apply (moveL_transportb_p P).
        exact (pr2_on_paths (toforallpaths _ _ _ (toforallpaths _ _ _ (pr2 f) tt) c)).
      }
      transitivity (g.f tt (pr2 (pr2 C tt c) tt (uf # b))). {
        exact (maponpaths (λ h, h.f tt _) p).
      }
      transitivity (transportb (λ a, B a → M A1 B)
                               (uf @ ! ug)
                               (m_arg (g.f tt c)) b). {
        change (pr2 ((F.1 (g.f) ∘ⁱ pr2 C) tt c) tt (uf # b) =
                transportb (λ a, B a -> M A1 B)
                           (uf @ !ug)
                           (pr2 ((@m_out _ _ _ ∘ⁱ g.f) tt c) tt) b).
        rewrite transportb_fun'; apply (maponpaths (λ f, f b)).
        rewrite <- transport_b_b; apply maponpaths.
        unfold transportb; rewrite pathsinv0inv0.
        refine (_ @ transportf_sec_constant (λ a i, B a -> pr1 (m_coalgebra _ _) i)
                  ug
                  _
                  tt).
        apply (maponpaths (λ f, f tt)).
        symmetry.
        exact (pr2_on_paths (toforallpaths _ _ _ (toforallpaths _ _ _ (pr2 g) tt) c)).
      }
      apply pathsinv0; apply transportb_fun'.
    }
    exact (transportf Addr q addr).
Defined.

Lemma transported_addr : ∏ C (f g : coalgebra_morphism C (m_coalgebra _ _)) (p : f = g)
     (c : pr1 C tt) (b : B (m_label (f.f tt c))) (addr : Addr (m_arg (f.f tt c) b)),
Addr (g.f tt c).
Proof.
  intros C f g p c b addr.
  apply (transportf Addr (maponpaths (λ h, h.f tt c) p)).
  use subtree_addr.
  - exact b.
  - exact addr.
Defined.


Lemma op : ∏ C (f g : coalgebra_morphism C (m_coalgebra _ _)) (p : f = g)
     (c : pr1 C tt) (b : B (m_label (f.f tt c))) (addr : Addr (m_arg (f.f tt c) b)),
transported_addr C f g p c b addr = from_transported_addr C f g p c b addr.
Proof.
  intros. induction p.
  cbn. unfold idfun.
Abort.


Definition G : functor unit unit := ⟦ (λ _, A1) ◁ (λ _ a _, B a) ⟧.
Definition C : coalgebra G.
Proof.
  exists (λ _, ∑ m : M A1 B, Addr m -> A2).
  intros i [m g]; cbn.
  exists (m_label m).
  intros j b.
  exists (m_arg m b).
  exact (g ∘ subtree_addr m b).
Defined.

Goal coalgebra_morphism C (m_coalgebra _ _).
Proof.
  exists (λ i, match i return pr1 C i -> m_type _ _ i with tt => pr1 end).
  apply funextsec; intros []. apply funextfun; intros [m g]. cbn -[m_out].
  reflexivity.

Goal ∏ m g, m_out (pr1 (m,, g)) =
            ⟦ (λ _, A1) ◁ (λ _ a _, B a) ⟧.1 (λ _, pr1) tt
            (tpair (λ a, ∏ j, B a -> ∑ m, Addr m -> A2)
                   (m_label m)
                   (λ _, dec_step_arg (m,, g))).

Definition undec1_dec m g : m = undec1 (dec (m,, g)) :=
  eta pr1 (undec1 ∘ dec)
      dec_step_arg
      (λ _, idpath _)
      (λ _ _, idpath _)
      (λ _ _, idpath _)
      (m,, g).

Lemma undec2_dec m g :
  g = transportb (λ m, Addr m -> A2) (undec1_dec m g) (undec2 (dec (m,, g))).
Proof.
  apply funextfun; intros addr.
  rewrite <- transportb_fun'.
  induction addr as [ | m b addr].
  - transitivity (undec2 (dec (m,, g)) (root_addr (undec1 (dec (m,, g))))). {
      reflexivity.
    }
    apply maponpaths.
    generalize (undec1 (dec (m,, g))) (undec1_dec m g); intros m' p.
    induction p; reflexivity.
  - transitivity (
        undec2 (dec (m,, g)) (subtree_addr (undec1 (dec (m,, g)))
          b (undec1_dec (m_arg m b) (g ∘ subtree_addr _ b) # addr))). {
      exact (IHaddr (g ∘ subtree_addr _ b)).
    }
    apply maponpaths.





    unfold undec1_dec.
    unfold eta.
    set (p := uniqueness_morphism_coalgebra
                (m_coalgebra _ _)
                (m_coalgebra_is_final _ _)
                (c_coalg pr1 dec_step_arg)
                (f_hom pr1 dec_step_arg (λ c' b0, idpath (m_arg (pr1 c') b0)))
                (g_hom pr1 (undec1 ∘ dec) dec_step_arg
                       (λ c', idpath (m_label (pr1 c')))
                       (λ c' b0,
                        idpath
                          (m_arg ((undec1 ∘ dec) c')
                                 (transportf B (idpath (m_label (pr1 c'))) b0))))).
    change (subtree_addr (undec1 (dec (m,, g))) b
                (transportf Addr
                   (maponpaths (λ h : coalgebra_morphism (c_coalg pr1 dec_step_arg) _, h.f tt (m_arg m b,, g ∘ subtree_addr m b)) p)
                   addr)
            =
            transportf Addr
                       (maponpaths (λ h : coalgebra_morphism (c_coalg pr1 dec_step_arg) _, h.f tt (m,, g)) p)
                       (subtree_addr m b addr)).
    intermediate_path (from_transported_addr _ _ _ p (m,, g) b addr). {
      unfold from_transported_addr. hnf. cbn -[m_out].
      apply (maponpaths (subtree_addr (undec1 (dec (m,, g))) b)).
    transitivity (transported_addr _ _ _ p (m,, g) b addr). {
      admit.
    }
    reflexivity.





    assert (H : destruct_m_path (undec1_dec m g) =
            tpair (λ p : m_label m = m_label (undec1 (dec (m,, g))),
                         ∏ b, m_arg m b = m_arg (undec1 (dec (m,, g))) (p # b))
                  (idpath (m_label m))
                  (λ b, undec1_dec (m_arg m b) (g ∘ subtree_addr m b))). {
      refine (pathscomp0 (destruct_eta pr1 (undec1 ∘ dec)
                                       dec_step_arg
                                       (λ _, idpath _)
                                       (λ _ _, idpath _)
                                       (λ _ _, idpath _)
                                       (m,, g))
                         _).
      use total2_paths2_f.
      - reflexivity.
      - apply funextsec; intros b'; cbn.
        rewrite pathscomp0rid. reflexivity.
    }
    (* assert (sup : ∏ a, (B a -> M A1 B) -> M A1 B). admit. *)
    (* transitivity (transportf Addr (maponpaths (sup (m_label m)) (funextfun _ _ *)
    (*                 (λ b, undec1_dec (m_arg m b) (g ∘ subtree_addr m b)))) *)
    (*                          (subtree_addr m b addr)). *)

    transitivity (subtree_addr (undec1 (dec (m,, g)))
                               (m_path_label (undec1_dec m g) # b)
                               (transportf Addr
                                           (m_path_arg (undec1_dec m g) b)
                                           addr)). {
      set (ψ := λ '((p,, q) : ∑ p : m_label m = m_label (undec1 (dec (m,, g))),
                                   ∏ b, m_arg m b = m_arg (undec1 (dec (m,, g))) (p # b)),
                  subtree_addr (undec1 (dec (m,, g)))
                               (transportf B p b)
                               (transportf Addr (q b) addr)).
      change (ψ (tpair (λ p : m_label m = m_label (undec1 (dec (m,, g))), ∏ b, m_arg m b = m_arg (undec1 (dec (m,, g))) (p # b))
                       (idpath (m_label m))
                       (λ b, undec1_dec (m_arg m b) (g ∘ subtree_addr m b))) =
             ψ (destruct_m_path (undec1_dec m g))).
      apply maponpaths.
      symmetry. exact H.
      (* set (φ := λ '(b,, addr), subtree_addr (undec1 (dec (m,, g))) b addr). *)
      (* change (φ (tpair (λ b, Addr (m_arg (undec1 (dec (m,, g))) b)) *)
      (*                  (idpath (m_label m) # b) *)
      (*                  (undec1_dec (m_arg m b) (g ∘ subtree_addr m b) # addr)) *)
      (*         = *)
      (*         φ (tpair (λ b, Addr (m_arg (undec1 (dec (m,, g))) b)) *)
      (*                  (m_path_label (undec1_dec m g) # b) *)
      (*                  (m_path_arg (undec1_dec m g) b # addr))); *)
      (*   apply maponpaths; clear φ. *)
      (* use total2_paths2_f. *)
      (* - apply (maponpaths (λ p, p # b)). *)
      (*   admit. *)
      (* - Check (transport_f_f (Addr ∘ m_arg (undec1 (dec (m,, g))))). *)

    }
    generalize (undec1 (dec (m,, g))) (undec1_dec m g); intros m' p.
    induction p. reflexivity.
Defined.


Goal forall m, dec (undec m) = m.
Proof.
  intros m.
  apply m_path_to_path.
  refine (@m_corec _ _ _ (tpair (coalgebra_structure _) (λ '(m1,, m2), dec (undec m2) = m1) _) (dec (undec m),, m) _).
  cbn. reflexivity.
  Unshelve.
  clear m.
  unfold coalgebra_structure. cbn.
  intros [m' m] p. destruct p. cbn.
  use tpair.
  - change ((pr1 (m_label m),, pr2 (m_label m)) = m_label m).
    apply dirprod_paths; reflexivity.
  - cbn.
    intros [m1 m2] [b [p1 p2]].
    rewrite p1. clear p1 m1.
    rewrite p2. clear p2 m2.
    reflexivity.
Qed.

Check @m_arg.

Definition transport_addr {m1 m2 : M A1 B} (p : m_path m1 m2) (addr : Addr m1) :
  Addr m2.
Proof.
  destruct addr as [ | b addr'].
  - exact (root_addr m2).
  - refine (subtree_addr m2 (m_label p # b) _).
    refine (transportf Addr (m_path_to_path (m_arg p _)) addr').
    unfold Bᵖ.
    exists b.
    split; reflexivity.
    Show Proof.
Defined.

Lemma undec1_dec' m f : m_path (undec1 (dec (m,, f))) m.
Proof.
  use (m_corec (tpair (coalgebra_structure _)
                      (λ '(m1,, m2), ∑ f, undec1 (dec (m2,, f)) = m1)
                      _)).
  - clear m f.
    unfold coalgebra_structure; cbn.
    intros [m' m] [f p]. induction p.
    use tpair.
    * reflexivity.
    * cbn. intros [m1 m2] [b [p1 p2]]. unfold idfun in p2.
      change (m1 = undec1 (dec (dec_step_arg (m,, f) b))) in p1.
      unfold dec_step_arg in p1. cbn in p1.
      rewrite p1, p2.
      exists (f ∘ subtree_addr m b).
      reflexivity.
  - cbn.
    exists f.
    reflexivity.
Defined.


Goal forall m f, undec (dec (m,, f)) = (m,, f).
Proof.
  intros m f.
  use total2_paths_f; cbn.
  - exact (m_path_to_path (undec1_dec' m f)).
  - apply funextfun; intros addr.
    rewrite transportf_fun.
    rewrite transportf_const. unfold idfun.
    revert f; induction addr as [ | m b addr']; intros.
    + unfold transportb.
      rewrite transport_section.
      reflexivity.
    + transitivity
        (undec2 (dec (m,, f))
                (subtree_addr
                   (undec1 (dec (m,, f)))
                   b
                   (transportb Addr
                               (m_path_to_path
                                  (undec1_dec' (m_arg m b)
                                               (f ∘ subtree_addr m b)))
                               addr'))). {
        apply maponpaths.
        transparent assert (H : (∑ x, undec1_dec' (m_arg m b) (f ∘ subtree_addr m b) =
                m_arg (undec1_dec' m f)
                      x)). {
          use tpair.
          - unfold Bᵖ; cbn.
            exists b.
            split.
            + change (undec1 (dec (m_arg m b,, f ∘ subtree_addr m b)) =
                      undec1 (dec (m_arg m b,, f ∘ subtree_addr m b))).
              reflexivity.
            + reflexivity.
          - reflexivity.
        }
        rewrite (pr2 H).
(*         transitivity (subtree_addr (undec1 (dec (m,, f))) b *)
(*                      transportb (fun )) *)
(*       } *)
(*       apply IHaddr'. *)
(* Qed. *)
Abort.


Goal forall (A1 A2 : Type) (B : A1 -> Type),
    M (A1 * A2) (B ∘ fst) ≃
      ∑ m : M A1 B, Addr m -> A2.


Goal ∏ I, ∏ c : Container I I,
      ∑ c_μ : Container I I,
              ∏ X : Fam I, ⟦ c_μ ⟧.0 X ≃ⁱ M (c.S) (c.P).
Proof.
  intros I c.
Defined.
