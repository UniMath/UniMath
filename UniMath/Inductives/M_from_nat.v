Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Export UniMath.Inductives.algebras.
Require Export UniMath.Inductives.containers.
Require Import UniMath.Inductives.auxiliary_lemmas.


Lemma transportf_fun
      {A : UU} (B C : A -> UU)
      {a1 a2 : A} (p : a1 = a2)
      (f : B a1 -> C a1) (b : B a2) :
  transportf (λ a, B a -> C a) p f b = transportf C p (f (transportb B p b)).
Proof.
  induction p.
  reflexivity.
Defined.


Section M_From_Nat.

  Context {I : UU}.


  Definition Chain :=
    ∑ (X : nat -> Fam I),
    ∏ n, X (1 + n) ->__i X n.
  Opaque Chain.

  Definition build_chain (X : nat -> Fam I) (π : ∏ n, X (1 + n) ->__i X n) : Chain :=
    X,, π.

  Definition chain_types (chain : Chain) : nat -> Fam I :=
    pr1 chain.

  Definition chain_functions (chain : Chain) :
    let X := chain_types chain in
    ∏ n, X (1 + n) ->__i X n :=
    pr2 chain.


  Section Chain_Limit.

    Variable chain : Chain.
    Let X := chain_types chain.
    Let π := chain_functions chain.

    Definition limit :=
      λ i,
      ∑ (x : ∏ n, X n i),
      ∏ n, π n i (x (1 + n)) = x n.

    Definition Cone (A : Fam I) :=
      ∑ (f : ∏ n, A ->__i X n),
      ∏ n, π n ∘__i f (1 + n) = f n.

    Definition to_cone {A : Fam I} (f : A ->__i limit) : Cone A.
    Proof.
      exists (λ n i a, pr1 (f i a) n).
      intros n.
      apply funextsec; intros i.
      apply funextfun; intros a.
      exact (pr2 (f i a) n).
    Defined.

    Definition from_cone {A : Fam I} (cone : Cone A) : A ->__i limit.
    Proof.
      intros i a.
      exists (λ n, pr1 cone n i a).
      intros n.
      revert a; apply toforallpaths.
      revert i; apply toforallpaths.
      exact (pr2 cone n).
    Defined.

    Lemma universal_property_of_limit (A : Fam I) :
      (A ->__i limit) ≃ Cone A.
    Proof.
      use (weq_iso to_cone from_cone).
      - intros f.
        unfold from_cone, to_cone. cbn.
        apply funextsec; intros i.
        apply funextfun; intros a.
        use total2_paths_f.
        + reflexivity.
        + cbn.
          apply funextsec; intros n.
          intermediate_path (toforallpaths
                               _ _ _
                               (funextfun _ _ (λ a, pr2 (f i a) n)) a). {
            use maponpaths.
            clear a; revert i; use toforallpaths.
            apply (homotweqinvweq (weqtoforallpaths _ _ _)).
          }
          apply (toforallpaths
                   _ _ _
                   (homotweqinvweq (weqtoforallpaths _ _ _) (λ a', pr2 (f i a') n))
                   a).
      - intros cone; induction cone as [u p].
        unfold to_cone, from_cone; cbn.
        apply maponpaths.
        apply funextsec; intros n.
        intermediate_path (funextsec _ _ _ (toforallpaths _ _ _ (p n))). {
          use maponpaths.
          apply funextsec; intros i.
          apply (homotinvweqweq (weqtoforallpaths _ _ _)).
        }
        apply (homotinvweqweq (weqtoforallpaths _ _ _)).
    Defined.

  End Chain_Limit.


  Lemma weq_cochain_limit_simpl (X : UU) :
    let limit := ∑ (x : nat -> X),
                 ∏ n, x (1 + n) = x n in
    limit ≃ X.
  Proof.
    set (limit := ∑ (x : nat -> X),
                  ∏ n, x (1 + n) = x n);
      cbn.
    set (f (xp : limit) := pr1 xp 0).
    transparent assert (g : (X -> limit)). {
      intros x. unfold limit.
      exists (λ _, x).
      exact (λ _, idpath _).
    }
    use weq_iso.
    - exact f.
    - exact g.
    - intros xp; induction xp as [x p]; cbn.
      transparent assert ( q : ((λ _, x 0) ~ x )). {
        intros n; induction n; cbn.
        * reflexivity.
        * exact (IHn @ !p n).
      }
      set (q' := funextsec _ _ _ q).
      use total2_paths_f; cbn.
      + exact q'.
      + apply funextsec; intros n.
        rewrite transportf_sec_constant.
        intermediate_path (!maponpaths (λ x, x (S n)) q' @
                            maponpaths (λ x, x n) q'). {
          use transportf_paths_FlFr.
        }
        intermediate_path (! q (S n) @ q n). {
          unfold q'. repeat rewrite (maponpaths_funextsec _ _ _ q). reflexivity.
        }
        intermediate_path (! (q n @ ! p n) @ q n). {
          reflexivity.
        }
        rewrite pathscomp_inv.
        rewrite <- path_assoc.
        rewrite pathsinv0l.
        rewrite pathsinv0inv0.
        rewrite pathscomp0rid.
        reflexivity.
    - cbn.
      reflexivity.
  Defined.

  Lemma weq_cochain_limit (X : nat -> UU) (l : ∏ n, X n -> X (1 + n)) :
    let limit := ∑ (x : ∏ n, X n),
                 ∏ n, x (1 + n) = l n (x n) in
    limit ≃ X 0.
  Proof.
    set (limit := ∑ (x : ∏ n, X n),
                  ∏ n, x (1 + n) = l n (x n));
      cbn.
    set (f (xp : limit) := pr1 xp 0).
    transparent assert (g : (X 0 -> limit)). {
      intros x.
      exists (nat_rect _ x l).
      exact (λ n, idpath _).
    }
    use weq_iso.
    - exact f.
    - exact g.
    - cbn.
      intros xp; induction xp as [x p].
      transparent assert ( q : (nat_rect X (x 0) l ~ x )). {
        intros n; induction n; cbn.
        * reflexivity.
        * exact (maponpaths (l n) IHn @ !p n).
      }
      set (q' := funextsec _ _ _ q).
      use total2_paths_f; cbn.
      + exact q'.
      + apply funextsec; intros n.
        rewrite transportf_sec_constant.
        intermediate_path (!maponpaths (λ x, x (S n)) q' @
                            maponpaths (λ x, l n (x n)) q'). {
          use transportf_paths_FlFr.
        }
        intermediate_path (!maponpaths (λ x, x (S n)) q' @
                            maponpaths (l n) (maponpaths (λ x, x n) q')). {
          apply maponpaths. symmetry. use maponpathscomp.
        }
        intermediate_path (! q (S n) @ maponpaths (l n) (q n)). {
          unfold q'. repeat rewrite maponpaths_funextsec. reflexivity.
        }
        intermediate_path (! (maponpaths (l n) (q n) @ ! p n) @
                             maponpaths (l n) (q n)). {
          reflexivity.
        }
        rewrite pathscomp_inv.
        rewrite <- path_assoc.
        rewrite pathsinv0l.
        rewrite pathsinv0inv0.
        rewrite pathscomp0rid.
        reflexivity.
    - cbn.
      reflexivity.
  Defined.


  Definition shift (chain : Chain) : Chain :=
    build_chain (chain_types chain ∘ S)
                (chain_functions chain ∘ S).

  Lemma weq_limit_shift (chain : Chain) :
    limit (shift chain) ≃__i limit chain.
  Proof.
    induction chain as [X π].
    intros i.
    intermediate_weq (∑ x : ∏ n, X (1 + n) i,
                            ∏ n, π (1 + n) i (x (1 + n)) = x n). {
      apply idweq.
    }
    intermediate_weq (∑ x : ∏ n, X (1 + n) i,
                            (∑ x0 : X 0 i, π 0 i (x 0) = x0) ×
                            ∏ n, π (1 + n) i (x (1 + n)) = x n). {
      apply weq_functor_total2_id; intros x.
      apply invweq. apply weq_prod_contr_l. apply iscontr_based_paths.
    }
    intermediate_weq (∑ x : ∏ n, X (1 + n) i,
                            ∑ x0 : X 0 i,
                                   π 0 i (x 0) = x0 ×
                                   ∏ n, π (1 + n) i (x (1 + n)) = x n). {
      apply weq_functor_total2_id; intros x. apply weqtotal2asstor.
    }
    intermediate_weq (∑ x : (∏ n, X (1 + n) i) × X 0 i,
                            π 0 i (pr1 x 0) = pr2 x ×
                            ∏ n, π (1 + n) i (pr1 x (1 + n)) = pr1 x n). {
      use weqtotal2asstol.
    }
    intermediate_weq (∑ x : ∏ n, X n i,
                            ∏ n, π n i (x (1 + n)) = x n). {
      use weq_functor_total2.
      - apply (weqcomp (weqdirprodcomm _ _)). use weq_sequence_cons.
      - intros [xS x0]; cbn.
        use weq_sequence_cons.
    }
    apply idweq.
  Defined.


  Definition apply_on_chain (F : functor I I) (chain : Chain) : Chain.
  Proof.
    induction chain as [X π].
    use build_chain.
    - exact (λ n, F (X n)).
    - exact (λ n, F.map (π n)).
  Defined.

  Lemma weq_polynomial_functor_on_limit
        (c : Container I I) (chain : Chain) :
    ⟦c⟧ (limit chain) ≃__i limit (apply_on_chain (⟦c⟧) chain).
  Proof.
    induction c as [A B].
    induction chain as [X π]; unfold apply_on_chain; cbn;
      unfold container_extension, limit; cbn.
    intros i.
    intermediate_weq (∑ a : A i,
                            ∏ j, ∑ x : B i a j -> ∏ n, X n j,
                                       ∏ b n, π n j (x b (1 + n)) = x b n). {
      apply weq_functor_total2_id; intros a.
      apply weq_functor_sec_id; intros j.
      use func_total2_distributivity.
    }
    intermediate_weq (∑ a : A i,
                            ∑ x : ∏ j, B i a j -> ∏ n, X n j,
                                  ∏ j b n, π n j (x j b (1 + n)) = x j b n). {
      apply weq_functor_total2_id; intros a.
      use sec_total2_distributivity.
    }
    intermediate_weq (∑ a : A i,
                            ∑ x : ∏ n j, B i a j -> X n j,
                                  ∏ n j b, π n j (x (1 + n) j b) = x n j b). {
      apply weq_functor_total2_id; intros a.
      use weq_functor_total2.
      - intermediate_weq (∏ j n (b : B i a j), X n j). {
          apply weq_functor_sec_id; intros j.
          apply sec_symmetry.
        }
        apply sec_symmetry.
      - cbn. intros x.
        intermediate_weq (∏ j n b, π n j (x j b (1 + n)) = x j b n). {
          apply weq_functor_sec_id; intros j.
          apply sec_symmetry.
        }
        apply sec_symmetry.
    }
    intermediate_weq (∑ a,
                      ∑ x : ∏ n j, B i a j → X n j,
                            ∏ n : nat, π n ∘__i x (S n) = x n). {
      apply weq_functor_total2_id; intros a.
      apply weq_functor_total2_id; intros x.
      apply weq_functor_sec_id; intros n.
      apply invweq.
      intermediate_weq (∏ j, π n j ∘ x (1 + n) j = x n j). {
        apply weqtoforallpaths.
      }
      apply weq_functor_sec_id; intros j.
      apply weqtoforallpaths.
    }
    intermediate_weq (∑ ap : ∑ a : nat -> A i, ∏ n, a (1 + n) = a n,
                                   ∑ x  : ∏ n j, B i (pr1 ap n) j -> X n j,
                                          ∏ n, transportf
                                                 (λ a, ∏ j, B i a j -> X n j)
                                                 (pr2 ap n)
                                                 (π n ∘__i x (1 + n))
                                               = x n). {
      use weq_functor_total2.
      - apply invweq.
        apply weq_cochain_limit_simpl.
      - cbn. intros a.
        apply idweq.
    }
    intermediate_weq (∑ a : nat -> A i,
                            ∑ p : ∏ n, a (1 + n) = a n,
                                  ∑ x : ∏ n j, B i (a n) j -> X n j,
                                        ∏ n, transportf
                                               (λ a, ∏ j, B i a j -> X n j)
                                               (p n)
                                               (π n ∘__i x (1 + n))
                                             = x n). {
      apply invweq.
      apply invweq.
      apply total2_associativity.
    }
    intermediate_weq (∑ a : nat -> A i,
                            ∑ x : ∏ n j, B i (a n) j -> X n j,
                                  ∑ p : ∏ n, a (1 + n) = a n,
                                        ∏ n, transportf
                                               (λ a, ∏ j, B i a j -> X n j)
                                               (p n)
                                               (π n ∘__i x (1 + n))
                                             = x n). {
      apply weq_functor_total2_id; intros a.
      apply total2_symmetry.
    }
    intermediate_weq (∑ a : nat -> A i,
                            ∑ x : ∏ n j, B i (a n) j -> X n j,
                                  ∏ n, ∑ p : a (1 + n) = a n,
                                             transportf
                                               (λ a, ∏ j, B i a j -> X n j)
                                               p
                                               (π n ∘__i x (1 + n))
                                             = x n). {
      apply weq_functor_total2_id; intros a.
      apply weq_functor_total2_id; intros x.
      apply invweq.
      apply sec_total2_distributivity.
    }
    intermediate_weq (∑ a : nat -> A i,
                            ∑ x : ∏ n j, B i (a n) j -> X n j,
                                  ∏ n, tpair (λ a, ∏ j, B i a j -> X n j)
                                             (a (1 + n))
                                             (π n ∘__i x (1 + n))
                                       = tpair (λ a, ∏ j, B i a j -> X n j)
                                               (a n)
                                               (x n)). {
      apply weq_functor_total2_id; intros a.
      apply weq_functor_total2_id; intros x.
      apply weq_functor_sec_id; intros n.
      use weq_total2_paths_f.
    }
    intermediate_weq (∑ x : ∑ a : nat -> A i, ∏ n j, B i (a n) j → X n j,
                                  ∏ n : nat, tpair (λ a, ∏ j, B i a j -> X n j)
                                                 (pr1 x (1 + n))
                                                 (π n ∘__i pr2 x (1 + n))
                                           = tpair (λ a, ∏ j, B i a j -> X n j)
                                                   (pr1 x n)
                                                   (pr2 x n)). {
      apply invweq.
      apply total2_associativity.
    }
    use weq_functor_total2.
    - apply invweq.
      apply sec_total2_distributivity.
    - intros x. cbn.
      apply idweq.
  Defined.


  Variable A : Fam I.
  Variable B : ∏ i, A i -> I -> UU.
  Local Definition P := ⟦ A ◁ B ⟧.
  Opaque P.

  Definition W : nat -> Fam I.
  Proof.
    intros n; induction n.
    - exact (λ _, unit).
    - exact (P IHn).
  Defined.

  Definition π : ∏ n, W (1 + n) ->__i W n.
  Proof.
    intros n; induction n.
    - exact (λ _ _, tt).
    - exact (P.map IHn).
  Defined.

  Definition chain := build_chain W π.

  Definition m0_type := limit chain.

  Definition m0_in : P m0_type ≃__i m0_type :=
    weqcomp__i (weq_polynomial_functor_on_limit _ chain)
             (weq_limit_shift chain).
  Opaque m0_in.

  Definition m0_out : coalgebra_structure P m0_type := invweq__i m0_in.

  Definition m0_coalgebra : coalgebra P := m0_type,, m0_out.

  Lemma m0_coalgebra_is_final : is_final_coalgebra m0_coalgebra.
  Proof.
    unfold is_final_coalgebra.
    intros coalgebra; induction coalgebra as [C γ];
      unfold coalgebra_structure in γ.
    apply iscontrifweqtounit.
    intermediate_weq (∑ f, m0_out ∘__i f = P.map f ∘__i γ). {
      apply idweq.
    }
    intermediate_weq (∑ f, m0_in ∘__i m0_out ∘__i f = m0_in ∘__i P.map f ∘__i γ). {
      apply weq_functor_total2_id; intros f.
      apply (weqonpaths (weq_comp_l__i _ _ _ m0_in)).
    }
    set (Ψ f := m0_in ∘__i P.map f ∘__i γ :
                  C ->__i m0_type).
    intermediate_weq (∑ f, f = Ψ f). {
      apply weq_functor_total2_id; intros f.
      apply weq_comp0_l.
      apply funextsec; intros i.
      apply funextfun; intros c.
      apply pathsinv0.
      exact (homotweqinvweq (m0_in i) (f i c)).
    }
    set (Cone := Cone chain C).
    set (e := invweq (universal_property_of_limit chain C) :
                Cone ≃ (C ->__i m0_type)).
    intermediate_weq (∑ c : Cone, e c = Ψ (e c)). {
      apply invweq.
      use weq_functor_total2.
      - exact e.
      - intros c.
        apply idweq.
    }
    set (Φ := invmap e ∘ Ψ ∘ e :
                Cone -> Cone).
    intermediate_weq (∑ c : Cone, e c = e (Φ c)). {
      apply weq_functor_total2_id; intros c.
      apply weq_comp0_r. unfold Φ.
      change (Ψ (e c) = e (invmap e (Ψ (e c)))).
      rewrite homotweqinvweq.
      reflexivity.
    }
    intermediate_weq (∑ c : Cone, c = Φ c). {
      apply weq_functor_total2_id; intros c.
      apply invweq.
      apply weqonpaths.
    }
    set (Cone0' n := C ->__i W n).
    set (Cone0 := ∏ n, Cone0' n).
    set (Cone1' (u : Cone0) n := π n ∘__i u (1 + n) = u n).
    set (Cone1 (u : Cone0) := ∏ n, Cone1' u n).
    assert (Cone = (∑ u : Cone0, Cone1 u)) by reflexivity.
    intermediate_weq (∑ u : Cone0, ∑ q : Cone1 u, u,, q = Φ (u,, q)). {
      apply total2_associativity.
    }
    transparent assert (Φ0' : (∏ n, Cone0' n -> Cone0' (S n))). {
      exact (λ (n : nat) (un : Cone0' n), P.map un ∘__i γ).
    }
    transparent assert (Φ0 : (Cone0 -> Cone0)). {
      exact (λ u n i c,
             nat_rect (λ n, W n i)
                      (tt)
                      (λ n _, Φ0' n (u n) i c)
                      n).
    }
    transparent assert (Φ1' : (∏ (u : Cone0) n,
                               Cone1' u n ->
                               ∏ i c, (π (1 + n) ∘__i Φ0 u (2 + n)) i c =
                                      Φ0 u (1 + n) i c)). {
      exact (λ (u : Cone0) (n : nat) (pn : Cone1' u n) (i : I) (c : C i),
             @total2_paths_f _ _
               ((P.map (π n ∘__i u (S n)) ∘__i γ) i c)
               ((P.map (u n) ∘__i γ) i c)
               (idpath _)
               (funextsec _ _ _
                  (λ j, funextfun _ _
                          (toforallpaths _ _ _
                             (toforallpaths _ _ _ pn j) ∘
                             pr2 (γ i c) j)))).
    }
    transparent assert (Φ1 : (∏ u : Cone0, Cone1 u -> Cone1 (Φ0 u))). {
      exact (λ (u : Cone0) (p : Cone1 u) (n : nat),
             funextsec _
               (π n ∘__i Φ0 u (1 + n))
               (Φ0 u n)
               (λ i : I,
                      funextfun _ _
                        (λ c : C i,
                               nat_rect
                                 (λ n', (π n' ∘__i Φ0' n' (u n')) i c =
                                        Φ0 u n' i c)
                                 (idpath tt)
                                 (λ n' _, Φ1' u n' (p n') i c)
                                 n))).
    }
    assert (∏ u q, Φ (u,, q) = Φ0 u,, Φ1 u q) by reflexivity.
    intermediate_weq (∑ (u : Cone0) (q : Cone1 u), u,, q = Φ0 u,, Φ1 u q). {
      apply idweq.
    }
    intermediate_weq (∑ (u : Cone0) (q : Cone1 u),
                      ∑ p : u = Φ0 u, transportf Cone1 p q = Φ1 u q). {
      apply weq_functor_total2_id; intros u.
      apply weq_functor_total2_id; intros q.
      apply invweq.
      apply weq_total2_paths_f.
    }
    intermediate_weq (∑ u : Cone0,
                      ∑ p : u = Φ0 u,
                      ∑ q : Cone1 u,
                            transportf Cone1 p q = Φ1 u q). {
      apply weq_functor_total2_id; intros u.
      apply total2_symmetry.
    }
    intermediate_weq (∑ up : ∑ u : Cone0, u = Φ0 u,
                      ∑ q  : Cone1 (pr1 up),
                             transportf Cone1 (pr2 up) q = Φ1 (pr1 up) q). {
      apply invweq.
      apply total2_associativity.
    }
    intermediate_weq (∑ _ : unit, unit). {
      use weq_functor_total2.
      - intermediate_weq (∑ u : Cone0, ∏ n, u n = Φ0 u n). {
          apply weq_functor_total2_id; intros u.
          apply weqtoforallpaths.
        }
        intermediate_weq (∑ u : Cone0, u 0 = Φ0 u 0 × ∏ n, u (S n) = Φ0 u (S n)). {
          apply weq_functor_total2_id; intros u.
          apply invweq.
          use weq_sequence_cons.
        }
        intermediate_weq (∑ u : Cone0, ∏ n, u (S n) = Φ0 u (S n)). {
          apply weq_functor_total2_id; intros u.
          apply weq_prod_contr_l.
          apply impred_isaprop; intros i.
          apply impred_isaprop; intros c.
          apply isapropunit.
        }
        intermediate_weq (C ->__i W 0). {
          unfold Φ0; cbn.
          apply (weq_cochain_limit Cone0' (λ n un, Φ0' n un)).
        }
        apply weqcontrtounit.
        apply impred_iscontr; intros i.
        apply impred_iscontr; intros c.
        apply iscontrunit.
      - induction 0 as [u p]; cbn.
        intermediate_weq (∑ q : Cone1 u,
                                transportb Cone1 p (transportf Cone1 p q) =
                                transportb Cone1 p (Φ1 u q)). {
          apply weq_functor_total2_id; intros q.
          apply (weqonpaths (make_weq _ (isweqtransportb Cone1 p))).
        }
        intermediate_weq (∑ q : Cone1 u, q = transportb Cone1 p (Φ1 u q)). {
          apply weq_functor_total2_id; intros q.
          rewrite transport_b_f.
          rewrite pathsinv0r.
          apply idweq.
        }
        intermediate_weq (∑ q : Cone1 u,
                                ∏ n, q n = transportb Cone1 p (Φ1 u q) n). {
          apply weq_functor_total2_id; intros q.
          apply weqtoforallpaths.
        }
        intermediate_weq (∑ q : Cone1 u,
                                ∏ n, q n =
                                     transportb (λ u, Cone1' u n) p (Φ1 u q n)). {
          apply weq_functor_total2_id; intros q.
          apply weq_functor_sec_id; intros n.
          apply weq_comp0_r.
          apply transportb_sec_constant.
        }
        intermediate_weq (∑ q : Cone1 u,
                                q 0 = transportb (λ u, Cone1' u 0) p (Φ1 u q 0) ×
                                ∏ n, q (S n) =
                                     transportb (λ u, Cone1' u (S n))
                                                p
                                                (Φ1 u q (S n))). {
          apply weq_functor_total2_id; intros q.
          apply invweq.
          use weq_sequence_cons.
        }
        intermediate_weq (∑ q : Cone1 u,
                                ∏ n, q (S n) =
                                     transportb (λ u, Cone1' u (S n))
                                                p
                                                (Φ1 u q (S n))). {
          apply weq_functor_total2_id; intros q.
          apply weq_prod_contr_l.
          apply impred_isaset; intros i.
          apply impred_isaset; intros c.
          apply isasetunit.
        }
        intermediate_weq (Cone1' u 0). {
          unfold Φ1.
          apply (weq_cochain_limit
                   (λ n, π n ∘__i u (S n) = u n)
                   (λ n pn, transportb (λ u, Cone1' u (S n))
                              p
                              (funextsec _ _ _
                                         (λ i, funextfun _ _ (Φ1' u n pn i))))).
        }
        apply weqcontrtounit.
        apply impred_isaprop; intros i.
        apply impred_isaprop; intros c.
        apply isapropunit.
    }
    apply weqtotal2overunit.
  Qed.

  Definition m0_corec (C : coalgebra P) {i : I} (c : coalgebra_to_type C i) :
    m0_type i :=
    coalgebra_morphism_to_function
      (finality_morphism_coalgebra _ m0_coalgebra_is_final C)
      i
      c.

  Definition m0_corec_beta (C : coalgebra P) {i : I} (c : coalgebra_to_type C i) :
    m0_out i (m0_corec C c) =
    P.map (@m0_corec C) i (coalgebra_to_coalgebra_str C i c).
  Proof.
    change ((m0_out ∘__i @m0_corec C) i c =
            (P.map (@m0_corec C) ∘__i coalgebra_to_coalgebra_str C) i c).
    revert c; apply toforallpaths.
    revert i; apply toforallpaths.
    exact (pr2 (finality_morphism_coalgebra _ m0_coalgebra_is_final C)).
  Defined.



  Definition m_type : Fam I :=
    λ i,
    ∑ m : m0_type i,
          ∃ C c, m0_corec C c = m.

  Definition m_corec (C : coalgebra P) {i : I} (c : coalgebra_to_type C i) :
    m_type i.
  Proof.
    exists (m0_corec C c).
    apply (hinhpr (C,, c,, idpath _)).
  Defined.

  Lemma H : ∏ i (m : m_type i), isaprop
    (∑ af : P m_type i, m0_out i (pr1 m) = P.map (λ _, pr1) i af).
  Proof.
    intros.
    induction m as [m Ccp]; simpl. clear Ccp.
    change (isaprop (∑ af : P m_type i,
                            m0_out i m =
                            P.map (λ _, pr1) i af)).
    use (@isofhlevelweqb
           _
           _
           (∑ ap : ∑ a : A i, pr1 (m0_out i m) = a,
                   ∏ (j : I) (b : B i (pr1 ap) j),
                   ∑ mp : ∑ m' : m0_type j,
                                 transportf (λ a, B i a j -> m0_type j)
                                            (pr2 ap)
                                            (pr2 (m0_out i m) j) b =
                                 m',
                          ∥ ∑ C c, m0_corec C c = pr1 mp ∥)).
    - refine (weqcomp (total2_associativity _ _ _) _).
      refine (weqcomp _ (invweq (total2_associativity _ _ _))).
      apply weq_functor_total2_id; intros a.
      intermediate_weq (
          ∑ f : ∏ j, B i a j → m_type j,
                m0_out i m = P.map (λ _, pr1) i (a,, f)). {
        apply idweq.
      }
      intermediate_weq (
          ∑ f : ∏ j, B i a j → m_type j,
                ∑ p : pr1 (m0_out i m) = a,
                      transportf
                        (λ a, ∏ j, B i a j -> m0_type j)
                        p
                        (pr2 (m0_out i m)) =
                      (λ _, pr1) ∘__i f). {
        apply weq_functor_total2_id; intros f.
        apply invweq.
        assert (H : ∏ A B (x : ∑ a : A, B a), x = pr1 x,, pr2 x). {
          reflexivity.
        }
        rewrite (H _ _ (m0_out i m)).
        change ((∑ p : pr1 (m0_out i m) = a,
                       transportf
                         (λ a, ∏ j, B i a j → m0_type j)
                         p
                         (pr2 (m0_out i m)) =
                       (λ _, pr1) ∘__i f) ≃
                                        tpair (λ a, ∏ j, B i a j -> m0_type j)
                                        (pr1 (m0_out i m)) (pr2 (m0_out i m)) =
                         P.map (λ _, pr1) i (a,, f)).
        apply (weq_total2_paths_f (A i) (λ a, ∏ j, B i a j -> m0_type j)
                                  (pr1 (m0_out i m)) a (pr2 (m0_out i m))
                                  ((λ _, pr1) ∘__i f)).
      }
      intermediate_weq (∑ p : pr1 (m0_out i m) = a,
                        ∑ f : ∏ j, B i a j → m_type j,
                              transportf
                                (λ a, ∏ j, B i a j → m0_type j)
                                p
                                (pr2 (m0_out i m)) =
                              (λ _, pr1) ∘__i f). {
        apply total2_symmetry.
      }
      apply weq_functor_total2_id; intros p.
      intermediate_weq (∑ fg : ∑ f : ∏ j, B i a j -> m0_type j,
                                     ∏ j b, ∃ C c, m0_corec C c = f j b,
                               transportf
                                 (λ a, ∏ j, B i a j -> m0_type j)
                                 p
                                 (pr2 (m0_out i m)) =
                               pr1 fg). {
        use weq_functor_total2.
        - refine (weqcomp
                    _
                    (sec_total2_distributivity
                       I
                       (λ j, B i a j -> m0_type j)
                       (λ j f, ∏ b, ∃ C c, m0_corec C c = f b))).
          apply weq_functor_sec_id; intros j.
          apply func_total2_distributivity.
        - simpl.
          intros f.
          apply idweq.
      }
      intermediate_weq (∑ f : ∏ j, B i a j → m0_type j,
                        ∑ _ : ∏ j b, ∃ C c, m0_corec C c = f j b,
                              transportf
                                (λ a, ∏ j, B i a j → m0_type j)
                                p
                                (pr2 (m0_out i m)) =
                              f). {
        apply total2_associativity.
      }
      intermediate_weq (∑ f : ∏ j, B i a j → m0_type j,
                        ∑ _ : ∏ j b, ∃ C c, m0_corec C c = f j b,
                              ∏ j b, transportf
                                       (λ a, ∏ j, B i a j → m0_type j)
                                       p
                                       (pr2 (m0_out i m)) j b =
                                     f j b). {
        apply weq_functor_total2_id; intros f.
        apply weq_functor_total2_id; intros _.
        intermediate_weq (∏ j, transportf (λ a, ∏ j, B i a j -> m0_type j)
                                          p
                                          (pr2 (m0_out i m))
                                          j =
                               f j). {
          apply weqtoforallpaths.
        }
        apply weq_functor_sec_id; intros j.
        apply weqtoforallpaths.
      }
      intermediate_weq (∑ f : ∏ j, B i a j → m0_type j,
                              ∏ j b, ∑ _ : ∃ C c, m0_corec C c = f j b,
                                           transportf
                                             (λ a, ∏ j, B i a j → m0_type j)
                                             p
                                             (pr2 (m0_out i m)) j b =
                                           f j b). {
        apply weq_functor_total2_id; intros f.
        refine (weqcomp (invweq (sec_total2_distributivity
                                   I
                                   (λ j, ∏ b, ∃ C c, m0_corec C c = f j b)
                                   (λ j _, ∏ b, transportf
                                                  (λ a, ∏ j, B i a j -> m0_type j)
                                                  p
                                                  (pr2 (m0_out i m)) j b = f j b)))
                        _).
        apply weq_functor_sec_id; intros j.
        apply invweq.
        apply sec_total2_distributivity.
      }
      intermediate_weq (∏ j b, ∑ m' : m0_type j,
                               ∑ _ : ∃ C c, m0_corec C c = m',
                                     transportf
                                       (λ a, ∏ j, B i a j -> m0_type j)
                                       p
                                       (pr2 (m0_out i m)) j b =
                                     m'). {
        apply invweq.
        refine (weqcomp _ (sec_total2_distributivity
                          I
                          (λ j, B i a j -> m0_type j)
                          (λ j f, ∏ b, ∑ _ : ∃ C c, m0_corec C c = f b,
                                             transportf
                                               (λ a, ∏ j, B i a j -> m0_type j)
                                               p
                                               (pr2 (m0_out i m))
                                               j
                                               b =
                                             f b))).
        apply weq_functor_sec_id; intros j.
        apply sec_total2_distributivity.
      }
      apply weq_functor_sec_id; intros j.
      apply weq_functor_sec_id; intros b.
      intermediate_weq (∑ m' : m0_type j,
                               ∑ _ : transportf
                                       (λ a, ∏ j, B i a j -> m0_type j)
                                       p
                                       (pr2 (m0_out i m)) j b =
                                     m',
                                     ∃ C c, m0_corec C c = m'). {
        apply weq_functor_total2_id; intros m'.
        apply weqdirprodcomm.
      }
      intermediate_weq (∑ mp : ∑ m', transportf (λ a, ∏ j, B i a j → m0_type j) p
                                                (pr2 (m0_out i m)) j b = m',
                               ∃ C c, m0_corec C c = pr1 mp). {
        apply invweq.
        apply total2_associativity.
      }
      use weq_functor_total2.
      + apply weq_functor_total2_id; intros m'.
        rewrite transportf_sec_constant.
        apply idweq.
      + simpl.
        induction 0 as [m' q].
        apply idweq.
    - apply isofhleveltotal2.
      + apply isofhlevelcontr.
        apply iscontr_based_paths.
      + induction 0 as [a p].
        apply impred; intros j.
        apply impred; intros b.
        apply isofhleveltotal2.
        * apply isofhlevelcontr.
          apply iscontr_based_paths.
        * induction 0 as [m' q].
          apply isapropishinh.
  Qed.

  Definition m_out : m_type ->__i P m_type.
  Proof.
    cut (∑ m_out : m_type ->__i (P m_type),
                   ∏ i m, m0_out i (pr1 m) =
                          P.map (λ _, pr1) i (m_out i m)). {
      exact pr1.
    }
    apply (sec_total2_distributivity
             I
             (λ i, m_type i -> P m_type i)
             (λ i m_out_i, ∏ m, m0_out i (pr1 m) =
                                 P.map (λ _, pr1) i (m_out_i m))).
    intros i.
    apply (sec_total2_distributivity
             (m_type i)
             (λ _, P m_type i)
             (λ m m_out_i_m, m0_out i (pr1 m) =
                              P.map (λ _, pr1) i m_out_i_m)).
    intros m.
    apply (squash_to_prop (pr2 m)).
    - apply H.
    - induction 1 as [C [c p]].
      exists (P.map (@m_corec C) i (coalgebra_to_coalgebra_str C i c)).
      rewrite <- p.
      change (m0_out i (m0_corec C c) =
              P.map (@m0_corec C) i (coalgebra_to_coalgebra_str C i c)).
      apply m0_corec_beta.
  Defined.

  Goal ∏ (C : coalgebra P) (i : I) (c : coalgebra_to_type C i),
  m_out i (m_corec C c) =
  P.map (@m_corec C) i (coalgebra_to_coalgebra_str C i c).
  Proof.
    reflexivity.
  Qed.

  Definition m_coalgebra : coalgebra P :=
    m_type,,
    m_out.

  Definition m_label {i} (m : m_type i) : A i :=
    pr1 (m_out i m).

  Definition m_arg {i} (m : m_type i) {j} (b : B i (m_label m) j) : m_type j :=
    pr2 (m_out i m) j b.


  Definition weq_m_m0 : m_type ≃__i m0_type.
  Proof.
    intros i.
    use weq_iso.
    - exact pr1.
    - intros m.
      exists m.
      apply hinhpr.
      exists m0_coalgebra.
      exists m.
      abstract (
          change (coalgebra_morphism_to_function
                    (finality_morphism_coalgebra
                       _
                       m0_coalgebra_is_final
                       m0_coalgebra)
                    i
                    m =
                  coalgebra_morphism_to_function
                    (coalgebra_morphism_identity m0_coalgebra)
                    i
                    m);
          revert m; apply toforallpaths;
          revert i; apply toforallpaths;
          apply maponpaths;
          apply uniqueness_morphism_coalgebra;
          exact m0_coalgebra_is_final
      ).
    - induction 0 as [m p].
      use total2_paths_f.
      + reflexivity.
      + apply (@isaprop_uniqueness (∃ C c, m0_corec C c = m)).
        apply propproperty.
    - reflexivity.
  Defined.


  Definition m_coalgebra_is_m0_coalgebra : m_coalgebra = m0_coalgebra.
  Proof.
    use total2_paths_f.
    - apply funextsec; intros i.
      apply weqtopaths.
      apply weq_m_m0.
    - apply funextsec; intros i.
      apply funextfun; intros m.
      simpl.
      rewrite (@transportf_sec_constant (Fam I) I (λ C i, C i -> P C i)).
      rewrite transportf_fun.
      rewrite (functtransportb (λ f, f i) (idfun _)).
      rewrite (@maponpaths_funextsec I (λ _, UU)).
      rewrite transportb_weqtopaths.
      Transparent P. simpl.
      rewrite transportf_total2_const.
      use total2_paths_f; simpl.
      + reflexivity.
      + change (transportf
                  (λ X, ∏ j, B i (pr1 (m0_out i m)) j -> X j)
                  (funextfun m_type m0_type (λ j, weqtopaths (weq_m_m0 j)))
                  (λ j b, m_corec m0_coalgebra (pr2 (m0_out i m) j b)) =
                pr2 (m0_out i m)).
        apply funextsec; intros j.
        apply funextsec; intros b.
        rewrite transportf_sec_constant.
        rewrite transportf_sec_constant.
        change funextfun with (funextsec (λ _ : I, UU)).
        rewrite (transportf_funextfun (idfun _) m_type m0_type
                                      (λ j, weqtopaths (weq_m_m0 j)) j).
        unfold idfun.
        rewrite transportf_weqtopaths.
        change (coalgebra_morphism_to_function
                  (finality_morphism_coalgebra
                     _
                     m0_coalgebra_is_final
                     m0_coalgebra)
                  j
                  (pr2 (m0_out i m) j b) =
                (coalgebra_morphism_to_function
                   (coalgebra_morphism_identity m0_coalgebra)
                   j
                   (pr2 (m0_out i m) j b))).
        use (maponpaths (λ h, coalgebra_morphism_to_function h _ _)).
        apply uniqueness_morphism_coalgebra.
        exact m0_coalgebra_is_final.
  Qed.

  Lemma m_coalgebra_is_final : is_final_coalgebra m_coalgebra.
  Proof.
    intros C.
    apply iscontr_move_point.
    - exists (@m_corec C).
      reflexivity.
    - rewrite m_coalgebra_is_m0_coalgebra.
      apply m0_coalgebra_is_final.
  Defined.

  Lemma isweq_m_out : isweq__i m_out.
  Proof.
    change (isweq__i m_coalgebra.2).
    apply isweq_final_coalgebra_struct. apply m_coalgebra_is_final.
  Defined.

  Definition weq_m_out : m_type ≃__i P m_type :=
    λ i, make_weq (m_out i) (isweq_m_out i).

  Definition m_sup {i} (label : A i) (arg : ∏ j, B i label j -> m_type j) :
    m_type i :=
    invmap (weq_m_out i) (label,, arg).

  Lemma m_sup_m_out {i} (m : m_type i) :
    m_sup (m_label m) (@m_arg i m) = m.
  Proof.
    Fail reflexivity.
    change (invmap (weq_m_out i) (weq_m_out i m) = m).
    apply homotinvweqweq.
  Qed.

  Lemma m_out_m_sup {i} (a : A i) (f : B i a ->__i m_type) :
    tpair (λ label, B i label ->__i m_type)
          (m_label (m_sup a f))
          (@m_arg i (m_sup a f)) =
    (a,, f).
  Proof.
    Fail reflexivity.
    change (weq_m_out i (invmap (weq_m_out i) (a,, f)) = (a,, f)).
    apply homotweqinvweq.
  Qed.


  Transparent P.

End M_From_Nat.

Opaque m0_out m0_in m0_coalgebra_is_final m0_corec m0_corec_beta.

Arguments m_label {_ _ _ _} _.
Arguments m_arg {_ _ _ _} _ {_} _.
Arguments m_corec {_ _ _} _ {_} _.
Arguments m_sup {_ _ _ _} _ _.
Arguments m_sup_m_out {_ _ _ _} _.
Arguments m_out_m_sup {_ _ _ _} _ _.
