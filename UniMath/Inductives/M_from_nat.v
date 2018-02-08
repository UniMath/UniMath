Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Inductives.algebras.
Require Import UniMath.Inductives.containers.
Require Import UniMath.Inductives.auxiliary_lemmas.


Section M_From_Nat.

  Context {I : UU}.


  Definition Chain :=
    ∑ (X : nat -> Fam I),
    ∏ n, X (1 + n) ->ⁱ X n.
  Opaque Chain.

  Definition build_chain (X : nat -> Fam I) (π : ∏ n, X (1 + n) ->ⁱ X n) : Chain :=
    X,, π.

  Definition chain_types (chain : Chain) : nat -> Fam I :=
    pr1 chain.

  Definition chain_functions (chain : Chain) :
    let X := chain_types chain in
    ∏ n, X (1 + n) ->ⁱ X n :=
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
      ∑ (f : ∏ n, A ->ⁱ X n),
      ∏ n, π n ∘ⁱ f (1 + n) = f n.

    Definition to_cone {A : Fam I} (f : A ->ⁱ limit) : Cone A.
    Proof.
      exists (λ n i a, pr1 (f i a) n).
      intros n.
      apply funextsec; intros i.
      apply funextfun; intros a.
      exact (pr2 (f i a) n).
    Defined.

    Definition from_cone {A : Fam I} (cone : Cone A) : A ->ⁱ limit.
    Proof.
      intros i a.
      exists (λ n, pr1 cone n i a).
      intros n.
      revert a; apply toforallpaths.
      revert i; apply toforallpaths.
      exact (pr2 cone n).
    Defined.

    Lemma universal_property_of_limit (A : Fam I) :
      (A ->ⁱ limit) ≃ Cone A.
    Proof.
      use (weqgradth to_cone from_cone).
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
    use weqgradth.
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
      + rewrite transportf_sec_constant. apply funextsec; intros n.
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
    use weqgradth.
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
      + rewrite transportf_sec_constant. apply funextsec; intros n.
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
    limit (shift chain) ≃ⁱ limit chain.
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
    - exact (λ n, F.0 (X n)).
    - exact (λ n, F.1 (π n)).
  Defined.

  Lemma weq_polynomial_functor_on_limit
        (c : Container I I) (chain : Chain) :
    ⟦c⟧.0 (limit chain) ≃ⁱ limit (apply_on_chain ⟦c⟧ chain).
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
                            ∏ n : nat, π n ∘ⁱ x (S n) = x n). {
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
                                                 (π n ∘ⁱ x (1 + n))
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
                                               (π n ∘ⁱ x (1 + n))
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
                                               (π n ∘ⁱ x (1 + n))
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
                                               (π n ∘ⁱ x (1 + n))
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
                                             (π n ∘ⁱ x (1 + n))
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
                                                 (π n ∘ⁱ pr2 x (1 + n))
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
  Definition P := ⟦ A ◁ B ⟧.
  Opaque P.

  Definition W : nat -> Fam I.
  Proof.
    intros n; induction n.
    - exact (λ _, unit).
    - exact (P.0 IHn).
  Defined.

  Definition π : ∏ n, W (1 + n) ->ⁱ W n.
  Proof.
    intros n; induction n.
    - exact (λ _ _, tt).
    - exact (P.1 IHn).
  Defined.

  Definition chain := build_chain W π.

  Definition m_type := limit chain.

  Definition m_in : P.0 m_type ≃ⁱ m_type :=
    weqcompⁱ (weq_polynomial_functor_on_limit _ chain)
             (weq_limit_shift chain).
  Opaque m_in.

  Definition m_out : coalgebra_structure P m_type := invweqⁱ m_in.

  Definition m_coalgebra : coalgebra P := m_type,, m_out.

  Lemma m_coalgebra_is_final : is_final_coalgebra m_coalgebra.
  Proof.
    unfold is_final_coalgebra.
    intros coalgebra; induction coalgebra as [C γ];
      unfold coalgebra_structure in γ.
    apply iscontrifweqtounit.
    intermediate_weq (∑ f, m_out ∘ⁱ f = P.1 f ∘ⁱ γ). {
      apply idweq.
    }
    intermediate_weq (∑ f, m_in ∘ⁱ m_out ∘ⁱ f = m_in ∘ⁱ P.1 f ∘ⁱ γ). {
      apply weq_functor_total2_id; intros f.
      apply (weqonpaths (weq_comp_lⁱ _ _ _ m_in)).
    }
    set (Ψ f := m_in ∘ⁱ P.1 f ∘ⁱ γ :
                  C ->ⁱ m_type).
    intermediate_weq (∑ f, f = Ψ f). {
      apply weq_functor_total2_id; intros f.
      apply weq_comp0_l.
      apply funextsec; intros i.
      apply funextfun; intros c.
      apply pathsinv0.
      exact (homotweqinvweq (m_in i) (f i c)).
    }
    set (Cone := Cone chain C).
    set (e := invweq (universal_property_of_limit chain C) :
                Cone ≃ (C ->ⁱ m_type)).
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
    set (Cone0' n := C ->ⁱ W n).
    set (Cone0 := ∏ n, Cone0' n).
    set (Cone1' (u : Cone0) n := π n ∘ⁱ u (1 + n) = u n).
    set (Cone1 (u : Cone0) := ∏ n, Cone1' u n).
    assert (Cone = (∑ u : Cone0, Cone1 u)) by reflexivity.
    intermediate_weq (∑ u : Cone0, ∑ q : Cone1 u, u,, q = Φ (u,, q)). {
      apply total2_associativity.
    }
    transparent assert (Φ0' : (∏ n, Cone0' n -> Cone0' (S n))). {
      exact (λ (n : nat) (un : Cone0' n), P.1 un ∘ⁱ γ).
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
                               ∏ i c, (π (1 + n) ∘ⁱ Φ0 u (2 + n)) i c =
                                      Φ0 u (1 + n) i c)). {
      exact (λ (u : Cone0) (n : nat) (pn : Cone1' u n) (i : I) (c : C i),
             @total2_paths_f _ _
               ((P.1 (π n ∘ⁱ u (S n)) ∘ⁱ γ) i c)
               ((P.1 (u n) ∘ⁱ γ) i c)
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
               (π n ∘ⁱ Φ0 u (1 + n))
               (Φ0 u n)
               (λ i : I,
                      funextfun _ _
                        (λ c : C i,
                               nat_rect
                                 (λ n', (π n' ∘ⁱ Φ0' n' (u n')) i c =
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
        intermediate_weq (C ->ⁱ W 0). {
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
          apply (weqonpaths (weqpair _ (isweqtransportb Cone1 p))).
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
          revert n; apply weqtoforallpaths.
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
                   (λ n, π n ∘ⁱ u (S n) = u n)
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
  Defined.

End M_From_Nat.
