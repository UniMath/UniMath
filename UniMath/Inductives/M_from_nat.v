Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Inductives.algebras.



(*** Auxiliary Lemmas ***)

Definition transportf_paths_FlFr {A B : UU} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transportf (λ x, f x = g x) p q = !maponpaths f p @ q @ maponpaths g p.
Proof.
  induction p; cbn.
  symmetry.
  apply pathscomp0rid.
Defined.

Definition transportf_sec_constant
  {A B : UU} {C : A -> B -> UU}
  {x1 x2 : A} (p : x1 = x2) (f : ∏ y : B, C x1 y)
  : (transportf (λ x, ∏ y : B, C x y) p f)
    = (λ y, transportf (λ x, C x y) p (f y)).
Proof.
  induction p; cbn; unfold idfun.
  reflexivity.
Defined.

Definition transportb_sec_constant
  {A B : UU} (C : A -> B -> UU)
  {x1 x2 : A} (p : x1 = x2) (f : ∏ y : B, C x2 y)
  : (transportb (λ x, ∏ y : B, C x y) p f)
    = (λ y, transportb (λ x, C x y) p (f y)).
Proof.
  induction p; cbn; unfold idfun.
  reflexivity.
Defined.

Definition maponpaths_funextsec {A : UU} {B : A -> UU}
           (f g : ∏ x, B x) (x : A) (p : f ~ g) :
  maponpaths (λ h, h x) (funextsec _ f g p) = p x.
Proof.
  intermediate_path (toforallpaths _ _ _ (funextsec _ f g p) x). {
    generalize (funextsec _ f g p); intros q.
    induction q.
    reflexivity.
  }
  intermediate_path (weqcomp (invweq (weqtoforallpaths B f g))
                             (weqtoforallpaths B f g)
                             p
                             x). {
    reflexivity.
  }
  intermediate_path (p x). {
  rewrite weqcompinvl.
  reflexivity.
  }
  reflexivity.
Defined.

Lemma weq_functor_total2 {A B : UU} (C : A -> UU) (D : B -> UU) :
  ∏ e : A ≃ B,
        (∏ x, C x ≃ D (e x)) ->
        (∑ x, C x) ≃ (∑ x, D x).
Proof.
  intros e f.
  exact (weqbandf e C D f).
Defined.

Lemma weq_functor_total2_id {A : UU} (B C : A -> UU) :
  (∏ x, B x ≃ C x) ->
  (∑ x, B x) ≃ (∑ x, C x).
Proof.
  intros e.
  apply (weqfibtototal B C e).
Defined.

Lemma weq_prod_contr_l (A B : UU) :
  iscontr A ->
  A × B ≃ B.
Proof.
  induction 1 as [a0 a0_unique].
  use weqgradth.
  - exact pr2.
  - exact (λ b, a0,, b).
  - induction 0 as [a b]; cbn.
    apply pathsdirprod.
    + symmetry.
      apply a0_unique.
    + reflexivity.
  - intros b; cbn.
    reflexivity.
Defined.

Lemma iscontr_based_paths {A : UU} (x : A) :
  iscontr (∑ y, x = y).
Proof.
  use iscontrpair.
  - exact (x,, idpath x).
  - induction 0 as [y p].
    induction p.
    reflexivity.
Defined.

Lemma weq_sequence_cons (A : nat -> UU) :
  (A 0 × ∏ n, A (1 + n)) ≃ ∏ n, A n.
Proof.
  use weqgradth.
  - intros [xO xS] n; induction n.
    + exact xO.
    + exact (xS n).
  - exact (λ x, x 0,, x ∘ S).
  - reflexivity.
  - intros x; cbn.
    apply funextsec; intros n; induction n; reflexivity.
Defined.

Lemma func_total2_distributivity (A B : UU) (C : B -> UU) :
  (A -> ∑ b : B, C b)
    ≃ (∑ b : A -> B, ∏ a, C (b a)).
Proof.
  apply weqfuntototaltototal.
Defined.

Lemma sec_symmetry (A B : UU) (C : A -> B -> UU) :
  (∏ a b, C a b)
    ≃ (∏ b a, C a b).
Proof.
  use weqgradth.
  - exact (λ f b a, f a b).
  - exact (λ f a b, f b a).
  - reflexivity.
  - reflexivity.
Defined.

Lemma total2_symmetry (A B : UU) (C : A -> B -> UU) :
  (∑ a b, C a b)
    ≃ (∑ b a, C a b).
Proof.
  use weqgradth.
  - intros abc; induction abc as [a [b c]].
    exact (b,, a,, c).
  - intros bac; induction bac as [b [a c]].
    exact (a,, b,, c).
  - reflexivity.
  - reflexivity.
Defined.

Lemma weq_functor_sec_id (A : UU) (B C : A -> UU) :
  (∏ a, B a ≃ C a) ->
  (∏ a, B a) ≃ (∏ a, C a).
Proof.
  apply weqonsecfibers.
Defined.

Lemma total2_associativity (A : UU) (B : A -> UU) (C : (∑ a, B a) -> UU) :
  (∑ ab : ∑ a : A, B a, C ab)
    ≃ (∑ a : A, ∑ b : B a, C (a,, b)).
Proof.
  use weqgradth.
  - induction 1 as [ab c].
    induction ab as [a b].
    exact (a,, b,, c).
  - induction 1 as [a bc].
    induction bc as [b c].
    exact ((a,, b),, c).
  - induction 0 as [ab c].
    induction ab as [a b].
    reflexivity.
  - induction 0 as [a bc].
    induction bc as [b c].
    reflexivity.
Defined.

Lemma sec_total2_distributivity (A : UU) (B : A -> UU) (C : ∏ a, B a -> UU) :
  (∏ a : A, ∑ b : B a, C a b)
    ≃ (∑ b : ∏ a : A, B a, ∏ a, C a (b a)).
Proof.
  use weqgradth.
  - intros f.
    exists (λ a, pr1 (f a)).
    exact (λ a, pr2 (f a)).
  - intros fg; induction fg as [f g].
    exact (λ a, f a,, g a).
  - reflexivity.
  - reflexivity.
Defined.

Lemma weq_total2_paths_f (A : UU) (B : A -> UU)
      (a1 a2 : A) (b1 : B a1) (b2 : B a2) :
  (∑ p : a1 = a2, transportf B p b1 = b2)
    ≃ (a1,, b1 = a2,, b2).
Proof.
  use weqgradth.
  - induction 1 as [p q].
    use (total2_paths2_f p q).
  - intros p.
    exists (base_paths _ _ p).
    exact (fiber_paths p).
  - induction 0 as [p q].
    use total2_paths2_f.
    + exact (@base_total2_paths _ _ (a1,, b1) (a2,, b2) p q).
    + cbn.
      exact (transportf_fiber_total2_paths B (a1,, b1) (a2,, b2) p q).
  - intros p. cbn.
    apply (total2_fiber_paths p).
Defined.

Lemma weq_comp_l {A B C : UU} :
  B ≃ C ->
  (A -> B) ≃ (A -> C).
Proof.
  intros f.
  use weqgradth.
  - exact (λ g, f ∘ g).
  - exact (λ g, invmap f ∘ g).
  - intros g. cbn.
    apply funextfun; intros a.
    change (invmap f (f (g a)) = g a). rewrite homotinvweqweq.
    reflexivity.
  - intros g. cbn.
    apply funextfun; intros a.
    change (f (invmap f (g a)) = g a). rewrite homotweqinvweq.
    reflexivity.
Defined.

Lemma weq_comp0_l {A : UU} (a b c : A) :
  b = a ->
  (a = c) ≃ (b = c).
Proof.
  induction 1.
  apply idweq.
Defined.

Lemma weq_comp0_r {A : UU} (a b c : A) :
  b = c ->
  (a = b) ≃ (a = c).
Proof.
  induction 1.
  apply idweq.
Defined.



(*** Main Proof ***)

Definition Chain :=
  ∑ (X : nat -> UU),
  ∏ n, X (1 + n) -> X n.
Opaque Chain.

Definition build_chain (X : nat -> UU) (π : ∏ n, X (1 + n) -> X n) : Chain :=
  X,, π.

Definition chain_types (chain : Chain) : nat -> UU :=
  pr1 chain.

Definition chain_functions (chain : Chain) :
  let X := chain_types chain in
  ∏ n, X (1 + n) -> X n :=
  pr2 chain.


Section Limit.

  Variable chain : Chain.
  Let X := chain_types chain.
  Let π := chain_functions chain.

  Definition limit :=
    ∑ (x : ∏ n, X n),
    ∏ n, π n (x (1 + n)) = x n.

  Definition Cone (A : UU) :=
    ∑ (f : ∏ n, A -> X n),
    ∏ n, π n ∘ f (1 + n) = f n.

  Lemma universal_property_of_limit (A : UU) :
    (A -> limit) ≃ Cone A.
  Proof.
    use weqgradth.
    - intros f.
      exists (λ n a, pr1 (f a) n).
      intros n.
      apply funextfun; intros a.
      exact (pr2 (f a) n).
    - intros [u p] a.
      exists (λ n, u n a).
      intros n.
      revert a.
      apply toforallpaths.
      exact (p n).
    - intros f.
      cbn.
      apply funextfun; intros a.
      use total2_paths_f.
      + reflexivity.
      + cbn.
        apply funextsec; intros n.
        apply (toforallpaths _ _ _
                             (homotweqinvweq (weqtoforallpaths _ _ _)
                                             (λ a', pr2 (f a') n))
                             a).
    - intros [u p]; cbn.
      apply maponpaths.
      apply funextsec; intros n.
      apply (homotinvweqweq (weqtoforallpaths _ _ _)).
  Defined.

End Limit.


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
  limit (shift chain) ≃ limit chain.
Proof.
  induction chain as [X π].
  intermediate_weq (∑ x : ∏ n, X (1 + n),
                          ∏ n, π (1 + n) (x (1 + n)) = x n). {
    apply idweq.
  }
  intermediate_weq (∑ x : ∏ n, X (1 + n),
                          (∑ x0 : X 0, π 0 (x 0) = x0) ×
                          ∏ n, π (1 + n) (x (1 + n)) = x n). {
    apply weq_functor_total2_id; intros x.
    apply invweq. apply weq_prod_contr_l. apply iscontr_based_paths.
  }
  intermediate_weq (∑ x : ∏ n, X (1 + n),
                          ∑ x0 : X 0,
                                 π 0 (x 0) = x0 ×
                                 ∏ n, π (1 + n) (x (1 + n)) = x n). {
    apply weq_functor_total2_id; intros x. apply weqtotal2asstor.
  }
  intermediate_weq (∑ x : (∏ n, X (1 + n)) × X 0,
                          π 0 (pr1 x 0) = pr2 x ×
                          ∏ n, π (1 + n) (pr1 x (1 + n)) = pr1 x n). {
    use weqtotal2asstol.
  }
  intermediate_weq (∑ x : ∏ n, X n,
                          ∏ n, π n (x (1 + n)) = x n). {
    use weq_functor_total2.
    - apply (weqcomp (weqdirprodcomm _ _)). apply weq_sequence_cons.
    - intros [xS x0]; cbn.
      use weq_sequence_cons.
  }
  apply idweq.
Defined.


Definition apply_on_chain (F : functor) (chain : Chain) :=
  build_chain (λ n, F.0 (chain_types chain n))
              (λ n, F.1 (chain_functions chain n)).

Lemma weq_polynomial_functor_on_limit
      (A : UU) (B : A -> UU) (chain : Chain) :
  let P := polynomial_functor A B in
  P.0 (limit chain) ≃ limit (apply_on_chain P chain).
Proof.
  induction chain as [X π]; unfold apply_on_chain; cbn;
    unfold polynomial_functor_on_maps, polynomial_functor_on_types, limit; cbn.
  intermediate_weq (∑ a : A,
                    ∑ x : B a -> ∏ n, X n,
                          ∏ b n, π n (x b (1 + n)) = x b n). {
    apply weq_functor_total2_id; intros a.
    use func_total2_distributivity.
  }
  intermediate_weq (∑ a : A,
                    ∑ x : ∏ n, B a -> X n,
                          ∏ n b, π n (x (1 + n) b) = x n b). {
    apply weq_functor_total2_id; intros a.
    use weq_functor_total2.
    - apply sec_symmetry.
    - cbn. intros x.
      use sec_symmetry.
  }
  intermediate_weq (∑ a,
                    ∑ x : ∏ n, B a → X n,
                          ∏ n : nat, π n ∘ x (S n) = x n). {
    apply weq_functor_total2_id; intros a.
    apply weq_functor_total2_id; intros x.
    apply weq_functor_sec_id; intros n.
    apply invweq.
    apply weqtoforallpaths.
  }
  intermediate_weq (∑ ap : ∑ a : nat -> A, ∏ n, a (1 + n) = a n,
                    ∑ x  : ∏ n, B (pr1 ap n) -> X n,
                           ∏ n, transportf (λ a, B a -> X n)
                                           (pr2 ap n)
                                           (π n ∘ x (1 + n))
                                = x n). {
    use weq_functor_total2.
    - apply invweq.
      apply weq_cochain_limit_simpl.
    - cbn. intros a.
      apply idweq.
  }
  intermediate_weq (∑ a : nat -> A,
                    ∑ p : ∏ n, a (1 + n) = a n,
                    ∑ x : ∏ n, B (a n) -> X n,
                          ∏ n, transportf (λ a, B a -> X n)
                                          (p n)
                                          (π n ∘ x (1 + n))
                               = x n). {
    apply invweq.
    apply invweq.
    apply total2_associativity.
  }
  intermediate_weq (∑ a : nat -> A,
                    ∑ x : ∏ n, B (a n) -> X n,
                    ∑ p : ∏ n, a (1 + n) = a n,
                          ∏ n, transportf (λ a, B a -> X n)
                                          (p n)
                                          (π n ∘ x (1 + n))
                               = x n). {
    apply weq_functor_total2_id; intros a.
    apply total2_symmetry.
  }
  intermediate_weq (∑ a : nat -> A,
                    ∑ x : ∏ n, B (a n) -> X n,
                          ∏ n, ∑ p : a (1 + n) = a n,
                                     transportf (λ a, B a -> X n)
                                                p
                                                (π n ∘ x (1 + n))
                                     = x n). {
    apply weq_functor_total2_id; intros a.
    apply weq_functor_total2_id; intros x.
    apply invweq.
    apply sec_total2_distributivity.
  }
  intermediate_weq (∑ a : nat -> A,
                    ∑ x : ∏ n, B (a n) -> X n,
                          ∏ n, tpair (λ a, B a -> X n)
                                     (a (1 + n))
                                     (π n ∘ x (1 + n))
                               = tpair (λ a, B a -> X n)
                                       (a n)
                                       (x n)). {
    apply weq_functor_total2_id; intros a.
    apply weq_functor_total2_id; intros x.
    apply weq_functor_sec_id; intros n.
    use weq_total2_paths_f.
  }
  intermediate_weq (∑ x : ∑ a : nat -> A, ∏ n, B (a n) → X n,
                                ∏ n : nat, tpair (λ a, B a -> X n)
                                               (pr1 x (1 + n))
                                               (π n ∘ pr2 x (1 + n))
                                         = tpair (λ a, B a -> X n)
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


Section M_From_Nat.

  Variable A : UU.
  Variable B : A -> UU.
  Definition P := polynomial_functor A B.
  Opaque P.

  Definition W : nat -> UU.
  Proof.
    intros n; induction n.
    - exact unit.
    - exact (P.0 IHn).
  Defined.

  Definition π : ∏ n, W (1 + n) -> W n.
  Proof.
    intros n; induction n.
    - exact (λ _, tt).
    - exact (P.1 IHn).
  Defined.

  Definition chain := build_chain W π.

  Definition m_type := limit chain.

  Definition m_in : P.0 m_type ≃ m_type :=
    weqcomp (weq_polynomial_functor_on_limit A B chain)
            (weq_limit_shift chain).
  Opaque m_in.

  Definition m_out : coalgebra_structure P m_type := invweq m_in.

  Definition m_coalgebra : coalgebra P := m_type,, m_out.

  Lemma m_coalgebra_is_final : is_final_coalgebra m_coalgebra.
  Proof.
    unfold is_final_coalgebra.
    intros coalgebra; induction coalgebra as [C γ].
    apply iscontrifweqtounit.
    intermediate_weq (∑ f, m_out ∘ f = P.1 f ∘ γ). {
      apply idweq.
    }
    intermediate_weq (∑ f, m_in ∘ m_out ∘ f = m_in ∘ P.1 f ∘ γ). {
      apply weq_functor_total2_id; intros f.
      apply (weqonpaths (weq_comp_l m_in)).
    }
    set (Ψ f := m_in ∘ P.1 f ∘ γ :
                  C -> m_type).
    intermediate_weq (∑ f, f = Ψ f). {
      apply weq_functor_total2_id; intros f.
      apply weq_comp0_l.
      apply funextfun; intros c.
      apply pathsinv0.
      exact (homotweqinvweq m_in (f c)).
    }
    set (Cone := Cone chain C).
    set (e := invweq (universal_property_of_limit chain C) :
                Cone ≃ (C -> m_type)).
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
    set (Cone0' n := C -> W n).
    set (Cone0 := ∏ n, Cone0' n).
    set (Cone1' (u : Cone0) n := π n ∘ u (1 + n) = u n).
    set (Cone1 (u : Cone0) := ∏ n, Cone1' u n).
    assert (Cone = (∑ u : Cone0, Cone1 u)) by reflexivity.
    intermediate_weq (∑ u : Cone0, ∑ q : Cone1 u, u,, q = Φ (u,, q)). {
      apply total2_associativity.
    }
    set (Φ0' (n : nat) (un : Cone0' n) := P.1 un ∘ γ).
    set (Φ0 (u : Cone0) n c :=
           nat_rect (λ n, W n)
                    (tt)
                    (λ n _, Φ0' n (u n) c)
                    n).
    set (Φ1' (u : Cone0) (n : nat) (pn : Cone1' u n) (c : C) :=
           @total2_paths_f _ _ (P.1 (π n ∘ u (S n)) (γ c)) (P.1 (u n) (γ c))
                           (idpath _)
                           (funextfun (π n ∘ u (S n) ∘ pr2 (γ c))
                                      (u n ∘ pr2 (γ c))
                                      (toforallpaths _ (π n ∘ u (S n)) (u n) pn ∘
                                       pr2 (γ c)))).
    set (Φ1 (u : Cone0) (p : Cone1 u) (n : nat) :=
           funextfun (π n ∘ P.1 (u n) ∘ γ) (Φ0 u n)
                     (λ c : C,
                            nat_rect (λ n', (π n' ∘ P.1 (u n') ∘ γ) c = Φ0 u n' c)
                                     (idpath tt)
                                     (λ n' _, Φ1' u n' (p n') c)
                                     n)).
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
          apply impred_isaprop; intros c.
          apply isapropunit.
        }
        intermediate_weq (C -> W 0). {
          unfold Φ0; cbn.
          apply (weq_cochain_limit Cone0' (λ n un, Φ0' n un)).
        }
        apply weqcontrtounit.
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
                                ∏ n, q n = transportb (λ u, Cone1' u n) p (Φ1 u q n)). {
          apply weq_functor_total2_id; intros q.
          apply weq_functor_sec_id; intros n.
          apply weq_comp0_r.
          apply (weqtoforallpaths _ _ _ (transportb_sec_constant Cone1' p (Φ1 u q)) n).
        }
        intermediate_weq (∑ q : Cone1 u,
                                q 0 = transportb (λ u, Cone1' u 0) p (Φ1 u q 0) ×
                                ∏ n, q (S n) =
                                     transportb (λ u, Cone1' u (S n)) p (Φ1 u q (S n))). {
          apply weq_functor_total2_id; intros q.
          apply invweq.
          use weq_sequence_cons.
        }
        intermediate_weq (∑ q : Cone1 u,
                                ∏ n, q (S n) =
                                     transportb (λ u, Cone1' u (S n)) p (Φ1 u q (S n))). {
          apply weq_functor_total2_id; intros q.
          apply weq_prod_contr_l.
          apply impred_isaset; intros c.
          apply isasetunit.
        }
        intermediate_weq (Cone1' u 0). {
          unfold Φ1.
          apply (weq_cochain_limit (λ n, π n ∘ u (S n) = u n)
                                   (λ n pn, transportb (λ u, Cone1' u (S n)) p
                                                       (funextfun _ _ (Φ1' u n pn)))).
        }
        apply weqcontrtounit.
        apply impred_isaprop; intros c.
        apply isapropunit.
    }
    apply weqtotal2overunit.
  Defined.

End M_From_Nat.
