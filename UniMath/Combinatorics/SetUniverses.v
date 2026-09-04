(**

 Universes of sets

 A universe of sets is given by a set `u` together with a map that assigns to each
 member of `u` a set. One can require various closure conditions, like closure under
 ∑-types and ∏-types, and then this notion gives us a type theoretic universe in the
 set model of extensional type theory. In this file, we give some basic notions for
 universes of sets.

 While the type `hSet` of sets is not a set itself, there are various alternative
 constructions in homotopy type theory that allows one to construct an actual universe
 of sets that is a set itself. These constructions are iterative sets and induction
 recursion. Note that induction-recursion requires one to assume a class of inductive
 types that are not supported by Rocq, one can construct the type of iterative sets
 solely by using W-types.

 Content
 1. Basis definition
 2. Equality of codes
 3. Closure under type formers
 3.1. Unit type
 3.2. Natural numbers
 3.3. The type of propositions
 3.4. Resizing
 3.5. ∑-types
 3.6. ∏-types
 4. Topos universes

 *)
Require Import UniMath.MoreFoundations.All.

(** * 1. Basis definition *)
Definition set_universe : UU := ∑ (u : hSet), u → hSet.

Coercion set_universe_to_universe (u : set_universe) : hSet := pr1 u.

Definition set_universe_el {u : set_universe} (a : u) : hSet := pr2 u a.

(** * 2. Equality of codes *)
Definition set_universe_eq
           {u : set_universe}
           {a₁ a₂ : u}
           (p : a₁ = a₂)
           (x : set_universe_el a₁)
  : set_universe_el a₂.
Proof.
  induction p.
  exact x.
Defined.

Proposition transportf_set_universe_el
           {u : set_universe}
           {a₁ a₂ : u}
           (p : a₁ = a₂)
           (x : set_universe_el a₁)
  : transportf (@set_universe_el u) p x = set_universe_eq p x.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition set_universe_eq_idpath
            {u : set_universe}
            {a : u}
            (p : a = a)
            (x : set_universe_el a)
  : set_universe_eq p x = x.
Proof.
  assert (p = idpath _) as ->.
  {
    apply setproperty.
  }
  cbn.
  apply idpath.
Qed.

Proposition set_universe_eq_comp
            {u : set_universe}
            {a₁ a₂ a₃ : u}
            (p : a₁ = a₂)
            (q : a₂ = a₃)
            (x : set_universe_el a₁)
  : set_universe_eq q (set_universe_eq p x) = set_universe_eq (p @ q) x.
Proof.
  induction p, q.
  cbn.
  apply idpath.
Qed.

Proposition set_universe_eq_path
            {u : set_universe}
            {a₁ a₂ : u}
            (p q : a₁ = a₂)
            (x : set_universe_el a₁)
  : set_universe_eq p x = set_universe_eq q x.
Proof.
  assert (p = q) as ->.
  {
    apply setproperty.
  }
  apply idpath.
Qed.

Proposition set_universe_eq_path'
            {u : set_universe}
            {a₁ a₂ : u}
            (p q : a₁ = a₂)
            {x₁ x₂ : set_universe_el a₁}
            (r : x₁ = x₂)
  : set_universe_eq p x₁ = set_universe_eq q x₂.
Proof.
  induction r.
  apply set_universe_eq_path.
Qed.

Definition set_universe_eq_weq
           {u : set_universe}
           {a₁ a₂ : u}
           (p : a₁ = a₂)
  : set_universe_el a₁ ≃ set_universe_el a₂.
Proof.
  use weq_iso.
  - exact (set_universe_eq p).
  - exact (set_universe_eq (!p)).
  - abstract
      (intro z ;
       rewrite set_universe_eq_comp ;
       apply set_universe_eq_idpath).
  - abstract
      (intro z ;
       rewrite set_universe_eq_comp ;
       apply set_universe_eq_idpath).
Defined.

(** * 3. Closure under type formers *)

(** * 3.1. Unit type *)
Definition set_universe_contains_unit
           (u : set_universe)
  : UU
  := ∑ (un : u), set_universe_el un ≃ unit.

Definition make_set_universe_contains_unit
           (u : set_universe)
           (un : u)
           (f : set_universe_el un ≃ unit)
  : set_universe_contains_unit u
  := un ,, f.

Definition set_universe_unit_code
           {u : set_universe}
           (un : set_universe_contains_unit u)
  : u
  := pr1 un.

Definition set_universe_unit_weq
           {u : set_universe}
           (un : set_universe_contains_unit u)
  : set_universe_el (set_universe_unit_code un) ≃ unit
  := pr2 un.

(** * 3.2. Natural numbers *)
Definition set_universe_contains_nat
           (u : set_universe)
  : UU
  := ∑ (n : u), set_universe_el n ≃ ℕ.

Definition make_set_universe_contains_nat
           (u : set_universe)
           (n : u)
           (f : set_universe_el n ≃ ℕ)
  : set_universe_contains_nat u
  := n ,, f.

Definition set_universe_nat_code
           {u : set_universe}
           (n : set_universe_contains_nat u)
  : u
  := pr1 n.

Definition set_universe_nat_weq
           {u : set_universe}
           (n : set_universe_contains_nat u)
  : set_universe_el (set_universe_nat_code n) ≃ ℕ
  := pr2 n.

(** * 3.3. The type of propositions *)
Definition set_universe_contains_hProp
           (u : set_universe)
  : UU
  := ∑ (ω : u), set_universe_el ω ≃ hProp.

Definition make_set_universe_contains_hProp
           (u : set_universe)
           (ω : u)
           (f : set_universe_el ω ≃ hProp)
  : set_universe_contains_hProp u
  := ω ,, f.

Definition set_universe_hProp_code
           {u : set_universe}
           (ω : set_universe_contains_hProp u)
  : u
  := pr1 ω.

Definition set_universe_hProp_weq
           {u : set_universe}
           (ω : set_universe_contains_hProp u)
  : set_universe_el (set_universe_hProp_code ω) ≃ hProp
  := pr2 ω.

(** * 3.4. Resizing *)
Definition set_universe_resizing
           (u : set_universe)
  : UU
  := ∏ (A : hProp), ∑ (a : u), set_universe_el a ≃ A.

Definition make_set_universe_contains_resizing
           (u : set_universe)
           (resize : hProp → u)
           (f : ∏ (A : hProp), set_universe_el (resize A) ≃ A)
  : set_universe_resizing u
  := λ A, resize A ,, f A.

Definition set_universe_resizing_code
           {u : set_universe}
           (r : set_universe_resizing u)
           (A : hProp)
  : u
  := pr1 (r A).

Definition set_universe_resizing_code'
           {u : set_universe}
           (r : set_universe_resizing u)
           (A : UU)
           (HA : isaprop A)
  : u
  := set_universe_resizing_code r (make_hProp A HA).

Definition set_universe_resizing_weq
           {u : set_universe}
           (r : set_universe_resizing u)
           (A : hProp)
  : set_universe_el (set_universe_resizing_code r A) ≃ A
  := pr2 (r A).

Definition set_universe_resizing_weq'
           {u : set_universe}
           (r : set_universe_resizing u)
           (A : UU)
           (HA : isaprop A)
  : set_universe_el (set_universe_resizing_code' r A HA) ≃ A
  := set_universe_resizing_weq r (make_hProp A HA).

Proposition set_universe_resizing_code_eq
            {u : set_universe}
            (r : set_universe_resizing u)
            (A : UU)
            (HA HA' : isaprop A)
  : set_universe_resizing_code' r A HA = set_universe_resizing_code' r A HA'.
Proof.
  assert (HA = HA') as ->.
  {
    apply isapropisaprop.
  }
  apply idpath.
Qed.

Definition set_universe_resizing_contains_unit
           {u : set_universe}
           (r : set_universe_resizing u)
  : set_universe_contains_unit u.
Proof.
  use make_set_universe_contains_unit.
  - exact (set_universe_resizing_code r htrue).
  - exact (set_universe_resizing_weq r htrue).
Defined.

(** * 3.5. ∑-types *)
Definition set_universe_contains_sigma
           (u : set_universe)
  : UU
  := ∏ (a : u)
       (b : set_universe_el a → u),
     ∑ (sig : u),
     set_universe_el sig ≃ ∑ (x : set_universe_el a), set_universe_el (b x).

Definition make_set_universe_contains_sigma
           (u : set_universe)
           (sig : ∏ (a : u), (set_universe_el a → u) → u)
           (f : ∏ (a : u) (b : set_universe_el a → u),
                set_universe_el (sig a b)
                ≃
                ∑ (x : set_universe_el a), set_universe_el (b x))
  : set_universe_contains_sigma u
  := λ a b, sig a b ,, f a b.

Definition set_universe_sigma_code
           {u : set_universe}
           (sig : set_universe_contains_sigma u)
           (a : u)
           (b : set_universe_el a → u)
  : u
  := pr1 (sig a b).

Definition set_universe_sigma_weq
           {u : set_universe}
           (sig : set_universe_contains_sigma u)
           (a : u)
           (b : set_universe_el a → u)
  : set_universe_el (set_universe_sigma_code sig a b)
    ≃
    ∑ (x : set_universe_el a), set_universe_el (b x)
  := pr2 (sig a b).

Proposition set_universe_sigma_code_eq
            {u : set_universe}
            (sig : set_universe_contains_sigma u)
            {a₁ a₂ : u}
            (p : a₁ = a₂)
            {b₁ : set_universe_el a₁ → u}
            {b₂ : set_universe_el a₂ → u}
            (q : ∏ (x : set_universe_el a₁), b₁ x = b₂ (set_universe_eq p x))
  : set_universe_sigma_code sig a₁ b₁ = set_universe_sigma_code sig a₂ b₂.
Proof.
  induction p.
  apply maponpaths.
  use funextsec.
  intro x.
  exact (q x).
Qed.

Proposition set_universe_sigma_weq_eq_path
            {u : set_universe}
            (sig : set_universe_contains_sigma u)
            {a₁ a₂ : u}
            (p : a₁ = a₂)
            {b₁ : set_universe_el a₁ → u}
            {b₂ : set_universe_el a₂ → u}
            (q : ∏ (x : set_universe_el a₁), b₁ x = b₂ (set_universe_eq p x))
            (z : set_universe_el (set_universe_sigma_code sig a₁ b₁))
            (z' := set_universe_sigma_weq sig
                     a₂ b₂
                     (set_universe_eq (set_universe_sigma_code_eq sig p q) z))
  : b₂ (pr1 z') = b₁ (set_universe_eq (! p) (pr1 z')).
Proof.
  unfold z'.
  refine (_ @ !(q _)).
  apply maponpaths.
  rewrite set_universe_eq_comp.
  rewrite set_universe_eq_idpath.
  apply idpath.
Qed.

Proposition set_universe_sigma_weq_eq
            {u : set_universe}
            (sig : set_universe_contains_sigma u)
            {a₁ a₂ : u}
            (p : a₁ = a₂)
            {b₁ : set_universe_el a₁ → u}
            {b₂ : set_universe_el a₂ → u}
            (q : ∏ (x : set_universe_el a₁), b₁ x = b₂ (set_universe_eq p x))
            (z : set_universe_el (set_universe_sigma_code sig a₁ b₁))
            (z' := set_universe_sigma_weq sig
                     a₂ b₂
                     (set_universe_eq (set_universe_sigma_code_eq sig p q) z))
  : set_universe_sigma_weq sig a₁ b₁ z
    =
    set_universe_eq
      (!p)
      (pr1 z')
    ,,
    set_universe_eq
      (set_universe_sigma_weq_eq_path sig p q z)
      (pr2 z').
Proof.
  unfold z' ; clear z'.
  induction p.
  assert (b₁ = b₂) as r.
  {
    use funextsec.
    exact q.
  }
  induction r ; cbn.
  use total2_paths_f.
  - cbn.
    rewrite set_universe_eq_idpath.
    apply idpath.
  - cbn.
    rewrite (functtransportf b₁ set_universe_el).
    rewrite transportf_set_universe_el.
    rewrite set_universe_eq_idpath.
    generalize (set_universe_sigma_code_eq sig (idpath a₁) q).
    intro p.
    assert (p = idpath _) as ->.
    {
      apply setproperty.
    }
    cbn.
    rewrite set_universe_eq_idpath.
    apply idpath.
Qed.

Definition set_universe_sigma_weq_eq_on_el
           {u : set_universe}
           (sig : set_universe_contains_sigma u)
           (a : u)
           (b : set_universe_el a → u)
           {z₁ z₂ : set_universe_el (set_universe_sigma_code sig a b)}
           (p : z₁ = z₂)
  : pr2 (set_universe_sigma_weq sig a b z₁)
    =
    set_universe_eq
      (maponpaths (λ x, b (pr1 (set_universe_sigma_weq sig a b x))) (!p))
      (pr2 (set_universe_sigma_weq sig a b z₂)).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Definition set_universe_sigma_el_eq
           {u : set_universe}
           {a : u}
           {b : set_universe_el a → u}
           {xy₁ xy₂ : ∑ (x : set_universe_el a), set_universe_el (b x)}
           (p : pr1 xy₁ = pr1 xy₂)
           (q : pr2 xy₁ = set_universe_eq (maponpaths b (!p)) (pr2 xy₂))
  : xy₁ = xy₂.
Proof.
  induction xy₁ as [ x₁ y₁ ].
  induction xy₂ as [ x₂ y₂ ].
  cbn in p.
  induction p.
  cbn in q.
  apply maponpaths.
  exact q.
Qed.

(** * 3.6. ∏-types *)
Definition set_universe_contains_pi
           (u : set_universe)
  : UU
  := ∏ (a : u)
       (b : set_universe_el a → u),
     ∑ (pi : u),
     set_universe_el pi ≃ ∏ (x : set_universe_el a), set_universe_el (b x).

Definition make_set_universe_contains_pi
           (u : set_universe)
           (pi : ∏ (a : u), (set_universe_el a → u) → u)
           (f : ∏ (a : u) (b : set_universe_el a → u),
                set_universe_el (pi a b)
                ≃
                ∏ (x : set_universe_el a), set_universe_el (b x))
  : set_universe_contains_pi u
  := λ a b, pi a b ,, f a b.

Definition set_universe_pi_code
           {u : set_universe}
           (pi : set_universe_contains_pi u)
           (a : u)
           (b : set_universe_el a → u)
  : u
  := pr1 (pi a b).

Definition set_universe_pi_weq
           {u : set_universe}
           (pi : set_universe_contains_pi u)
           (a : u)
           (b : set_universe_el a → u)
  : set_universe_el (set_universe_pi_code pi a b)
    ≃
    ∏ (x : set_universe_el a), set_universe_el (b x)
  := pr2 (pi a b).

Proposition set_universe_pi_code_eq
            {u : set_universe}
            (pi : set_universe_contains_pi u)
            {a₁ a₂ : u}
            (p : a₁ = a₂)
            {b₁ : set_universe_el a₁ → u}
            {b₂ : set_universe_el a₂ → u}
            (q : ∏ (x : set_universe_el a₁), b₁ x = b₂ (set_universe_eq p x))
  : set_universe_pi_code pi a₁ b₁ = set_universe_pi_code pi a₂ b₂.
Proof.
  induction p.
  apply maponpaths.
  use funextsec.
  intro x.
  exact (q x).
Qed.

Proposition set_universe_pi_weq_eq
            {u : set_universe}
            (pi : set_universe_contains_pi u)
            {a₁ a₂ : u}
            (p : a₁ = a₂)
            {b₁ : set_universe_el a₁ → u}
            {b₂ : set_universe_el a₂ → u}
            (q : ∏ (x : set_universe_el a₁), b₁ x = b₂ (set_universe_eq p x))
            (z : set_universe_el (set_universe_pi_code pi a₁ b₁))
  : set_universe_pi_weq pi a₁ b₁ z
    =
    λ x,
    set_universe_eq
      (!(q x))
      (set_universe_pi_weq
         pi
         a₂ b₂
         (set_universe_eq (set_universe_pi_code_eq pi p q) z)
         (set_universe_eq p x)).
Proof.
  induction p.
  assert (b₁ = b₂) as r.
  {
    use funextsec.
    exact q.
  }
  induction r.
  use funextsec.
  intro x.
  cbn.
  rewrite !set_universe_eq_idpath.
  apply idpath.
Qed.

Proposition set_universe_pi_weq_eq_el
            {u : set_universe}
            (pi : set_universe_contains_pi u)
            (a : u)
            (b : set_universe_el a → u)
            {z₁ z₂ : set_universe_el (set_universe_pi_code pi a b)}
            (p : z₁ = z₂)
            {x₁ x₂ : set_universe_el a}
            (q : x₁ = x₂)
  : set_universe_pi_weq pi a b z₁ x₁
    =
    set_universe_eq (!(maponpaths b q)) (set_universe_pi_weq pi a b z₂ x₂).
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

(** * 4. Topos universes *)
Definition set_universe_topos
  : UU
  := ∑ (u : set_universe),
     set_universe_contains_nat u
     ×
     set_universe_contains_hProp u
     ×
     set_universe_resizing u
     ×
     set_universe_contains_sigma u
     ×
     set_universe_contains_pi u.

Coercion set_universe_topos_to_univ
         (u : set_universe_topos)
  : set_universe
  := pr1 u.

Coercion set_universe_topos_contains_nat
         (u : set_universe_topos)
  : set_universe_contains_nat u
  := pr12 u.

Coercion set_universe_topos_contains_hProp
         (u : set_universe_topos)
  : set_universe_contains_hProp u
  := pr122 u.

Coercion set_universe_topos_resizing
         (u : set_universe_topos)
  : set_universe_resizing u
  := pr1 (pr222 u).

Coercion set_universe_topos_contains_sigma
         (u : set_universe_topos)
  : set_universe_contains_sigma u
  := pr12 (pr222 u).

Coercion set_universe_topos_contains_pi
         (u : set_universe_topos)
  : set_universe_contains_pi u
  := pr22 (pr222 u).
