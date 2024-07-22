(********************************************************************************************

 Partial equivalence relations in a first-order hyperdoctrine

 To construct a topos from a tripos, we look at the category of partial equivalence relations.
 This generalizes several constructions in topos theory, such as the construction of
 realizability toposes (partial equivalence relations valued in partial combinatory algebras)
 and localic toposes (sets with a partial equivalence relation valued in a complete Heyting
 algebra). In this file, we define the notion of partial equivalence relation in first-order
 hyperdoctrines. Note that we use the terminology 'partial equivalence relation to denote
 a relation and the terminology 'partial setoid' to denote a type equipped with a partial
 equivalence relation. In the paper "Tripos Theory in Retrospect" by Andrew Pitts only the
 terminology partial equivalence relation is used (Definition 3.1) and it agrees with our
 usage. However, the word 'partial setoids' is not used

 To do so, we work in the internal language. The internal language of a first-order
 hyperdoctrine is implemented via a shallow embedding. Variable names are represented via
 De Bruijn indies, and the laws for substitution are represented via propositional equalities.
 As a consequence, goals can easily become very unreadable.

 However, there are some tricks that we can use to obtain more readable goals. These are
 discussed in more detail and using an example in the proof of [eq_per_axioms]. The limitations
 of this method are discussed as well.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Partial equivalence relations
 2. Partial setoids
 3. Every type is a partial setoid with equality
 4. The product of partial setoids

 ********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.FirstOrderHyperdoctrine.

Local Open Scope cat.
Local Open Scope hd.

Section PartialEquivalenceRelation.
  Context {H : first_order_hyperdoctrine}.

  (** * 1. Partial equivalence relations *)
  Definition per_data
             (X : ty H)
    : UU
    := form (X ×h X).

  (**
     Symmetry and transitivity are expressed via the internal language
   *)
  Definition per_symm_axiom
             {X : ty H}
             (e : per_data X)
    : UU
    := let x := π₂ (π₁ (tm_var _)) : tm ((𝟙 ×h X) ×h X) X in
       let y := π₂ (tm_var _) : tm ((𝟙 ×h X) ×h X) X in
       ⊤ ⊢ (∀h ∀h (e [ ⟨ x , y ⟩ ] ⇒ e [ ⟨ y , x ⟩ ])).

  Definition per_trans_axiom
             {X : ty H}
             (e : per_data X)
    : UU
    := let x := π₂ (π₁ (π₁ (tm_var _))) : tm (((𝟙 ×h X) ×h X) ×h X) X in
       let y := π₂ (π₁ (tm_var _)) : tm (((𝟙 ×h X) ×h X) ×h X) X in
       let z := π₂ (tm_var _) : tm (((𝟙 ×h X) ×h X) ×h X) X in
       ⊤ ⊢ (∀h ∀h ∀h (e [ ⟨ x , y ⟩ ] ⇒ e [ ⟨ y , z ⟩ ] ⇒ e [ ⟨ x , z ⟩ ])).

  Definition per_axioms
             {X : ty H}
             (e : per_data X)
    : UU
    := per_symm_axiom e × per_trans_axiom e.

  Definition per
             (X : ty H)
    : UU
    := ∑ (e : per_data X), per_axioms e.

  Coercion per_to_data
           {X : ty H}
           (e : per X)
    : form (X ×h X).
  Proof.
    exact (pr1 e).
  Defined.

  (**
     We want to have nice accessors for symmetry and transitivity.
     However, while the statements in the internal language accurately
     represent symmetry and transitivity, they are not easy to use.
     For this reason, the accessors of symmetry and transitivity are
     modified. In these accessors elimination rules for the universal
     quantifier and implication are already used, and suitable weakenings
     are applied. This makes it possible to use symmetry and transitivity
     more directly.
   *)
  Proposition per_sym
              {X : ty H}
              {e : per X}
              {Γ : ty H}
              {Δ : form Γ}
              {s : tm Γ (X ×h X)}
              (p : Δ ⊢ e [ ⟨ π₂ s , π₁ s ⟩ ])
    : Δ ⊢ e [ s ].
  Proof.
    pose proof (pr12 e) as q.
    unfold per_symm_axiom in q.
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) q) as q'.
    clear q.
    rewrite truth_subst in q'.
    rewrite !forall_subst in q'.
    rewrite impl_subst in q'.
    rewrite !hyperdoctrine_comp_subst in q'.
    rewrite !hyperdoctrine_pair_subst in q'.
    pose proof (forall_elim q' (π₂ s)) as r.
    clear q'.
    rewrite !forall_subst in r.
    rewrite impl_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose proof (forall_elim r (π₁ s)) as r'.
    clear r.
    rewrite impl_subst in r'.
    rewrite !hyperdoctrine_comp_subst in r'.
    rewrite !hyperdoctrine_pair_subst in r'.
    rewrite !hyperdoctrine_pr2_subst in r'.
    rewrite !var_tm_subst in r'.
    rewrite !tm_subst_comp in r'.
    rewrite !hyperdoctrine_pr1_subst in r'.
    rewrite !var_tm_subst in r'.
    rewrite hyperdoctrine_pair_pr1 in r'.
    rewrite tm_subst_var in r'.
    rewrite hyperdoctrine_pair_pr2 in r'.
    pose proof (weaken_to_empty r' : Δ ⊢ _) as r''.
    clear r'.
    pose proof (impl_elim p r'') as r'''.
    clear r''.
    rewrite (hyperdoctrine_pair_eta s).
    exact r'''.
  Qed.

  Proposition per_trans
              {X : ty H}
              {e : per X}
              {Γ : ty H}
              {Δ : form Γ}
              {s : tm Γ (X ×h X)}
              (t : tm Γ X)
              (p : Δ ⊢ e [ ⟨ π₁ s , t ⟩ ])
              (q : Δ ⊢ e [ ⟨ t , π₂ s ⟩ ])
    : Δ ⊢ e [ s ].
  Proof.
    pose proof (pr22 e) as r₁.
    cbn in r₁.
    unfold per_trans_axiom in r₁.
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) r₁) as r₂.
    clear r₁.
    rewrite truth_subst in r₂.
    rewrite !forall_subst in r₂.
    rewrite !impl_subst in r₂.
    rewrite !hyperdoctrine_comp_subst in r₂.
    rewrite !hyperdoctrine_pair_subst in r₂.
    rewrite !hyperdoctrine_pr2_subst in r₂.
    rewrite !hyperdoctrine_pr1_subst in r₂.
    rewrite !var_tm_subst in r₂.
    rewrite hyperdoctrine_pair_pr2 in r₂.
    rewrite !hyperdoctrine_pair_pr1 in r₂.
    rewrite !hyperdoctrine_pair_pr2 in r₂.
    pose proof (forall_elim r₂ (π₁ s)) as r₃.
    clear r₂.
    rewrite !forall_subst in r₃.
    rewrite !impl_subst in r₃.
    rewrite !hyperdoctrine_comp_subst in r₃.
    rewrite !hyperdoctrine_pair_subst in r₃.
    rewrite !hyperdoctrine_pr2_subst in r₃.
    rewrite !hyperdoctrine_pr1_subst in r₃.
    rewrite !var_tm_subst in r₃.
    rewrite !hyperdoctrine_pr1_subst in r₃.
    rewrite hyperdoctrine_pair_pr2 in r₃.
    rewrite !hyperdoctrine_pair_pr1 in r₃.
    rewrite !hyperdoctrine_pair_pr2 in r₃.
    rewrite !var_tm_subst in r₃.
    rewrite !hyperdoctrine_pair_pr1 in r₃.
    pose proof (forall_elim r₃ t) as r₄.
    clear r₃.
    rewrite !forall_subst in r₄.
    rewrite !impl_subst in r₄.
    rewrite !hyperdoctrine_comp_subst in r₄.
    rewrite !hyperdoctrine_pair_subst in r₄.
    rewrite !hyperdoctrine_pr2_subst in r₄.
    rewrite !hyperdoctrine_pr1_subst in r₄.
    rewrite !var_tm_subst in r₄.
    rewrite hyperdoctrine_pair_pr2 in r₄.
    rewrite !hyperdoctrine_pair_pr1 in r₄.
    rewrite !hyperdoctrine_pair_pr2 in r₄.
    rewrite !hyperdoctrine_pair_subst in r₄.
    rewrite !hyperdoctrine_pair_pr2 in r₄.
    rewrite !hyperdoctrine_pr1_subst in r₄.
    rewrite !tm_subst_comp in r₄.
    rewrite !hyperdoctrine_pr1_subst in r₄.
    rewrite !var_tm_subst in r₄.
    rewrite !hyperdoctrine_pair_pr1 in r₄.
    pose proof (forall_elim r₄ (π₂ s)) as r₅.
    clear r₄.
    rewrite !impl_subst in r₅.
    rewrite !hyperdoctrine_comp_subst in r₅.
    rewrite !hyperdoctrine_pair_subst in r₅.
    rewrite !hyperdoctrine_pr2_subst in r₅.
    rewrite !hyperdoctrine_pr1_subst in r₅.
    rewrite !var_tm_subst in r₅.
    rewrite hyperdoctrine_pair_pr2 in r₅.
    rewrite !tm_subst_comp in r₅.
    rewrite !hyperdoctrine_pr1_subst in r₅.
    rewrite !var_tm_subst in r₅.
    rewrite !hyperdoctrine_pair_pr1 in r₅.
    rewrite !tm_subst_var in r₅.
    pose proof (weaken_to_empty r₅ : Δ ⊢ _) as r₆.
    clear r₅.
    pose proof (impl_elim p r₆) as r₇.
    clear r₆.
    pose proof (impl_elim q r₇) as r₈.
    clear r₇.
    rewrite (hyperdoctrine_pair_eta s).
    exact r₈.
  Qed.

  Definition make_per
             {X : ty H}
             (e : form (X ×h X))
             (He : per_axioms e)
    : per X
    := e ,, He.
End PartialEquivalenceRelation.

(** * 2. Partial setoids *)
Definition partial_setoid
           (H : first_order_hyperdoctrine)
  : UU
  := ∑ (X : ty H), per X.

Definition make_partial_setoid
           {H : first_order_hyperdoctrine}
           (X : ty H)
           (e : per X)
  : partial_setoid H
  := X ,, e.

Coercion partial_setoid_to_type
         {H : first_order_hyperdoctrine}
         (X : partial_setoid H)
  : ty H.
Proof.
  exact (pr1 X).
Defined.

Coercion partial_setoid_to_per
         {H : first_order_hyperdoctrine}
         (X : partial_setoid H)
  : per X.
Proof.
  exact (pr2 X).
Defined.

Definition partial_setoid_formula
           {H : first_order_hyperdoctrine}
           {X : partial_setoid H}
           {Γ : ty H}
           (x y : tm Γ X)
  : form Γ
  := X [ ⟨ x , y ⟩ ].

Notation "x ~ y" := (partial_setoid_formula x y) : hyperdoctrine.

Proposition partial_setoid_sym
            {H : first_order_hyperdoctrine}
            {X : partial_setoid H}
            {Γ : ty H}
            {Δ : form Γ}
            {x y : tm Γ X}
            (p : Δ ⊢ x ~ y)
  : Δ ⊢ y ~ x.
Proof.
  use per_sym.
  simplify.
  exact p.
Qed.

Proposition partial_setoid_trans
            {H : first_order_hyperdoctrine}
            {X : partial_setoid H}
            {Γ : ty H}
            {Δ : form Γ}
            {x : tm Γ X}
            (y : tm Γ X)
            {z : tm Γ X}
            (p : Δ ⊢ x ~ y)
            (q : Δ ⊢ y ~ z)
  : Δ ⊢ x ~ z.
Proof.
  use per_trans.
  - exact y.
  - simplify.
    exact p.
  - simplify.
    exact q.
Qed.

Proposition partial_setoid_refl_l
            {H : first_order_hyperdoctrine}
            {X : partial_setoid H}
            {Γ : ty H}
            {Δ : form Γ}
            {x y : tm Γ X}
            (p : Δ ⊢ x ~ y)
  : Δ ⊢ x ~ x.
Proof.
  use (partial_setoid_trans y p).
  use partial_setoid_sym.
  exact p.
Qed.

Proposition partial_setoid_refl_r
            {H : first_order_hyperdoctrine}
            {X : partial_setoid H}
            {Γ : ty H}
            {Δ : form Γ}
            {x y : tm Γ X}
            (p : Δ ⊢ x ~ y)
  : Δ ⊢ y ~ y.
Proof.
  use (partial_setoid_trans x _ p).
  use partial_setoid_sym.
  exact p.
Qed.

Proposition partial_setoid_subst
            {H : first_order_hyperdoctrine}
            {X : partial_setoid H}
            {Γ Γ' : ty H}
            (s : tm Γ Γ')
            (x y : tm Γ' X)
  : (x ~ y)[ s ] = (x [ s ]tm ~ y [ s ]tm).
Proof.
  unfold partial_setoid_formula.
  simplify.
  apply idpath.
Qed.

Section Constructions.
  Context {H : first_order_hyperdoctrine}.

  (** * 3. Every type is a partial setoid with equality *)
  Proposition eq_per_axioms (X : ty H)
    : per_axioms (π₁ (tm_var (X ×h X)) ≡ π₂ (tm_var (X ×h X))).
  Proof.
    split.
    - unfold per_symm_axiom.
      (**
         At this point, the goal is kinda hard to read. It is 5 lines long,
         and there are multiple substitutions in place that it hard to read.
         In addition, De Bruijn indices were never invented to improve the
         readability of formulas and terms. More specifically, the goal looks
         as follows
         ```
         ⊤
  ⊢ ∀h (∀h ((π₁ (tm_var (X ×h X)) ≡ π₂ (tm_var (X ×h X)))
            [⟨ π₂ (π₁ (tm_var ((𝟙 ×h X) ×h X))), π₂ (tm_var ((𝟙 ×h X) ×h X)) ⟩]
            ⇒ (π₁ (tm_var (X ×h X)) ≡ π₂ (tm_var (X ×h X)))
              [⟨ π₂ (tm_var ((𝟙 ×h X) ×h X)), π₂ (π₁ (tm_var ((𝟙 ×h X) ×h X))) ⟩]))
         ```

         First, we shall introduce some abbreviations for the variables that
         we use in the term. We are using two variables. The first one, which
         we call `x`, is represented by `π₂ (π₁ (tm_var _))`, and the second
         one, which we call `y`, by `π₂ (tm_var _)`. We want our goal to use
         these abbreviations instead of the full De Bruijn indices.

         To do so, we use the following commands. We pose the variables `x`
         and `y`, and then we use `fold` to make the goal use `x` and `y`
         instead of the De Bruijn indices.

         Note that in order to guarantee that Coq can actually type the
         terms `x` and `y`, we must give it enough information. For this
         reason, we also introduce the type `T`. This `T` is an abbreviation
         of the carrier of the partial equivalence relation that we are
         defining. The usage of this abbreviation `T` makes it easier to
         copy paste this code fragment in other situations where the type
         might be more complicated.
       *)
      pose (T := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T)))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T))).
      unfold T in *.
      fold x y.
      (**
         At this point, the goal has become a bit more readable, but it is
         still not readable enough. It looks as follows
         ```
         ⊤
  ⊢ ∀h (∀h ((π₁ (tm_var (X ×h X)) ≡ π₂ (tm_var (X ×h X))) [⟨ x, y ⟩]
            ⇒ (π₁ (tm_var (X ×h X)) ≡ π₂ (tm_var (X ×h X))) [⟨ y, x ⟩]))
         ```

         The problem is that there are numerous substitutions here that
         destroy the readability. To solve this problem, we must simplify
         the term by calculating the substitutions and possibly by doing
         some normalization. This process is fully mechanics: one
         repeatedly rewrites using the substitution laws. To automate this,
         we use the tactic `simplify`. This tactic does the following:
         - simplify substitutions of formulas and terms
         - simplify beta-redexes in terms
         Essentially, the resulting term consists of a bunch of `rewrites`
         that are possible in the term.
       *)
      simplify.
      (**
         Now the goal is as follows
         ```
         ⊤ ⊢ ∀h (∀h (x ≡ y ⇒ y ≡ x))
         ```
         This is readable if we keep in mind that `x` is the first
         variable over which we quantify and `y` is the second.

         To prove this goal, we following the usual procedure of
         applying introduction and elimination rules.
       *)
      use forall_intro.
      use forall_intro.
      use impl_intro.
      (**
         Now the goal is as follows
         ```
         (⊤ [π₁ (tm_var (𝟙 ×h X))]) [π₁ (tm_var ((𝟙 ×h X) ×h X))] ∧ x ≡ y ⊢ y ≡ x
         ```
         We could simplify the context. However, we don't need to
         the truth assumption. For this reason, we use weakining
         rules. Note that weakening is done by hand as well.
       *)
      use weaken_right.
      (**
         Now the goal is as follows
         ```
         x ≡ y ⊢ y ≡ x
         ```
         We proved symmetry before, so actually, nothing at all
         is happening in this proof. We just use symmetry now,
         and we finish it.
       *)
      use hyperdoctrine_eq_sym.
      (**
         Now the goal is as follows
         ```
         x ≡ y ⊢ x ≡ y
         ```
         We finish it by using the assumption rule.
       *)
      apply hyperdoctrine_hyp.
      (**
         For each of the statements that we prove using the
         internal language, we essentally use the same steps
         and the same ideas. We first introduce abbreviations
         for the De Bruijn indices that we are using. Then we
         use the `simplify` tactic to calculate substitutions
         and to normalize the term.

         There are a couple of limitations
         - The De Bruijn index of a variable changes if the
           context changes. For statements like `∀ x ∀ y, P x y`
           where `P` is a propositional formula depending on `x`
           and `y`, this is no problem, because the context is
           fixed in `P`. However, if we look at a statement like
           `∀ x ((∃ y, R x y) ⇒ P x)`, then the De Bruijn index
           of `x` is different in the two positions that it has.
           As such, for such formulas this method is less suitable.
         - The `simplify` tactic works by trying to rewrite
           equations if it is possible. This is fine for very small
           formulas and terms. However, when the goal becomes more
           complicated, `simplify` will become more inefficient.
           In this proof, the usage of `simplify` was quite fast
           (0.081 seconds). However, this is not the case for
           every proof that one might do. For instance, in the
           proof of [prod_per_axioms], we do not use `simplify`
           after introducing abbreviations for the variables,
           because it would take too long (0.447 seconds for
           symmetry and 0.938 seconds for transitivity). There
           we delay normalizing the terms after doing weakening.
           The comments show the simplified goals.
       *)
    - unfold per_trans_axiom.
      pose (T := X).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T) ×h T))))).
      pose (y := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T) ×h T)))).
      pose (z := π₂ (tm_var (((𝟙 ×h T) ×h T) ×h T))).
      unfold T in *.
      fold x y z.
      simplify.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use impl_intro.
      simplify.
      (**
         Here the goal is
         ```
         (⊤ ∧ x ≡ y) ∧ y ≡ z ⊢ x ≡ z
         ```
         This accurately represents transitivity of equality.
       *)
      use hyperdoctrine_eq_trans.
      + exact y.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Definition eq_per (X : ty H) : per X.
  Proof.
    use make_per.
    - exact (π₁ (tm_var _) ≡ π₂ (tm_var _)).
    - exact (eq_per_axioms X).
  Defined.

  Definition eq_partial_setoid (X : ty H) : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact X.
    - exact (eq_per X).
  Defined.

  Proposition eq_in_eq_partial_setoid
              {Γ X : ty H}
              {t₁ t₂ : tm Γ (eq_partial_setoid X)}
              {Δ : form Γ}
              (p : Δ ⊢ t₁ ≡ t₂)
    : Δ ⊢ t₁ ~ t₂.
  Proof.
    unfold partial_setoid_formula ; cbn.
    simplify.
    exact p.
  Qed.

  Proposition from_eq_in_eq_partial_setoid
              {Γ X : ty H}
              {t₁ t₂ : tm Γ (eq_partial_setoid X)}
              {Δ : form Γ}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ t₁ ≡ t₂.
  Proof.
    unfold partial_setoid_formula in p ; cbn in p.
    rewrite equal_subst in p.
    rewrite hyperdoctrine_pr1_subst in p.
    rewrite hyperdoctrine_pr2_subst in p.
    rewrite !var_tm_subst in p.
    rewrite hyperdoctrine_pair_pr1 in p.
    rewrite hyperdoctrine_pair_pr2 in p.
    exact p.
  Qed.

  (** * 4. The product of partial setoids *)
  Section ProdPartialSetoid.
    Context (X Y : partial_setoid H).

    Definition prod_per_data
      : form ((X ×h Y) ×h X ×h Y)
      := let x := π₁ (tm_var _) : tm ((X ×h Y) ×h X ×h Y) (X ×h Y) in
         let y := π₂ (tm_var _) : tm ((X ×h Y) ×h X ×h Y) (X ×h Y) in
         π₁ x ~ π₁ y ∧ π₂ x ~ π₂ y.

    Proposition prod_per_axioms
      : per_axioms prod_per_data.
    Proof.
    split.
    - unfold per_symm_axiom, prod_per_data.
      pose (T := X ×h Y).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T)))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T))).
      unfold T in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      (**
         Using `simplify` would give the following goal
         ```
         ⊤ ∧ eX [⟨ π₁ x, π₁ y ⟩] ∧ eY [⟨ π₂ x, π₂ y ⟩] ⊢ eX [⟨ π₁ y, π₁ x ⟩] ∧ eY [⟨ π₂ y, π₂ x ⟩]
         ```
         By delaying simplify the terms, we save some time
       *)
      simplify_form.
      rewrite !partial_setoid_subst.
      use conj_intro.
      + use partial_setoid_sym.
        use weaken_right.
        use weaken_left.
        simplify_term.
        apply hyperdoctrine_hyp.
      + use partial_setoid_sym.
        use weaken_right.
        use weaken_right.
        simplify_term.
        apply hyperdoctrine_hyp.
    - unfold per_trans_axiom, prod_per_data.
      pose (T := X ×h Y).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T) ×h T))))).
      pose (y := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T) ×h T)))).
      pose (z := π₂ (tm_var (((𝟙 ×h T) ×h T) ×h T))).
      unfold T in *.
      fold x y z.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use impl_intro.
      (**
         Using `simplify` would give the following goal
         ```
         (⊤ ∧ eX [⟨ π₁ x, π₁ y ⟩] ∧ eY [⟨ π₂ x, π₂ y ⟩]) ∧ eX [⟨ π₁ y, π₁ z ⟩] ∧ eY [⟨ π₂ y, π₂ z ⟩]
  ⊢ eX [⟨ π₁ x, π₁ z ⟩] ∧ eY [⟨ π₂ x, π₂ z ⟩]
         ````
         By delaying simplify the terms, we save some time
       *)
      simplify_form.
      rewrite !partial_setoid_subst.
      use conj_intro.
      + use (partial_setoid_trans (π₁ y)).
        * use weaken_left.
          use weaken_right.
          use weaken_left.
          simplify_term.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use weaken_left.
          simplify_term.
          apply hyperdoctrine_hyp.
      + use (partial_setoid_trans (π₂ y)).
        * use weaken_left.
          use weaken_right.
          use weaken_right.
          simplify_term.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use weaken_right.
          simplify_term.
          apply hyperdoctrine_hyp.
    Qed.

    Definition prod_per
      : per (X ×h Y).
    Proof.
      use make_per.
      - exact prod_per_data.
      - exact prod_per_axioms.
    Defined.

    Definition prod_partial_setoid
      : partial_setoid H.
    Proof.
      use make_partial_setoid.
      - exact (X ×h Y).
      - exact prod_per.
    Defined.

    Proposition eq_in_prod_partial_setoid
                {Γ : ty H}
                {t₁ t₂ : tm Γ prod_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ π₁ t₁ ~ π₁ t₂)
                (q : Δ ⊢ π₂ t₁ ~ π₂ t₂)
      : Δ ⊢ t₁ ~ t₂.
    Proof.
      unfold partial_setoid_formula ; cbn ; unfold prod_per_data.
      simplify.
      rewrite !partial_setoid_subst.
      simplify.
      use conj_intro.
      - exact p.
      - exact q.
    Qed.

    Proposition eq_in_prod_partial_setoid_l
                {Γ : ty H}
                {t₁ t₂ : tm Γ prod_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ t₁ ~ t₂)
      : Δ ⊢ π₁ t₁ ~ π₁ t₂.
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold partial_setoid_formula ; cbn ; unfold prod_per_data.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use weaken_left.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition eq_in_prod_partial_setoid_r
                {Γ : ty H}
                {t₁ t₂ : tm Γ prod_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ t₁ ~ t₂)
      : Δ ⊢ π₂ t₁ ~ π₂ t₂.
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold partial_setoid_formula ; cbn ; unfold prod_per_data.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use weaken_right.
      apply hyperdoctrine_hyp.
    Qed.
  End ProdPartialSetoid.
End Constructions.

Arguments prod_per_data {H} X Y /.
