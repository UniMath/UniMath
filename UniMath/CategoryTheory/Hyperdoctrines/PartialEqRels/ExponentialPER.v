(******************************************************************************************

 Exponentials of partial setoids

 Our goal is to show that the category of partial setoids in a tripos has exponentials. The
 first step to that is to construct the partial setoid of functions. The idea behind this
 construction is that we can represent function spaces using powersets. More specifically,
 the idea is that a function from `X` to `Y` can be represented as a subset of pairs of `X`
 and `Y` such that every member in `X` is paired with a unique member in `Y`.

 To translate this idea to partial setoids, we need to make a couple of modifications, and
 these modifcations are based on how morphisms are defined (see [PERMorphisms.v]). Recall
 that, given partial setoids `X` and `Y` a morphism from `X` to `Y` is given by a relation `φ`
 on `X` and `Y` such that:
 - if `φ (x , y)` then `x ~_X x` and `y ~_Y y`
 - if `x ~_X x'` and `y ~_Y y'` and `φ (x , y)`, then we also have `φ (x' , y')`
 - if `φ (x , y)` and `φ (x , y')`, then `y ~_Y y'`
 - if `x ~_X x'`, then there is `y` such that `φ (x , y)`

 We define the exponential partial setoid from `X` to `Y` as follows. The carrier is given by
 the powerset `ℙ(X ×h Y)` and we identify `f : ℙ(X ×h Y)` and `g : ℙ(X ×h Y)` if
 - `f` is a function (i.e., it satisfies the aforementioned requirements)
 - for all `x : X` and `y : Y`, we have `(x , y) ∈ f` if and only if `(x , y) ∈ g`
 As a consequence, whenever we have `f ~ f`, then `f` must be a function, and thus this
 partial setoid consists of functions that are identified if they are pointwise equal.

 The constructon in this file is based on the proof of Theorem 2.2.1 in "Realizability: an
 introduction to its categorical side". In that proof, exponentials are constructed explicitly.
 One can also use another construction, which is done in "Tripos Theory in Retrospect", where
 power objects are constructed instead of exponentials. Both approaches are sufficient in
 order to construct the topos arising from a tripos.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts
 - "Realizability: an introduction to its categorical side" by Jaap van Oosten

 Content
 1. Functions of partial setoids via the powerset
 2. Accessors
 3. Pointwise equality of partial setoid functions
 4. The partial setoid of functions
 5. Accessors for the partial equivalence relation of functions

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.

Local Open Scope cat.
Local Open Scope hd.

Section ExponentialPartialSetoid.
  Context {H : tripos}
          (X Y : partial_setoid H).

  (** * 1. Functions of partial setoids via the powerset *)
  Definition exp_partial_setoid_dom_defined_law
    : form (ℙ (X ×h Y))
    := let f := π₁ (π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y))) in
       let x := π₂ (π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y))) in
       let y := π₂ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y)) in
       (∀h ∀h (⟨ x , y ⟩ ∈ f ⇒ x ~ x)).

  Definition exp_partial_setoid_cod_defined_law
    : form (ℙ (X ×h Y))
    := let f := π₁ (π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y))) in
       let x := π₂ (π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y))) in
       let y := π₂ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y)) in
       (∀h ∀h (⟨ x , y ⟩ ∈ f ⇒ y ~ y)).

  Definition exp_partial_setoid_eq_defined_law
    : form (ℙ (X ×h Y))
    := let f := π₁ (π₁ (π₁ (π₁ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y))))) in
       let x := π₂ (π₁ (π₁ (π₁ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y))))) in
       let x' := π₂ (π₁ (π₁ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y)))) in
       let y := π₂ (π₁ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y))) in
       let y' := π₂ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y)) in
       (∀h ∀h ∀h ∀h (x ~ x' ⇒ y ~ y' ⇒ ⟨ x , y ⟩ ∈ f ⇒ ⟨ x' , y' ⟩ ∈ f)).

  Definition exp_partial_setoid_unique_im_law
    : form (ℙ (X ×h Y))
    := let f := π₁ (π₁ (π₁ (tm_var (((ℙ (X ×h Y) ×h X) ×h Y) ×h Y)))) in
       let x := π₂ (π₁ (π₁ (tm_var (((ℙ (X ×h Y) ×h X) ×h Y) ×h Y)))) in
       let y := π₂ (π₁ (tm_var (((ℙ (X ×h Y) ×h X) ×h Y) ×h Y))) in
       let y' := π₂ (tm_var (((ℙ (X ×h Y) ×h X) ×h Y) ×h Y)) in
       (∀h ∀h ∀h (⟨ x , y ⟩ ∈ f ⇒ ⟨ x , y' ⟩ ∈ f ⇒ y ~ y')).

  Definition exp_partial_setoid_im_exists_law
    : form (ℙ (X ×h Y))
    := let f := π₁ (tm_var (ℙ (X ×h Y) ×h X)) in
       let x := π₂ (tm_var (ℙ (X ×h Y) ×h X)) in
       let γ := π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y)) in
       (∀h (x ~ x ⇒ ∃h (⟨ x [ γ ]tm , π₂ (tm_var _) ⟩ ∈ (f [ γ ]tm)))).

  Definition exp_partial_setoid_is_function
    : form (ℙ (X ×h Y))
    := exp_partial_setoid_dom_defined_law
       ∧
       exp_partial_setoid_cod_defined_law
       ∧
       exp_partial_setoid_eq_defined_law
       ∧
       exp_partial_setoid_unique_im_law
       ∧
       exp_partial_setoid_im_exists_law.

  (** * 2. Accessors *)
  Proposition exp_partial_setoid_dom_defined
              {Γ : ty H}
              {Δ : form Γ}
              {f : tm Γ (ℙ (X ×h Y))}
              {x : tm Γ X}
              {y : tm Γ Y}
              (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
              (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
    : Δ ⊢ x ~ x.
  Proof.
    unfold exp_partial_setoid_is_function in p.
    rewrite !conj_subst in p.
    pose proof (r := conj_elim_left p).
    clear p.
    unfold exp_partial_setoid_dom_defined_law in r.
    rewrite !forall_subst in r.
    pose proof (r' := forall_elim r x).
    clear r ; rename r' into r.
    rewrite forall_subst in r.
    pose proof (r' := forall_elim r y).
    clear r ; rename r' into r.
    refine (weaken_cut r _).
    simplify_form.
    rewrite partial_setoid_subst.
    simplify.
    refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
    use weaken_left.
    exact q.
  Qed.

  Proposition exp_partial_setoid_cod_defined
              {Γ : ty H}
              {Δ : form Γ}
              {f : tm Γ (ℙ (X ×h Y))}
              {x : tm Γ X}
              {y : tm Γ Y}
              (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
              (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
    : Δ ⊢ y ~ y.
  Proof.
    unfold exp_partial_setoid_is_function in p.
    rewrite !conj_subst in p.
    pose proof (r := conj_elim_left (conj_elim_right p)).
    clear p.
    unfold exp_partial_setoid_cod_defined_law in r.
    rewrite !forall_subst in r.
    pose proof (r' := forall_elim r x).
    clear r ; rename r' into r.
    rewrite forall_subst in r.
    pose proof (r' := forall_elim r y).
    clear r ; rename r' into r.
    refine (weaken_cut r _).
    simplify_form.
    rewrite partial_setoid_subst.
    simplify.
    refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
    use weaken_left.
    exact q.
  Qed.

  Proposition exp_partial_setoid_eq_defined
              {Γ : ty H}
              {Δ : form Γ}
              {f : tm Γ (ℙ (X ×h Y))}
              (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
              {x x' : tm Γ X}
              (qx : Δ ⊢ x ~ x')
              {y y' : tm Γ Y}
              (qy : Δ ⊢ y ~y')
              (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
    : Δ ⊢ ⟨ x' , y' ⟩ ∈ f.
  Proof.
    unfold exp_partial_setoid_is_function in p.
    rewrite !conj_subst in p.
    pose proof (r := conj_elim_left (conj_elim_right (conj_elim_right p))).
    clear p.
    unfold exp_partial_setoid_eq_defined_law in r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    pose proof (r' := forall_elim r x).
    clear r ; rename r' into r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !tripos_in_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    pose proof (r' := forall_elim r x').
    clear r ; rename r' into r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !tripos_in_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose proof (r' := forall_elim r y).
    clear r ; rename r' into r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !tripos_in_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose proof (r' := forall_elim r y').
    clear r ; rename r' into r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !tripos_in_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !tm_subst_var in r.
    use (weaken_cut r _).
    refine (weaken_cut
              (impl_elim
                 _
                 (impl_elim
                    _
                    (impl_elim
                       _
                       (weaken_right (hyperdoctrine_hyp _) _))))
              _).
    - use weaken_left.
      exact q.
    - use weaken_left.
      exact qy.
    - use weaken_left.
      exact qx.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition exp_partial_setoid_unique_im
              {Γ : ty H}
              {Δ : form Γ}
              {f : tm Γ (ℙ (X ×h Y))}
              (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
              {x : tm Γ X}
              {y y' : tm Γ Y}
              (q₁ : Δ ⊢ ⟨ x , y ⟩ ∈ f)
              (q₂ : Δ ⊢ ⟨ x , y' ⟩ ∈ f)
    : Δ ⊢ y ~ y'.
  Proof.
    unfold exp_partial_setoid_is_function in p.
    rewrite !conj_subst in p.
    pose proof (r := conj_elim_left (conj_elim_right (conj_elim_right (conj_elim_right p)))).
    clear p.
    unfold exp_partial_setoid_unique_im_law in r.
    rewrite !forall_subst in r.
    pose proof (r' := forall_elim r x).
    clear r ; rename r' into r.
    rewrite !forall_subst in r.
    pose proof (r' := forall_elim r y).
    clear r ; rename r' into r.
    rewrite !forall_subst in r.
    pose proof (r' := forall_elim r y').
    clear r ; rename r' into r.
    refine (weaken_cut r _).
    simplify_form.
    rewrite !partial_setoid_subst.
    simplify.
    refine (impl_elim
              _
              (impl_elim
                 _
                 (weaken_right (hyperdoctrine_hyp _) _))).
    - use weaken_left.
      exact q₂.
    - use weaken_left.
      exact q₁.
  Qed.

  Proposition exp_partial_setoid_im_exists
              {Γ : ty H}
              {Δ : form Γ}
              {f : tm Γ (ℙ (X ×h Y))}
              (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
              {x : tm Γ X}
              (q : Δ ⊢ x ~ x)
    : Δ ⊢ (∃h (⟨ x [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ∈ (f [ π₁ (tm_var _) ]tm))).
  Proof.
    unfold exp_partial_setoid_is_function in p.
    rewrite !conj_subst in p.
    pose proof (r := conj_elim_right (conj_elim_right (conj_elim_right (conj_elim_right p)))).
    clear p.
    unfold exp_partial_setoid_im_exists_law in r.
    rewrite !forall_subst in r.
    pose (r' := forall_elim r x).
    refine (weaken_cut r' _).
    simplify_form.
    rewrite partial_setoid_subst.
    simplify.
    use (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
    use weaken_left.
    exact q.
  Qed.

  (** * 3. Pointwise equality of partial setoid functions *)
  Definition exp_partial_setoid_eq
    : form (ℙ (X ×h Y) ×h ℙ (X ×h Y))
    := let f := π₁ (π₁ (π₁ (tm_var (((ℙ (X ×h Y) ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
       let g := π₂ (π₁ (π₁ (tm_var (((ℙ (X ×h Y) ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
       let x := π₂ (π₁ (tm_var (((ℙ (X ×h Y) ×h ℙ (X ×h Y)) ×h X) ×h Y))) in
       let y := π₂ (tm_var (((ℙ (X ×h Y) ×h ℙ (X ×h Y)) ×h X) ×h Y)) in
       (∀h ∀h ((⟨ x , y ⟩ ∈ f) ⇔ (⟨ x , y ⟩ ∈ g))).

  Proposition from_exp_partial_setoid_eq
              {Γ : ty H}
              {Δ : form Γ}
              {f g : tm Γ (ℙ (X ×h Y))}
              (p : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , g ⟩ ])
              {x : tm Γ X}
              {y : tm Γ Y}
              (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
    : Δ ⊢ ⟨ x , y ⟩ ∈ g.
  Proof.
    unfold exp_partial_setoid_eq in p.
    rewrite !forall_subst in p.
    pose proof (forall_elim p x) as p'.
    clear p ; rename p' into p.
    rewrite forall_subst in p.
    pose proof (forall_elim p y) as p'.
    clear p ; rename p' into p.
    refine (weaken_cut p _).
    simplify.
    use (iff_elim_left (weaken_right (hyperdoctrine_hyp _) _)).
    use weaken_left.
    exact q.
  Qed.

  Proposition exp_partial_setoid_eq_refl
              {Γ : ty H}
              {Δ : form Γ}
              (f : tm Γ (ℙ (X ×h Y)))
    : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , f ⟩ ].
  Proof.
    unfold exp_partial_setoid_eq.
    rewrite !forall_subst.
    do 2 use forall_intro.
    simplify.
    apply iff_refl.
  Qed.

  Proposition exp_partial_setoid_eq_sym
              {Γ : ty H}
              {Δ : form Γ}
              {f g : tm Γ (ℙ (X ×h Y))}
              (p : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , g ⟩ ])
    : Δ ⊢ exp_partial_setoid_eq [ ⟨ g , f ⟩ ].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold exp_partial_setoid_eq.
    simplify.
    do 2 use forall_intro.
    simplify.
    pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
    pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
    pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
    fold γ x y.
    simple refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) x) _).
    simplify_form.
    simple refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) y) _).
    simplify.
    fold γ.
    use iff_sym.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition exp_partial_setoid_eq_trans
              {Γ : ty H}
              {Δ : form Γ}
              {f g h : tm Γ (ℙ (X ×h Y))}
              (p : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , g ⟩ ])
              (q : Δ ⊢ exp_partial_setoid_eq [ ⟨ g , h ⟩ ])
    : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , h ⟩ ].
  Proof.
    refine (weaken_cut p _).
    unfold exp_partial_setoid_eq.
    simplify_form.
    do 2 use forall_intro.
    simplify.
    pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
    pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
    pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
    fold γ x y.
    use hyp_sym.
    simple refine (weaken_cut (weaken_left (forall_elim (hyperdoctrine_hyp _) x) _) _).
    use hyp_ltrans.
    use weaken_right.
    simplify_form.
    use hyp_sym.
    simple refine (weaken_cut (weaken_left (forall_elim (hyperdoctrine_hyp _) y) _) _).
    use hyp_ltrans.
    use weaken_right.
    simplify.
    use (iff_trans (weaken_right (hyperdoctrine_hyp _) _)).
    use weaken_left.
    refine (hyperdoctrine_cut (hyperdoctrine_proof_subst _ q) _).
    unfold exp_partial_setoid_eq.
    simplify.
    simple refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) x) _).
    simplify_form.
    simple refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) y) _).
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition exp_partial_setoid_eq_is_function
              {Γ : ty H}
              {Δ : form Γ}
              {f g : tm Γ (ℙ (X ×h Y))}
              (p : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , g ⟩ ])
              (q : Δ ⊢ exp_partial_setoid_is_function [ f ])
    : Δ ⊢ exp_partial_setoid_is_function [ g ].
  Proof.
    unfold exp_partial_setoid_is_function.
    simplify_form.
    repeat use conj_intro.
    - unfold exp_partial_setoid_dom_defined_law.
      simplify_form.
      do 2 use forall_intro.
      use impl_intro.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
      fold γ x y.
      use exp_partial_setoid_dom_defined.
      + exact (f [ γ ]tm).
      + exact y.
      + use weaken_left.
        refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
        simplify.
        apply hyperdoctrine_hyp.
      + use (weaken_cut (weaken_left (hyperdoctrine_proof_subst γ p) _) _).
        use hyp_ltrans.
        use weaken_right.
        simplify.
        use from_exp_partial_setoid_eq.
        * exact (g [ γ ]tm).
        * use weaken_right.
          use exp_partial_setoid_eq_sym.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_cod_defined_law.
      simplify_form.
      do 2 use forall_intro.
      use impl_intro.
      rewrite partial_setoid_subst.
      simplify.
      pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
      fold γ x y.
      use exp_partial_setoid_cod_defined.
      + exact (f [ γ ]tm).
      + exact x.
      + use weaken_left.
        refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
        simplify.
        apply hyperdoctrine_hyp.
      + use (weaken_cut (weaken_left (hyperdoctrine_proof_subst γ p) _) _).
        use hyp_ltrans.
        use weaken_right.
        simplify.
        use from_exp_partial_setoid_eq.
        * exact (g [ γ ]tm).
        * use weaken_right.
          use exp_partial_setoid_eq_sym.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_eq_defined_law.
      simplify_form.
      do 4 use forall_intro.
      do 3 use impl_intro.
      rewrite !partial_setoid_subst.
      simplify.
      pose (γ := π₁ (π₁ (π₁ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y)))))).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y)))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y)))).
      pose (y₂ := π₂ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y))).
      fold γ x₁ x₂ y₁ y₂.
      use from_exp_partial_setoid_eq.
      + exact (f [ γ ]tm).
      + do 3 use weaken_left.
        refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
        simplify.
        apply hyperdoctrine_hyp.
      + use exp_partial_setoid_eq_defined.
        * do 3 use weaken_left.
          refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
          simplify.
          apply hyperdoctrine_hyp.
        * exact x₁.
        * do 2 use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        * exact y₁.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        * use from_exp_partial_setoid_eq.
          ** exact (g [ γ ]tm).
          ** do 3 use weaken_left.
             refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
             simplify.
             use exp_partial_setoid_eq_sym.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_unique_im_law.
      simplify_form.
      do 3 use forall_intro.
      do 2 use impl_intro.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      pose (γ := π₁ (π₁ (π₁ (tm_var (((Γ ×h X) ×h Y) ×h Y))))).
      pose (x := π₂ (π₁ (π₁ (tm_var (((Γ ×h X) ×h Y) ×h Y))))).
      pose (y₁ := π₂ (π₁ (tm_var (((Γ ×h X) ×h Y) ×h Y)))).
      pose (y₂ := π₂ (tm_var (((Γ ×h X) ×h Y) ×h Y))).
      fold γ x y₁ y₂.
      use exp_partial_setoid_unique_im.
      + exact (f [ γ ]tm).
      + do 2 use weaken_left.
        refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
        simplify.
        apply hyperdoctrine_hyp.
      + exact x.
      + use from_exp_partial_setoid_eq.
        * exact (g [ γ ]tm).
        * do 2 use weaken_left.
          refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
          simplify.
          use exp_partial_setoid_eq_sym.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
      + use from_exp_partial_setoid_eq.
        * exact (g [ γ ]tm).
        * do 2 use weaken_left.
          refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
          simplify.
          use exp_partial_setoid_eq_sym.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_im_exists_law.
      simplify_form.
      use forall_intro.
      use impl_intro.
      rewrite partial_setoid_subst.
      simplify.
      pose (γ := π₁ (tm_var (Γ ×h X))).
      pose (x := π₂ (tm_var (Γ ×h X))).
      fold γ x.
      use (exists_elim (exp_partial_setoid_im_exists _ _)).
      + exact (f [ γ ]tm).
      + use weaken_left.
        refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
        simplify.
        apply hyperdoctrine_hyp.
      + exact x.
      + use weaken_right.
        apply hyperdoctrine_hyp.
      + unfold γ, x ; clear γ x.
        simplify.
        pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
        pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
        fold γ x y.
        use exists_intro.
        * exact y.
        * simplify.
          fold γ x.
          use from_exp_partial_setoid_eq.
          ** exact (f [ γ ]tm).
          ** do 2 use weaken_left.
             refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
             simplify.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
  Qed.

  (** * 4. The partial setoid of functions *)
  Definition exp_partial_setoid_per_form
    : form (ℙ (X ×h Y) ×h ℙ (X ×h Y))
    := exp_partial_setoid_is_function [ π₁ (tm_var _) ]
       ∧
       exp_partial_setoid_eq.

  Arguments exp_partial_setoid_per_form /.

  Proposition exp_partial_setoid_per_axioms
    : per_axioms exp_partial_setoid_per_form.
  Proof.
    split.
    - unfold per_symm_axiom ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify.
      pose (f := π₂ (π₁ (tm_var ((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
      pose (g := π₂ (tm_var ((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
      fold f g.
      use conj_intro.
      + use exp_partial_setoid_eq_is_function.
        * exact f.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
      + use weaken_right.
        use exp_partial_setoid_eq_sym.
        apply hyperdoctrine_hyp.
    - unfold per_trans_axiom ; cbn.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      simplify.
      pose (f := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))))).
      pose (g := π₂ (π₁ (tm_var (((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
      pose (h := π₂ (tm_var (((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
      fold f g h.
      use conj_intro.
      + do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use exp_partial_setoid_eq_trans.
        * exact g.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        * do 2 use weaken_right.
          apply hyperdoctrine_hyp.
  Qed.

  Definition exp_partial_setoid_per
    : per (ℙ (X ×h Y)).
  Proof.
    use make_per.
    - exact exp_partial_setoid_per_form.
    - exact exp_partial_setoid_per_axioms.
  Defined.

  Definition exp_partial_setoid
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact (ℙ (X ×h Y)).
    - exact exp_partial_setoid_per.
  Defined.

  (** * 5. Accessors for the partial equivalence relation of functions *)
  Proposition eq_in_exp_partial_setoid
              {Γ : ty H}
              {f g : tm Γ exp_partial_setoid}
              {Δ : form Γ}
              (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
              (q : Δ ⊢ exp_partial_setoid_eq [⟨ f , g ⟩])
    : Δ ⊢ f ~ g.
  Proof.
    unfold partial_setoid_formula ; cbn.
    simplify.
    use conj_intro.
    - exact p.
    - exact q.
  Qed.

  Proposition from_eq_in_exp_partial_setoid_function_left
              {Γ : ty H}
              {f g : tm Γ exp_partial_setoid}
              {Δ : form Γ}
              (p : Δ ⊢ f ~ g)
    : Δ ⊢ exp_partial_setoid_is_function [ f ].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    simplify.
    use weaken_left.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition from_eq_in_exp_partial_setoid_function_right
              {Γ : ty H}
              {f g : tm Γ exp_partial_setoid}
              {Δ : form Γ}
              (p : Δ ⊢ f ~ g)
    : Δ ⊢ exp_partial_setoid_is_function [ g ].
  Proof.
    refine (hyperdoctrine_cut (partial_setoid_sym p) _).
    unfold partial_setoid_formula ; cbn.
    simplify.
    use weaken_left.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition from_eq_in_exp_partial_setoid_function_eq
              {Γ : ty H}
              {f g : tm Γ exp_partial_setoid}
              {Δ : form Γ}
              (p : Δ ⊢ f ~ g)
    : Δ ⊢ exp_partial_setoid_eq [⟨ f , g ⟩].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    simplify.
    use weaken_right.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition from_eq_in_exp_partial_setoid
              {Γ : ty H}
              {f g : tm Γ exp_partial_setoid}
              {Δ : form Γ}
              (p : Δ ⊢ f ~ g)
    : Δ ⊢ exp_partial_setoid_is_function [ f ] ∧ exp_partial_setoid_eq [⟨ f , g ⟩].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.
End ExponentialPartialSetoid.

Arguments exp_partial_setoid_per_form {H} X Y /.
Arguments exp_partial_setoid_is_function {H X Y}.
Arguments exp_partial_setoid_eq {H X Y}.
