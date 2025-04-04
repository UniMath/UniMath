(******************************************************************************************

 Lambda abstraction for partial setoids

 In this file, we define lambda abstraction for partial setoids, which is yet another piece
 necessary to construct exponentials in the category of partial setoids.

 Fix partial setoids `X`, `Y`, and `Z`, and let `φ` be a morphism from `X ×h Z` to `Y`. The
 lambda abstraction of `φ` is a morphism from `Z` to the exponential from `X` to `Y`. Recall
 that the exponential was defined using the powerset operation, and in essence, the function
 space from `X` to `Y` is defined as the collection of all  functional relations between  `X`
 and `Y`. The underlying formula of the lambda abstraction operator is thus given by a relation
 between `Z` and the exponential from `X` to `Y`. Let's say we have some term `z` of type `X`
 and a term `f` of the exponential, then these are related if both `z` and `f` are defined
 (i.e., `z ~ z` and `f ~ f`), and if for all `x` and `y` we have that `φ` sends the pair
 `⟨ x , z ⟩` to `y` if and only if `f` sends `x` to `y`. The requirements are written down
 formally in [lam_partial_setoid_is_def] and [lam_partial_setoid_eq].

 We are required to check that this is a partial setoid morphism, and thus we must show
 that every `z` such that `z ~ z` has an image, and thus we must verify that every `z` gets
 mapped to an actual function by lambda abstraction.  One of the required checks is that
 images exist and for that we use [lam_image_form].

 Content
 1. The formula defining abstraction
 2. Accessors
 3. The image
 4. Lambda abstraction

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.

Local Open Scope cat.
Local Open Scope hd.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Require Import Ltac2.Control.
Require Import Ltac2.Notations.

(** Executes a function for all terms of a list, until the function returns something *)
Ltac2 rec iterate_until
  (f : 'a -> 'a list -> 'b option)
  (l : 'a list)
  : 'b option
  := match l with
  | []     => None
  | x :: l => match f x l with
    | Some y => Some y
    | None   => iterate_until f l
    end
  end.

(** Executes `f`, and if it returns a value, recurses with that value *)
Ltac2 rec repeat_while
  (f : 'a -> ('a option))
  (t : 'a)
  : unit
  :=
  match f t with
  | Some t' => repeat_while f t'
  | None => ()
  end.

(** Fails with an arbitrary return type, because the `fail` tactic is only of type `unit -> unit` *)
Ltac2 failv0 () : 'a := zero (Tactic_failure None).
Ltac2 Notation "failv" := failv0 ().

(** Executes a tactic. Returns its result if it succeeds and `None` if not. *)
Ltac2 try_opt (f : unit -> 'a) : 'a option :=
  once_plus
    (fun () => Some (f ()))
    (fun _ => None).

Ltac2 Notation "pn:" p(pattern) : 0 := p.

(**
  A traversal consists of
  - A pattern `p`, describing the goal `p = _` where the traversal activates;
  - A term `t` describing the step `refine '(maponpaths t _)`;
  - Strings `l` and `r` such that the string `λ x, l x r` is `t`.
*)
Ltac2 Type rec t_traversal := {
  p : pattern;
  c : unit -> constr;
  s : (string * string);
  t : (t_traversal list) option
}.

Ltac2 make_traversal0 (p : pattern) (c : unit -> constr) (l : string) (r : string)
  : t_traversal
  := {p := p; c := c; s := (l, r); t := None}.

Ltac2 Notation "make_traversal" p(pattern) x(thunk(open_constr)) := make_traversal0 p x.

(**
  A rewrite consists of
  - A pattern `p`, describing the goal `p = _` where the rewrite activates;
  - A term `t` of an identity type, describing the rewrite;
  - A string representation of `t`.
*)
Ltac2 Type t_rewrite := (pattern * (unit -> constr) * string).

(**
  While traversing, the `navigation`, deconstructed as `(l, r, (pr, in, po))`, gives the contextual
  information for printing rewrites:
    `refine (pr (λ x, ` + (join "(" reverse(l)) + ` x ` + (join ")" r) + `) in (_) po)`
  For example: `maponpaths (λ x, _ ∧ (x ~ _)) (_) @ _` or `transportf (λ x, (x ∨ _) ⊢ _) (_) _`.
*)
Ltac2 Type navigation := {
  left: string list;
  right: string list;
  preinpostfix: (string * string * string)
}.

(** Adds a new step on the inside of the navigation *)
Ltac2 append_navigation
  (n : navigation)
  ((l, r) : string * string)
  : navigation
  := {n with
    left := (l :: n.(left));
    right := (r :: n.(right));
  }.

(** Prints a rewrite with navigation n and identity t (in its string representation) *)
Ltac2 print_refine (n : navigation) (t : string) :=
  let (prefix, infix, postfix) := n.(preinpostfix) in
  Message.print (Message.of_string (
      String.concat "" [
        prefix ;
        "(λ x, " ;
        String.concat "(" (List.rev (n.(left))) ;
        "x" ;
        String.concat ")" (n.(right)) ;
        ")" ;
        infix ;
        "(" ;
        t ;
        ")" ;
        postfix
      ]
  )).

Ltac2 traverse_subterm
  (traverse : (t_traversal list) option -> navigation -> (t_traversal list) option)
  (n : navigation)
  (t : t_traversal)
  (l : t_traversal list)
  : (t_traversal list) option
  := let p := t.(p) in
    try_opt (fun () =>
      match! goal with
      | [ |- $pattern:p = _ ] =>
        let c := t.(c) () in
        refine '(maponpaths $c _);
        focus 2 2 (fun () =>
          Option.get_bt (Option.map
            (fun (x : t_traversal list) => ({t with t := Some x}) :: l)
            (traverse (t.(t)) (append_navigation n (t.(s)))))
        )
      end
    ).

(**
  At each subterm of the left hand side of the goal, executes `preorder`, then recurses, and then
  executes `postorder`. If either preorder or postorder returns true, stops executing and returns
  the remaining traversals at each level.
*)
Ltac2 rec traverse
  (traversals : t_traversal list)
  (preorder :  navigation -> bool)
  (postorder : navigation -> bool)
  (first_traversals : (t_traversal list) option)
  (n : navigation)
  : (t_traversal list) option
  := if preorder n then Some traversals else
    match iterate_until
      (traverse_subterm (traverse traversals preorder postorder) n)
      (Option.default traversals first_traversals)
    with
    | Some x => Some x
    | _ => if postorder n then Some [] else None
    end.

(** Tries to rewrite any subterm of the left hand side of the goal, from the top level downwards *)
Ltac2 simplify_component
  (traversals : t_traversal list)
  (rewrites : t_rewrite list)
  : (t_traversal list) option -> navigation -> (t_traversal list) option
  := traverse
      traversals
      (fun n => List.fold_left (fun b (p, c, t) =>
          if b then true else
            match (try_opt (fun () =>
              match! goal with
              | [ |- $pattern:p = _ ] =>
                refine (c ());
                print_refine n t
              end
            )) with
            | Some _ => true
            | None => false
            end
        ) false rewrites
      )
      (fun _ => false).

(**
  Uses `top_traversals` to get a goal of the form `[term] = _`, and tries to repeatedly rewrite the
  highest rewritable subterm of the left hand side of that goal.
*)
Ltac2 simplify
  (traversals : t_traversal list)
  (rewrites : t_rewrite list)
  (top_traversals : ((unit -> unit) * navigation) list)
  : unit
  :=
  List.iter (fun (m, n) =>
    try (
      m ();
      focus 2 2 (fun () =>
        repeat_while
        (fun (l : t_traversal list) =>
          try_opt (fun () =>
            refine '(_ @ _);
            focus 2 2 (fun () => Option.get_bt (simplify_component traversals rewrites (Some l) n))
          )
        )
        traversals;
        reflexivity
      )
    )
  ) top_traversals.

Ltac2 mutable hyperrewrites () : t_rewrite list := [].
Ltac2 mutable hypertraversals () : t_traversal list := [].

Ltac2 Set hypertraversals as traversals := fun _ =>
  (make_traversal ( _ [ _ ]tm) (λ x,  x [ _ ]tm)  "" " [ _ ]tm") ::
  (make_traversal ( _ [ _ ]tm) (λ x,  _ [ x ]tm)    "_ [" "]tm") ::
  (make_traversal ( _ [ _ ]  ) (λ x,  x [ _ ]  ) " " " [ _ ]"  ) ::
  (make_traversal ( _ [ _ ]  ) (λ x,  _ [ x ]  )    "_ [" "]"  ) ::
  (make_traversal ( _ ∧ _    ) (λ x,  x ∧ _    )  "" " ∧ _"    ) ::
  (make_traversal ( _ ∧ _    ) (λ x,  _ ∧ x    )    "_ ∧ " ""  ) ::
  (make_traversal ( _ ∨ _    ) (λ x,  x ∨ _    )  "" " ∨ _"    ) ::
  (make_traversal ( _ ∨ _    ) (λ x,  _ ∨ x    )    "_ ∨ " ""  ) ::
  (make_traversal ( _ ⇒ _    ) (λ x,  x ⇒ _    )  "" " ⇒ _"    ) ::
  (make_traversal ( _ ⇒ _    ) (λ x,  _ ⇒ x    )    "_ ⇒ " ""  ) ::
  (make_traversal ( _ ≡ _    ) (λ x,  x ≡ _    )  "" " ≡ _"    ) ::
  (make_traversal ( _ ≡ _    ) (λ x,  _ ≡ x    )    "_ ≡ " ""  ) ::
  (make_traversal ( _ ⇔ _    ) (λ x,  x ⇔ _    )  "" " ⇔ _"    ) ::
  (make_traversal ( _ ⇔ _    ) (λ x,  _ ⇔ x    )    "_ ⇔ " ""  ) ::
  (make_traversal ( _ ~ _    ) (λ x,  x ~ _    )  "" " ~ _"    ) ::
  (make_traversal ( _ ~ _    ) (λ x,  _ ~ x    )    "_ ~ " ""  ) ::
  (make_traversal (⟨_ , _⟩   ) (λ x, ⟨x , _⟩   ) "⟨" " , _⟩"   ) ::
  (make_traversal (⟨_ , _⟩   ) (λ x, ⟨_ , x⟩   )   "⟨_ , " "⟩" ) ::
  (make_traversal (∀h _      ) (λ x, ∀h x      )  "∀h " ""     ) ::
  (make_traversal (∃h _      ) (λ x, ∃h x      )  "∃h " ""     ) ::
  (make_traversal (¬  _      ) (λ x, ¬  x      )   "¬ " ""     ) ::
  (make_traversal (π₁ _      ) (λ x, π₁ x      )  "π₁ " ""     ) ::
  (make_traversal (π₂ _      ) (λ x, π₂ x      )  "π₂ " ""     ) ::
  traversals ().

Ltac2 Set hyperrewrites as rewrites := fun () =>
  (pn:(⊤[_]),            (fun () => '(truth_subst _                 )), "truth_subst _"                 ) ::
  (pn:(⊥[_]),            (fun () => '(false_subst _                 )), "false_subst _"                 ) ::
  (pn:((_ ∧ _)[_]),      (fun () => '(conj_subst _ _ _              )), "conj_subst _ _ _"              ) ::
  (pn:((_ ∨ _)[_]),      (fun () => '(disj_subst _ _ _              )), "disj_subst _ _ _"              ) ::
  (pn:((_ ⇒ _)[_]),      (fun () => '(impl_subst _ _ _              )), "impl_subst _ _ _"              ) ::
  (pn:((_ ⇔ _)[_]),      (fun () => '(iff_subst _ _ _               )), "iff_subst _ _ _"               ) ::
  (pn:((_ ≡ _)[_]),      (fun () => '(equal_subst _ _ _             )), "equal_subst _ _ _"             ) ::
  (pn:((_ ~ _)[_]),      (fun () => '(partial_setoid_subst   _ _ _  )), "partial_setoid_subst   _ _ _"  ) ::
  (pn:((∀h _)[_]),       (fun () => '(forall_subst _ _              )), "forall_subst _ _"              ) ::
  (pn:((∃h _)[_]),       (fun () => '(exists_subst _ _              )), "exists_subst _ _"              ) ::
  (pn:((¬ _)[_]),        (fun () => '(neg_subst _ _                 )), "neg_subst _ _"                 ) ::
  (pn:((_[_])[_]),       (fun () => '(hyperdoctrine_comp_subst _ _ _)), "hyperdoctrine_comp_subst _ _ _") ::
  (pn:(_[tm_var _]),     (fun () => '(hyperdoctrine_id_subst _      )), "hyperdoctrine_id_subst _"      ) ::
  (pn:((π₁ _)[_]tm),     (fun () => '(hyperdoctrine_pr1_subst _ _   )), "hyperdoctrine_pr1_subst _ _"   ) ::
  (pn:((π₂ _)[_]tm),     (fun () => '(hyperdoctrine_pr2_subst _ _   )), "hyperdoctrine_pr2_subst _ _"   ) ::
  (pn:(⟨_, _⟩[_]tm),     (fun () => '(hyperdoctrine_pair_subst _ _ _)), "hyperdoctrine_pair_subst _ _ _") ::
  (pn:((tm_var _)[_]tm), (fun () => '(var_tm_subst _                )), "var_tm_subst _"                ) ::
  (pn:((_ [_]tm)[_]tm),  (fun () => '(tm_subst_comp _ _ _           )), "tm_subst_comp _ _ _"           ) ::
  (pn:(_[tm_var _]tm),   (fun () => '(tm_subst_var _                )), "tm_subst_var _"                ) ::
  (pn:(π₁⟨_, _⟩),        (fun () => '(hyperdoctrine_pair_pr1 _ _    )), "hyperdoctrine_pair_pr1 _ _"    ) ::
  (pn:(π₂⟨_, _⟩),        (fun () => '(hyperdoctrine_pair_pr2 _ _    )), "hyperdoctrine_pair_pr2 _ _"    ) ::
  (pn:(!![_]tm),         (fun () => '(hyperdoctrine_unit_tm_subst _ )), "hyperdoctrine_unit_tm_subst _ ") ::
  rewrites ().

Ltac2 hypertop_traversals () : ((unit -> unit) * navigation) list :=
  ((fun () => match! goal with
    | [ |- _ = _ ] => refine '(!(!_ @ !_))
    end),
    {left := [""]; right := [""]; preinpostfix := ("refine '(_ @ !maponpaths ", " ", ").")}) ::
  ((fun () => match! goal with
    | [ |- _ = _ ] => refine '(_ @ _)
    end),
    {left := [""]; right := [""]; preinpostfix := ("refine '(maponpaths ", " ", " @ _).")}) ::
  ((fun () => match! goal with
    | [ |- ?a ⊢ _ ] => refine '(transportb (λ x, $a ⊢ x) _ _); cbv beta
    end),
    {left := ["_ ⊢ "]; right := [""]; preinpostfix := ("refine '(transportb ", " ", " _).")}) ::
  ((fun () => match! goal with
    | [ |- _ ⊢ ?b ] => refine '(transportb (λ x, x ⊢ $b) _ _); cbv beta
    end),
    {left := [""]; right := [" ⊢ _"]; preinpostfix := ("refine '(transportb ", " ", " _).")}) ::
  [].

Ltac2 hypersimplify0 () :=
  simplify
  (List.rev (hypertraversals ()))
  (List.rev (hyperrewrites ()))
  (List.rev (hypertop_traversals ())).

Ltac2 Notation hypersimplify := hypersimplify0 ().

Section PERLambda.
  Context {H : tripos}
          {X Y Z : partial_setoid H}
          (φ : partial_setoid_morphism (prod_partial_setoid X Z) Y).

  (** * 1. The formula defining abstraction *)
  Definition lam_partial_setoid_is_def
    : form (Z ×h exp_partial_setoid X Y)
    := let z := π₁ (tm_var (Z ×h exp_partial_setoid X Y)) in
       let f := π₂ (tm_var (Z ×h exp_partial_setoid X Y)) in
       z ~ z
       ∧
       exp_partial_setoid_is_function [ f ].

  Definition lam_partial_setoid_eq
    : form (Z ×h exp_partial_setoid X Y)
    := let z := π₁ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
       let f := π₂ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
       let x := π₂ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y))) in
       let y := π₂ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)) in
       (∀h ∀h (φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ] ⇔ ⟨ x , y ⟩ ∈ f)).

  Definition lam_partial_setoid_form
    : form (Z ×h exp_partial_setoid X Y)
    := lam_partial_setoid_is_def
       ∧
       lam_partial_setoid_eq.

  (** * 2. Accessors *)
  Section Accessors.
    Context {Γ : ty H}
            {Δ : form Γ}
            (z : tm Γ Z)
            (f : tm Γ (exp_partial_setoid X Y))
            (p : Δ ⊢ lam_partial_setoid_form [⟨ z , f ⟩]).

    Proposition lam_partial_setoid_form_def_dom
      : Δ ⊢ z ~ z.
    Proof.
      refine '(hyperdoctrine_cut p _).
      unfold lam_partial_setoid_form.
      hypersimplify.
      apply weaken_left.
      unfold lam_partial_setoid_is_def.
      hypersimplify.
      apply weaken_left.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition lam_partial_setoid_form_is_function
      : Δ ⊢ exp_partial_setoid_is_function [ f ].
    Proof.
      refine '(hyperdoctrine_cut p _).
      unfold lam_partial_setoid_form.
      hypersimplify.
      apply weaken_left.
      unfold lam_partial_setoid_is_def.
      hypersimplify.
      apply weaken_right.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition lam_partial_setoid_form_def_fun
      : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , f ⟩ ].
    Proof.
      refine '(hyperdoctrine_cut p _).
      unfold lam_partial_setoid_form.
      hypersimplify.
      apply weaken_left.
      unfold lam_partial_setoid_is_def.
      hypersimplify.
      apply weaken_right.
      apply exp_partial_setoid_eq_refl.
    Qed.

    Proposition lam_partial_setoid_eq_iff
                (x : tm Γ X)
                (y : tm Γ Y)
      : Δ ⊢ φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ] ⇔ ⟨ x , y ⟩ ∈ f.
    Proof.
      refine '(hyperdoctrine_cut p _).
      unfold lam_partial_setoid_form.
      hypersimplify.
      apply weaken_right.
      unfold lam_partial_setoid_eq.
      hypersimplify.
      refine '(hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) x) _).
      hypersimplify.
      refine '(hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) y) _).
      cbn.
      hypersimplify.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition lam_partial_setoid_eq_left
                (x : tm Γ X)
                (y : tm Γ Y)
                (q : Δ ⊢ φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ])
      : Δ ⊢ ⟨ x , y ⟩ ∈ f.
    Proof.
      apply (iff_elim_left (lam_partial_setoid_eq_iff x y)).
      exact q.
    Qed.

    Proposition lam_partial_setoid_eq_right
                (x : tm Γ X)
                (y : tm Γ Y)
                (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
      : Δ ⊢ φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ].
    Proof.
      apply (iff_elim_right (lam_partial_setoid_eq_iff x y)).
      exact q.
    Qed.
  End Accessors.

  Proposition to_lam_partial_setoid_eq
              {Γ : ty H}
              (z : tm Γ Z)
              (f : tm Γ (exp_partial_setoid X Y))
              {Δ : form Γ}
              (p₁ : Δ ⊢ z ~ z)
              (p₂ : Δ ⊢ exp_partial_setoid_is_function [ f ])
              (p₃ : Δ ⊢ lam_partial_setoid_eq [⟨ z , f ⟩])
    : Δ ⊢ lam_partial_setoid_form [ ⟨ z , f ⟩ ].
  Proof.
    unfold lam_partial_setoid_form, lam_partial_setoid_is_def.
    cbn.
    hypersimplify.
    repeat (apply conj_intro).
    - exact p₁.
    - exact p₂.
    - exact p₃.
  Qed.

  (** The formula is preserved under the partial setoid relation of the first argument *)
  Proposition lam_partial_setoid_eq_arg
              {Γ : ty H}
              (z z' : tm Γ Z)
              (f : tm Γ (exp_partial_setoid X Y))
              {Δ : form Γ}
              (p : Δ ⊢ z ~ z')
              (q : Δ ⊢ f ~ f)
              (r : Δ ⊢ lam_partial_setoid_form [⟨ z , f ⟩])
    : Δ ⊢ lam_partial_setoid_form [⟨ z' , f ⟩].
  Proof.
    apply to_lam_partial_setoid_eq.
    - exact (partial_setoid_refl_r p).
    - exact (lam_partial_setoid_form_is_function _ _ r).
    - unfold lam_partial_setoid_eq.
      hypersimplify.
      do 2 (refine '(forall_intro _)).
      hypersimplify.
      pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
      fold γ x y.
      apply iff_intro.
      + refine '(lam_partial_setoid_eq_left _ _ _ _ _ _).
        * exact (z [ γ ]tm).
        * apply weaken_left.
          refine '(hyperdoctrine_cut
                    (hyperdoctrine_proof_subst γ r)
                    _).
          hypersimplify.
          apply hyperdoctrine_hyp.
        * refine '(partial_setoid_mor_eq_defined φ _ _ _).
          ** exact ⟨ x , z' [ γ ]tm ⟩.
          ** exact y.
          ** apply eq_in_prod_partial_setoid.
             *** hypersimplify.
                 apply weaken_right.
                 refine '(hyperdoctrine_cut
                           (partial_setoid_mor_dom_defined
                              φ ⟨ x , z' [ γ ]tm ⟩ y
                              (hyperdoctrine_hyp _))
                           _).
                 refine '(hyperdoctrine_cut
                        (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _))
                        _).
                 hypersimplify.
                 apply hyperdoctrine_hyp.
             *** apply weaken_left.
                 hypersimplify.
                 rewrite <- partial_setoid_subst.
                 apply hyperdoctrine_proof_subst.
                 apply partial_setoid_sym.
                 exact p.
          ** refine '(partial_setoid_mor_cod_defined φ _ _ _).
             *** exact ⟨ x , z' [ γ ]tm ⟩.
             *** apply weaken_right.
                 apply hyperdoctrine_hyp.
          ** apply weaken_right.
             apply hyperdoctrine_hyp.
      + assert (Δ [γ] ∧ ⟨ x, y ⟩ ∈ f [γ ]tm ⊢ x ~ x) as lem₁.
        {
          refine '(hyperdoctrine_cut (partial_setoid_mor_dom_defined φ ⟨ x , z [ γ ]tm ⟩ y _) _).
          * refine '(lam_partial_setoid_eq_right (z [ γ ]tm) (f [ γ ]tm) _ x y _).
            ** apply weaken_left.
               refine '(hyperdoctrine_cut
                         (hyperdoctrine_proof_subst γ r)
                         _).
               hypersimplify.
               apply hyperdoctrine_hyp.
            ** apply weaken_right.
               apply hyperdoctrine_hyp.
          * refine '(hyperdoctrine_cut
                      (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _))
                      _).
            hypersimplify.
            apply hyperdoctrine_hyp.
        }
        assert (Δ [γ] ∧ ⟨ x, y ⟩ ∈ f [γ ]tm ⊢ y ~ y) as lem₂.
        {
          refine '(partial_setoid_mor_cod_defined φ ⟨ x , z [ γ ]tm ⟩ y _).
          refine '(lam_partial_setoid_eq_right (z [ γ ]tm) (f [ γ ]tm) _ x y _).
          {
            apply weaken_left.
            refine '(hyperdoctrine_cut
                      (hyperdoctrine_proof_subst γ r)
                      _).
            hypersimplify.
            apply hyperdoctrine_hyp.
          }
          apply weaken_right.
          apply hyperdoctrine_hyp.
        }
        refine '(partial_setoid_mor_eq_defined φ _ _ _).
        * exact ⟨ x , z [ γ ]tm ⟩.
        * exact y.
        * apply eq_in_prod_partial_setoid.
          ** hypersimplify.
             exact lem₁.
          ** hypersimplify.
             apply weaken_left.
             rewrite <- partial_setoid_subst.
             apply hyperdoctrine_proof_subst.
             exact p.
        * exact lem₂.
        * refine '(lam_partial_setoid_eq_right _ _ _ _ _ _).
          ** exact (f [ γ ]tm).
          ** apply weaken_left.
             refine '(hyperdoctrine_cut
                       (hyperdoctrine_proof_subst γ r)
                       _).
             hypersimplify.
             apply hyperdoctrine_hyp.
          ** apply weaken_right.
             apply hyperdoctrine_hyp.
  Qed.

  (** * 3. The image *)
  Definition lam_image_form
    : form ((X ×h Y) ×h 𝟙 ×h Z)
    := let x := π₁ (π₁ (tm_var ((X ×h Y) ×h 𝟙 ×h Z))) in
       let y := π₂ (π₁ (tm_var ((X ×h Y) ×h 𝟙 ×h Z))) in
       let z := π₂ (π₂ (tm_var ((X ×h Y) ×h 𝟙 ×h Z))) in
       φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ].

  Proposition lam_image_form_eq_help
              (x := π₁ (tm_var ((X ×h Y) ×h 𝟙 ×h Z)))
              (γ := π₂ (tm_var ((X ×h Y) ×h 𝟙 ×h Z)))
    : lam_image_form = (x ∈ {{lam_image_form}} [ γ ]tm).
  Proof.
    exact (mor_to_tripos_power_eq _ _ lam_image_form).
  Qed.

  Proposition lam_image_form_eq
              {Γ : ty H}
              (x : tm Γ X)
              (y : tm Γ Y)
              (z : tm Γ Z)
    : ⟨ x , y ⟩ ∈ {{lam_image_form}} [⟨ !!, z ⟩ ]tm
      =
      φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ].
  Proof.
    refine '(!_).
    refine '(_ @ maponpaths (λ φ, φ [ ⟨ ⟨ x , y ⟩ , ⟨ !! , z ⟩ ⟩ ]) lam_image_form_eq_help @ _).
    * unfold lam_image_form.
      symmetry.
      now hypersimplify.
    * now hypersimplify.
  Qed.

  Proposition is_function_lam_image_form
              (Δ : form (𝟙 ×h Z))
              (p : Δ ⊢ π₂ (tm_var _) ~ π₂ (tm_var _))
    : Δ ⊢ exp_partial_setoid_is_function [{{lam_image_form}}].
  Proof.
    unfold exp_partial_setoid_is_function.
    hypersimplify.
    repeat (apply conj_intro).
    - unfold exp_partial_setoid_dom_defined_law.
      hypersimplify.
      do 2 (apply forall_intro).
      apply impl_intro.
      apply weaken_right.
      hypersimplify.
      pose (x := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))).
      pose (y := π₂ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))).
      pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
      fold x y z.
      rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
      fold z.
      assert (π₁ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))) = !!) as ->.
      {
        apply hyperdoctrine_unit_eta.
      }
      rewrite lam_image_form_eq.
      refine '(hyperdoctrine_cut
                (partial_setoid_mor_dom_defined φ ⟨ x , z ⟩ y (hyperdoctrine_hyp _))
                _).
      refine '(hyperdoctrine_cut (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _)) _).
      hypersimplify.
      apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_cod_defined_law.
      hypersimplify.
      do 2 (apply forall_intro).
      apply impl_intro.
      apply weaken_right.
      hypersimplify.
      pose (x := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))).
      pose (y := π₂ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))).
      pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
      fold x y z.
      rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
      fold z.
      assert (π₁ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))) = !!) as ->.
      {
        apply hyperdoctrine_unit_eta.
      }
      refine '(partial_setoid_mor_cod_defined φ ⟨ x , z ⟩ y _).
      rewrite lam_image_form_eq.
      apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_eq_defined_law.
      hypersimplify.
      do 4 (apply forall_intro).
      do 3 (apply impl_intro).
      hypersimplify.
      pose (Γ := ((((𝟙 ×h Z) ×h X) ×h X) ×h Y) ×h Y).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var Γ)))).
      pose (y₁ := π₂ (π₁ (tm_var Γ))).
      pose (y₂ := π₂ (tm_var Γ)).
      pose (z := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
      (* unfold Γ in * ; clear Γ. *)
      fold x₁ x₂ y₁ y₂ z.
      rewrite (hyperdoctrine_pair_eta
                 (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h X) ×h X) ×h Y) ×h Y))))))).
      fold z.
      assert (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h X) ×h X) ×h Y) ×h Y)))))) = !!)
        as ->.
      {
        apply hyperdoctrine_unit_eta.
      }
      rewrite !lam_image_form_eq.
      refine '(partial_setoid_mor_eq_defined φ _ _ _).
      + exact ⟨ x₁ , z ⟩.
      + exact y₁.
      + apply eq_in_prod_partial_setoid.
        * hypersimplify.
          do 2 (apply weaken_left).
          apply weaken_right.
          apply hyperdoctrine_hyp.
        * hypersimplify.
          do 3 (apply weaken_left).
          refine '(hyperdoctrine_cut
                    (hyperdoctrine_proof_subst ⟨ !! , z ⟩ p)
                    _).
          rewrite partial_setoid_subst.
          hypersimplify.
          apply hyperdoctrine_hyp.
      + apply weaken_left.
        apply weaken_right.
        apply hyperdoctrine_hyp.
      + apply weaken_right.
        apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_unique_im_law.
      Time hypersimplify.
      do 3 apply forall_intro.
      apply impl_intro.
      apply weaken_right.
      apply impl_intro.
      hypersimplify.
      rewrite partial_setoid_subst.
      hypersimplify.
      pose (z := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y)))))).
      pose (x := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y))))).
      pose (y := π₂ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y)))).
      pose (y' := π₂ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y))).
      fold x y y' z.
      rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y)))))).
      fold z.
      assert (π₁ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y))))) = !!) as ->.
      {
        apply hyperdoctrine_unit_eta.
      }
      rewrite !lam_image_form_eq.
      apply (partial_setoid_mor_unique_im φ).
      + exact ⟨ x , z ⟩.
      + apply weaken_left.
        apply hyperdoctrine_hyp.
      + apply weaken_right.
        apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_im_exists_law.
      hypersimplify.
      apply forall_intro.
      apply impl_intro.
      rewrite partial_setoid_subst.
      hypersimplify.
      pose (x := π₂ (tm_var ((𝟙 ×h Z) ×h X))).
      pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h X)))).
      fold x.
      refine '(weaken_cut _ _).
      {
        apply weaken_left.
        exact (hyperdoctrine_proof_subst (π₁ (tm_var ((𝟙 ×h Z) ×h X))) p).
      }
      apply hyp_ltrans.
      apply weaken_right.
      rewrite partial_setoid_subst.
      hypersimplify.
      fold z.
      apply (exists_elim (partial_setoid_mor_hom_exists φ (x := ⟨ x , z ⟩) _)).
      + apply eq_in_prod_partial_setoid.
        * hypersimplify.
          apply weaken_left.
          apply hyperdoctrine_hyp.
        * hypersimplify.
          apply weaken_right.
          apply hyperdoctrine_hyp.
      + unfold x, z ; clear x z.
        rewrite exists_subst.
        pose (x := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))).
        pose (y := π₂ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))).
        pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
        apply exists_intro.
        {
          exact y.
        }
        cbn.
        hypersimplify.
        rewrite !partial_setoid_subst.
        hypersimplify.
        fold x y z.
        rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
        fold z.
        assert (π₁ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))) = !!) as ->.
        {
          apply hyperdoctrine_unit_eta.
        }
        rewrite lam_image_form_eq.
        apply weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Proposition lam_partial_setoid_eq_image_form
              (Δ : form (𝟙 ×h Z))
    :  Δ ⊢ lam_partial_setoid_eq [⟨ π₂ (tm_var (𝟙 ×h Z)) , {{lam_image_form}} ⟩].
  Proof.
    unfold lam_partial_setoid_eq.
    rewrite !forall_subst.
    do 2 apply forall_intro.
    cbn.
    hypersimplify.
    pose (x := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))).
    pose (y := π₂ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))).
    pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
    fold x y z.
    rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
    fold z.
    assert (π₁ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))) = !!) as ->.
    {
      apply hyperdoctrine_unit_eta.
    }
    rewrite lam_image_form_eq.
    apply iff_refl.
  Qed.

  (** * 4. Lambda abstraction *)
  Proposition lam_partial_setoid_laws
    : partial_setoid_morphism_laws lam_partial_setoid_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law ; cbn.
      hypersimplify.
      apply forall_intro.
      apply forall_intro.
      apply impl_intro.
      apply weaken_right.
      pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y))))).
      pose (f := π₂ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y)))).
      fold z f.
      apply (lam_partial_setoid_form_def_dom z f).
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law ; cbn.
      hypersimplify.
      do 2 apply forall_intro.
      apply impl_intro.
      apply weaken_right.
      pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y))))).
      pose (f := π₂ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y)))).
      fold z f.
      apply eq_in_exp_partial_setoid.
      + apply (lam_partial_setoid_form_is_function z f).
        apply hyperdoctrine_hyp.
      + apply (lam_partial_setoid_form_def_fun z f).
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law ; cbn.
      do 4 apply forall_intro.
      apply impl_intro.
      apply weaken_right.
      do 2 apply impl_intro.
      pose (Γ := (((𝟙 ×h Z) ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)).
      pose (f' := π₂ (tm_var Γ)).
      pose (f := π₂ (π₁ (tm_var Γ))).
      pose (z' := π₂ (π₁ (π₁ (tm_var Γ)))).
      pose (z := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
      unfold Γ in * ; clear Γ.
      fold f f' z z'.
      apply to_lam_partial_setoid_eq.
      + refine '(partial_setoid_refl_r _).
        do 2 apply weaken_left.
        apply hyperdoctrine_hyp.
      + apply exp_partial_setoid_eq_is_function.
        * exact f.
        * apply weaken_left.
          apply weaken_right.
          apply from_eq_in_exp_partial_setoid_function_eq.
          apply hyperdoctrine_hyp.
        * apply weaken_right.
          apply (lam_partial_setoid_form_is_function z f).
          apply hyperdoctrine_hyp.
      + unfold lam_partial_setoid_eq.
        hypersimplify.
        do 2 apply forall_intro.
        unfold f', f, z', z ; cbn ; clear f' f z' z.
        hypersimplify.
        rewrite !partial_setoid_subst.
        hypersimplify.
        pose (Γ := (((((𝟙 ×h Z) ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y).
        pose (y := π₂ (tm_var Γ)).
        pose (x := π₂ (π₁ (tm_var Γ))).
        pose (f' := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (f := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (z' := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        pose (z := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ))))))).
        unfold Γ in * ; clear Γ ; cbn.
        fold x y z z' f f'.
        apply iff_intro.
        * apply from_exp_partial_setoid_eq.
          ** exact f.
          ** do 2 apply weaken_left.
             apply weaken_right.
             apply from_eq_in_exp_partial_setoid_function_eq.
             apply hyperdoctrine_hyp.
          ** refine '(lam_partial_setoid_eq_left z f _ x y _).
             *** apply weaken_left.
                 apply weaken_right.
                 apply hyperdoctrine_hyp.
             *** apply (partial_setoid_mor_eq_defined φ).
                 **** exact ⟨ x , z' ⟩.
                 **** exact y.
                 **** apply eq_in_prod_partial_setoid ; hypersimplify.
                      {
                        apply weaken_right.
                        refine '(hyperdoctrine_cut
                                  (partial_setoid_mor_dom_defined
                                     φ
                                     ⟨ x , z' ⟩ y
                                     (hyperdoctrine_hyp _))
                                  _).
                        refine '(hyperdoctrine_cut
                                  (eq_in_prod_partial_setoid_l
                                     _ _
                                     (hyperdoctrine_hyp _))
                                  _).
                        hypersimplify.
                        apply hyperdoctrine_hyp.
                      }
                      do 3 apply weaken_left.
                      apply partial_setoid_sym.
                      apply hyperdoctrine_hyp.
                 **** apply weaken_right.
                      exact (partial_setoid_mor_cod_defined
                               φ
                               ⟨ x , z' ⟩ y
                               (hyperdoctrine_hyp _)).
                 **** apply weaken_right.
                      apply hyperdoctrine_hyp.
        * refine '(lam_partial_setoid_eq_right z' f _ x y _).
          ** apply lam_partial_setoid_eq_arg.
             *** exact z.
             *** do 3 apply weaken_left.
                 apply hyperdoctrine_hyp.
             *** do 2 apply weaken_left.
                 apply weaken_right.
                 exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
             *** apply weaken_left.
                 apply weaken_right.
                 apply hyperdoctrine_hyp.
          ** apply from_exp_partial_setoid_eq.
             *** exact f'.
             *** do 2 apply weaken_left.
                 apply weaken_right.
                 apply from_eq_in_exp_partial_setoid_function_eq.
                 apply partial_setoid_sym.
                 apply hyperdoctrine_hyp.
             *** apply weaken_right.
                 apply hyperdoctrine_hyp.
    - unfold  partial_setoid_mor_unique_im_law ; cbn -[lam_partial_setoid_form].
      do 3 apply forall_intro.
      apply impl_intro.
      apply weaken_right.
      apply impl_intro.
      pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))))).
      pose (f := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
      pose (g := π₂ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
      fold z f g.
      hypersimplify.
      apply eq_in_exp_partial_setoid.
      + apply weaken_left.
        apply (lam_partial_setoid_form_is_function z f).
        apply hyperdoctrine_hyp.
      + unfold exp_partial_setoid_eq, f, g, z ; clear f g z.
        hypersimplify.
        do 2 apply forall_intro.
        hypersimplify.
        pose (Γ := ((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y).
        pose (x := π₂ (π₁ (tm_var Γ))).
        pose (y := π₂ (tm_var Γ)).
        pose (f := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (g := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (z := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        unfold Γ in * ; clear Γ.
        fold x y z f g.
        refine '(iff_trans _ _).
        {
          apply iff_sym.
          apply (lam_partial_setoid_eq_iff z g).
          apply weaken_left.
          apply hyperdoctrine_hyp.
        }
        apply (lam_partial_setoid_eq_iff z f).
        apply weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law ; cbn.
      apply forall_intro.
      apply impl_intro.
      apply weaken_right.
      hypersimplify.
      apply exists_intro.
      + exact {{ lam_image_form }}.
      + pose (z := π₂ (tm_var (𝟙 ×h Z))).
        hypersimplify.
        fold z.
        apply to_lam_partial_setoid_eq.
        * apply hyperdoctrine_hyp.
        * apply is_function_lam_image_form.
          fold z.
          apply hyperdoctrine_hyp.
        * apply lam_partial_setoid_eq_image_form.
  Qed.

  Definition lam_partial_setoid
    : partial_setoid_morphism Z (exp_partial_setoid X Y).
  Proof.
    apply make_partial_setoid_morphism.
    - exact lam_partial_setoid_form.
    - exact lam_partial_setoid_laws.
  Defined.
End PERLambda.
