Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Notations.

Require Import Tactic.Simplify.
Require Import Tactic.Common.

Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.

Local Open Scope hd.

Ltac2 mutable hypertraversals () : t_traversal list := [].

Ltac2 Set hypertraversals as traversals := fun _ =>
  (make_traversal (fun () => match! goal with | [|- (_  [ ?b]tm) = _ ] => '(λ x,  x [$b ]tm) end)  "" " [ _ ]tm") ::
  (make_traversal (fun () => match! goal with | [|- (?a [  _]tm) = _ ] => '(λ x,  $a[ x ]tm) end)    "_ [" "]tm") ::
  (make_traversal (fun () => match! goal with | [|- (_  [ ?b]  ) = _ ] => '(λ x,  x [$b ]  ) end) " " " [ _ ]"  ) ::
  (make_traversal (fun () => match! goal with | [|- (?a [  _]  ) = _ ] => '(λ x,  $a[ x ]  ) end)    "_ [" "]"  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ∧ ?b   ) = _ ] => '(λ x,  x ∧$b    ) end)  "" " ∧ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ∧  _   ) = _ ] => '(λ x,  $a∧ x    ) end)    "_ ∧ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ∨ ?b   ) = _ ] => '(λ x,  x ∨$b    ) end)  "" " ∨ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ∨  _   ) = _ ] => '(λ x,  $a∨ x    ) end)    "_ ∨ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ⇒ ?b   ) = _ ] => '(λ x,  x ⇒$b    ) end)  "" " ⇒ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ⇒  _   ) = _ ] => '(λ x,  $a⇒ x    ) end)    "_ ⇒ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ≡ ?b   ) = _ ] => '(λ x,  x ≡$b    ) end)  "" " ≡ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ≡  _   ) = _ ] => '(λ x,  $a≡ x    ) end)    "_ ≡ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ⇔ ?b   ) = _ ] => '(λ x,  x ⇔$b    ) end)  "" " ⇔ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ⇔  _   ) = _ ] => '(λ x,  $a⇔ x    ) end)    "_ ⇔ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (⟨_ ,?b⟩   ) = _ ] => '(λ x, ⟨x ,$b⟩   ) end) "⟨" " , _⟩"   ) ::
  (make_traversal (fun () => match! goal with | [|- (⟨?a, _⟩   ) = _ ] => '(λ x, ⟨$a, x⟩   ) end)   "⟨_ , " "⟩" ) ::
  (make_traversal (fun () => match! goal with | [|- (∀h _      ) = _ ] => '(λ x, ∀h x      ) end)  "∀h " ""     ) ::
  (make_traversal (fun () => match! goal with | [|- (∃h _      ) = _ ] => '(λ x, ∃h x      ) end)  "∃h " ""     ) ::
  (make_traversal (fun () => match! goal with | [|- (¬  _      ) = _ ] => '(λ x, ¬  x      ) end)   "¬ " ""     ) ::
  (make_traversal (fun () => match! goal with | [|- (π₁ _      ) = _ ] => '(λ x, π₁ x      ) end)  "π₁ " ""     ) ::
  (make_traversal (fun () => match! goal with | [|- (π₂ _      ) = _ ] => '(λ x, π₂ x      ) end)  "π₂ " ""     ) ::
  traversals ().

Ltac2 mutable hyperrewrites () : (int * t_rewrite) list := [].

Ltac2 Set hyperrewrites as rewrites := fun () =>
  (0, (pn:(⊤[_]),            (fun () => '(truth_subst _                 )), "truth_subst _"                 )) ::
  (0, (pn:(⊥[_]),            (fun () => '(false_subst _                 )), "false_subst _"                 )) ::
  (0, (pn:((_ ∧ _)[_]),      (fun () => '(conj_subst _ _ _              )), "conj_subst _ _ _"              )) ::
  (0, (pn:((_ ∨ _)[_]),      (fun () => '(disj_subst _ _ _              )), "disj_subst _ _ _"              )) ::
  (0, (pn:((_ ⇒ _)[_]),      (fun () => '(impl_subst _ _ _              )), "impl_subst _ _ _"              )) ::
  (0, (pn:((_ ⇔ _)[_]),      (fun () => '(iff_subst _ _ _               )), "iff_subst _ _ _"               )) ::
  (0, (pn:((_ ≡ _)[_]),      (fun () => '(equal_subst _ _ _             )), "equal_subst _ _ _"             )) ::
  (0, (pn:((∀h _)[_]),       (fun () => '(forall_subst _ _              )), "forall_subst _ _"              )) ::
  (0, (pn:((∃h _)[_]),       (fun () => '(exists_subst _ _              )), "exists_subst _ _"              )) ::
  (0, (pn:((¬ _)[_]),        (fun () => '(neg_subst _ _                 )), "neg_subst _ _"                 )) ::
  (0, (pn:((_[_])[_]),       (fun () => '(hyperdoctrine_comp_subst _ _ _)), "hyperdoctrine_comp_subst _ _ _")) ::
  (0, (pn:(_[tm_var _]),     (fun () => '(hyperdoctrine_id_subst _      )), "hyperdoctrine_id_subst _"      )) ::
  (1, (pn:((π₁ _)[_]tm),     (fun () => '(hyperdoctrine_pr1_subst _ _   )), "hyperdoctrine_pr1_subst _ _"   )) ::
  (1, (pn:((π₂ _)[_]tm),     (fun () => '(hyperdoctrine_pr2_subst _ _   )), "hyperdoctrine_pr2_subst _ _"   )) ::
  (1, (pn:(⟨_, _⟩[_]tm),     (fun () => '(hyperdoctrine_pair_subst _ _ _)), "hyperdoctrine_pair_subst _ _ _")) ::
  (1, (pn:((tm_var _)[_]tm), (fun () => '(var_tm_subst _                )), "var_tm_subst _"                )) ::
  (1, (pn:((_ [_]tm)[_]tm),  (fun () => '(tm_subst_comp _ _ _           )), "tm_subst_comp _ _ _"           )) ::
  (1, (pn:(_[tm_var _]tm),   (fun () => '(tm_subst_var _                )), "tm_subst_var _"                )) ::
  (1, (pn:(π₁⟨_, _⟩),        (fun () => '(hyperdoctrine_pair_pr1 _ _    )), "hyperdoctrine_pair_pr1 _ _"    )) ::
  (1, (pn:(π₂⟨_, _⟩),        (fun () => '(hyperdoctrine_pair_pr2 _ _    )), "hyperdoctrine_pair_pr2 _ _"    )) ::
  (1, (pn:(!![_]tm),         (fun () => '(hyperdoctrine_unit_tm_subst _ )), "hyperdoctrine_unit_tm_subst _ ")) ::
  rewrites ().

Ltac2 hypertop_traversals (ltac2 : bool) : ((unit -> unit) * navigation) list :=
  ((fun () => match! goal with
    | [ |- _ = _ ] => refine '(!(_ @ !_))
    end), {
      left := [""];
      right := [""];
      preinpostfix := (String.concat "" ["refine "; (if ltac2 then "'" else ""); "(_ @ !maponpaths "], " ", ").")
  }) :: ((fun () => match! goal with
    | [ |- _ = _ ] => refine '(_ @ _)
    end), {
      left := [""];
      right := [""];
      preinpostfix := (String.concat "" ["refine "; (if ltac2 then "'" else ""); "(maponpaths "], " ", " @ _).")
  }) :: ((fun () => match! goal with
    | [ |- ?a ⊢ _ ] => refine '(transportb (λ x, $a ⊢ x) _ _); cbv beta
    end), {
      left := ["_ ⊢ "];
      right := [""];
      preinpostfix := (String.concat "" ["refine "; (if ltac2 then "'" else ""); "(transportb "], " ", " _).")}) ::
  ((fun () => match! goal with
    | [ |- _ ⊢ ?b ] => refine '(transportb (λ x, x ⊢ $b) _ _); cbv beta
    end),
    {left := [""]; right := [" ⊢ _"]; preinpostfix := (String.concat "" ["refine "; (if ltac2 then "'" else ""); "(transportb "], " ", " _).")}) ::
  [].

Ltac2 hypersimplify0 (ltac2 : bool option) : int option -> unit :=
  simplify
  (List.rev (hypertraversals ()))
  (List.rev (hyperrewrites ()))
  (List.rev (hypertop_traversals (Option.default true ltac2))).

Ltac2 Notation "hypersimplify" n(opt(next)) := hypersimplify0 (n).

Ltac2 Set hypertraversals as traversals := fun _ =>
  (make_traversal (fun () => match! goal with | [|- (_  ~ ?b   ) = _ ] => '(λ x,  x ~$b    ) end)  "" " ~ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ~  _   ) = _ ] => '(λ x,  $a~ x    ) end)    "_ ~ " ""  ) ::
  traversals ().

Ltac2 Set hyperrewrites as rewrites := fun () =>
  (1, (pn:((_ ~ _)[_]),      (fun () => '(partial_setoid_subst   _ _ _  )), "partial_setoid_subst   _ _ _"  )) ::
  rewrites ().

Set Default Proof Mode "Classic".

Tactic Notation "hypersimplify" := ltac2:(hypersimplify0 (Some false) None).
Tactic Notation "hypersimplify" int(n) := let f := ltac2:(n |- hypersimplify0 (Some false) (Ltac1.to_int n)) in f n.

Tactic Notation "simplify" := ltac2:(hypersimplify0 (Some false) None).
Tactic Notation "simplify_form" := ltac2:(hypersimplify0 (Some false) (Some 0)).
