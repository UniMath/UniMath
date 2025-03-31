Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Require Import Ltac2.Control.
Require Import Ltac2.Notations.
Require Import Ltac2.Constr.

Ltac2 printb (b : bool) :=
  match b with
  | true =>  print (of_string "True")
  | false => print (of_string "False")
  end.

Ltac2 t1 () : unit
  :=
  reflexivity.

Ltac2 t2 () : unit
  :=
  print (of_int (numgoals ())).
  (* match! goal with
  | [ |- _ ] => printb false
  end. *)

Ltac2 t3 : constr -> constr
  := fun x => '($x = _).

Ltac2 make_function
  (f : constr -> constr)
  (t : constr)
  : constr
  :=
  let q := Fresh.in_goal @x in
  Constr.in_context q t (fun _ =>
    let y := f (hyp q) in
    exact $y
  ).

Definition test : tt = tt.
Proof.
  print (of_constr (make_function (fun x => t3 (t3 x)) '(_))).

  pose ().
  refine '(_ @ _);
  t2 ().
  printb (t1 ()).
Defined.

Ltac2 Set hypertraversals as traversals := fun _ =>
  (pn:( _ [ _]tm), (fun x => '( $x [ _ ]tm))) ::
  (pn:( _ [ _]tm), (fun x => '( _  [ $x]tm))) ::
  (pn:( _ [ _]  ), (fun x => '( $x [ _ ]  ))) ::
  (pn:( _ [ _]  ), (fun x => '( _  [ $x]  ))) ::
  (pn:( _ ∧ _   ), (fun x => '( $x ∧ _    ))) ::
  (pn:( _ ∧ _   ), (fun x => '( _  ∧ $x   ))) ::
  (pn:( _ ∨ _   ), (fun x => '( $x ∨ _    ))) ::
  (pn:( _ ∨ _   ), (fun x => '( _  ∨ $x   ))) ::
  (pn:( _ ⇒ _   ), (fun x => '( $x ⇒ _    ))) ::
  (pn:( _ ⇒ _   ), (fun x => '( _  ⇒ $x   ))) ::
  (pn:( _ ≡ _   ), (fun x => '( $x ≡ _    ))) ::
  (pn:( _ ≡ _   ), (fun x => '( _  ≡ $x   ))) ::
  (pn:( _ ⇔ _   ), (fun x => '( $x ⇔ _    ))) ::
  (pn:( _ ⇔ _   ), (fun x => '( _  ⇔ $x   ))) ::
  (pn:( _ ~ _   ), (fun x => '( $x ~ _    ))) ::
  (pn:( _ ~ _   ), (fun x => '( _  ~ $x   ))) ::
  (pn:(⟨_ , _⟩  ), (fun x => '(⟨$x, _ ⟩   ))) ::
  (pn:(⟨_ , _⟩  ), (fun x => '(⟨_ , $x⟩   ))) ::
  (pn:(∀h _     ), (fun x => '(∀h $x      ))) ::
  (pn:(∃h _     ), (fun x => '(∃h $x      ))) ::
  (pn:(¬  _     ), (fun x => '(¬  $x      ))) ::
  (pn:(π₁ _     ), (fun x => '(π₁ $x      ))) ::
  (pn:(π₂ _     ), (fun x => '(π₂ $x      ))) ::
  traversals ().

Ltac2 Set hyperrewrites as rewrites := fun () =>
  (pn:(⊤[_]),            '(truth_subst _)) ::
  (pn:(⊥[_]),            '(false_subst _)) ::
  (pn:((_ ∧ _)[_]),      '(conj_subst _ _ _)) ::
  (pn:((_ ∨ _)[_]),      '(disj_subst _ _ _)) ::
  (pn:((_ ⇒ _)[_]),      '(impl_subst _ _ _)) ::
  (pn:((_ ⇔ _)[_]),      '(iff_subst _ _ _)) ::
  (pn:((_ ≡ _)[_]),      '(equal_subst _ _ _)) ::
  (pn:((_ ~ _)[_]),      '(partial_setoid_subst   _ _ _)) ::
  (pn:((∀h _)[_]),       '(forall_subst _ _)) ::
  (pn:((∃h _)[_]),       '(exists_subst _ _)) ::
  (pn:((¬ _)[_]),        '(neg_subst _ _)) ::
  (pn:((_[_])[_]),       '(hyperdoctrine_comp_subst _ _ _)) ::
  (pn:(_[tm_var _]),     '(hyperdoctrine_id_subst _)) ::
  (pn:((π₁ _)[_]tm),     '(hyperdoctrine_pr1_subst _ _)) ::
  (pn:((π₂ _)[_]tm),     '(hyperdoctrine_pr2_subst _ _)) ::
  (pn:(⟨_, _⟩[_]tm),     '(hyperdoctrine_pair_subst _ _ _)) ::
  (pn:((tm_var _)[_]tm), '(var_tm_subst _)) ::
  (pn:((_ [_]tm)[_]tm),  '(tm_subst_comp _ _ _)) ::
  (pn:(_[tm_var _]tm),   '(tm_subst_var _)) ::
  (pn:(π₁⟨_, _⟩),        '(hyperdoctrine_pair_pr1 _ _)) ::
  (pn:(π₂⟨_, _⟩),        '(hyperdoctrine_pair_pr2 _ _)) ::
  (pn:(!![_]tm),         '(hyperdoctrine_unit_tm_subst _)) ::
  rewrites ().
