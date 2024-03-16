From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

Ltac2 print_goal t := Control.enter (fun () => match! goal with | [ |- ?a ] => print (concat (of_string t) (of_constr a)) end).

Ltac2 count_goals (_ : unit) :=
  let cnt : int ref := { contents := 0} in
  Control.enter (fun _ =>
    cnt.(contents) := Int.add (cnt.(contents)) 1
  );
  print (of_int (cnt.(contents))).

Ltac2 mutable rducel := fun () => ().

(* Ltac2 branch () := rduce () ; print_goal "idpath 1" ; apply idpath ; print(of_string "idpath 2"). *)
Ltac2 branch () := print_goal "inside" ; rducel () ; apply idpath.

Ltac2 Set rducel as rduce0 := fun () =>
  Control.plus
  (fun _ =>
    match! goal with
    | [ |- app (abs ?a) ?b = _] =>
      refine '(beta_equality _ _ $a $b @ _);
      Control.focus 1 1 (fun () => assumption);
      rducel ()
    | [ |- abs ?a = _] =>
      refine '(maponpaths abs _ @ _);
      Control.focus 2 2 branch
    | [ |- app ?a ?b = _] =>
      refine '(maponpaths (λ x, app x _) _ @ _);
      Control.focus 2 2 branch;
      refine '(maponpaths (λ x, app _ x) _ @ _);
      Control.focus 2 2 branch
    end)
  (fun _ => rduce0 ()).

Ltac2 Set rducel as rduce0 := fun () =>
  Control.plus
  (fun _ =>
    match! goal with
    | [ |- (var ?a) • ?b = _] => refine '(var_subst _ $a $b @ _)
    | [ |- (abs ?a) • ?b = _] => refine '(subst_abs _ $a $b @ _)
    | [ |- (app ?a ?b) • ?c = _] => refine '(subst_app _ $a $b $c @ _)
    | [ |- (?a • ?b) • ?c = _] => refine '(subst_subst _ $a $b $c @ _)
    end)
  (fun _ => rduce0 ()).

Ltac2 Set rducel as rduce0 := fun () =>
  Control.plus
  (fun _ =>
    match! goal with
    | [ |- (inflate ?a) • ?b = _] => refine '(subst_inflate _ $a $b @ _)
    | [ |- inflate (var ?a) = _] => refine '(inflate_var _ $a @ _)
    | [ |- inflate (abs ?a) = _] => refine '(inflate_abs _ $a @ _)
    | [ |- inflate (app ?a ?b) = _] => refine '(inflate_app _ $a $b @ _)
    | [ |- inflate (?a • ?b) = _] => refine '(inflate_subst _ $a $b @ _)
    end)
  (fun _ => rduce0 ()).

Ltac2 Set rducel as rduce0 := fun () =>
  Control.plus
  (fun _ =>
    match! goal with
    | [ |- extend_tuple ?a ?b (_ (inl ?c)) = _] => refine '(extend_tuple_inl $a $b $c @ _)
    | [ |- extend_tuple ?a ?b (_ (inr ?c)) = _] => refine '(extend_tuple_inr $a $b $c @ _)
    end)
  (fun _ => rduce0 ()).

Ltac2 rduce0 () :=
  do 2 (
    refine '(_ @ !_);
    Control.focus 2 2 (fun () => now repeat (progress (rducel ())))).

Ltac2 Notation rduce := rduce0 ().

Ltac2 Set rducel as rduce0 := fun () =>
  Control.plus
  (fun _ =>
    match! goal with
    | [ |- inflate (?a ∘ ?b) = _] => refine '(inflate_compose $a $b @ _)
    | [ |- (?a ∘ ?b) • ?c = _] => refine '(subst_compose $a $b $c @ _)
    | [ |- ?a ∘ ?b = _] =>
      refine '(maponpaths (λ x, x ∘ _) _ @ _);
      Control.focus 2 2 branch;
      refine '(maponpaths (λ x, _ ∘ x) _ @ _);
      Control.focus 2 2 branch
    end)
  (fun _ => rduce0 ()).
