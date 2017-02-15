  Section ListByInduction.

    (* for testing only  *)

      Local Notation "[]" := nil (at level 0, format "[]").
      Local Infix "::" := cons.

      Context {X:Type} (unit:X) (op:X -> X -> X).

      Definition prod : list X -> X.
      Proof.
        intro k.
        induction k as [|x m y].
        - exact unit.
        - exact (op x y).
      Defined.
      (* list_rect (fun _ : list X => X) unit (fun (x : X) (_ : list X) (y : X) => op x y) k *)

      Definition q : X -> list X -> X.
      Proof.
        intros x m.
        generalize x; clear x.
        induction m as [|y _ z].
        - intro x. exact x.
        - intro x. exact (op x (z y)).
      Defined.

      Definition prod' : list X -> X.
      Proof.
        intro k.
        induction k as [|x m _].
        - exact unit.
        - generalize x; clear x.
          induction m as [|y _ z].
          + intro x. exact x.
          + intro x. exact (op x (z y)).
      Defined.

      Context (w x y z:X).

      Goal prod' [] = unit. reflexivity. Qed.
      Goal prod' (w::x::y::z::[]) = op w (op x (op y z)). reflexivity. Qed.
      Goal prod' (x::[]) = x. reflexivity. Qed.
