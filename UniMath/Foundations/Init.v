(** Initial setup unrelated to Univalent Foundations *)

Require Export Coq.Init.Logic.  (* this fixes the advanced forms of the 'rewrite' tactic, but we want to eliminate it eventually *)

Require Export Coq.Init.Notations. (* get the standard Coq reserved notations *)

(** Notations *)

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \prod *)

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
  (* type this in emacs in agda-input method with \lambda *)

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Notation "X <- Y" := (Y -> X) (at level 90, only parsing, left associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
(* written \to or \r- in Agda input method *)
(* the level comes from sub/coq/theories/Unicode/Utf8_core.v *)

(** Reserved notations *)

Reserved Notation "x :: y" (at level 60, right associativity). (* originally in Coq.Init.Datatypes *)

Reserved Notation "x ++ y" (at level 60, right associativity). (* originally in Coq.Init.Datatypes *)

Reserved Notation "g ∘ f"  (at level 50, left associativity).
(* to input: type "\circ" with Agda input method *)

Reserved Notation "p # x" (right associativity, at level 65, only parsing).

Reserved Notation "a ╝ b" (at level 70, no associativity).
(* in agda input mode use \--= and select the 6-th one in the first set,
   or use \chimney *)

Reserved Notation "X ≃ Y" (at level 80, no associativity).
(* written \~- or \simeq in Agda input method *)

Reserved Notation "p #' x" (right associativity, at level 65, only parsing).

Reserved Notation "f ~ g" (at level 70, no associativity).

Reserved Notation "p @ q" (at level 60, right associativity).

Reserved Notation "'¬¬' X" (at level 35, right associativity).
(* type this in emacs in agda-input method with \neg twice *)

Reserved Notation "x != y" (at level 70).

Reserved Notation "'¬' X" (at level 35, right associativity).
(* type this in emacs in agda-input method with \neg *)

Reserved Notation "A × B" (at level 75, right associativity).

Reserved Notation "C ⟦ a , b ⟧" (at level 49, right associativity).
(* ⟦   to input: type "\[[" or "\(" with Agda input method
   ⟧   to input: type "\]]" or "\)" with Agda input method *)

Reserved Notation "⟦ a ⟧" (at level 48, left associativity).

Reserved Notation "f ;; g"  (at level 50, left associativity, only parsing). (* deprecated *)

Reserved Notation "f · g"  (at level 40, format "f  ·  g", left associativity).
(* to input: type "\centerdot" or "\cdot" with Agda input method *)

Reserved Notation "a --> b" (at level 50, left associativity).

Reserved Notation "! p " (at level 50, left associativity).

(* conflict:
    Reserved Notation "# F"  (at level 3).
    Reserved Notation "p # x" (right associativity, at level 65, only parsing).
*)

Reserved Notation "p #' x" (right associativity, at level 65, only parsing).

Reserved Notation "C '^op'" (at level 3, format "C ^op").

Reserved Notation "a <-- b" (at level 50, left associativity).

Reserved Notation "[ C , D ]" .

Reserved Notation "C [ a , b ]"  (at level 50, left associativity).

Reserved Notation "X ⟶ Y"  (at level 39).
(* to input: type "\-->" with Agda input method *)

Reserved Notation "X ⟹ Y"  (at level 39).
(* same parsing level as ⟶ *)
(* to input: type "\==>" with Agda input method *)

Reserved Notation "F ∙ G" (at level 35).
(* to input: type "\." with Agda input method *)
(* the old notation had the arguments in the opposite order *)

(* conflict:
    Reserved Notation "s □ x" (at level 64, left associativity).
    Reserved Notation "G □ F" (at level 35).
    (* to input: type "\Box" or "\square" or "\sqw" or "\sq" with Agda input method *)
*)

Reserved Notation "X ⊗ Y"  (at level 40, left associativity).
(* to input: type "\ox" or "\otimes" with Agda input method *)

Reserved Notation "F ◾ b"  (at level 40, left associativity).
(* to input: type "\sqb" or "\sq" with Agda input method *)

Reserved Notation "F ▭ f"  (at level 40, left associativity). (* \rew1 *)
(* to input: type "\rew" or "\re" with Agda input method *)

Reserved Notation "A ⇒ B" (at level 95, right associativity).
(* to input: type "\Rightarrow" or "\r=" or "\r" or "\Longrightarrow" or "\=>" with Agda input method *)

Reserved Notation "X ⇐ c"   (at level 94, left associativity).
(* to input: type "\Leftarrow" or "\Longleftarrow" or "\l=" or "\l" with Agda input method *)

Reserved Notation "x ⟲ f"  (at level 50, left associativity).
(* to input: type "\l" and select from the menu, row 4, spot 2, with Agda input method *)

Reserved Notation "q ⟳ x"  (at level 50, left associativity).
(* to input: type "\r" and select from the menu, row 4, spot 3, with Agda input method *)

Reserved Notation "p ◽ b"  (at level 40).
(* to input: type "\sqw" or "\sq" with Agda input method *)

Reserved Notation "xe ⟲⟲ p"  (at level 50, left associativity).
(* to input: type "\l" and select from the menu, row 4, spot 2, with Agda input method *)

Reserved Notation "r \\ x"  (at level 50, left associativity).

Reserved Notation "x // r"  (at level 50, left associativity).

Reserved Notation "X ⨿ Y" (at level 50, left associativity).
(* type this in emacs with C-X 8 RET AMALGAMATION OR COPRODUCT *)

Reserved Notation "x ,, y" (at level 60, right associativity).

(** Tactics *)

(* Apply this tactic to a proof of ([X] and [X -> ∅]), in either order: *)
Ltac contradicts a b := solve [ induction (a b) | induction (b a) ].

(** A few more tactics, thanks go to Jason Gross *)

Ltac simple_rapply p :=
  simple refine p ||
  simple refine (p _) ||
  simple refine (p _ _) ||
  simple refine (p _ _ _) ||
  simple refine (p _ _ _ _) ||
  simple refine (p _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

Tactic Notation "use" uconstr(p) := simple_rapply p.

Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let name := (_ : type) in _).

Ltac exact_op x := (* from Jason Gross: same as "exact", but with unification the opposite way *)
  let T := type of x in
  let G := match goal with |- ?G => constr:(G) end in
  exact (((λ g:G, g) : T -> G) x).
