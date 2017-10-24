(** * The induction principle for the half line. *)

Require Import UniMath.Foundations.UnivalenceAxiom
               UniMath.Ktheory.Utilities.
Require UniMath.CategoryTheory.Categories.
Require UniMath.Ktheory.Nat.
Unset Automatic Introduction.
Notation ℕ := nat.

Definition target_paths {Y} (f:ℕ->Y) := ∏ n, f n=f(S n).

Definition gHomotopy {Y} (f:ℕ->Y) (s:target_paths f) := fun
     y:Y => ∑ (h:nullHomotopyFrom f y), ∏ n, h(S n) = h n @ s n.

Definition GuidedHomotopy {Y} (f:ℕ->Y) (s:target_paths f) :=
  total2 (gHomotopy f s).

Theorem iscontrGuidedHomotopy {Y} {f:ℕ->Y} (s:target_paths f) :
  iscontr (GuidedHomotopy f s).
Proof. intros. unfold GuidedHomotopy, nullHomotopyFrom.
       refine (@iscontrweqb _ (∑ y, y=f 0) _ _).
       { apply weqfibtototal. intro y.
         exact (Nat.Uniqueness.hNatRecursion_weq
                  (λ n, y = f n) (λ n hn, hn @ s n)). }
       { apply iscontrcoconustot. } Defined.

Definition halfline := ∥ ℕ ∥.

Definition makeNullHomotopy {Y} {f:ℕ->Y} (s:target_paths f) {y:Y} (h0:y=f 0) :
  nullHomotopyFrom f y.
Proof. intros. intro n. induction n as [|n IHn]. { exact (h0). } { exact (IHn @ s _). } Defined.

Definition map {Y} {f:ℕ->Y} (s:target_paths f) :
  halfline -> GuidedHomotopy f s.
Proof. intros ? ? ? r. apply (squash_to_prop r).
       { apply isapropifcontr. apply iscontrGuidedHomotopy. }
       { intro n. exists (f n). induction n as [|n IHn].
         { exists (makeNullHomotopy s (idpath _)). intro n. reflexivity. }
         { exact (transportf (gHomotopy f s) (s n) IHn). } } Defined.

Definition map_path {Y} {f:ℕ->Y} (s:target_paths f) :
  ∏ n, map s (squash_element n) = map s (squash_element (S n)).
Proof. intros. apply (two_arg_paths_f (s n)).
       simpl. reflexivity. Defined.

Definition map_path_check {Y} {f:ℕ->Y} (s:target_paths f) (n:ℕ) :
  ∏ p : map s (squash_element n) = map s (squash_element (S n)),
    ap pr1 p = s n.
Proof. intros. set (q := map_path s n).
       assert (path_inverse_to_right : q=p).
       { apply (hlevelntosn 1). apply (hlevelntosn 0). apply iscontrGuidedHomotopy. }
       destruct path_inverse_to_right. apply total2_paths2_comp1. Defined.

(** ** universal property for the half line *)

Definition halfline_map {Y} {target_points:ℕ->Y} (s:target_paths target_points) :
  halfline -> Y.
Proof. intros ? ? ? r. exact (pr1 (map s r)). Defined.

Definition check_values {Y} {target_points:ℕ->Y}
           (s:target_paths target_points) (n:ℕ) :
  halfline_map s (squash_element n) = target_points n.
Proof. reflexivity. Defined.

Definition check_paths {Y} {target_points:ℕ->Y}
           (s:target_paths target_points) (n:ℕ) :
  ap (halfline_map s) (squash_path n (S n)) = s n.
Proof. intros. refine (_ @ map_path_check s n _).
       apply pathsinv0. apply maponpathscomp. Defined.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/Halfline.vo"
End:
*)
