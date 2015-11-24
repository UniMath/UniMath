Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Sets
        UniMath.Ktheory.Precategories.

Local Open Scope cat.

Set Automatic Introduction.

Definition functor_object_application {B C:Precategory} (F : [B,C]) (b:B) : C
  := (F:_==>_) b.
Notation "F ◾ b" := (functor_object_application F b) (at level 40, left associativity) : cat. (* \sqb3 *)

Definition functor_mor_application {B C:Precategory} {b b':B} (F:[B,C]) :
  b → b'  ->  F ◾ b → F ◾ b'
  := λ f, # (F:_==>_) f.
Notation "F ▭ f" := (functor_mor_application F f) (at level 40, left associativity) : cat. (* \rew1 *)

Definition arrow {C:Precategory} (X : [C,SET]) (c : C) : hSet := (X:_==>_) c.
Notation "X ⇒ c" := (arrow X c)  (at level 50) : cat. (* \r= *)

Definition arrow_morphism_composition {C:Precategory} {X:[C,SET]} {c c':C} :
  X⇒c -> c→c' -> X⇒c'
  := λ x f, # (X:_==>_) f x.
Notation "f ◎ x" := (arrow_morphism_composition x f) (at level 50) : cat. (* agda mode: \ci. *)

Definition nattrans_arrow_composition {C:Precategory} {X X':[C,SET]^op} {c:C} :
  X'→X -> X⇒c -> X'⇒c
  := λ q x, (q:_⟶_) c (x:(X:_==>_) c:hSet).
Notation "x ○ q" := (nattrans_arrow_composition q x) (at level 50) : cat. (* agda mode: \ciw *)

Definition nattrans_object_application {B C:Precategory} {F F' : [B,C]} (b:B) :
  F → F'  ->  F ◾ b → F' ◾ b
  := λ p, (p:_⟶_) b.
Notation "p ◽ b" := (nattrans_object_application b p) (at level 40) : cat. (* \sqw3 *)

Definition arrow_mor_id {C:Precategory} {X:[C,SET]} {c:C} (x:X⇒c) :
  identity c ◎ x = x
  := apevalat x (functor_id X c).

Definition arrow_mor_mor_assoc {C:Precategory} {X:[C,SET]} {c c' c'':C}
           (x:X⇒c) (f:c→c') (g:c'→c'') :
  (g ∘ f) ◎ x = g ◎ (f ◎ x)
  := apevalat x (functor_comp X c c' c'' f g).

Definition nattrans_naturality {B C:Precategory} {F F':[B, C]} {b b':B}
           (p : F → F') (f : b → b') :
  p ◽ b'  ∘  F ▭ f  =  F' ▭ f  ∘  p ◽ b
  := nat_trans_ax p _ _ f.

Definition nattrans_arrow_mor_assoc {C:Precategory} {X X':[C,SET]^op} {c c':C}
           (p:X'→X) (x:X⇒c) (g:c→c') :
  g ◎ (x ○ p) = (g ◎ x) ○ p
  := !apevalat x (nat_trans_ax p _ _ g).

Definition nattrans_arrow_id {C:Precategory} {X:[C,SET]^op} {c:C} (x:X⇒c) :
  x ○ nat_trans_id _ = x
  := idpath _.

Notation "p ● q" := (nat_trans_comp _ _ _ p q) (at level 50) : cat. (* agda mode: \cib *)

Definition nattrans_nattrans_arrow_assoc {C:Precategory} {X X' X'':[C,SET]^op} {c:C}
           (q:X''→X') (p:X'→X) (x:X⇒c) :
  (x ○ p) ○ q = x ○ (p ● q)
  := idpath _.

(* move upstream *)

Lemma isaset_total2_subset (X:hSet) (Y:X->hProp) : isaset (Σ x, Y x).
Proof.
  intros. apply isaset_total2.
  - apply setproperty.
  - intro x. apply isasetaprop, propproperty.
Defined.

Definition total2_subset {X:hSet} (Y:X->hProp) : hSet
  := hSetpair (Σ x, Y x) (isaset_total2_subset X Y).

Delimit Scope set with set.

Notation "'Σ'  x .. y , P" := (total2_subset (fun x => .. (total2_subset (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : subset.
  (* type this in emacs in agda-input method with \Sigma *)

Delimit Scope subset with subset.

Lemma isaset_forall_hProp (X:UU) (Y:X->hProp) : isaprop (∀ x, Y x).
Proof. intros. apply impred_isaprop. intro x. apply propproperty. Defined.

Definition forall_hProp {X:UU} (Y:X->hProp) : hProp := hProppair (∀ x, Y x) (isaset_forall_hProp X Y).

Notation "∀  x .. y , P" := (forall_hProp (fun x => .. (forall_hProp (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : prop.
  (* type this in emacs in agda-input method with \Sigma *)

Delimit Scope prop with prop.

Definition θ {B C:Precategory} (X : [B^op, [C, SET]]) (F : [B, C]) : hSet
  := (
      Σ x : (∀ b, X ◾ b ⇒ F ◾ b) % set,
            (∀ (b b':B) (f:b→b'), F ▭ f ◎ x b = x b' ○ X ▭ f)
    ) % set.

Definition θ_subset {B C:Precategory} {X : [B^op, [C, SET]]} {F : [B, C]} (t u : θ X F) :
  pr1 t = pr1 u -> t = u.
Proof.
  apply subtypeEquality.
  intros x. apply impred; intro b;apply impred; intro b'; apply impred; intro f.
  apply setproperty.
Defined.

Definition θ_map {B C:Precategory} {X : [B^op, [C, SET]]} {F F':[B, C]} (p:F→F') :
  θ X F -> θ X F'.
Proof.
  intro xe. set (x := pr1 xe). refine (_,,_).
  { exact (λ b:B, p ◽ b  ◎  x b). }
  intros b b' f; simpl.
  intermediate_path ((F' ▭ f  ∘  p ◽ b) ◎ x b).
  { apply pathsinv0, arrow_mor_mor_assoc. }
  intermediate_path ((p ◽ b'  ∘  F ▭ f) ◎ x b).
  { apply maponpaths. apply pathsinv0, nattrans_naturality. }
  intermediate_path (p ◽ b'  ◎  (F ▭ f  ◎  x b)).
  { apply arrow_mor_mor_assoc. }
  intermediate_path (p ◽ b'  ◎  (x b'  ○  X ▭ f)).
  { apply (maponpaths (λ k, p ◽ b'  ◎  k)). apply (pr2 xe). }
  apply nattrans_arrow_mor_assoc.
Defined.

Definition bifunctor_assoc {B C:Precategory} : [B^op, [C,SET]] -> [[B,C],SET].
Proof.
  intros X. refine (makeFunctor _ _ _ _).
  { intro F. exact (θ X F). }
  { intros F F' p xe. exact (θ_map p xe). }
  { intros F. apply funextsec; intro xe. apply θ_subset.
    simpl. apply funextsec; intro b. apply arrow_mor_id. }
  { intros F F' F'' p q; simpl. apply funextsec; intro xe. apply θ_subset.
    simpl. apply funextsec; intro b. apply arrow_mor_mor_assoc. }
Defined.

Definition bifunctor_comm_functor_data {I A B:Precategory} :
  [I, [A, B] ] -> A -> functor_data I B
  := λ D a, functor_data_constr I B (λ i, D ◾ i ◾ a) (λ i j e, D ▭ e ◽ a).

Lemma isfunctor_bifunctor_comm_functor_data {I A B:Precategory} :
  ∀ (D:[I,[A,B]]) (a:A), is_functor (bifunctor_comm_functor_data D a).
Proof.
  split.
  { unfold functor_idax. intro i; simpl. unfold functor_mor_application.
    now rewrite functor_id. }
  { intros i j k f g; simpl. unfold functor_mor_application.
    now rewrite functor_comp. }
Qed.

Definition bifunctor_comm_functor {I A B:Precategory} :
  [I, [A, B] ] -> A -> [I,B].
Proof.
  intros D a.
  exists (bifunctor_comm_functor_data D a).
  exact (isfunctor_bifunctor_comm_functor_data D a).
Defined.

Definition bifunctor_comm_functor_data_2 (I A B:Precategory) : functor_data [I,[A,B]] [A,[I,B]].
Proof.
  refine (_,,_).
  { intros D.
    refine (_,,_).
    { refine (_,,_).
      { intros a. exact (bifunctor_comm_functor D a). }
      intros a a' f; simpl.
      refine (_,,_).
      { simpl; intro i. exact (D ◾ i ▭ f). }
      { abstract (intros i j r; simpl; eqn_logic) using L. } }
    { abstract ( split;
                 [ intros a; simpl; apply nat_trans_eq;
                   [ apply homset_property
                   | intros i; simpl; apply functor_id ]
                 | intros a b g r s; simpl; apply nat_trans_eq;
                   [ apply homset_property
                   | simpl; intros i; apply functor_comp ] ] ) using M. } }
  { intros D D' p. simpl.
    refine (_,,_).
    { intros a. simpl.
      refine (_,,_).
      { exact (λ i, p ◽ i ◽ a). }
      { abstract (exact (λ i j e, maponpaths (λ v : _ ⟶ _, v a) (nat_trans_ax p _ _ e))) using N. } }
    { abstract (intros a b f; apply nat_trans_eq;
                [ apply homset_property
                | intros i; simpl; apply nat_trans_ax]) using O. } }
Defined.

Definition isfunctor_bifunctor_comm_functor_data_2 {I A B:Precategory} :
  is_functor (bifunctor_comm_functor_data_2 I A B).
Proof.
  split.
  { intros D. simpl. apply nat_trans_eq.
    { exact (homset_property [I,B]). }
    simpl; intros a. apply nat_trans_eq.
    { apply homset_property. }
    reflexivity. }
  { intros D D' D'' p q; simpl. apply nat_trans_eq. exact (homset_property [I,B]).
    intros a; simpl. apply nat_trans_eq.
    { apply homset_property. }
    intros i; simpl. eqn_logic. }
Qed.

Definition bifunctor_comm (I A B:Precategory) : [I,[A,B]] ==> [A,[I,B]].
Proof.
  exists (bifunctor_comm_functor_data_2 I A B).
  apply isfunctor_bifunctor_comm_functor_data_2.
Defined.

(* *)
