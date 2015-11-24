Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Sets
        UniMath.Ktheory.Precategories.

Local Open Scope cat.

Set Automatic Introduction.

Definition bifunctor_comm {I A B:Precategory} : [I, [A, B] ] ==> [A, [I, B] ].
Proof.
  refine (_,,_).
  { refine (_,,_).
    { intros D.
      refine (_,,_).
      { refine (_,,_).
        { intros a.
          refine (_,,_).
          - refine (_,,_).
            + intro i. exact (((D : _ ==> _) i : _ ==> _) a).
            + simpl. intros i j e. exact ((# (D : _ ==> _) e : _ ⟶ _) a).
          - abstract (split ;
                      [abstract (intro i; simpl;
                        exact (maponpaths (λ F : _⟶_, F _) (functor_id D _)))
                      |(intros i j k f g; simpl;
                        exact (maponpaths (λ F : _⟶_, F _) (functor_comp D _ _ _ _ _)))])
            using is_functor_0.
          }
        intros a a' f.
        refine (_,,_).
        { simpl. intro i. exact (# ((D:_==>_) i :_==>_) f). }
        { abstract (intros i j r; simpl; eqn_logic) using is_nat_trans_0. } }
      { abstract ( split;
                   [intros a; simpl; eqn_logic
                   |
                   intros a b g r s; simpl;
                   refine (total2_paths2 _ _) ;
                   [ abstract (apply funextsec; intro i; simpl; apply functor_comp) |
                     eqn_logic ]]) using is_functor_0. } }
    { intros D D' p. simpl.
      refine (_,,_).
      { intros a. simpl.
        refine (_,,_).
        { intros i; simpl. exact (((p : _ ⟶ _) i : _ ⟶ _) a). }
        { abstract (intros i j e; simpl;
                    exact (maponpaths (λ v : _ ⟶ _, v a) (nat_trans_ax p _ _ e))) using is_nat_trans_0. } }
      { abstract (intros a b f; simpl;
                  refine (total2_paths2 _ _);
                  [ apply funextsec; intro i; simpl;
                    exact (nat_trans_ax ((p : _ ⟶ _) i) _ _ f)
                    | simpl; apply isaprop_is_nat_trans, homset_property ]) using is_nat_trans_0. } } }
  { abstract (split;
    [ abstract (
          intros D; simpl; refine (total2_paths2 _ _);
          [ abstract (apply funextsec; intro a; refine (total2_paths2 _ _) ;
            [ reflexivity | apply isaprop_is_nat_trans, homset_property ] )
          |
          simpl; apply isaprop_is_nat_trans; apply (homset_property [I,B]) ]) using functor_idax_0 |
      abstract (
          simpl; intros D D' D'' p q; simpl; refine (total2_paths2 _ _);
          [abstract (
                apply funextsec; intro a; refine (total2_paths2 _ _);
                [ reflexivity |
                  apply funextsec; intro i;
                  apply funextsec; intro j;
                  apply funextsec; intro e;
                  apply homset_property])
          | apply isaprop_is_nat_trans; exact (homset_property [I,B]) ]) using functor_compax_0 ])
    using is_functor_0. }
Defined.

Definition arrow {C:Precategory} (X : [C,SET]) (c : C) : hSet := (X:_==>_) c.

Notation "X ---> c" := (arrow X c)  (at level 50) : cat.

Definition apply0 {C:Precategory} {X X':[C,SET]^op} {c:C} : (X'→X) -> (X--->c) -> (X'--->c)
  := λ q x, (q:_⟶_) c (x:(X:_==>_) c:hSet).

Notation "x ○ q" := (apply0 q x) (at level 50) : cat. (* agda mode: \ciw *)

Definition apply2 {C:Precategory} {X:[C,SET]} {c c':C} : (X--->c) -> (c→c') -> X--->c'
  := λ x f, # (X:_==>_) f x.

Notation "f ◎ x" := (apply2 x f) (at level 50) : cat. (* agda mode: \ci. *)

Definition apply {B C:Precategory} (F : [B,C]) (b:B) : C := (F:_==>_) b.

Notation "F @@ b" := (apply F b) (at level 40) : cat.

Definition apply3 {B C:Precategory} {F F' : [B,C]} (p:F→F') (b:B) : F @@ b → F' @@ b
  := (p:_⟶_) b.

Notation "p ** b" := (apply3 p b) (at level 40) : cat.

Definition apply4 {B C:Precategory} {b b':B} (F:[B,C]) (f:b→b') : F @@ b → F @@ b'
  := # (F:_==>_) f.

Notation "F ## f" := (apply4 F f) (at level 40) : cat.

Definition assoc1 {C:Precategory} {X:[C,SET]} {c c' c'':C} (x:X--->c) (f:c→c') (g:c'→c'') :
  (g ∘ f) ◎ x = g ◎ (f ◎ x)
  := apevalat x (functor_comp X c c' c'' f g).

Definition nattransax {B C:Precategory} {F F':[B, C]} (p:F→F') {b b':B} (f:b→b') :
  p ** b' ∘ F ## f = F' ## f ∘ p ** b
  := nat_trans_ax p _ _ f.

Definition assoc2 {C:Precategory} {X X':[C,SET]^op} {c c':C} (p:X'→X) (x:X--->c) (g:c→c') :
  g ◎ (x ○ p) = (g ◎ x) ○ p
  := !apevalat x (nat_trans_ax p _ _ g).

Definition bifunctor_assoc {B C:Precategory} : [B^op, [C,SET]] -> [[B,C],SET].
Proof.
  intros X.
  set (ρ := λ (X : [B^op, [C, SET]]) (F : [B, C]), ∀ b, X @@ b ---> F @@ b).
  set (ρ' := λ (X : [B^op, [C, SET]]) (F F' : [B, C]) (p : F → F') (x : ρ X F),
             (λ b, (p ** b) ◎ x b) : ρ X F').
  set (σ := λ (X : [B^op, [C, SET]]) (F : [B, C]) (x : ρ X F), ∀ (b b':B) (f:b→b'),
                     (F ## f) ◎ x b = x b' ○ (X ## f)).
  set (θ := λ (X : [B^op, [C, SET]]) (F : [B, C]), Σ x : ρ X F, σ X F x).
  assert (S : ∀ X F, isaset (θ X F)).
  { intros. apply isaset_total2.
    { apply impred_isaset; intro b. apply setproperty. }
    { intros x. apply impred_isaset; intro b;
                apply impred_isaset; intro b'; apply impred_isaset; intro f.
      apply isasetaprop; apply setproperty. } }
  refine (makeFunctor _ _ _ _).
  { intro F. exists (θ X F). abstract apply S using S. }
  { intros F F' p xe; simpl. induction xe as [x e].
    exists (ρ' _ _ _ p x).
    unfold ρ'. intros b b' f.
    intermediate_path ((F' ## f ∘ p ** b) ◎ x b).
    { apply pathsinv0, assoc1. }
    intermediate_path ((p ** b' ∘ F ## f) ◎ x b).
    { apply maponpaths. apply pathsinv0, nattransax. }
    intermediate_path (p ** b' ◎ (F ## f ◎ x b)).
    { apply assoc1. }
    intermediate_path (p ** b' ◎ (x b' ○ X ## f)).
    { apply (maponpaths (λ k, (p ** b') ◎ k)). exact (e b b' f ). }
    apply assoc2. }
  { intros F. apply funextsec; intro xe.
    set (P := @paths).


Abort.


     (*  *)