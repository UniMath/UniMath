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

Definition bifunctor_assoc {B C:Precategory} : [B^op, [C,SET] ] -> [[B,C],SET].
Proof.
  intros X.
  set (ρ := λ (X : [B ^op, [C, SET]]) (F : [B, C]),
            ∀ b, ((X:_==>_) b : _==>_) ((F:_==>_) b) : hSet).
  set (ρ' := λ (X : [B ^op, [C, SET]]) (F F' : [B, C]) (p : F → F') (x : ρ X F),
             (λ b, # ((X:_==>_) b : _==>_) ((p:_⟶_) b) (x b)) : ρ X F').
  set (σ := λ (X : [B ^op, [C, SET]]) (F : [B, C]) (x : ρ X F),
            ∀ b b' (f:b'→b),
                     # ((X:_==>_) b : _==>_) (# (F:_==>_) f) (x b)
                     =
                     ((# (X:_==>_) f) : _⟶_) _ (x b')).
  set (θ := λ (X : [B ^op, [C, SET]]) (F : [B, C]), Σ x : ρ X F, σ X F x).
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
    intros b' b f.
    unfold ρ'.


Abort.


     (*  *)