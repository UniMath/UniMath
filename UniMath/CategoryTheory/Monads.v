(** **********************************************************

Contents:

        - Definition of monads ([Monad])
        - Precategory of monads [Precategory_Monad C] on [C]
        - Forgetful functor [forgetfunctor_Monad] from monads
             to endofunctors on [C]
        - Haskell style bind operation ([bind])
        - A substitution operator for monads ([monadSubst])

TODO:
        - Proof that [precategory_Monad C] is saturated if [C] is


Written by: Benedikt Ahrens (started March 2015)
Extended by: Anders Mörtberg, 2016

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of monads *)
Section Monad_def.

Definition functor_with_μ (C : precategory) : UU
  := ∑ F : functor C C, F □ F ⟹ F.

Coercion functor_from_functor_with_μ (C : precategory) (F : functor_with_μ C)
  : functor C C := pr1 F.

Definition μ {C : precategory} (F : functor_with_μ C) : F□F ⟹ F := pr2 F.

Definition Monad_data (C : precategory) : UU :=
   ∑ F : functor_with_μ C, functor_identity C ⟹ F.

Coercion functor_with_μ_from_Monad_data (C : precategory) (F : Monad_data C)
  : functor_with_μ C := pr1 F.

Definition η {C : precategory} (F : Monad_data C)
  : functor_identity C ⟹ F := pr2 F.

Definition Monad_laws {C : precategory} (T : Monad_data C) : UU :=
    (
      (∏ c : C, η T (T c) · μ T c = identity (T c))
        ×
      (∏ c : C, #T (η T c) · μ T c = identity (T c)))
      ×
    (∏ c : C, #T (μ T c) · μ T c = μ T (T c) · μ T c).

Lemma isaprop_Monad_laws (C : precategory) (hs : has_homsets C) (T : Monad_data C) :
   isaprop (Monad_laws T).
Proof.
  repeat apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition Monad (C : precategory) : UU := ∑ T : Monad_data C, Monad_laws T.

Coercion Monad_data_from_Monad (C : precategory) (T : Monad C) : Monad_data C := pr1 T.

Lemma Monad_law1 {C : precategory} {T : Monad C} : ∏ c : C, η T (T c) · μ T c = identity (T c).
Proof.
exact (pr1 (pr1 (pr2 T))).
Qed.

Lemma Monad_law2 {C : precategory} {T : Monad C} : ∏ c : C, #T (η T c) · μ T c = identity (T c).
Proof.
exact (pr2 (pr1 (pr2 T))).
Qed.

Lemma Monad_law3 {C : precategory} {T : Monad C} : ∏ c : C, #T (μ T c) · μ T c = μ T (T c) · μ T c.
Proof.
exact (pr2 (pr2 T)).
Qed.

End Monad_def.

(** * Monad precategory *)
Section Monad_precategory.

Definition Monad_Mor_laws {C : precategory} {T T' : Monad_data C} (α : T ⟹ T')
  : UU :=
  (∏ a : C, μ T a · α a = α (T a) · #T' (α a) · μ T' a) ×
  (∏ a : C, η T a · α a = η T' a).

Lemma isaprop_Monad_Mor_laws (C : precategory) (hs : has_homsets C)
  (T T' : Monad_data C) (α : T ⟹ T')
  : isaprop (Monad_Mor_laws α).
Proof.
  apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition Monad_Mor {C : precategory} (T T' : Monad C) : UU
  := ∑ α : T ⟹ T', Monad_Mor_laws α.

Coercion nat_trans_from_monad_mor (C : precategory) (T T' : Monad C) (s : Monad_Mor T T')
  : T ⟹ T' := pr1 s.

Definition Monad_Mor_η {C : precategory} {T T' : Monad C} (α : Monad_Mor T T')
  : ∏ a : C, η T a · α a = η T' a.
Proof.
  exact (pr2 (pr2 α)).
Qed.

Definition Monad_Mor_μ {C : precategory} {T T' : Monad C} (α : Monad_Mor T T')
  : ∏ a : C, μ T a · α a = α (T a) · #T' (α a) · μ T' a.
Proof.
  exact (pr1 (pr2 α)).
Qed.

Lemma Monad_identity_laws {C : precategory} (T : Monad C)
  : Monad_Mor_laws (nat_trans_id T).
Proof.
  split; intros a; simpl.
  - now rewrite id_left, id_right, functor_id, id_left.
 - now apply id_right.
Qed.

Definition Monad_identity {C : precategory} (T : Monad C)
  : Monad_Mor T T := tpair _ _ (Monad_identity_laws T).

Lemma Monad_composition_laws {C : precategory} {T T' T'' : Monad C}
  (α : Monad_Mor T T') (α' : Monad_Mor T' T'') : Monad_Mor_laws (nat_trans_comp _ _ _ α α').
Proof.
  split; intros; simpl.
  - rewrite assoc.
    set (H:=Monad_Mor_μ α a); simpl in H.
    rewrite H; clear H; rewrite <- !assoc.
    set (H:=Monad_Mor_μ α' a); simpl in H.
    rewrite H; clear H.
    rewrite functor_comp.
    apply maponpaths.
    now rewrite !assoc, nat_trans_ax.
  - rewrite assoc.
    eapply pathscomp0; [apply cancel_postcomposition, Monad_Mor_η|].
    apply Monad_Mor_η.
Qed.

Definition Monad_composition {C : precategory} {T T' T'' : Monad C}
  (α : Monad_Mor T T') (α' : Monad_Mor T' T'')
  : Monad_Mor T T'' := tpair _ _ (Monad_composition_laws α α').

Definition Monad_Mor_equiv {C : precategory} (hs : has_homsets C)
  {T T' : Monad C} (α β : Monad_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_Monad_Mor_laws, hs.
Defined.

Definition precategory_Monad_ob_mor (C : precategory) : precategory_ob_mor.
Proof.
  exists (Monad C).
  exact (λ T T' : Monad C, Monad_Mor T T').
Defined.

Definition precategory_Monad_data (C : precategory) : precategory_data.
Proof.
  exists (precategory_Monad_ob_mor C).
  exists (@Monad_identity C).
  exact (@Monad_composition C).
Defined.

Lemma precategory_Monad_axioms (C : precategory) (hs : has_homsets C)
  : is_precategory (precategory_Monad_data C).
Proof.
  repeat split; simpl; intros.
  - apply (invmap (Monad_Mor_equiv hs _ _ )).
    apply (@id_left (functor_precategory C C hs)).
  - apply (invmap (Monad_Mor_equiv hs _ _ )).
    apply (@id_right (functor_precategory C C hs)).
  - apply (invmap (Monad_Mor_equiv hs _ _ )).
    apply (@assoc (functor_precategory C C hs)).
Qed.

Definition precategory_Monad (C : precategory) (hs : has_homsets C) : precategory
  := tpair _ _ (precategory_Monad_axioms C hs).


Lemma has_homsets_Monad (C:Precategory) : has_homsets (precategory_Monad C (homset_property C)).
Proof.
  intros F G.
  simpl.
  unfold Monad_Mor.
  apply isaset_total2 .
  apply isaset_nat_trans.
  apply homset_property.
  intro m.
  apply isasetaprop.
  apply isaprop_Monad_Mor_laws.
  apply homset_property.
Qed.

Definition Precategory_Monad (C:Precategory) : Precategory :=
  (precategory_Monad C (homset_property C) ,, has_homsets_Monad C ).


Definition forgetfunctor_Monad (C:Precategory) :
  functor (Precategory_Monad C) (functor_Precategory C C).
Proof.
  use mk_functor.
  - use mk_functor_data.
    + exact (fun M => pr1 M:functor C C).
    + exact (fun M N f => pr1 f).
  - abstract (split; red; intros;  reflexivity).
Defined.

Lemma forgetMonad_faithful C : faithful (forgetfunctor_Monad C).
Proof.
  intros M N.
  apply isinclpr1.
  apply isaprop_Monad_Mor_laws.
  apply homset_property.
Qed.

End Monad_precategory.

(** * Definition and lemmas for bind *)
Section bind.

Context {C : precategory} {T : Monad C}.

(** Definition of bind *)
Definition bind {a b : C} (f : C⟦a,T b⟧) : C⟦T a,T b⟧ := # T f · μ T b.

Lemma η_bind {a b : C} (f : C⟦a,T b⟧) : η T a · bind f = f.
Proof.
unfold bind.
rewrite assoc.
eapply pathscomp0;
  [apply cancel_postcomposition, (! (nat_trans_ax (η T) _ _ f))|]; simpl.
rewrite <- assoc.
eapply pathscomp0; [apply maponpaths, Monad_law1|].
apply id_right.
Qed.

Lemma bind_η {a : C} : bind (η T a) = identity (T a).
Proof.
apply Monad_law2.
Qed.

Lemma bind_bind {a b c : C} (f : C⟦a,T b⟧) (g : C⟦b,T c⟧) :
  bind f · bind g = bind (f · bind g).
Proof.
unfold bind; rewrite <- assoc.
eapply pathscomp0; [apply maponpaths; rewrite assoc;
                    apply cancel_postcomposition, (!nat_trans_ax (μ T) _ _ g)|].
rewrite !functor_comp, <- !assoc.
now apply maponpaths, maponpaths, (!Monad_law3 c).
Qed.

End bind.

(** * Substitution operation for monads *)
Section MonadSubst.

Context {C : precategory} (T : Monad C) (TC : Terminal C) (BC : BinCoproducts C).

Local Notation "1" := TC.
Local Notation "a ⊕ b" := (BinCoproductObject _ (BC a b)) (at level 50).

Definition monadSubst (a : C) (e : C⟦1,T a⟧) : C⟦T (a ⊕ 1), T a⟧ :=
  bind (BinCoproductArrow _ _ (η T a) e).

End MonadSubst.