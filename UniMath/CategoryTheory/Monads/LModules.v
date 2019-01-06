(** **********************************************************
Contents:
        - Definition of left modules ([LModule R]) over a monad [R] on [C]
        - category of left modules [category_LModule R D] of range [D] over a monad [R] on [C]
        - Tautological left module [tautological_LModule] : a monad is a module over itself
        - Forgetful functor to the category of endofunctors [LModule_forget_functor]
        - Pullback f* M of a module M along a monad morphism f [pb_LModule]
        - Pullback of a module morphism along a monad morphism [pb_LModule_Mor]
        - The pullback functor [pb_LModule_functor]
        - Isomorphisms between modules sharing the same underlying
          functor and have pointwise equal multiplication [LModule_same_func_iso]
        - Isomorphism between a module and its pullback along the identity morphism [pb_LModule_id_iso]
        - Isomorphism between f*(g*(M)) and (fog)* M, where f and g are monad morphisms and M
          is a module [pb_LModule_comp_iso]


Following the scheme of Monads.v

Written by: Ambroise Lafont (November 2016)

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

(** * Definition of module *)
Section LModule_over_monad.

 Context {B:precategory_data} (M:Monad B) .
  (** Definition of modules over M of codomain D **)

Section LModule_def.




Definition LModule_data (D:precategory_data) : UU
  := ∑ F : functor B D, F □ M ⟹ F.

Coercion functor_from_LModule_data (C : precategory_data) (F : LModule_data C)
  : functor B C := pr1 F.

Definition lm_mult {C : precategory_data} (F : LModule_data C) : F□M ⟹ F := pr2 F.
Local Notation σ := lm_mult.

Definition LModule_laws  {C:precategory_data} (T : LModule_data C) : UU :=
      (∏ c : B, #T (η M c) · σ T c = identity (T c))
        × (∏ c : B, #T ((μ M) c) · σ T c = σ T (M c) · σ T c).

Lemma isaprop_LModule_laws (C : precategory_data) (hs : has_homsets C) (T : LModule_data C) :
   isaprop (LModule_laws T).
Proof.
  repeat apply isapropdirprod;
  apply impred; intro c; apply hs.
Qed.

Definition LModule (C : precategory_data) : UU := ∑ T : LModule_data C, LModule_laws T.

Coercion LModule_data_from_LModule (C : precategory_data) (T : LModule C) : LModule_data C := pr1 T.


Lemma LModule_law1 {C : precategory_data} {T : LModule C} : ∏ c : B, #T (η M c) · σ T c = identity (T c).
Proof.
exact ( (pr1 (pr2 T))).
Qed.

Lemma LModule_law2 {C : precategory_data} {T : LModule C} :
  ∏ c : B, #T ((μ M) c) · σ T c = σ T (M c) · σ T c.
Proof.
exact (pr2 ( (pr2 T))).
Qed.

End LModule_def.

(** * Monad precategory *)
Section LModule_precategory.

Local Notation σ := lm_mult.
Definition LModule_Mor_laws {C : precategory_data} {T T' : LModule_data C} (α : T ⟹ T')
  : UU :=
  ∏ a : B, α (M a) · σ T' a = σ T a · α a.


Lemma isaprop_LModule_Mor_laws (C : precategory_data) (hs : has_homsets C)
  (T T' : LModule_data C) (α : T ⟹ T')
  : isaprop (LModule_Mor_laws α).
Proof.
  apply impred; intro c; apply hs.
Qed.

Definition LModule_Mor {C : precategory_data} (T T' : LModule C) : UU
  := ∑ α : T ⟹ T', LModule_Mor_laws α.


Coercion nat_trans_from_module_mor (C : precategory_data) (T T' : LModule C) (s : LModule_Mor T T')
   : T ⟹ T' := pr1 s.

Definition LModule_Mor_σ {C : precategory_data} {T T' : LModule C} (α : LModule_Mor T T')
           : ∏ a : B, α (M a) · σ T' a = σ T a · α a
  := pr2 α.

Lemma LModule_identity_laws {C : precategory} (T : LModule C)
  : LModule_Mor_laws (nat_trans_id T).
Proof.
  intro x.
  now rewrite id_right, id_left.
Qed.

Definition LModule_identity {C : precategory} (T : LModule C)
: LModule_Mor T T := tpair _ _ (LModule_identity_laws T).

Lemma LModule_composition_laws {C : precategory} {T T' T'' : LModule C}
  (α : LModule_Mor T T') (α' : LModule_Mor T' T'') : LModule_Mor_laws (nat_trans_comp _ _ _ α α').
Proof.
  red;intros; simpl.
  unfold nat_trans_from_module_mor.
  rewrite assoc.
    etrans; revgoals.
    apply cancel_postcomposition.
    apply (LModule_Mor_σ α a).
    rewrite <- !assoc.
    apply cancel_precomposition.
    apply (LModule_Mor_σ α' a).
Qed.

Definition LModule_composition {C : precategory} {T T' T'' : LModule C}
  (α : LModule_Mor T T') (α' : LModule_Mor T' T'')
  : LModule_Mor T T'' := tpair _ _ (LModule_composition_laws α α').

Definition LModule_Mor_equiv {C : precategory_data} (hs : has_homsets C)
  {T T' : LModule C} (α β : LModule_Mor T T')
  : α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_LModule_Mor_laws, hs.
Defined.

Definition precategory_LModule_ob_mor (C : precategory_data) : precategory_ob_mor.
Proof.
  exists (LModule C).
  exact (λ T T' : LModule C, LModule_Mor T T').
Defined.

Definition precategory_LModule_data (C : precategory) : precategory_data.
Proof.
  exists (precategory_LModule_ob_mor C).
  exists (@LModule_identity C).
  exact (@LModule_composition C).
Defined.


Lemma precategory_LModule_axioms (C : precategory) (hs : has_homsets C)
  : is_precategory (precategory_LModule_data C).
Proof.
    repeat split; simpl; intros.
  - apply (invmap (LModule_Mor_equiv hs _ _ )).
    apply (@id_left (functor_precategory B C hs)).
  - apply (invmap (LModule_Mor_equiv hs _ _ )).
    apply (@id_right (functor_precategory B C hs)).
  - apply (invmap (LModule_Mor_equiv hs _ _ )).
    apply (@assoc (functor_precategory B C hs)).
  - apply (invmap (LModule_Mor_equiv hs _ _ )).
    apply (@assoc' (functor_precategory B C hs)).
Qed.

Definition precategory_LModule (C : category) : precategory
  := tpair _ _ (precategory_LModule_axioms C (homset_property C)).

Lemma has_homsets_LModule (C : category) :
  has_homsets (precategory_LModule C).
Proof.
  intros F G.
  apply isaset_total2 .
  - apply isaset_nat_trans.
    apply homset_property.
  - intros m.
    apply isasetaprop.
    apply isaprop_LModule_Mor_laws.
    apply homset_property.
Qed.

Definition category_LModule (C : category) : category :=
  (precategory_LModule C,, has_homsets_LModule C).



End LModule_precategory.

(** Any monad is a left module over itself *)
Definition tautological_LModule_data  : LModule_data B := ((M:functor _ _) ,, μ M).

Lemma tautological_LModule_law  : LModule_laws tautological_LModule_data.
Proof.
  split; intro c.
  - apply Monad_law2.
  - apply Monad_law3.
Qed.

Definition tautological_LModule : LModule B :=
  (tautological_LModule_data ,, tautological_LModule_law).

End LModule_over_monad.

(** The forgetful functor from the category of left modules to the category of
  endofunctors *)
Section ForgetLModFunctor.
  Context {B : precategory} (R : Monad B) (C : category).
  Local Notation MOD := (precategory_LModule R C).

  Definition LModule_forget_functor_data : functor_data MOD [B,C] :=
    mk_functor_data (C := MOD) (C' := [B,C])
                    (fun X => ((X : LModule _ _): functor _ _))
                    (fun a b f => ((f : LModule_Mor _ _ _) : nat_trans _ _)).

  Definition LModule_forget_is_functor : is_functor LModule_forget_functor_data :=
    (( fun x => idpath _) : functor_idax LModule_forget_functor_data)
      ,, ((fun a b c f g => idpath _) : functor_compax LModule_forget_functor_data).

  Definition LModule_forget_functor: functor MOD [B,C] :=
    mk_functor LModule_forget_functor_data LModule_forget_is_functor.
End ForgetLModFunctor.

(** Let m : M -> M' a monad morphism.

m induces a functor m* between the category of left modules over M' and the category of
left modules over M

If T is a module over M', we call m* T the pullback module of T along m
*)
Section Pullback_module.


  Context {B: precategory_data} {M M': Monad B} (m: Monad_Mor M M').
  Context {C: precategory}.

  Variable (T:LModule M' C).
  Notation "Z ∘ α" := (post_whisker α Z).
  Local Notation σ := lm_mult.

  Definition pb_LModule_σ : T □ M ⟹ T :=  nat_trans_comp _ _ _ (T ∘ m)  (σ _ T).

  Definition pb_LModule_data : ∑ F : functor B C, F □ M ⟹ F :=
    tpair _ (T:functor B C) pb_LModule_σ.

  Lemma pb_LModule_laws : LModule_laws M pb_LModule_data.
  Proof.
    split.
    - intro c.
      cbn.
      rewrite <- (LModule_law1 _ (T:=T)).
      rewrite <- (Monad_Mor_η m).
      rewrite functor_comp.
      apply assoc.
    - simpl.
      intro c.
      rewrite assoc.
      rewrite <- (functor_comp T).
      etrans.
      apply cancel_postcomposition.
      apply maponpaths.
      apply Monad_Mor_μ.
      rewrite functor_comp.
      rewrite <- assoc.
      etrans.
      apply cancel_precomposition.
      apply LModule_law2.
      repeat rewrite functor_comp.
      etrans.
      rewrite <- assoc.
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      apply (nat_trans_ax (σ M' T)).
      now repeat rewrite assoc.
  Qed.

  Definition pb_LModule : LModule M C := tpair _ _ pb_LModule_laws.

End Pullback_module.

(**

Let m:M -> M' be a monad morphism et n : T -> T' a morphism in the category of modules over M'.
In this section we construct the morphism m* n : m*T -> m*T' in the category of modules over M
between the pullback modules along m.

*)
Section Pullback_Module_Morphism.

  Context {B: precategory_data} {M M': Monad B} (m: Monad_Mor M M') {C: precategory} {T T': LModule M' C}
          (n: LModule_Mor _ T T').

  Local Notation pbmT := (pb_LModule m T).
  Local Notation pbmT' := (pb_LModule m T').

  Lemma pb_LModule_Mor_law : LModule_Mor_laws M (T:=pbmT) (T':=pbmT') n.
  Proof.
    intros b.
    cbn.
    eapply pathscomp0; revgoals.
    - rewrite <-assoc.
      apply cancel_precomposition.
      apply LModule_Mor_σ.
    - repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0.
      apply nat_trans_ax.
  Qed.

  Definition pb_LModule_Mor : LModule_Mor _  pbmT pbmT'  := (_ ,, pb_LModule_Mor_law).

End Pullback_Module_Morphism.

(**  The pullback functor
A monad morphism  f : R -> S induces a functor between the category of modules over S
and the category of modules over R.
 *)
Section PbmFunctor.
  Context {B : precategory} {C : category} {R S : Monad B} (f : Monad_Mor R S).
  Let MOD (R : Monad B) := (precategory_LModule R C).
  Definition pb_LModule_functor_data : functor_data (MOD S) (MOD R) :=
    mk_functor_data (C := MOD S) (C' := MOD R) (pb_LModule f )
                    (@pb_LModule_Mor _ _ _ f _).
  Lemma pb_LModule_is_functor : is_functor pb_LModule_functor_data.
  Proof.
    split.
    - intro M.
      apply LModule_Mor_equiv;[apply homset_property|]; apply idpath.
    - intros X Y Z u v.
      apply LModule_Mor_equiv;[apply homset_property|]; apply idpath.
  Qed.

  Definition pb_LModule_functor : functor (MOD S) (MOD R) :=
                              mk_functor _ pb_LModule_is_functor.
End PbmFunctor.
(**
Construction of an isomorphism between modules sharing the same underlying
      functor and have pointwise equal multiplication [LModule_M1_M2_iso]
*)
Section IsoLModPb.
  Context {B} {R:Monad B}  {C:precategory}
          {F : functor B C}.

  (**  Module morphism between two modules sharing the same functor F
    and having pointwise equal multiplication *)
  Lemma LModule_same_func_Mor_laws
    {m1 m2 : R ∙ F ⟹ F }
      (hm : ∏ c, m1 c = m2 c)
    :
      LModule_Mor_laws R (T := (F ,, m1)) (T' := (F ,, m2)) (nat_trans_id _).
  Proof.
    intro c.
    etrans;[apply id_left|].
    apply pathsinv0.
    etrans;[apply ( (id_right _))|].
    apply hm.
  Qed.

  Definition LModule_same_func_Mor
    {m1 m2 : R ∙ F ⟹ F }
      (hm : ∏ c, m1 c = m2 c)
    (m1_law : LModule_laws _ (F ,, m1))
    (m2_law : LModule_laws _ (F ,, m2))
    (M1 : LModule _ _ := _ ,, m1_law)
    (M2 : LModule _ _ := _ ,, m2_law)
    :
      LModule_Mor R M1 M2 :=
      _ ,, LModule_same_func_Mor_laws hm .


  Context {m1 m2 : R ∙ F ⟹ F }.

  Let F_data1 : LModule_data _ _ := F ,, m1.
  Let F_data2 : LModule_data _ _ := F ,, m2.

  Context (m1_law : LModule_laws _ F_data1).
  Context (m2_law : LModule_laws _ F_data2).

  (** The multiplication are pointwise equal *)
  Context (hm : ∏ c, m1 c = m2 c).

  Let M1 : LModule _ _ := _ ,, m1_law.
  Let M2 : LModule _ _ := _ ,, m2_law.



  (** Isomorphism between M1 and M2 *)
  Lemma LModule_same_func_Mor_is_inverse hsC :
    is_inverse_in_precat (C := precategory_LModule R (category_pair C hsC) )
                         (LModule_same_func_Mor hm m1_law m2_law)
                         (LModule_same_func_Mor (fun c => ! (hm c)) m2_law m1_law).
  Proof.
    use mk_is_inverse_in_precat.
    - apply LModule_Mor_equiv;[ apply homset_property|].
      apply  (id_left (C := [B ,C , hsC])).
    - apply LModule_Mor_equiv;[ apply homset_property|].
      apply  (id_right (C := [B ,C , hsC])).
  Qed.

  Definition LModule_same_func_iso hsC : iso (C := precategory_LModule R (category_pair C hsC) )
                                         M1 M2.
  Proof.
    eapply isopair.
    eapply is_iso_from_is_z_iso.
    eapply mk_is_z_isomorphism.
    apply LModule_same_func_Mor_is_inverse.
  Defined.

End IsoLModPb.

(**
Let T be a module on M'.

In this section, we construct the module morphism T -> id* T (which is
actully an iso) where id* T is the pullback module of T along
the identity morphism in M'.

and also the morphism id* T -> T

*)
Section Pullback_Identity_Module.

Context {B : precategory} {M' : Monad B}  {C : precategory} {T : LModule M' C}.

Local Notation pbmid := (pb_LModule (Monad_identity M') T).

Lemma pbm_id_law :
  ∏ c : B, (lm_mult _ T) c = (pb_LModule_σ (Monad_identity M') T) c.
Proof.
  intro c.
  cbn.
  apply pathsinv0.
  etrans;[|apply id_left].
  apply cancel_postcomposition.
  apply functor_id.
Qed.

Definition pb_LModule_id_iso hsC : iso (C := precategory_LModule _ (C ,, hsC)) T pbmid :=
  LModule_same_func_iso _ _ pbm_id_law hsC.



End Pullback_Identity_Module.

(**
In this section, we construct the isomorphism between
m*(m'*(T'')) and (m o m')*(T'') where m and m' are monad
 morphisms, and T'' is a left module.
*)

Section Pullback_Composition.

Context {B : precategory} {M M' : Monad B} (m : Monad_Mor M M') {C : precategory}
        {M'' : Monad B} (m' : Monad_Mor M' M'') (T'' : LModule M'' C).

Local Notation comp_pbm := (pb_LModule m (pb_LModule m' T'')).
Local Notation pbm_comp := (pb_LModule (Monad_composition m  m') T'').

  Lemma pb_LModule_comp_law  (c : B) :
    (pb_LModule_σ m (pb_LModule m' T'')) c = (pb_LModule_σ (Monad_composition m m') T'') c.
  Proof.
    cbn.
    etrans; [apply assoc|].
    apply cancel_postcomposition.
    apply pathsinv0.
    apply functor_comp.
  Qed.
  Definition pb_LModule_comp_iso hsC : iso  (C := category_LModule _ (category_pair C hsC)) comp_pbm pbm_comp  :=
    LModule_same_func_iso _ _ pb_LModule_comp_law hsC.


End Pullback_Composition.