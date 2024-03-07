Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.


Local Open Scope cat.


Section Mon_alg.

Import BifunctorNotations.
Import MonoidalNotations.

Context {C : category} (V : monoidal C).

Definition pointed : UU :=
    ∑ T, I_{V} --> T.

#[reversible=no] Coercion pointed_obj (T : pointed) : C := pr1 T.
Definition pointed_pt (T : pointed) : I_{V} --> T := pr2 T.

Definition Mon_alg_data (T : pointed) (A : C) : UU :=
    ∑ (a : T ⊗_{V} A --> A),
      (luinv_{V} _) · ((pointed_pt T) ⊗^{V}_{r} A) · a  = identity _.

#[reversible=no] Coercion Mon_alg_map {T : pointed} {X : C} (XX : Mon_alg_data T X) := pr1 XX.
Definition Mon_alg_map_comm {T : pointed} {X : C} (XX : Mon_alg_data T X) := pr2 XX.

Definition Mon_alg_mor_axioms
    {T : pointed}
    {X Y : C}
    (XX : Mon_alg_data T X)
    (YY : Mon_alg_data T Y)
    (f : X --> Y) : UU :=
  XX · f = (T ⊗^{V}_{l} f) · YY.

Lemma isaprop_Mon_alg_mor_axioms
    {T : pointed}
    {X Y : C}
    (XX : Mon_alg_data T X)
    (YY : Mon_alg_data T Y)
    (f : X --> Y) :
  isaprop (Mon_alg_mor_axioms XX YY f).
Proof.
  apply homset_property.
Qed.

Definition Mon_alg_disp_ob_mor (T : pointed) : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    exact (Mon_alg_data T X).
  - intros X Y XX YY f.
    exact (Mon_alg_mor_axioms XX YY f).
Defined.

Definition Mon_alg_disp_id_comp (T : pointed) :
    disp_cat_id_comp _ (Mon_alg_disp_ob_mor T).
Proof.
  split.
  - intros X XX.
    (* simpl.
    unfold Mon_alg_mor_axioms. *)
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply maponpaths_2.
            use (bifunctor_leftid V).
    apply id_left.
  - intros X Y Z f g XX YY ZZ ff gg.
    simpl.
    unfold Mon_alg_mor_axioms.

    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            exact ff.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            exact gg.

    apply pathsinv0.
    etrans. apply maponpaths_2.
            use (bifunctor_leftcomp V).
    apply assoc'.
(* Qed because morphisms are propositional anyway *)
Qed.

Definition Mon_alg_disp_data (T : pointed) :
    disp_cat_data C := (_,, Mon_alg_disp_id_comp T).

Definition Mon_alg_axioms (T : pointed) :
    disp_cat_axioms _ (Mon_alg_disp_data T).
Proof.
  repeat split; intros; try apply homset_property.
  apply isasetaprop.
  apply homset_property.
Defined.

Definition Mon_alg_disp (T : pointed) :
    disp_cat C := (_,, Mon_alg_axioms T).

Definition Mon_alg (T : pointed) :
    category := total_category (Mon_alg_disp T).

Lemma Mon_alg_action_alg_map_rel {T : pointed}
    (X : Mon_alg T) (A : C) :
  luinv^{ V }_{ pr1 X ⊗_{ V} A} · pointed_pt T ⊗^{ V}_{r} (pr1 X ⊗_{ V} A)
  · (αinv^{ V }_{ T, pr1 X, A} · pr12 X ⊗^{ V}_{r} A) =
  identity _.
Proof.
  destruct X as [X [x xrel]].
  (* cbn. *)

  set (trinv := monoidal_triangle_identity'_inv V X A).
  set (associnvnat := monoidal_associatorinvnatright V _ _ X A (pointed_pt T)).
  set (whiskerrightcomp := bifunctor_rightcomp V).

  etrans. apply assoc.
  etrans. apply assoc4.
  etrans. apply maponpaths_2.
          apply maponpaths.
          exact associnvnat.

  etrans. apply cancel_postcomposition.
          apply assoc.
  etrans. do 2 apply cancel_postcomposition.
          exact trinv.

  etrans. apply cancel_postcomposition.
          exact (pathsinv0 (whiskerrightcomp A _ _ _ _ _)).
  etrans. exact (pathsinv0 (whiskerrightcomp A _ _ _ _ _)).

  etrans. apply maponpaths.
          exact xrel.
  apply (bifunctor_rightid V).
Qed.

Lemma Mon_alg_action_mor_rel {T : pointed} (X : Mon_alg T)
    {A B : C} (f : A --> B) :
    Mon_alg_mor_axioms
      (_,, Mon_alg_action_alg_map_rel X A)
      (_,, Mon_alg_action_alg_map_rel X B) (pr1 X ⊗^{ V}_{l} f).
Proof.
  (* unfold Mon_alg_mor_axioms. *)
  destruct X as [X [x xrel]].
  (* cbn. *)

  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          use (whiskerscommutes _ (bifunctor_equalwhiskers V)).

  etrans. apply assoc.
  apply pathsinv0.
  etrans. apply assoc.
  apply cancel_postcomposition.

  apply (monoidal_associatorinvnatleft V).
Qed.

Definition Mon_alg_right_action_data {T : pointed} (X : Mon_alg T) :
  functor_data C (Mon_alg T).
Proof.
  use make_functor_data.
  - intro A.
    exists ((pr1 X) ⊗_{V} A).
    cbn.
    (* unfold Mon_alg_data. *)
    exists ((αinv_{V} T (pr1 X) A) · ((pr12 X) ⊗^{V}_{r} A)).
    apply Mon_alg_action_alg_map_rel.
  - intros A B f.
    simpl.
    exists ((pr1 X) ⊗^{V}_{l} f).
    exact (Mon_alg_action_mor_rel X f).
Defined.

Definition Mon_alg_right_action_axioms {T : pointed} (X : Mon_alg T) :
    is_functor (Mon_alg_right_action_data X).
Proof.
  split.
  - intro x.
    apply subtypePath; [intro; apply isaprop_Mon_alg_mor_axioms|].
    use (bifunctor_leftid V).
  - intros A B D f g.
    apply subtypePath; [intro; apply isaprop_Mon_alg_mor_axioms|].
    use (bifunctor_leftcomp V).
Qed.

Definition Mon_alg_right_action {T : pointed} (X : Mon_alg T) :
    functor C (Mon_alg T) :=
  (_,, Mon_alg_right_action_axioms X).

(* basically want to formalize Garner / Kelly (generalized) stuff about
   T-Alg (/ T-Mod in Garner)
   and how one obtains a monoid from the free T-algebra
   Mon should be a monoidal category (Ff_C) is at least
*)
Definition Mon_alg_forgetful_functor (T : pointed) :
    functor (Mon_alg T) C :=
  pr1_category _.

(* todo: show that this holds whenever sequence on I --> X
   converges *)
Definition alg_forgetful_functor_right_action_is_adjoint {T : pointed} (X : Mon_alg T) : UU :=
    are_adjoints (Mon_alg_right_action X) (Mon_alg_forgetful_functor T).

(* not every object can be pointed in a general monoidal category *)
Definition alg_forgetful_functor_right_action_is_adjoint_induced_mul {T : pointed} (X : Mon_alg T)
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :
  (pr1 X) ⊗_{V} (pr1 X) --> (pr1 X).
Proof.
  destruct X as [X [x rel]].
  set (m := Monad_from_adjunction Adj).
  set (μ := μ m (I_{V})).

  (* simpl in μ.
  cbn. *)
  exact (X ⊗^{V}_{l} (ruinv_{V} X) ·
         μ ·
         ru_{V} X).
Defined.

Definition alg_forgetful_functor_right_action_is_adjoint_monoid_data
    {T : pointed} {X : Mon_alg T}
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :
  monoid_data V (pr1 X).
Proof.
  exists (alg_forgetful_functor_right_action_is_adjoint_induced_mul X Adj).
  set (η := unit_from_are_adjoints Adj I_{V} · ru_{V} (pr1 X)).
  exact η.
Defined.

Definition alg_forgetful_functor_right_action_adjoint_monad_unit_preserves_right_tensor
    {T : pointed} {X : Mon_alg T}
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :=
  let m := Monad_from_adjunction Adj in
  ∏ (Y : C),
    η m Y =
      luinv_{V} Y ·
      η m I_{V} ⊗^{V}_{r} Y ·
      (ru_{V} (pr1 X)) ⊗^{V}_{r} Y.


(* need:
pr1 X ⊗^{ V}_{l} (pr1 X ⊗^{ V}_{l} ruinv^{ V }_{ pr1 X}) · μ m (m I_{ V})
    =
    αinv^{ V }_{ pr1 X, pr1 X, pr1 X}
    · (pr1 X ⊗^{ V}_{l} ruinv^{ V }_{ pr1 X}
        · μ (Monad_from_adjunction Adj) I_{ V} · ru^{ V }_{ pr1 X})
      ⊗^{ V}_{r} pr1 X · pr1 X ⊗^{ V}_{l} ruinv^{ V }_{ pr1 X} *)
Definition alg_forgetful_functor_right_action_adjoint_monad_mul_preserves_right_tensor
      {T : pointed} {X : Mon_alg T}
      (Adj : alg_forgetful_functor_right_action_is_adjoint X) :=
    let m := Monad_from_adjunction Adj in
    ∏ (Y : C),
        μ m Y =
          αinv_{V} _ _ _ ·
          (_ ⊗^{V}_{l} ruinv_{V} _) ⊗^{V}_{r} _ ·
          μ m I_{V} ⊗^{V}_{r} Y ·
          ru_{V} _ ⊗^{V}_{r} _.

(* Definition alg_forgetful_functor_right_action_adjoint_monad_mul_preserves_right_tensor
      {T : pointed} {X : Mon_alg T}
      (Adj : alg_forgetful_functor_right_action_is_adjoint X) :=
    let m := Monad_from_adjunction Adj in
    ∏ (Y : C),
        μ m Y =
          (pr1 X) ⊗^{V}_{l} ((pr1 X) ⊗^{V}_{l} luinv_{V} Y) ·
          (pr1 X) ⊗^{V}_{l} αinv_{V} _ _ _ ·
          αinv_{V} _ _ _ ·
          μ m I_{V} ⊗^{V}_{r} Y ·
          (α_{V} _ _ _) ·
          (pr1 X) ⊗^{V}_{l} lu_{V} Y. *)

Definition alg_forgetful_functor_right_action_is_adjoint_monoid_laws
    {T : pointed} {X : Mon_alg T}
    {Adj : alg_forgetful_functor_right_action_is_adjoint X}
    (ηr : alg_forgetful_functor_right_action_adjoint_monad_unit_preserves_right_tensor Adj)
    (μr : alg_forgetful_functor_right_action_adjoint_monad_mul_preserves_right_tensor Adj) :
  monoid_laws V (alg_forgetful_functor_right_action_is_adjoint_monoid_data Adj).
Proof.
  (* these should just follow from the monad laws of Monad_from_adjunction Adj *)
  set (m := Monad_from_adjunction Adj).
  set (u := unit_from_are_adjoints Adj).
  repeat split.
  -
    (* unfold monoid_laws_unit_left.
    cbn.
    unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul. *)
    (* cbn. *)

    etrans. apply maponpaths_2.
            apply (bifunctor_rightcomp V).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition, assoc.
    etrans. apply cancel_postcomposition, assoc4.
    etrans. do 2 apply cancel_postcomposition.
            apply maponpaths.
            apply (whiskerscommutes _ (bifunctor_equalwhiskers V)).

    etrans. do 2 apply cancel_postcomposition.
    {
      etrans. apply assoc.
      apply cancel_postcomposition.
      apply (whiskerscommutes _ (bifunctor_equalwhiskers V)).
    }

    (* transform rhs to identity (m I_{V}) (== identity (pr1 X))
       then plug in monad law 1 *)
    apply pathsinv0.
    apply (pre_comp_with_z_iso_is_inj
            (is_inverse_in_precat_inv (monoidal_leftunitorisolaw V _))).
    apply (pre_comp_with_z_iso_is_inj
             (monoidal_rightunitorisolaw V _)).
    apply (post_comp_with_z_iso_is_inj
             (is_inverse_in_precat_inv (monoidal_rightunitorisolaw V (pr1 X)))).
    etrans.
    {
      etrans. apply cancel_postcomposition.
              apply cancel_precomposition.
              apply (monoidal_leftunitorisolaw V _).
      etrans. apply cancel_postcomposition.
              apply id_right.
      etrans. apply (monoidal_rightunitorisolaw V _).
      exact (pathsinv0 (Monad_law1 (T := m) I_{V})).
    }

    (* cbn. *)

    apply pathsinv0.
    etrans. apply cancel_postcomposition, assoc.
    etrans. apply cancel_postcomposition, assoc.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply (monoidal_rightunitorisolaw V _).
    etrans. apply id_right.

    etrans. apply assoc.
    apply cancel_postcomposition.

    apply pathsinv0.
    etrans. apply ηr.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition, assoc.
    do 2 apply cancel_postcomposition.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply (monoidal_leftunitorinvnat V).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (monoidal_rightunitorisolaw V _).
    apply id_left.
  -
    (* unfold monoid_laws_unit_right.
    cbn.
    unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul.
     *)
    etrans. apply cancel_postcomposition.
            apply (bifunctor_leftcomp V).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. do 2 apply cancel_postcomposition.
    etrans. apply assoc'.
            apply cancel_precomposition.
    {
        etrans. apply (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
        etrans. apply maponpaths.
                exact (pr1 (monoidal_rightunitorisolaw V (pr1 X))).
        apply (bifunctor_leftid V).
    }
    etrans. do 2 apply cancel_postcomposition.
            apply id_right.

    apply pathsinv0.
    etrans. apply (pathsinv0 (id_left _)).
    apply cancel_postcomposition.
    apply pathsinv0.
    exact (Monad_law2 (T := m) I_{V}).
  -
    (* unfold monoid_laws_assoc. *)
    (* cbn. *)
    (* unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul. *)
    (* cbn. *)
    etrans. apply cancel_postcomposition.
            apply maponpaths.
            apply (bifunctor_leftcomp V).
    etrans. apply cancel_postcomposition.
            apply maponpaths.
            apply maponpaths_2.
            apply (bifunctor_leftcomp V).

    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. do 3 apply cancel_postcomposition.
            apply assoc.
    etrans. do 2 apply cancel_postcomposition.
            apply assoc'.
    etrans. do 2 apply cancel_postcomposition.
            apply maponpaths.
    {
      exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
    }
    etrans. do 2 apply cancel_postcomposition.
            do 2 apply maponpaths.
    {
      exact (pr1 (monoidal_rightunitorisolaw V (pr1 X))).
    }
    etrans. do 2 apply cancel_postcomposition.
            apply maponpaths.
            apply (bifunctor_leftid V).
    etrans. do 2 apply cancel_postcomposition.
            apply id_right.

    etrans. do 2 apply cancel_postcomposition.
            apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc'.
    etrans. apply cancel_postcomposition.
            apply cancel_precomposition.
    (* #m (μ m I_{V}) = X ⊗^{V}_{l} μ m I_{V} *)
            exact (Monad_law3 (T := m) I_{V}).

    (* cbn. *)
    etrans. apply maponpaths_2.
            apply assoc.
    apply pathsinv0.
    etrans. apply assoc.
    apply cancel_postcomposition.
    etrans. apply assoc.
    apply cancel_postcomposition.
    apply pathsinv0.

    apply (pre_comp_with_z_iso_is_inj
            (is_inverse_in_precat_inv (monoidal_associatorisolaw V _ _ _))).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition, assoc.
    etrans. do 2 apply cancel_postcomposition.
            apply (monoidal_associatorisolaw V).
    etrans. apply assoc'.
    etrans. apply id_left.

    etrans. apply maponpaths.
            apply μr.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition, assoc.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply cancel_precomposition.
    {
      etrans. apply (bifunctor_rightcomp V).
      apply cancel_postcomposition.
      apply (bifunctor_rightcomp V).
    }

    etrans. apply cancel_postcomposition, assoc.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply (whiskerscommutes _ (bifunctor_equalwhiskers V)).
    etrans. apply assoc.
    apply cancel_postcomposition.

    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
    {
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply (whiskerscommutes _ (bifunctor_equalwhiskers V)).
    }
    do 2 (etrans; [apply assoc|]).
    apply cancel_postcomposition.

    etrans. apply cancel_postcomposition.
            apply (pathsinv0 (monoidal_associatorinvnatleftright V _ _ _ _ _)).

    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply (pathsinv0 (monoidal_associatorinvnatleftright V _ _ _ _ _)).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
    {
      etrans. apply (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
      etrans. apply maponpaths.
      apply (pathsinv0 (whiskerscommutes _ (bifunctor_equalwhiskers V) _ _)).
      apply (bifunctor_leftcomp V).
    }
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    apply cancel_precomposition.

    apply pathsinv0.
    apply (monoidal_associatorinvnatleft V).
Qed.

Definition alg_forgetful_functor_right_action_is_adjoint_monoid
    {T : pointed} {X : Mon_alg T}
    {Adj : alg_forgetful_functor_right_action_is_adjoint X}
    (ηr : alg_forgetful_functor_right_action_adjoint_monad_unit_preserves_right_tensor Adj)
    (μr : alg_forgetful_functor_right_action_adjoint_monad_mul_preserves_right_tensor Adj) :
  monoid _ _ := (_,, alg_forgetful_functor_right_action_is_adjoint_monoid_laws ηr μr).

(* todo: define free monoid *)
(* Lemma alg_free_monad_exists_if_alg_forgetful_functor_right_action_is_adjoint {T : pointed} (X : Mon_alg T) :
    alg_forgetful_functor_right_action_is_adjoint X -> (total_category (NWFS C)).
Proof.
  intro Adj.

  exists (pr11 X).
  split; [exact (pr21 X)|].

  exists (alg_forgetful_functor_right_action_is_adjoint_induced_mul Adj).
  exact (alg_forgetful_functor_right_action_is_adjoint_monad_laws Adj).
Defined. *)

End Mon_alg.
