(** **********************************************************
Contents:
        - "Kleisli" definition of monad [kleisli]
        - equivalence of this definition and the "monoidal" definition [weq_kleisli_monad]

Written by: Joseph Helfer, Matthew Weaver, 2017

************************************************************)
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.

Local Open Scope cat.

(** * Definition of "Kleisli style" monad *)
Section kleisli_def.

  Definition kleisli_data (C : precategory) : UU :=
    ∑ T : C -> C, ((∏ a : C, a --> T a) × (∏ a b : C, a --> T b -> T a --> T b)).

  Definition ob_function_from_kleisli_data {C : precategory} (T : kleisli_data C) := pr1 T.
  Coercion ob_function_from_kleisli_data : kleisli_data >-> Funclass.

  Definition unit {C : precategory} (T : kleisli_data C) := pr1 (pr2 T).
  Definition bind {C : precategory} (T : kleisli_data C) {a b : C} := pr2 (pr2 T) a b.

  Definition kleisli_laws {C : precategory} (T : kleisli_data C) : UU :=
    ((∏ a : C, bind T (unit T a) = identity (T a)) ×
     (∏ (a b : C) (f : a --> T b), unit T a · bind T f = f)) ×
    (∏ (a b c : C) (f : a --> T b) (g : b --> T c), bind T f · bind T g = bind T (f · bind T g)).

  Lemma isaprop_kleisli_laws {C : precategory} (hs : has_homsets C) (T : kleisli_data C) :
    isaprop (kleisli_laws T).
  Proof.
    do 2 try apply isapropdirprod;
    do 5 try (apply impred; intro);
    apply hs.
  Defined.

  Definition kleisli (C : precategory) : UU := ∑ T : kleisli_data C, kleisli_laws T.

  Definition kleisli_data_from_kleisli {C : precategory} (T : kleisli C) : kleisli_data C := pr1 T.
  Coercion kleisli_data_from_kleisli : kleisli >-> kleisli_data.

  Definition kleisli_law1 {C : precategory} (T : kleisli C) := pr1 (pr1 (pr2 T)).
  Definition kleisli_law2 {C : precategory} (T : kleisli C) := pr2 (pr1 (pr2 T)).
  Definition kleisli_law3 {C : precategory} (T : kleisli C) := pr2 (pr2 T).

End kleisli_def.

(** * Equivalence of the types of Kleisli monads and "monoidal" monads *)
Section monad_types_equiv.
  Definition Monad_to_kleisli {C : precategory} : Monad C → kleisli C :=
    fun T => (functor_on_objects T ,, (pr1 (η T) ,, @Monads.bind C T))
               ,, (@Monad_law2 C T ,, @η_bind C T) ,, @bind_bind C T.

  Definition kleisli_to_functor {C : precategory} (T: kleisli C) : C ⟶ C.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + exact T.
      + exact (fun (a b : C) (f : a --> b) => bind T (f · unit T b)).
    - apply tpair.
      + intro a; simpl.
        now rewrite id_left, (kleisli_law1 T).
      + intros a b c f g; simpl.
        now rewrite (kleisli_law3 T), <- !assoc, (kleisli_law2 T).
  Defined.

  Definition kleisli_to_μ {C : precategory} (T: kleisli C) :
    kleisli_to_functor T ∙ kleisli_to_functor T ⟹ kleisli_to_functor T.
  Proof.
    mkpair.
    - exact (fun (x : C) => bind T (identity (T x))).
    - intros x x' f; simpl.
      now rewrite (kleisli_law3 T), <- assoc, (kleisli_law2 T), id_right, (kleisli_law3 T), id_left.
  Defined.

  Definition kleisli_to_η {C : precategory} (T: kleisli C) :
    functor_identity C ⟹ kleisli_to_functor T.
  Proof.
    mkpair.
    - exact (unit T).
    - intros x x' f; simpl.
      now rewrite (kleisli_law2 T).
  Defined.

  Definition kleisli_to_Monad {C : precategory} (T : kleisli C) : Monad C.
  Proof.
    refine (((kleisli_to_functor T,, kleisli_to_μ T) ,, kleisli_to_η T) ,, _).
    do 2 try apply tpair; intros; simpl.
    - apply kleisli_law2.
    - now rewrite (kleisli_law3 T), <- assoc, (kleisli_law2 T), id_right, (kleisli_law1 T).
    - now rewrite !(kleisli_law3 T), id_left, <- assoc, (kleisli_law2 T), id_right.
  Defined.

  Proposition kleisli_to_Monad_to_kleisli {C : precategory} (hs : has_homsets C) (T : kleisli C) :
    Monad_to_kleisli (kleisli_to_Monad T) = T.
  Proof.
    apply subtypeEquality'.
    - use total2_paths_f.
      + apply idpath.
      + rewrite idpath_transportf.
        apply dirprod_paths.
        * apply idpath.
        * repeat (apply funextsec; unfold homot; intro).
          simpl; unfold Monads.bind; simpl.
          now rewrite (kleisli_law3 T), <- assoc, (kleisli_law2 T), id_right.
    - apply (isaprop_kleisli_laws hs).
  Defined.

  Lemma Monad_to_kleisli_to_Monad_raw_data {C : precategory} (T : Monad C) :
    Monad_to_raw_data (kleisli_to_Monad (Monad_to_kleisli T)) = Monad_to_raw_data T.
  Proof.
    use total2_paths_f.
    - apply idpath.
    - rewrite idpath_transportf.
      apply dirprod_paths.
      + apply dirprod_paths;
        repeat (apply funextsec; unfold homot; intro);
        simpl.
        * unfold Monads.bind, bind, unit; simpl.
          rewrite (functor_comp T), <- assoc.
          change (# T x1 · (# T (η T x0) · μ T x0) = #T x1).
          now rewrite (@Monad_law2 C T x0), id_right.
        * unfold Monads.bind, bind; simpl.
          now rewrite (functor_id T), id_left.
      + apply idpath.
  Defined.

  Definition Monad_to_kleisli_to_Monad {C : precategory} (hs : has_homsets C) (T : Monad C) :
    kleisli_to_Monad (Monad_to_kleisli T) = T.
  Proof.
    apply (Monad_eq_raw_data hs).
    apply Monad_to_kleisli_to_Monad_raw_data.
  Defined.

  Definition isweq_Monad_to_kleisli {C : precategory} (hs: has_homsets C) :
    isweq Monad_to_kleisli :=
    gradth _ _ (Monad_to_kleisli_to_Monad hs) (kleisli_to_Monad_to_kleisli hs).

  Definition weq_kleisli_monad {C : precategory} (hs : has_homsets C) :
    weq (Monad C) (kleisli C) := _,, (isweq_Monad_to_kleisli hs).

End monad_types_equiv.
