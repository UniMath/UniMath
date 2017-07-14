(** **********************************************************
Contents:
        - "Kleisli" definition of monad [Kleisli]
        - equivalence of this definition and the "monoidal" definition [weq_Kleisli_Monad]

Written by: Joseph Helfer, Matthew Weaver, 2017

************************************************************)
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

(** * Definition of "Kleisli style" monad *)
Section Kleisli_def.

  Definition Kleisli_data (C : precategory) : UU :=
    ∑ T : C -> C, ((∏ a : C, a --> T a) × (∏ a b : C, a --> T b -> T a --> T b)).

  Definition ob_function_from_Kleisli_data {C : precategory} (T : Kleisli_data C) := pr1 T.
  Coercion ob_function_from_Kleisli_data : Kleisli_data >-> Funclass.

  Definition unit {C : precategory} (T : Kleisli_data C) := pr1 (pr2 T).
  Definition bind {C : precategory} (T : Kleisli_data C) {a b : C} := pr2 (pr2 T) a b.

  Definition Kleisli_laws {C : precategory} (T : Kleisli_data C) : UU :=
    ((∏ a : C, bind T (unit T a) = identity (T a)) ×
     (∏ (a b : C) (f : a --> T b), unit T a · bind T f = f)) ×
    (∏ (a b c : C) (f : a --> T b) (g : b --> T c), bind T f · bind T g = bind T (f · bind T g)).

  Lemma isaprop_Kleisli_laws {C : precategory} (hs : has_homsets C) (T : Kleisli_data C) :
    isaprop (Kleisli_laws T).
  Proof.
    do 2 try apply isapropdirprod;
    do 5 try (apply impred; intro);
    apply hs.
  Defined.

  Definition Kleisli (C : precategory) : UU := ∑ T : Kleisli_data C, Kleisli_laws T.

  Definition Kleisli_data_from_Kleisli {C : precategory} (T : Kleisli C) : Kleisli_data C := pr1 T.
  Coercion Kleisli_data_from_Kleisli : Kleisli >-> Kleisli_data.

  Definition Kleisli_law1 {C : precategory} (T : Kleisli C) := pr1 (pr1 (pr2 T)).
  Definition Kleisli_law2 {C : precategory} (T : Kleisli C) := pr2 (pr1 (pr2 T)).
  Definition Kleisli_law3 {C : precategory} (T : Kleisli C) := pr2 (pr2 T).

End Kleisli_def.

(** * Equivalence of the types of Kleisli monads and "monoidal" monads *)
Section monad_types_equiv.
  Definition Monad_to_Kleisli {C : precategory} : Monad C → Kleisli C :=
    fun T => (functor_on_objects T ,, (pr1 (η T) ,, @Monads.bind C T))
               ,, (@Monad_law2 C T ,, @η_bind C T) ,, @bind_bind C T.

  Definition Kleisli_to_functor {C : precategory} (T: Kleisli C) : C ⟶ C.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + exact T.
      + exact (fun (a b : C) (f : a --> b) => bind T (f · unit T b)).
    - apply tpair.
      + intro a; simpl.
        now rewrite id_left, (Kleisli_law1 T).
      + intros a b c f g; simpl.
        now rewrite (Kleisli_law3 T), <- !assoc, (Kleisli_law2 T).
  Defined.

  Definition Kleisli_to_μ {C : precategory} (T: Kleisli C) :
    Kleisli_to_functor T ∙ Kleisli_to_functor T ⟹ Kleisli_to_functor T.
  Proof.
    mkpair.
    - exact (fun (x : C) => bind T (identity (T x))).
    - intros x x' f; simpl.
      now rewrite (Kleisli_law3 T), <- assoc, (Kleisli_law2 T), id_right, (Kleisli_law3 T), id_left.
  Defined.

  Definition Kleisli_to_η {C : precategory} (T: Kleisli C) :
    functor_identity C ⟹ Kleisli_to_functor T.
  Proof.
    mkpair.
    - exact (unit T).
    - intros x x' f; simpl.
      now rewrite (Kleisli_law2 T).
  Defined.

  Definition Kleisli_to_Monad {C : precategory} (T : Kleisli C) : Monad C.
  Proof.
    refine (((Kleisli_to_functor T,, Kleisli_to_μ T) ,, Kleisli_to_η T) ,, _).
    do 2 try apply tpair; intros; simpl.
    - apply Kleisli_law2.
    - now rewrite (Kleisli_law3 T), <- assoc, (Kleisli_law2 T), id_right, (Kleisli_law1 T).
    - now rewrite !(Kleisli_law3 T), id_left, <- assoc, (Kleisli_law2 T), id_right.
  Defined.

  Proposition Kleisli_to_Monad_to_Kleisli {C : precategory} (hs : has_homsets C) (T : Kleisli C) :
    Monad_to_Kleisli (Kleisli_to_Monad T) = T.
  Proof.
    apply subtypeEquality'.
    - use total2_paths_f.
      + apply idpath.
      + rewrite idpath_transportf.
        apply dirprod_paths.
        * apply idpath.
        * repeat (apply funextsec; unfold homot; intro).
          simpl; unfold Monads.bind; simpl.
          now rewrite (Kleisli_law3 T), <- assoc, (Kleisli_law2 T), id_right.
    - apply (isaprop_Kleisli_laws hs).
  Defined.

  Lemma Monad_to_Kleisli_to_Monad_raw_data {C : precategory} (T : Monad C) :
    Monad_to_raw_data (Kleisli_to_Monad (Monad_to_Kleisli T)) = Monad_to_raw_data T.
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

  Definition Monad_to_Kleisli_to_Monad {C : precategory} (hs : has_homsets C) (T : Monad C) :
    Kleisli_to_Monad (Monad_to_Kleisli T) = T.
  Proof.
    apply (Monad_eq_raw_data hs).
    apply Monad_to_Kleisli_to_Monad_raw_data.
  Defined.

  Definition isweq_Monad_to_Kleisli {C : precategory} (hs: has_homsets C) :
    isweq Monad_to_Kleisli :=
    gradth _ _ (Monad_to_Kleisli_to_Monad hs) (Kleisli_to_Monad_to_Kleisli hs).

  Definition weq_Kleisli_Monad {C : precategory} (hs : has_homsets C) :
    weq (Monad C) (Kleisli C) := _,, (isweq_Monad_to_Kleisli hs).

End monad_types_equiv.
