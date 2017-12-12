(** The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Foundations.Propositions.

(* Functors and algebras *)

Definition prefunctor : UU :=
  total2 (λ F : UU -> UU, ∏ A B : UU, (A -> B) -> F A -> F B).

Definition on_objects (F : prefunctor) : UU -> UU :=
  pr1 F.

Definition on_maps (F : prefunctor) {A B : UU} (f : A -> B) :
                     on_objects F A -> on_objects F B :=
  pr2 F _ _ f.



(* I chose the levels arbitrarily *)
Notation "F .0" :=
  (on_objects F) (at level 60, right associativity) : functor_scope.
Notation "F .1" :=
  (on_maps F) (at level 60, right associativity) : functor_scope.

Open Scope functor_scope.

Definition id_to_id (F : prefunctor) : UU :=
  ∏ A : UU, F.1 (idfun A) = (idfun _).

Definition comp_to_comp (F : prefunctor) : UU :=
  ∏ A B C : UU, ∏ f : A -> B, ∏ g : B -> C,
    F.1 (g ∘ f) = (F.1 g) ∘ (F.1 f).

Definition is_functor (F : prefunctor) : UU :=
  (id_to_id F) × (comp_to_comp F).


Definition functor : UU :=
  total2 (λ F : prefunctor, is_functor F).


Coercion functor_to_prefunctor (F : functor) : prefunctor :=
  pr1 F.

Definition functor_id_to_id (F : functor) :
                              ∏ A : UU, F.1 (idfun A) = (idfun _) :=
  pr1 (pr2 F).

Definition functor_comp_to_comp (F : functor) :
                                  ∏ A B C : UU, ∏ f : A -> B, ∏ g : B -> C,
                                    F.1 (g ∘ f) = (F.1 g) ∘ (F.1 f) :=
  pr2 (pr2 F).


Definition polynomial_functor_on_types (A : UU) (B : A -> UU) : UU -> UU :=
  fun X : UU => total2 (fun a : A => B a -> X).

Definition polynomial_functor_on_maps (A : UU) (B : A -> UU) :
             ∏ X Y, (X -> Y) ->
               (polynomial_functor_on_types A B) X -> (polynomial_functor_on_types A B) Y.
Proof.
  intros A B X Y h.
  intro x. destruct x as [a f].
  exact (a ,, h ∘ f).
Defined.

Definition polynomial_prefunctor (A : UU) (B : A -> UU) : prefunctor :=
  (polynomial_functor_on_types A B ,, polynomial_functor_on_maps A B).

Definition polynomial_prefunctor_id_to_id (A : UU) (B : A -> UU) :
             id_to_id (polynomial_prefunctor A B).
Proof.
  intros. intro X.
  reflexivity.
Defined.

Definition polynomial_prefunctor_comp_to_comp (A : UU) (B : A -> UU) :
             comp_to_comp (polynomial_prefunctor A B).
Proof.
  intros. intros X Y Z f g.
  reflexivity.
Defined.

Definition polynomial_functor (A : UU) (B : A -> UU) : functor :=
  (polynomial_prefunctor A B ,,
    (polynomial_prefunctor_id_to_id A B ,,
      polynomial_prefunctor_comp_to_comp A B)).



Section Algebras.

  Definition algebra_structure (F : prefunctor) (A : UU) :=
    F.0 A -> A.

  Definition algebra (F : prefunctor) : UU :=
    total2 (algebra_structure F).


  Coercion algebra_to_type {F : prefunctor} (A : algebra F) : UU :=
    pr1 A.


  Definition algebra_to_algebra_str {F : prefunctor} (A : algebra F) :
                                      algebra_structure F A := pr2 _.



  Notation "A .s" :=
    (algebra_to_algebra_str A) (at level 60, right associativity) : algebra_scope.
  Open Scope algebra_scope.



  Definition algebra_str_morphism
             (F : functor) (A B : algebra F) (h : A -> B) : UU :=
    ∏ x : F.0 A, h (A.s x) = B.s (F.1 h x).



  Definition algebra_morphism {F : functor} (A B : algebra F) : UU :=
    total2 (algebra_str_morphism F A B).

  Definition algebra_morphism_to_function {F : functor} {A B : algebra F}
               (f : algebra_morphism A B) : A -> B :=
    pr1 f.

  (* this notation might be a bit weird *)
  Notation "f .f" :=
    (algebra_morphism_to_function f) (at level 60, right associativity) : algebra_scope.

  Definition algebra_morphism_identity {F : functor} (A : algebra F) :
    algebra_morphism A A.
  Proof.
    intros.
    exists (idfun _).
    intro x.
    rewrite (functor_id_to_id F _).
    reflexivity.
  Defined.


  Definition algebra_morphism_composition {F : functor} {A B C : algebra F}
    (f : algebra_morphism A B) (g : algebra_morphism B C) :
      algebra_morphism A C.
  Proof.
    intros.
    exists ((g.f) ∘ (f.f)).
    intro x.
    rewrite (functor_comp_to_comp F _).
    simpl.
    destruct f as [f0 f1]. destruct g as [g0 g1].
    unfold funcomp.
    rewrite (f1 _). rewrite (g1 _).
    reflexivity.
  Defined.


  Definition is_initial {F : functor} (A : algebra F) : UU :=
    ∏ B : algebra F, iscontr (algebra_morphism A B).

  Definition initiality_morphism {F : functor} (A : algebra F) (d : is_initial A)
               (B : algebra F) : algebra_morphism A B :=
    pr1 (d B).

  Definition uniqueness_morphism {F : functor} (A : algebra F) (d : is_initial A)
               (B : algebra F) (m m' : algebra_morphism A B) : m = m'.
  Proof.
    intros.
    apply proofirrelevancecontr. apply d.
  Qed.

  Definition is_prop_is_initial {F : functor} (A : algebra F) : isaprop (is_initial A).
  Proof.
    intros.
    apply impred ; intro.
    apply isapropiscontr.
  Qed.


  (* induction principle *)
  Definition unique_endomorphism {F : functor} (A : algebra F) (d : is_initial A)
             (B : algebra F) (m : algebra_morphism B A) :
    algebra_morphism_composition (initiality_morphism A d B) m = algebra_morphism_identity A.
  Proof.
    intros.
    apply uniqueness_morphism. apply d.
  Defined.

  Definition algebra_str_from_ind
               {F : functor} (A : algebra F)
               (P : A -> UU) (sP : ∏ x : F.0 (total2 P), P (A.s ((F.1 pr1) x))) :
                 algebra_structure F (total2 P) :=
    fun x => (_ ,, sP x).

  Definition algebra_from_ind
               {F : functor} (A : algebra F)
               (P : A -> UU) (sP : ∏ x : F.0 (total2 P), P (A.s ((F.1 pr1) x))) :
                 algebra F :=
    (total2 P ,, algebra_str_from_ind A P sP).

  Definition algebra_from_ind_morph
               {F : functor} (A : algebra F)
               (P : A -> UU) (sP : ∏ x : F.0 (total2 P), P (A.s ((F.1 pr1) x))) :
                 algebra_morphism (algebra_from_ind A P sP) A.
  Proof.
    intros.
    exists pr1.
    intro x. reflexivity.
  Defined.

  Definition algebra_from_ind_morph_is_section
               {F : functor} (A : algebra F) (d : is_initial A)
               (P : A -> UU) (sP : ∏ x : F.0 (total2 P), P (A.s ((F.1 pr1) x))) :
                 ∏ a : A,
                     (algebra_from_ind_morph A P sP).f
                     ((initiality_morphism A d (algebra_from_ind A P sP)).f a) = a.
  Proof.
    intros.
    change ((algebra_morphism_composition
             (initiality_morphism A d (algebra_from_ind A P sP))
             (algebra_from_ind_morph A P sP)).f a = a).
    rewrite unique_endomorphism.
    reflexivity.
  Defined.


  Definition initial_algebra_induction {F : functor} (A : algebra F) (d : is_initial A) :
    ∏ P : A -> UU,
      (∏ x : F.0 (total2 P),
        P (A.s ((F.1 pr1) x))) -> ∏ a : A, P a.
  Proof.
    intros F A d P sP a.
    apply (transportf P (algebra_from_ind_morph_is_section A d P sP a)).
    exact (pr2 ((initiality_morphism A d (algebra_from_ind A P sP)).f a)).
  Defined.

  Definition initial_algebra_iduction_eq_initiality_morphism
               {F : functor} (A : algebra F) (d : is_initial A) (P : A -> UU)
               (sP : ∏ x : F.0 (total2 P), P (A.s ((F.1 pr1) x)))
               (a : A) :
                 (a ,, initial_algebra_induction A d P sP a) =
                 (initiality_morphism A d (algebra_from_ind A P sP)).f a.
  Proof.
    intros.
    simple refine (total2_paths2_f _ _).
      - exact (! (algebra_from_ind_morph_is_section A d P sP a)).
      - unfold initial_algebra_induction.
        rewrite transport_f_f.
        rewrite pathsinv0r.
        rewrite idpath_transportf.
        reflexivity.
  Defined.

  Definition initial_algebra_iduction_eq_initiality_morphism_funext
               {F : functor} (A : algebra F) (d : is_initial A) (P : A -> UU)
               (sP : ∏ x : F.0 (total2 P), P (A.s ((F.1 pr1) x))) :
                 (λ a, (a ,, initial_algebra_induction A d P sP a)) =
                 (initiality_morphism A d (algebra_from_ind A P sP)).f.
  Proof.
    intros.
    apply funextfun.
    intro.
    apply initial_algebra_iduction_eq_initiality_morphism.
  Defined.


  Definition initial_algebra_induction_computation_rule
               {F : functor} (A : algebra F) (d : is_initial A) (P : A -> UU)
               (sP : ∏ x : F.0 (total2 P), P (A.s ((F.1 pr1) x)))
               (x : F.0 A) :
                 (A.s x ,, initial_algebra_induction A d P sP (A.s x)) =
                   (algebra_str_from_ind A P sP)
                     (F.1 (λ a, (a ,, initial_algebra_induction A d P sP a)) x).
  Proof.
    intros.
    rewrite (initial_algebra_iduction_eq_initiality_morphism A d P sP _).
    rewrite (initial_algebra_iduction_eq_initiality_morphism_funext A d P sP).
    exact ((pr2 (initiality_morphism A d (algebra_from_ind A P sP))) x).
  Defined.

End Algebras.


(* TODO: coalgebras *)

Section CoAlgebras.

  Definition coalgebra_structure (F : prefunctor) (A : UU) :=
    A -> F.0 A.

  Definition coalgebra (F : prefunctor) : UU :=
    total2 (coalgebra_structure F).


  Coercion coalgebra_to_type {F : prefunctor} (A : coalgebra F) : UU :=
    pr1 A.

  Definition coalgebra_to_coalgebra_str {F : prefunctor} (A : coalgebra F) :
                                      coalgebra_structure F A := pr2 _.

  Notation "A .s" :=
    (coalgebra_to_coalgebra_str A) (at level 60, right associativity) : coalgebra_scope.

  Open Scope coalgebra_scope.

  Definition coalgebra_str_morphism
             (F : functor) (A B : coalgebra F) (h : A -> B) : UU :=
    ∏ x : A, F.1 h (A.s x) = B.s (h x).

  Definition coalgebra_morphism {F : functor} (A B : coalgebra F) : UU :=
    total2 (coalgebra_str_morphism F A B).

  Definition coalgebra_morphism_to_function {F : functor} {A B : coalgebra F}
               (f : coalgebra_morphism A B) : A -> B :=
    pr1 f.

  (* this notation might be a bit weird *)
  Notation "f .f" :=
    (coalgebra_morphism_to_function f) (at level 60, right associativity) : coalgebra_scope.

  Definition coalgebra_morphism_identity {F : functor} (A : coalgebra F) :
    coalgebra_morphism A A.
  Proof.
    intros.
    exists (idfun _).
    intro x.
    rewrite (functor_id_to_id F _).
    reflexivity.
  Defined.


  Definition coalgebra_morphism_composition {F : functor} {A B C : coalgebra F}
    (f : coalgebra_morphism A B) (g : coalgebra_morphism B C) :
      coalgebra_morphism A C.
  Proof.
    intros.
    exists ((g.f) ∘ (f.f)).
    intro x.
    rewrite (functor_comp_to_comp F _).
    simpl.
    destruct f as [f0 f1]. destruct g as [g0 g1].
    unfold funcomp.
    rewrite (f1 _). rewrite (g1 _).
    reflexivity.
  Defined.


  Definition is_final_coalgebra {F : functor} (A : coalgebra F) : UU :=
    ∏ B : coalgebra F, iscontr (coalgebra_morphism A B).

  Definition finality_morphism_coalgebra {F : functor} (A : coalgebra F) (d : is_final_coalgebra A)
               (B : coalgebra F) : coalgebra_morphism A B :=
    pr1 (d B).

  Definition uniqueness_morphism_coalgebra {F : functor} (A : coalgebra F) (d : is_final_coalgebra A)
               (B : coalgebra F) (m m' : coalgebra_morphism A B) : m = m'.
  Proof.
    intros.
    apply proofirrelevancecontr. apply d.
  Qed.

  Definition is_prop_is_final_coalgebra {F : functor} (A : coalgebra F) : isaprop (is_final_coalgebra A).
  Proof.
    intros.
    apply impred ; intro.
    apply isapropiscontr.
  Qed.


  (* induction principle *)
  Definition unique_endomorphism_coalgebra {F : functor} (A : coalgebra F) (d : is_final_coalgebra A)
             (B : coalgebra F) (m : coalgebra_morphism B A) :
    coalgebra_morphism_composition (finality_morphism_coalgebra A d B) m = coalgebra_morphism_identity A.
  Proof.
    intros.
    apply uniqueness_morphism_coalgebra. apply d.
  Defined.

End CoAlgebras.
