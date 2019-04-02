Require Export UniMath.Inductives.functors.
Require Export UniMath.Foundations.Propositions.


(** Algebras for a functor *)
Section Algebras.

  Definition algebra_structure {I} (F : prefunctor I I) (A : Fam I) :=
    F A ->__i A.

  Definition algebra {I} (F : prefunctor I I) : UU :=
    ∑ carrier, algebra_structure F carrier.

  Definition algebra_to_type {I} {F : prefunctor I I} : algebra F -> I -> UU :=
    pr1.
  Coercion algebra_to_type : algebra >-> Funclass.

  Definition algebra_to_algebra_str {I} {F : prefunctor I I} (A : algebra F) :
    algebra_structure F A :=
    pr2 _.


  (* algebra morphisms *)
  Definition algebra_str_morphism
             {I} (F : functor I I) (A B : algebra F) (h : A ->__i B) : UU :=
    ∏ i x, h i (A.2 i x) = B.2 i (F.map h i x).

  Definition algebra_morphism {I} {F : functor I I} (A B : algebra F) : UU :=
    ∑ map, algebra_str_morphism F A B map.

  Definition algebra_morphism_to_function {I} {F : functor I I} {A B : algebra F}
             (f : algebra_morphism A B) : ∏ i, A i -> B i :=
    pr1 f.
  Coercion algebra_morphism_to_function : algebra_morphism >-> Funclass.


  Definition algebra_morphism_identity {I} {F : functor I I} (A : algebra F) :
    algebra_morphism A A.
  Proof.
    exists (λ _, idfun _).
    unfold algebra_str_morphism. rewrite (functor_id_to_id F _). reflexivity.
  Defined.

  Definition algebra_morphism_composition {I} {F : functor I I} {A B C : algebra F}
             (f : algebra_morphism A B) (g : algebra_morphism B C) :
    algebra_morphism A C.
  Proof.
    intros. exists (g ∘__i f).
    unfold algebra_str_morphism; intros.
    rewrite functor_comp_to_comp.
    unfold comp__i.
    exact (maponpaths (g i) (pr2 f i x) @ g.2 i (F.map f i x)).
  Defined.

  (* initial algebras *)
  Definition is_initial {I} {F : functor I I} (A : algebra F) : UU :=
    ∏ B : algebra F, iscontr (algebra_morphism A B).

  Definition initiality_morphism {I} {F : functor I I} (A : algebra F) (d : is_initial A)
             (B : algebra F) : algebra_morphism A B :=
    pr1 (d B).

  Definition uniqueness_morphism {I} {F : functor I I} (A : algebra F) (d : is_initial A)
             (B : algebra F) (m m' : algebra_morphism A B) : m = m'.
  Proof.
    intros. apply proofirrelevancecontr. apply d.
  Qed.

  Definition is_prop_is_initial {I} {F : functor I I} (A : algebra F) : isaprop (is_initial A).
  Proof.
    intros. apply impred ; intro. apply isapropiscontr.
  Qed.

  (* induction principle of initial algebras *)
  Definition unique_endomorphism {I} {F : functor I I} (A : algebra F) (d : is_initial A)
             (B : algebra F) (m : algebra_morphism B A) :
    algebra_morphism_composition (initiality_morphism A d B) m = algebra_morphism_identity A.
  Proof.
    intros. apply uniqueness_morphism. apply d.
  Defined.

  Definition algebra_str_from_ind
             {I} {F : functor I I} (A : algebra F)
             (P : ∏ i, A i -> UU)
             (sP : ∏ i (x : F (λ i, ∑ a, P i a) i),
                   P i (A.2 i (F.map (λ _, pr1) i x))) :
    algebra_structure F (λ i, ∑ a, P i a) :=
    fun i x => (_ ,, sP i x).

  Definition algebra_from_ind
             {I} {F : functor I I} (A : algebra F)
             (P : ∏ i, A i -> UU)
             (sP : ∏ i (x : F (λ i, ∑ a, P i a) i),
                   P i (A.2 i (F.map (λ _, pr1) i x))) :
    algebra F :=
    ((λ i, ∑ a, P i a) ,, algebra_str_from_ind A P sP).

  Definition algebra_from_ind_morph
             {I} {F : functor I I} (A : algebra F)
             (P : ∏ i, A i -> UU)
             (sP : ∏ i (x : F (λ i, ∑ a, P i a) i),
                   P i (A.2 i (F.map (λ _, pr1) i x))) :
    algebra_morphism (algebra_from_ind A P sP) A.
  Proof.
    intros. exists (λ _, pr1).
    intro x. reflexivity.
  Defined.

  Definition algebra_from_ind_morph_is_section
             {I} {F : functor I I} (A : algebra F) (d : is_initial A)
             (P : ∏ i, A i -> UU)
             (sP : ∏ i (x : F (λ i, ∑ a, P i a) i),
                   P i (A.2 i (F.map (λ _, pr1) i x))) :
    ∏ i (a : A i),
    algebra_from_ind_morph A P sP i
                           (initiality_morphism A d (algebra_from_ind A P sP) i a) =
    a.
  Proof.
    intros.
    change ((algebra_morphism_composition
               (initiality_morphism A d (algebra_from_ind A P sP))
               (algebra_from_ind_morph A P sP)) i a = a).
    rewrite unique_endomorphism.
    reflexivity.
  Defined.

  Definition initial_algebra_induction {I} {F : functor I I} (A : algebra F) (d : is_initial A) :
    ∏ P : ∏ i, A i -> UU,
          (∏ i (x : F (λ i, ∑ a, P i a) i),
           P i (A.2 i (F.map (λ _, pr1) i x))) -> ∏ i a, P i a.
  Proof.
    intros P sP i a.
    apply (transportf (P i) (algebra_from_ind_morph_is_section A d P sP i a)).
    exact (pr2 ((initiality_morphism A d (algebra_from_ind A P sP)) i a)).
  Defined.

  Definition initial_algebra_iduction_eq_initiality_morphism
             {I} {F : functor I I} (A : algebra F) (d : is_initial A) (P : ∏ i, A i -> UU)
             (sP : ∏ i (x : F (λ i, ∑ a, P i a) i),
                   P i (A.2 i (F.map (λ _, pr1) i x)))
             i (a : A i) :
    (a ,, initial_algebra_induction A d P sP i a) =
    (initiality_morphism A d (algebra_from_ind A P sP)) i a.
  Proof.
    intros.
    simple refine (total2_paths2_f _ _).
    - exact (! (algebra_from_ind_morph_is_section A d P sP i a)).
    - unfold initial_algebra_induction.
      rewrite transport_f_f. rewrite pathsinv0r. rewrite idpath_transportf.
      reflexivity.
  Defined.

  Definition initial_algebra_iduction_eq_initiality_morphism_funext
             {I} {F : functor I I} (A : algebra F) (d : is_initial A) (P : ∏ i, A i -> UU)
             (sP : ∏ i (x : F (λ i, ∑ a, P i a) i), P i (A.2 i (F.map (λ _, pr1) i x))) :
    (λ i a, (a ,, initial_algebra_induction A d P sP i a)) =
    (initiality_morphism A d (algebra_from_ind A P sP)).
  Proof.
    intros. apply funextsec. intros i. apply funextfun.
    intro. apply initial_algebra_iduction_eq_initiality_morphism.
  Defined.

  (* Definition initial_algebra_induction_computation_rule *)
  (*            {I} {F : functor I I} (A : algebra F) (d : is_initial A) *)
  (*            (P : ∏ i, A i -> UU) *)
  (*            (sP : ∏ i (x : F (λ i, ∑ a, P i a) i), *)
  (*                  P i (A.2 i (F.map (λ _, pr1) i x))) *)
  (*            i (x : F A i) : *)
  (*   (A.2 i x,, initial_algebra_induction A d P sP i (A.2 i x)) = *)
  (*   algebra_str_from_ind A P sP i *)
  (*     (F.map (λ i a, a ,, initial_algebra_induction A d P sP i a) i x). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite (initial_algebra_iduction_eq_initiality_morphism A d P sP _). *)
  (*   rewrite (initial_algebra_iduction_eq_initiality_morphism_funext A d P sP). *)
  (*   exact ((pr2 (initiality_morphism A d (algebra_from_ind A P sP))) x). *)
  (* Defined. *)

End Algebras.


Section CoAlgebras.

  Context {I : UU}.

  Definition coalgebra_structure (F : prefunctor I I) (A : Fam I) :=
    A ->__i F A.

  Definition coalgebra (F : prefunctor I I) : UU :=
    ∑ A, coalgebra_structure F A.

  Definition coalgebra_to_type {F : prefunctor I I} (A : coalgebra F) : I -> UU :=
    pr1 A.
  Coercion coalgebra_to_type : coalgebra >-> Funclass.


  Definition coalgebra_to_coalgebra_str {F : prefunctor I I} (A : coalgebra F) :
    coalgebra_structure F A := pr2 _.


  Definition coalgebra_morphism {F : prefunctor I I} (A B : coalgebra F) : UU :=
    ∑ f : A ->__i B,
          B.2 ∘__i f = F.map f ∘__i A.2.

  Definition coalgebra_morphism_to_function {F : prefunctor I I} {A B : coalgebra F}
             (f : coalgebra_morphism A B) : ∏ i, A i -> B i :=
    pr1 f.
  Coercion coalgebra_morphism_to_function : coalgebra_morphism >-> Funclass.

  Context {F : functor I I}.

  Definition coalgebra_morphism_identity (A : coalgebra F) :
    coalgebra_morphism A A.
  Proof.
    intros. exists (λ _, idfun _).
    rewrite (functor_id_to_id F _). reflexivity.
  Defined.

  Definition coalgebra_morphism_composition {A B C : coalgebra F}
             (f : coalgebra_morphism A B) (g : coalgebra_morphism B C) :
    coalgebra_morphism A C.
  Proof.
    intros. exists (g ∘__i f).
    change (C.2 ∘__i g ∘__i f = F.map (g ∘__i f) ∘__i A.2).
    intermediate_path (F.map g ∘__i B.2 ∘__i f). {
      apply (maponpaths (λ h, h ∘__i f : A ->__i F C)
                        (pr2 g)).
    }
    intermediate_path (F.map g ∘__i F.map f ∘__i A.2). {
      apply (maponpaths (λ h, F.map g ∘__i h : A ->__i F C)
                        (pr2 f)).
    }
    intermediate_path (F.map (g ∘__i f) ∘__i A.2). {
      apply (maponpaths (λ h, h ∘__i A.2) (!functor_comp_to_comp F _ _ _ _ _)).
    }
    reflexivity.
  Defined.

  (* final coalgebras *)
  Definition is_final_coalgebra (A : coalgebra F) : UU :=
    ∏ B : coalgebra F,
          iscontr (coalgebra_morphism B A).

  Definition finality_morphism_coalgebra
             (A : coalgebra F) (d : is_final_coalgebra A)
             (B : coalgebra F) :
    coalgebra_morphism B A :=
    pr1 (d B).

  Definition uniqueness_morphism_coalgebra
             (A : coalgebra F) (d : is_final_coalgebra A)
             (B : coalgebra F) (m m' : coalgebra_morphism B A) :
    m = m'.
  Proof.
    intros. apply proofirrelevancecontr. apply d.
  Qed.

  Definition is_prop_is_final_coalgebra
             (A : coalgebra F) : isaprop (is_final_coalgebra A).
  Proof.
    intros. apply impred ; intro. apply isapropiscontr.
  Qed.

  Definition unique_endomorphism_coalgebra
             (A : coalgebra F) (d : is_final_coalgebra A)
             (B : coalgebra F) (m : coalgebra_morphism A B) :
    coalgebra_morphism_composition m (finality_morphism_coalgebra A d B) = coalgebra_morphism_identity A.
  Proof.
    intros. apply uniqueness_morphism_coalgebra. apply d.
  Defined.


  Definition isweq__i {I} {A B : Fam I} (f : A ->__i B) :=
    ∏ i, isweq (f i).

  Theorem gradth__i {J} {X Y : Fam J} (f : X ->__i Y) (g : Y ->__i X)
          (egf: ∏ i x, g i (f i x) = x)
          (efg: ∏ i y, f i (g i y) = y) : isweq__i f.
  Proof.
    intros i.
    use gradth.
    - exact (g i).
    - exact (egf i).
    - exact (efg i).
  Qed.

  Lemma isweq_final_coalgebra_struct (C : coalgebra F) :
    is_final_coalgebra C -> isweq__i C.2.
  Proof.
    intros is_final.
    set (F_C := (F C,, F.map C.2) : coalgebra F).
    set (h := (C.2,, idpath _) : coalgebra_morphism C F_C); change (isweq__i h).
    set (h_inv := finality_morphism_coalgebra C is_final F_C).
    assert (H : h_inv ∘__i h = idmap__i C). {
      change ((coalgebra_morphism_composition h h_inv).1 =
              (coalgebra_morphism_identity C).1).
      apply maponpaths.
      apply uniqueness_morphism_coalgebra. exact is_final.
    }
    use gradth__i.
    - exact h_inv.
    - intros i x.
      change ((h_inv ∘__i h) i x = idmap__i C i x).
      apply (maponpaths (λ f : C ->__i C, f i x)).
      exact H.
    - intros i y.
      change ((h ∘__i h_inv) i y = idmap__i F_C i y).
      apply (maponpaths (λ f : F_C ->__i F_C, f i y)).
      intermediate_path (F.map h_inv ∘__i F.map h). {
        exact h_inv.2.
      }
      intermediate_path (F.map (h_inv ∘__i h)). {
        symmetry; apply functor_comp_to_comp.
      }
      intermediate_path (F.map (idmap__i C)). {
        apply maponpaths; exact H.
      }
      apply functor_id_to_id.
  Defined.


  (* TODO: coinduction *)

End CoAlgebras.
