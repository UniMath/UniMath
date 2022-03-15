Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.


Local Open Scope cat.

Import Notations.

Section local_helper_lemmas.
  (* I would assume that the following lemmas should already exists in the "iso file", but I can't find it (I need is_iso_stable_undertransportation)  *)
  Lemma iso_stable_under_equality {C : category} {x y : C} {f g : C⟦x,y⟧} : (g = f) → (is_z_isomorphism f) → (is_z_isomorphism g).
  Proof.
    intros pe pi.
    induction pe.
    exact pi.
  Qed.

  Lemma iso_stable_under_tranportation {C : category} {x y z : C} {f : C⟦x,y⟧} {pf : y=z} : (is_z_isomorphism f) → (is_z_isomorphism (transportf _ pf f)).
  Proof.
    intro pfi.
    induction pf.
    use pfi.
  Qed.

  Lemma iso_stable_under_equalitytransportation {C : category} {x y z : C} {f : C⟦x,y⟧} {g : C⟦x,z⟧} {pf : y=z} :
    (g = transportf _ pf f) -> (is_z_isomorphism f) -> (is_z_isomorphism g).
  Proof.
    intros p isof.
    use (iso_stable_under_equality p).
    use (iso_stable_under_tranportation).
    exact isof.
  Qed.
End local_helper_lemmas.


Section MonoidalFunctors.

  Context (C D : category) (M : monoidalcategory C) (N : monoidalcategory D) (F : functor C D).

  Local Notation "F ·· G" := (functor_composite F G) (at level 31).
  Local Notation "α ··· β" := (nat_trans_comp _ _ _ α β) (at level 31).

  Local Notation "I_{ M }" := (unit_from_monoidalcatdata M).
  Local Notation "lu^{ M }_{ x }" := ( (leftunitor_from_monoidalcatdata M) x ).
  Local Notation "ru^{ M }_{ x }" := ( (rightunitor_from_monoidalcatdata M) x ).
  Local Notation "α^{ M }_{ x , y , z }" := (associatordata_from_monoidalcatdata M x y z).

  (** (Weak) Monoidal functors **)
  (* Monoidal functor data *)

  Definition functor_imageoftensor : bifunctor C C D
    := compose_bifunctor_with_functor M F.

  Definition functor_tensorofimages : bifunctor C C D
    := compose_functor_with_bifunctor F F N.

  Definition preserves_tensor : UU := binat_trans functor_tensorofimages functor_imageoftensor.

  Definition preserves_unit : UU := D ⟦ I_{N} , F I_{M} ⟧.

  Definition monoidalfunctor_data :=
    preserves_tensor × preserves_unit.

  Definition tensorpreserved_from_monoidalfunctordata (mfd : monoidalfunctor_data) : preserves_tensor := pr1 mfd.
  Coercion tensorpreserved_from_monoidalfunctordata : monoidalfunctor_data >-> preserves_tensor.

  Definition unitpreserved_from_monoidalfunctordata (mfd : monoidalfunctor_data) : preserves_unit := pr2 mfd.
  Coercion unitpreserved_from_monoidalfunctordata : monoidalfunctor_data >-> preserves_unit.

  (* Definition preserves_leftunitality (pt : preserves_tensor) (pu : preserves_unit) :
    ∏ (x : C), ((#F (lu^{M}_{x})) ∘ ((pr1 pt) I_{M} x) ∘ (pu ⊗^{N} (identity (F x)))) = lu^{N}_{F x}.
  Proof.
    intro x.
    unfold functoronmorphisms1.
    Check  ((pu ⊗^{ N}_{r} F x) · (F I_{ M} ⊗^{ N}_{l} identity (F x)) · (pr1 pt I_{ M} x · # F lu^{ M }_{ x}) = lu^{ N }_{ F x}). *)





  Definition functor0 : functor C D :=
    F ·· leftwhiskering_functor N (bifunctor_leftid N) (bifunctor_leftcomp N) I_{N}.

  Definition functor0' : functor C D :=
    F ·· rightwhiskering_functor N (bifunctor_rightid N) (bifunctor_rightcomp N) I_{N}.

  Definition functor1 : functor C D :=
    F ·· leftwhiskering_functor N (bifunctor_leftid N) (bifunctor_leftcomp N) (F I_{M}).

  Definition functor1' : functor C D :=
    F ·· rightwhiskering_functor N (bifunctor_rightid N) (bifunctor_rightcomp N) (F I_{M}).

  Definition functor2 : functor C D :=
    leftwhiskering_functor M (bifunctor_leftid M) (bifunctor_leftcomp M) I_{M} ·· F.

  Definition functor2' : functor C D :=
    rightwhiskering_functor M (bifunctor_rightid M) (bifunctor_rightcomp M) I_{M} ·· F.

  (* functor3 := F *)

  Definition nattrans0_data (pu : preserves_unit): nat_trans_data functor0 functor1 := λ x, (pu ⊗^{N}_{r} (F x)).
  Lemma nattrans0_nat (pu : preserves_unit) : is_nat_trans functor0 functor1 (nattrans0_data pu).
  Proof.
    unfold is_nat_trans.
    intros x y f.
    unfold nattrans0_data.
    unfold functor0.
    unfold functor1.
    cbn. (* Doesn't work without cbn and don't know how to simplify manually so that I can use whiskerscommutes without firstly doing cbn. *)
    rewrite whiskerscommutes.
    - apply idpath.
    - apply bifunctor_equalwhiskers.
  Qed.
  Definition nattrans0 (pu : preserves_unit) : nat_trans functor0 functor1 := (nattrans0_data pu,,nattrans0_nat pu).

  Definition nattrans1_data (pt : preserves_tensor): nat_trans_data functor1 functor2 := λ x, (pr1 pt) I_{M} x.

  (** The proof of the naturality condition of nattrans1 should be cleaned, but don't see how,
      it follows immediate from the naturality of pt, but for some reason I have to show
      that they coincide while this is by definition. **)
  Lemma nattrans1_nat (pt : preserves_tensor) : is_nat_trans functor1 functor2 (nattrans1_data pt).
  Proof.
    intros x y f.
    unfold nattrans1_data.
    unfold functor1.
    unfold functor2.
    assert (pf : F I_{ M} ⊗^{ N}_{l} # F f =  identity I_{ M} ⊗^{ functor_tensorofimages} f ).
    {
      unfold functoronmorphisms1.
      unfold functor_tensorofimages.
      unfold compose_functor_with_bifunctor.
      unfold compose_functor_with_bifunctor_data.
      cbn.
      rewrite functor_id.
      rewrite bifunctor_rightid.
      rewrite id_left.
      apply idpath.
    }
    cbn.
    rewrite pf.
    etrans. { apply (full_naturality_condition (pr1 pt) (pr2 pt) (identity I_{M}) f). }

    assert (pg : identity I_{ M} ⊗^{ functor_imageoftensor} f =  # F (I_{ M} ⊗^{ M}_{l} f) ).
    {
      unfold functoronmorphisms1.
      unfold functor_imageoftensor.
      unfold compose_bifunctor_with_functor.
      unfold compose_bifunctor_with_functor_data.
      cbn.
      rewrite bifunctor_rightid.
      rewrite functor_id.
      rewrite id_left.
      apply idpath.
    }
    rewrite pg.
    apply idpath.
  Qed.
  Definition nattrans1 (pt : preserves_tensor) : nat_trans functor1 functor2 := (nattrans1_data pt,,nattrans1_nat pt).

  Definition nattrans2_data : nat_trans_data functor2 F := λ x, (#F (lu^{M}_{x})). (* F \cdot lu^{M} *)
  Lemma nattrans2_nat : is_nat_trans functor2 F nattrans2_data.
  Proof.
    unfold is_nat_trans.
    intros x y f.
    unfold nattrans2_data.
    unfold functor2.
    cbn.
    rewrite (pathsinv0 (functor_comp F _ _)).
    rewrite (pathsinv0 (functor_comp F _ _)).

    assert (pf : I_{ M} ⊗^{ M}_{l} f · lu^{ M }_{ y} = lu^{ M }_{ x} · f). {
      apply ((pr2 (leftunitor_from_monoidalcatdata M)) x y f).
    }

    assert (functorpreservesequalmorphisms : ∏ (a b : C) (p q : C⟦a, b⟧), p = q -> #F p = #F q). {
      intros. induction X. apply idpath.
    }

    apply functorpreservesequalmorphisms.
    apply pf.
  Qed.
  Definition nattrans2 : nat_trans functor2 F := (nattrans2_data,,nattrans2_nat).

  Definition nattrans3_data : nat_trans_data functor0 F := λ x, lu^{N}_{(F x)}.
  Lemma nattrans3_nat : is_nat_trans functor0 F nattrans3_data.
  Proof.
    unfold is_nat_trans.
    intros x y f.
    unfold nattrans3_data.
    unfold functor0.
    cbn.

    apply (((pr2 (leftunitor_from_monoidalcatdata N)) (F x) (F y)) (#F f)).
  Qed.
  Definition nattrans3 : nat_trans functor0 F := (nattrans3_data,,nattrans3_nat).

  Definition preserves_leftunitality (pt : preserves_tensor) (pu : preserves_unit) : UU :=
    (nattrans0 pu) ··· (nattrans1 pt) ··· nattrans2 = nattrans3.

  Definition nattrans0'_data (pu : preserves_unit): nat_trans_data functor0' functor1' := λ x, ((F x) ⊗^{N}_{l} pu).
  Lemma nattrans0'_nat (pu : preserves_unit) : is_nat_trans functor0' functor1' (nattrans0'_data pu).
  Proof.
    unfold is_nat_trans.
    intros x y f.
    unfold nattrans0'_data.
    unfold functor0'.
    unfold functor1'.
    cbn.
    rewrite whiskerscommutes.
    - apply idpath.
    - apply bifunctor_equalwhiskers.
  Qed.
  Definition nattrans0' (pu : preserves_unit) : nat_trans functor0' functor1' := (nattrans0'_data pu,,nattrans0'_nat pu).

  Definition nattrans1'_data (pt : preserves_tensor): nat_trans_data functor1' functor2' := λ x, (pr1 pt) x I_{M}.

  (** The proof of the naturality condition of nattrans1 should be cleaned, but don't see how,
      it follows immediate from the naturality of pt, but for some reason I have to show
      that they coincide while this is by definition. **)
  Lemma nattrans1'_nat (pt : preserves_tensor) : is_nat_trans functor1' functor2' (nattrans1'_data pt).
  Proof.
    intros x y f.
    unfold nattrans1_data.
    unfold functor1'.
    unfold functor2'.
    cbn.

    assert (pf : (#F f) ⊗^{ N}_{r} (F I_{ M}) =  f ⊗^{ functor_tensorofimages} identity I_{ M}).
    {
      (* unfold functor_tensorofimages. *)
      unfold functoronmorphisms1.
      unfold functor_tensorofimages.
      unfold compose_functor_with_bifunctor.
      unfold compose_functor_with_bifunctor_data.
      cbn.
      rewrite functor_id.
      rewrite bifunctor_leftid.
      rewrite id_right.
      apply idpath.
    }
    rewrite pf.
    etrans. {
      apply (full_naturality_condition (pr1 pt) (pr2 pt) f (identity I_{M})).
    }

    assert (pg : f ⊗^{ functor_imageoftensor} identity I_{ M} =  # F (f ⊗^{ M}_{r} I_{ M}) ).
    {
      unfold functoronmorphisms1.
      unfold functor_imageoftensor.
      unfold compose_bifunctor_with_functor.
      unfold compose_bifunctor_with_functor_data.
      cbn.
      rewrite bifunctor_leftid.
      rewrite functor_id.
      rewrite id_right.
      apply idpath.
    }
    rewrite pg.
    apply idpath.
  Qed.
  Definition nattrans1' (pt : preserves_tensor) : nat_trans functor1' functor2' := (nattrans1'_data pt,,nattrans1'_nat pt).

  Definition nattrans2'_data : nat_trans_data functor2' F := λ x, (#F (ru^{M}_{x})).
  Lemma nattrans2'_nat : is_nat_trans functor2' F nattrans2'_data.
  Proof.
    unfold is_nat_trans.
    intros x y f.
    unfold nattrans2'_data.
    unfold functor2'.
    cbn.
    rewrite (pathsinv0 (functor_comp F _ _)).
    rewrite (pathsinv0 (functor_comp F _ _)).

    assert (pf : f ⊗^{ M}_{r} I_{ M} · ru^{ M }_{ y} = ru^{ M }_{ x} · f). {
      apply ((pr2 (rightunitor_from_monoidalcatdata M)) x y f).
    }

    assert (functorpreservesequalmorphisms : ∏ (a b : C) (p q : C⟦a, b⟧), p = q -> #F p = #F q). {
      intros. induction X. apply idpath.
    }

    apply functorpreservesequalmorphisms.
    apply pf.
  Qed.
  Definition nattrans2' : nat_trans functor2' F := (nattrans2'_data,,nattrans2'_nat).

  Definition nattrans3'_data : nat_trans_data functor0' F := λ x, ru^{N}_{(F x)}.
  Lemma nattrans3'_nat : is_nat_trans functor0' F nattrans3'_data.
  Proof.
    unfold is_nat_trans.
    intros x y f.
    unfold nattrans3'_data.
    unfold functor0'.
    cbn.

    apply (((pr2 (rightunitor_from_monoidalcatdata N)) (F x) (F y)) (#F f)).
  Qed.
  Definition nattrans3' : nat_trans functor0' F := (nattrans3'_data,,nattrans3'_nat).

  Definition preserves_rightunitality (pt : preserves_tensor) (pu : preserves_unit) : UU :=
    (nattrans0' pu) ··· (nattrans1' pt) ··· nattrans2' = nattrans3'.

  Definition preserves_associativity (pt : preserves_tensor) : UU :=
    ∏ (x y z : C), ((pr1 pt x y) ⊗^{N}_{r} (F z)) · (pr1 pt (x ⊗_{M} y) z) · (#F (α^{M}_{x,y,z}))
                   = α^{N}_{F x, F y, F z} · ((F x) ⊗^{N}_{l} (pr1 pt y z)) · (pr1 pt x (y ⊗_{M} z)).

  Definition monoidalfunctor_laws (mfd : monoidalfunctor_data) : UU :=
    (preserves_associativity mfd) × (preserves_leftunitality mfd mfd) × (preserves_rightunitality mfd mfd).

  Definition monoidalfunctor : UU :=
    ∑ (mfd : monoidalfunctor_data), monoidalfunctor_laws mfd.

  (** Strong and strict monoidal properties *)

  Definition preserves_tensor_strongly (pt : preserves_tensor) : UU :=
    is_binatiso pt.

  Definition preserves_tensor_strictly (pt : preserves_tensor) : UU :=
      ∏ (x y : C), ∑ (pf : (F x) ⊗_{N} (F y) = F (x ⊗_{M} y)),
      (pr1 pt x y ) = transportf _ pf (identity ((F x) ⊗_{N} (F y))).

  Lemma strictlytensorpreserving_is_strong {pt : preserves_tensor} (pfstrict : preserves_tensor_strictly pt) : preserves_tensor_strongly pt.
  Proof.
    intros x y.
    use (iso_stable_under_equalitytransportation (pr2 (pfstrict x y)) (is_z_isomorphism_identity (F x ⊗_{N} F y))).
  Qed.
  Coercion strictlytensorpreserving_is_strong : preserves_tensor_strictly >-> preserves_tensor_strongly.

  Definition preserves_unit_strongly (pu : preserves_unit) : UU := is_z_isomorphism pu.

  Definition preserves_unit_strictly (pu : preserves_unit) : UU :=
    ∑ (pf : I_{N} = (F I_{M})), pu = transportf _ pf (identity I_{N}).

  Definition strictlyunitpreserving_is_strong {pu : preserves_unit} (pfstrict : preserves_unit_strictly pu) : preserves_unit_strongly pu.
  Proof.
    use (iso_stable_under_equalitytransportation (pr2 pfstrict) (is_z_isomorphism_identity I_{N})).
  Defined.
  Coercion strictlyunitpreserving_is_strong : preserves_unit_strictly >-> preserves_unit_strongly.

End MonoidalFunctors.
