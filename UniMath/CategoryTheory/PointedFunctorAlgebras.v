(**************************************************************************************************

  PointedFunctorAlgebras

  An algebra for a pointed endofunctor (F, σ : 1 ⟹ F) is an object X with a structure map F(X) ⟶ X
  which restricts to id on σ_X : X ⟶ F(X).

  This file contains the transfinite construction (due to Kelly) of the free-algebra for a
  *well-pointed*, ω-cocontinuous endofunctor, and the free-forgetful adjunction. There are also
  connections to reflective subcategories (idempotent monads).

  References:
  * `nLab: transfinite construction of free algebras https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras
  * `Max Kelly, A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/unified-treatment-of-transfinite-constructions-for-free-algebras-free-monoids-colimits-associated-sheaves-and-so-on/FE2E25E4959E4D8B4DE721718E7F55EE
  
  Contents
  1. Definitions
  1.1. Pointed endofunctors
  1.2. Well-pointedness
  1.3. Pointed endofunctor algebras (algebras for a pointed endofunctor)
  1.4. The category of pointed endofunctor algebras [ptd_alg_category] [forget_ptd_alg]
  2. Properties of algebras for well-pointed endofunctors
  2.1. Structure maps are iso-inverses [well_pointed_point_is_z_iso_at_algebra] 
  2.2. Any morphism is a morphism of algebras [well_pointed_mor_is_algebra_mor] 
  2.3. The forgetful functor is fully-faithful [well_pointed_forgetul_fully_faithful] 
  3. The transfinite construction
  3.1. The directed colimit A --> F(A) --> F^2(A) --> ... F^ω(A)
  3.2. The shift map F(F^ω A) --> F^ω A [shift_iter_map]
  3.3. The shift map forms a pointed algebra [shift_iter_map_forms_ptd_alg]
  3.4. The free functor C ⟶ ptd_alg_category F [free_ptd_alg]
  3.5. The free-forgetful adjunction [free_forgetful_form_adjunction]
  4. Reflective subcategories give well-pointed endofunctors
    [well_pointed_of_fully_faithful_right_adjoint]

  started September 2024
  Billy Snikkers

 **************************************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(*
To rewrite x to x' in x · y = z, use
rw_left_comp h.
where h has conclusion x = x'.
*)
Tactic Notation "rw_left_comp" constr(e) :=
  apply (transportb (λ x, x · _ = _) ltac:(apply e)).
(* Similarly `rw_right_comp h` uses h to rewrite x to x' in y · x = z *)
Tactic Notation "rw_right_comp" constr(e) :=
  apply (transportb (λ x, _ · x = _) ltac:(apply e)).

(** 1. Definitions *)

(** 1.1. Pointed endofunctors *)

(** A pointed endofunctor F comes with a natural transformation 1 ⟹ F *)
Definition pointed_endofunctor (C : category) : UU := ∑ F : C ⟶ C, functor_identity C ⟹ F.

#[reversible=no] Coercion pointed_endofunctor_endofunctor
  {C : category} (X : pointed_endofunctor C) : C ⟶ C := pr1 X.

Definition make_pointed_endofunctor {C : category}
    (F : C ⟶ C) (σ : functor_identity C ⟹ F)
  : pointed_endofunctor C := (F,,σ).

(** The *point* of a pointed endofunctor *)
Definition point {C : category} (F : pointed_endofunctor C) : functor_identity C ⟹ F := pr2 F.

(** Easier to use than nat_trans_ax since no identity functor is mentioned *)
Definition point_naturality {C : category} (F : pointed_endofunctor C) {x y : C} (f : x --> y)
  : (f · point F y = point F x · # F f).
Proof.
  apply (nat_trans_ax (point F)).
Qed.

(** 1.2. Well-pointedness
  A well-pointed functor (F,,σ) satisfies Fσ = σF, i.e. for every A : C, the two
  ways of constructing a morphism F A --> F (F A) coincide.
*)
Definition well_pointed {C : category} (F : pointed_endofunctor C)
  : UU
  := pre_whisker F (point F) = post_whisker (point F) F.

(** In practice we use this pointwise version, which is also easier to read *)
Definition well_pointed_pointwise {C : category} {F : pointed_endofunctor C}
  : well_pointed F → ∏ A : C, point F (F A) = #F (point F A)
  := λ H A, nat_trans_eq_pointwise H A.

(** 1.3. Pointed endofunctor algebras (algebras for a pointed endofunctor)
  Endofunctors, pointed-endofunctors, monads all have associated categories
  of algebras, consisting of a structure map obeying some subset of the
  laws for the algebras of a monad. These algebra-categories must be disambiguated,
  since a monad is a pointed endofunctor is an endofunctor. The terminology
  "algebras for the pointed endofunctor F" achieves this, but is a bit long.
  We call them "pointed algebras" here (or ptd_alg) for brevity, but we note
  the potentional for confusion: the algebras themselves don't have a "point",
  i.e. they aren't equipped with a morphisms 1 --> X.
*)
Section PointedAlgebras.

Context {C : category} (F : pointed_endofunctor C).

Let σ := point F.

Definition ptd_alg_data : UU := ∑ X : C, F X --> X.

Definition make_ptd_alg_data
  : ∏ X : C, (F X --> X) → ptd_alg_data
  := tpair (λ X, F X --> X).

(** This coercion is convenient for this file. Be aware of it. *)
#[reversible=no] Coercion ptd_alg_carrier (X : ptd_alg_data) : C := pr1 X.

Definition ptd_alg_map (X : ptd_alg_data) : F X --> X := pr2 X.

Definition is_ptd_alg (X : ptd_alg_data) : UU := (σ X) · (ptd_alg_map X) = identity X.

(** A pointed algebra for (F,σ) is a pair (a : F X --> X)
  which is a retraction of the point map, i.e., σ_X · a = id_X
*)
Definition ptd_alg : UU := ∑ X : ptd_alg_data, is_ptd_alg X.

#[reversible=no] Coercion ptd_alg_data_from_ptd_alg (X : ptd_alg) : ptd_alg_data := pr1 X.

Definition make_ptd_alg (X : C) (s : F X --> X) (r : σ X · s = identity X)
  : ptd_alg
  := (make_ptd_alg_data X s,, r).

Definition ptd_alg_law (X : ptd_alg) : σ X · (ptd_alg_map X) = identity X := pr2 X.

(** 1.4. The category of pointed endofunctor algebras [ptd_alg_category] [forget_ptd_alg] *)

Section ptd_alg_precategory_data.

Definition is_ptd_alg_mor (X Y : ptd_alg) (f : X --> Y) : UU
  := ptd_alg_map X · f = #F f · ptd_alg_map Y.

Definition ptd_alg_mor (X Y : ptd_alg) : UU
  := ∑ f : X --> Y, is_ptd_alg_mor X Y f.

Definition make_ptd_alg_mor {X Y : ptd_alg} (f : X --> Y) (p : is_ptd_alg_mor X Y f)
  : ptd_alg_mor X Y := (f,,p).

#[reversible=no] Coercion mor_from_ptd_alg_mor {X Y : ptd_alg} (f : ptd_alg_mor X Y)
  : X --> Y := pr1 f.

Definition ptd_alg_mor_commutes {X Y : ptd_alg} (f : ptd_alg_mor X Y)
  : ptd_alg_map X · f = #F f · ptd_alg_map Y := pr2 f.

Definition ptd_alg_mor_id (X : ptd_alg) : ptd_alg_mor X X.
Proof.
  apply make_ptd_alg_mor with (identity X).
  abstract (unfold is_ptd_alg_mor; now rewrite functor_id, id_right, id_left).
Defined.

Definition ptd_alg_mor_comp (X Y Z : ptd_alg) (f : ptd_alg_mor X Y) (g : ptd_alg_mor Y Z)
  : ptd_alg_mor X Z.
Proof.
  apply make_ptd_alg_mor with (f · g).
  abstract (unfold is_ptd_alg_mor;
            rewrite assoc;
            rewrite ptd_alg_mor_commutes;
            rewrite <- assoc;
            rewrite ptd_alg_mor_commutes;
            now rewrite functor_comp, assoc).
Defined.

Definition precategory_ptd_alg_ob_mor : precategory_ob_mor
  := make_precategory_ob_mor ptd_alg ptd_alg_mor.

Definition precategory_ptd_alg_data : precategory_data
  := make_precategory_data precategory_ptd_alg_ob_mor ptd_alg_mor_id ptd_alg_mor_comp.

End ptd_alg_precategory_data.

End PointedAlgebras.

Section PointedAlgebraCategory.

Context {C : category} (F : pointed_endofunctor C).

Definition ptd_alg_mor_eq {X Y : ptd_alg F} (f g : ptd_alg_mor F X Y)
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro h.
  apply homset_property.
Qed.

Lemma is_precategory_precategory_ptd_alg_data : is_precategory (precategory_ptd_alg_data F).
Proof.
  apply make_is_precategory_one_assoc; intros; apply ptd_alg_mor_eq.
  - apply id_left.
  - apply id_right.
  - apply assoc.
Qed.

Definition ptd_alg_precat : precategory
  := make_precategory (precategory_ptd_alg_data F) is_precategory_precategory_ptd_alg_data.

Lemma has_homsets_pointed_alegbra : has_homsets ptd_alg_precat.
Proof.
  intros X Y.
  apply (isofhleveltotal2 2).
  - apply homset_property.
  - intros f.
    apply isasetaprop.
    apply homset_property.
Qed.

Definition ptd_alg_category : category
  := make_category ptd_alg_precat has_homsets_pointed_alegbra.

(** The functor which forgets the pointed algebra stucture on the underlying object *)
Definition forget_ptd_alg : ptd_alg_category ⟶ C.
Proof.
  use make_functor.
  - use make_functor_data.
    + simpl. exact (ptd_alg_carrier F).
    + simpl. intros X Y. exact (mor_from_ptd_alg_mor F).
  - abstract (split; red; now intros).
Defined.

End PointedAlgebraCategory.

(** 2. Properties of algebras for well-pointed endofunctors

The notion of algebra for a pointed endofunctor F involves adding *structure* to a carrier object
X : C, i.e. a map F X --> X which is a retraction of the point at X, σ_X : X --> F X.
Here we discover that when F is well-pointed, such a map is also a section of σ_X, and so this
structure degenerates to a *property* of X, i.e. is σ_X iso?

In fact, this makes the category of pointed algebras for F into a reflective subcategory of C.
We will see later, that any reflective subcategory induces an idempotent monad, which is in
particular, a well-pointed endofunctor, and the algebras for this well-pointed endofunctor recover
the reflective subcategory.
*)

Section AlgebrasWellPointed.

Context {C : category}.
Context (F : pointed_endofunctor C).
Context (H : well_pointed F).

Let σ := point F.
Let H' := well_pointed_pointwise H.

(** 2.1. Structure maps are iso-inverses [well_pointed_point_is_z_iso_at_algebra]
If X is a pointed algebra for (F, σ) (well-pointed), then σ_X : X --> F X is iso.
*)
Definition well_pointed_point_is_z_iso_at_algebra (X : ptd_alg F) : is_z_isomorphism (σ X).
Proof.
  apply make_is_z_isomorphism with (ptd_alg_map F X).
  split.
  (* σ_X ⋅ s = id_X is the axiom for pointed algebras *)
  - apply ptd_alg_law.
  (* s · σ_X = id_{FX} follows from naturality + well-pointedness + law for pointed algebras *)
  - rewrite point_naturality.
    rewrite H'.
    refine (! functor_comp F _ _ @ _).
    rewrite <- functor_id.
    apply maponpaths.
    apply ptd_alg_law.
Qed.

(** There is at most one pointed algebra structure on a given X : C. *)
Corollary well_pointed_has_ptd_alg_isaprop (A : C)
  : isaprop (∑ a : F A --> A, (σ A) · a = identity A).
Proof.
  apply invproofirrelevance; red. intros [a ar] [b br].
  apply subtypeInjectivity; simpl. { intros f. apply homset_property. }
  set (is := (well_pointed_point_is_z_iso_at_algebra (make_ptd_alg F A a ar))).
  apply (pre_comp_with_z_iso_is_inj is); simpl.
  exact (ar @ ! br).
Qed.

(** 2.2. Any morphism is a morphism of algebras [well_pointed_mor_is_algebra_mor]  *)
Corollary well_pointed_mor_is_algebra_mor (X Y : ptd_alg F) (f : C ⟦ X, Y ⟧)
  : is_ptd_alg_mor F X Y f.
Proof.
  red.
  set (point_X_iso := make_z_iso' _ (well_pointed_point_is_z_iso_at_algebra X)).
  apply (pre_comp_with_z_iso_is_inj point_X_iso); simpl.
  rewrite assoc, assoc.
  rw_left_comp (ptd_alg_law F X). apply pathsinv0.
  rw_left_comp (! point_naturality F f).
  rewrite <- assoc.
  rw_right_comp (ptd_alg_law F Y).
  now rewrite id_left, id_right.
Qed.

(** 2.3. The forgetful functor is fully-faithful [well_pointed_forgetul_fully_faithful] *)

(** For a well-pointed algebra F, its category of pointed algebras can be viewed as a subcategory
of C via the forgetful functor, because it is fully-faithful. The transfinite construction
will exhibit a left adjoint, making this a reflective subcategory. *)
Lemma well_pointed_forgetul_fully_faithful : fully_faithful (forget_ptd_alg F).
Proof.
  red. intros X Y.
  apply isweq_iso with (λ f, make_ptd_alg_mor F f (well_pointed_mor_is_algebra_mor X Y f)).
  - abstract (intros; now apply ptd_alg_mor_eq).
  - abstract easy. 
Defined.

(** Being in the (strict) image of the forgetful functor is a proposition. *)
Lemma well_pointed_image_forgetful_isaprop
  : ∏ A : C, isaprop (∑ X : ptd_alg F, forget_ptd_alg F X = A).
Proof.
  intros A.
  (* We reduce to showing this proposition is equivalent to the previous one *)
  refine (isofhlevelweqf 1 _ (well_pointed_has_ptd_alg_isaprop A)).
  use weq_iso.
  (* These constructions are almost definitionally inverse *)
  - intros [a ar].
    exists (make_ptd_alg F A a ar).
    apply idpath.
  - intros [X h].
    induction h.
    exists (ptd_alg_map F X).
    apply ptd_alg_law.
  - easy.
  - now intros [X h]; induction h.
Qed.

End AlgebrasWellPointed.

(** The transfinite construction
For F : C ⟶ C well-pointed, we have a fully-faithful inclusion of ptd_alg_category F into C.
We will show that F-Alg is actually reflective in C by constructing its left-adjoint, the free
pointed-algebra functor.

We handle only the Κ=ℕ case of the transfinite-construction, where C is assumed to have Κ-filtered
colimits, and F preserves them. This means C has colimits of ℕ-indexed diagrams of the form
X_0 --> X_1 --> X_2 --> ..., and F preserves them.
*)
Section TransfiniteConstruction.

Context {C : category}.
Context (chain_colimits : Chains C).
Context (F : pointed_endofunctor C).
Context (F_omega_cocont : is_omega_cocont F).
(** We will also assume F is well-pointed, but that is not needed just yet *)

Let σ := point F.

Local Notation "F '^' i" := (iter_functor F i).

Definition iter_chain_mor (i : nat)
  : F^i ⟹ F^(S i).
Proof.
  induction i as [|i IHi].
  - exact σ.
  - exact (post_whisker IHi F).
Defined.

(** This property of the chain morphisms is definitional, but important conceptually. *)
Definition iter_chain_mor_shift (i : nat) (A : C)
  : iter_chain_mor (S i) A = # F (iter_chain_mor i A)
  := idpath _.

(** The diagram Id --> F --> FF --> ..., in [C,C] where the ith morphism is F^i (σ(-)) *)
Definition iter_chain : chain [C, C].
Proof.
  apply make_diagram with (λ i, F ^ i).
  intros i _ []. exact (iter_chain_mor i).
Defined.

(** The diagram A --> F(A) --> FF(A) --> ..., in C where the ith morphism is F^i (σ A) *)
Definition iter_chain_at (A : C) : chain C.
Proof. 
  apply make_diagram with (λ i, (F ^ i) A).
  intros i _ []. exact (iter_chain_mor i A).
Defined.

(** 3.1. The directed colimit A --> F(A) --> F^2(A) --> ... F^ω(A) *)
Let CC : ∏ A : C, ColimCocone (iter_chain_at A)
  := λ A, chain_colimits _.

Local Notation "'F^ω'" := (λ A, colim (CC A)) (at level 0).

(**
  F is ω-cocontinuous, so applying F gives us a new colimiting cocone of the mapped diagram
  F(A) -> F(FA) -> F(FFA) -> ...
  with vertex F(F^ω A).
*)
Let F_CC : ∏ A : C, ColimCocone (mapchain F (iter_chain_at A))
  := λ A, make_ColimCocone _ _ _
            (F_omega_cocont _ _ _ (isColimCocone_from_ColimCocone (CC A))).

Local Notation "'FF^ω'" := (λ A, colim (F_CC A)) (at level 0).

(** 3.2. The shift map F(F^ω A) --> F^ω A [shift_iter_map]

  We want a structure map of the form F(F^ω A) --> F^ω A.
  Since F(F^ω A) is a colimit, it suffices to construct a cocone
    F(A) --> F^ω A
    F(FA) --> F^ω A
    F(FFA) --> F^ω A
    ...
  and the (1+i)th map of the colimiting cone for F^ω A has the correct form,
  since F(F^i(A)) = F^(1+i) A definitionally.
*)
Definition shift_iter_cocone (A : C)
  : cocone (mapchain F (iter_chain_at A)) (F^ω A).
Proof.
  apply make_cocone with (λ i, colimIn (CC A) (S i)).
  abstract (intros i _ []; exact (colimInCommutes (CC A) (S i) _ (idpath (S (S i))))).
Defined.

Definition shift_iter_map (A : C) : F (F^ω A) --> (F^ω A)
  := colimArrow (F_CC A) (F^ω A) (shift_iter_cocone A).

(** The structure map restricted to F(F^i A) is the inclusion F^(1+i) A --> F^ω A *)
Definition shift_iter_map_restricts (A : C) (i : nat)
  : colimIn (F_CC A) i · shift_iter_map A = (colimIn (CC A)) (S i)
  := colimArrowCommutes _ _ _ _.

(** Alternative to previous *)
Definition shift_iter_map_restricts' (A : C) (i : nat)
  : # F (colimIn (CC A) i) · shift_iter_map A = (colimIn (CC A)) (S i)
  := shift_iter_map_restricts A i.

(**
  We need F to be well-pointed to prove (F^ω A, shift_iter_map A) forms a pointed
  algebra (this is the only place well-pointedness is used, but many things follow)
  Dependency chain is:
  F_well_pointed
    => iter_chain_mor_is_point
    => shift_iter_map_forms_ptd_alg
    => free_ptd_alg_ob => free_ptd_alg
  
  The pointed algebra law is then used to construct the cocone for the counit
  (see counit_FF_forms_cocone).
*)
Section TransfiniteConstructionWellPointed.

Context (F_well_pointed : well_pointed F).

(** Since F is well-pointed, the chain morphisms are all points, i.e. F^i σ = σ F^i *)
Lemma iter_chain_mor_is_point (i : nat) (A : C) : iter_chain_mor i A = σ ((F ^ i) A).
Proof.
  apply pathsinv0.
  induction i.
  - exact (idpath _).
  - exact (well_pointed_pointwise F_well_pointed ((F ^ i) A) @ maponpaths (#F) IHi).
Qed.

(** 3.3. The shift map forms a pointed algebra [shift_iter_map_forms_ptd_alg]
  The structure map restricts to the identity via σ (F^ω A),
  thus making (F^ω A, shift_iter_map A) a pointed algebra.
  Not surprising, since the structure map is a colimit of components of σ
*)
Lemma shift_iter_map_forms_ptd_alg (A : C)
  : is_ptd_alg F (make_ptd_alg_data F (F^ω A) (shift_iter_map A)).
Proof.
  unfold is_ptd_alg; simpl.
  set (s := shift_iter_map A).

  apply pathsinv0, colim_endo_is_identity.
  intro i.
  rewrite assoc.
  (* α_A^i · σ_{F^ω A} · s = σ_{F^i A} · F (α_A^i) · s *)
  rewrite point_naturality.
  rewrite <- assoc.
  (* ... = σ_{F^i A} · α_A^(1+i) *)
  rewrite shift_iter_map_restricts'.
  simpl. rewrite <- iter_chain_mor_is_point. (* well-pointedness used here! *)
  (* ... = α_A^i *)
  apply (colimInCommutes (CC A) i (1+i) (idpath _)).
Qed.

(** 3.4. The free functor C ⟶ ptd_alg_category F [free_ptd_alg] *)

(** The free pointed algebra on A, (F^ω A, shift_iter_map A) *)
Definition free_ptd_alg_ob (A : C) : ptd_alg F
  := make_ptd_alg F (F^ω A) (shift_iter_map A) (shift_iter_map_forms_ptd_alg A).

(**
  The free functor action on morphisms, given by the canonical map between the colimits
  NOTE: this is the underlying morphism in C, not in the category of algebras
*)
Definition free_ptd_alg_mor {A B : C} (f : A --> B)
  : C ⟦ free_ptd_alg_ob A, free_ptd_alg_ob B ⟧.
Proof.
  apply colimOfArrows with (λ i, # (F ^ i) f).
  intros i _ []; simpl.
  induction i.
  + abstract (simpl; apply pathsinv0, point_naturality).
  + abstract (simpl; do 2 rewrite <- functor_comp; apply maponpaths; exact IHi).
Defined.

Definition free_ptd_alg_mor_restricts {A B : C} (f : A --> B) (i : nat)
  : colimIn (CC A) i · free_ptd_alg_mor f = # (F ^ i) f · colimIn (CC B) i
  := colimArrowCommutes _ _ _ _.

Definition free_ptd_alg_mor_is_mor {A B : C} (f : A --> B)
  : is_ptd_alg_mor F _ _ (free_ptd_alg_mor f).
Proof.
  apply (colim_mor_eq (F_CC A)); simpl.
  intros i.
  rewrite assoc, assoc.
  rw_left_comp shift_iter_map_restricts.
  refine (free_ptd_alg_mor_restricts f (S i) @ _).
  change (colimIn (F_CC A) i) with (# F (colimIn (CC A) i)).
  rewrite <- functor_comp.
  apply (transportb (λ x, _ = # F x · _) (free_ptd_alg_mor_restricts f i)).
  simpl.
  rewrite functor_comp, <- assoc.
  apply cancel_precomposition.
  apply pathsinv0, shift_iter_map_restricts.
Qed.

Definition free_ptd_alg_functor_data : functor_data C (ptd_alg_category F).
Proof.
  use make_functor_data.
  - exact free_ptd_alg_ob.
  - intros A B f.
    exact (make_ptd_alg_mor F (free_ptd_alg_mor f) (free_ptd_alg_mor_is_mor f)).
Defined.

Lemma free_ptd_alg_is_functor : is_functor free_ptd_alg_functor_data.
Proof.
  split.
  - intros A. apply ptd_alg_mor_eq.
    apply pathsinv0, colim_endo_is_identity. intros i.
    refine (free_ptd_alg_mor_restricts _ _ @ _).
    rewrite functor_id.
    apply id_left.
  - red. intros X Y Z f g. apply pathsinv0, ptd_alg_mor_eq; simpl.
    apply colimArrowUnique; simpl. intros i.
    rewrite assoc.
    rw_left_comp (free_ptd_alg_mor_restricts f i).
    rewrite <- assoc.
    rw_right_comp (free_ptd_alg_mor_restricts g i).
    rewrite assoc. apply cancel_postcomposition.
    apply pathsinv0, functor_comp.
Qed.

Definition free_ptd_alg : C ⟶ ptd_alg_category F
  := make_functor free_ptd_alg_functor_data free_ptd_alg_is_functor.

(** 3.5. The free-forgetful adjunction [free_forgetful_form_adjunction]
  We now prove that this is indeed the free functor, by constructing an adjunction *)

Definition unit_FF_adjunction : functor_identity C ⟹ free_ptd_alg ∙ forget_ptd_alg F.
Proof.
  apply make_nat_trans with (λ A, colimIn (CC A) 0).
  abstract (intros A B f; apply pathsinv0, (free_ptd_alg_mor_restricts f 0)).
Defined.

Definition counit_FF_cocone_arrows (X : ptd_alg F) : ∏ i : nat, C ⟦ (F ^ i) X, X ⟧.
Proof.
  induction i as [|i IH].
  - exact (identity X). (* Forced by triangle identities *)
  - exact (# F IH · ptd_alg_map F X). (* Necessary to make ɛ an morphism of algebras *)
Defined.

Lemma counit_FF_forms_cocone (X : ptd_alg F)
  : forms_cocone (iter_chain_at X) (counit_FF_cocone_arrows X).
Proof.
  red; intros i _ []; simpl.
  set (ɛ := counit_FF_cocone_arrows).
  rewrite assoc.
  (* This could be done using iter_chain_mor_is_point, but it's not necessary! *)
  induction i.
  - simpl. rewrite functor_id, id_right. apply ptd_alg_law.
  - simpl. rewrite <- functor_comp, assoc.
    apply (maponpaths (λ x, # F x · _) IHi).
Qed.

(** The counit has a component at the pointed algebra X which is a morphism of algebras F^ω X --> X.
  This is the underlying morphism in C.
  (Be aware of the implicit coercion of X to it's underlying object in C)
*)
Definition counit_FF_map (X : ptd_alg F) : C ⟦ free_ptd_alg_ob X, X ⟧
  := colimArrow _ _ (make_cocone _ (counit_FF_forms_cocone X)).

Definition counit_FF_map_restricts (X : ptd_alg F) (i : nat)
  : colimIn (CC X) i · counit_FF_map X = counit_FF_cocone_arrows X i
  := colimArrowCommutes _ _ _ _.

Definition counit_FF_mor_is_mor (X : ptd_alg F) :
  is_ptd_alg_mor F (free_ptd_alg X) X (counit_FF_map X).
Proof.
  unfold is_ptd_alg_mor; simpl.
  apply (colim_mor_eq (F_CC X)).
  intros i.
  rewrite assoc, assoc.
  rewrite shift_iter_map_restricts.
  refine (counit_FF_map_restricts X (S i) @ _); simpl.
  apply cancel_postcomposition.
  change (colimIn (F_CC X) i) with (# F (colimIn (CC X) i)).
  rewrite <- functor_comp.
  apply maponpaths, pathsinv0.
  apply counit_FF_map_restricts.
Qed.

Definition counit_FF_mor (X : ptd_alg F) : free_ptd_alg X --> X
  := make_ptd_alg_mor F (counit_FF_map X) (counit_FF_mor_is_mor X).

Definition counit_FF_adjunction_is_nat_trans
  : is_nat_trans
      (forget_ptd_alg F ∙ free_ptd_alg)
      (functor_identity (ptd_alg_category F))
      counit_FF_mor.
Proof.
  intros X Y f. apply ptd_alg_mor_eq; simpl in *.
  apply colim_mor_eq; intros i. do 2 rewrite assoc.
  rw_left_comp (free_ptd_alg_mor_restricts f i).
  rewrite <- assoc.
  rw_right_comp (counit_FF_map_restricts Y i).
  rewrite (counit_FF_map_restricts X i).
  set (ɛ := counit_FF_cocone_arrows).

  induction i; simpl. { rewrite id_left. apply id_right. }
  rewrite assoc. rewrite <- functor_comp.
  apply (transportb (λ x, # F x · _ = _) IHi).
  rewrite <- assoc.
  rewrite functor_comp.
  rewrite <- (assoc _ _ (ptd_alg_map F Y)).
  apply cancel_precomposition.
  apply pathsinv0, ptd_alg_mor_commutes.
Qed.

Definition counit_FF_adjunction
  : (forget_ptd_alg F ∙ free_ptd_alg) ⟹ (functor_identity (ptd_alg_category F))
  := make_nat_trans _ _ _ counit_FF_adjunction_is_nat_trans.

(** This proves free construction is correctly named, it is left adjoint
  to the forgetful functor. *)
Theorem free_forgetful_form_adjunction
  : form_adjunction free_ptd_alg
      (forget_ptd_alg F)
      unit_FF_adjunction
      counit_FF_adjunction.
Proof.
  split; red.
  + intro A. apply ptd_alg_mor_eq, pathsinv0; simpl.
    apply colim_endo_is_identity. intros i.
    rewrite assoc.
    rw_left_comp (free_ptd_alg_mor_restricts (colimIn (CC A) 0) i).
    rewrite <- assoc.
    rw_right_comp (counit_FF_map_restricts (free_ptd_alg_ob A) i).
    set (ɛ := counit_FF_cocone_arrows).
    induction i; simpl. { apply id_right. }
    rewrite assoc, <- functor_comp.
    apply (transportb (λ x, # F x · _ = _) IHi).
    apply shift_iter_map_restricts.
  + intro X. simpl. apply (counit_FF_map_restricts X 0).
Qed.

Definition free_forgetful_are_adjoints : are_adjoints free_ptd_alg (forget_ptd_alg F)
  := make_are_adjoints _ _ _ _ free_forgetful_form_adjunction.

(* TODO: Involve fully-faithfulness of forget_ptd_alg F to say something
about reflective subcategories *)

End TransfiniteConstructionWellPointed.

End TransfiniteConstruction.

(** 4. Reflective subcategories give well-pointed endofunctors
  [well_pointed_of_fully_faithful_right_adjoint]

We've constructed the reflective subcategory given by the pointed algebras
of a well-pointed endofunctor.
Conversely, we can take *any* reflective subcategory of C and extract a
well-pointed endfunctor on C (in fact, an idempotent monad), whose
pointed algebras form the "same" reflective subcategory.
*)
Theorem well_pointed_of_fully_faithful_right_adjoint
  {C D : category} 
  (L : functor C D) (R : functor D C)
  (H : are_adjoints L R)
  (η := unit_from_are_adjoints H)
  : fully_faithful R → well_pointed (L∙R,,η).
Proof.
  intro R_ff.
  apply (nat_trans_eq (homset_property _)).
  intros A. simpl.
  set (ɛ := counit_from_are_adjoints H).
  (* The triangle identities imply that RLη and ηRL are sections of RɛLA, which is iso *)
  assert (t1 : # R (# L (η A)) · # R (ɛ (L A)) = identity (R (L A))). {
    rewrite <- functor_id, <- functor_comp.
    apply maponpaths.
    apply triangle_id_left_ad.
  }
  assert (t2 : η (R (L A)) · # R (ɛ (L A)) = identity (R (L A))). {
    apply triangle_id_right_ad.
  }
  assert (ɛ_z_iso := counit_is_z_iso_if_right_adjoint_is_fully_faithful H R_ff).
  assert (p : is_z_isomorphism (# R (ɛ (L A)))). {
    apply functor_on_is_z_isomorphism.
    apply counit_is_z_iso_if_right_adjoint_is_fully_faithful.
    exact R_ff.
  }
  apply (post_comp_with_z_iso_is_inj p).
  exact (t2 @ ! t1).
Qed.

(* TODO: prove the category of pointed algebras for (L∙R,,η) "is" D *)