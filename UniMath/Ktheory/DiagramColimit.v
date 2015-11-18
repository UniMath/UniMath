Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Sets
        UniMath.Ktheory.Precategories
        UniMath.CategoryTheory.colimits.colimits.
Require UniMath.Ktheory.Representation.

Local Open Scope cat.

Local Coercion coconeIn : cocone >-> Funclass.
Local Coercion vertex : graph >-> UU.
Local Coercion dob : diagram >-> Funclass.

Definition cocone_functor_data {C:Precategory} {I: graph} (D: diagram I C) : functor_data C SET.
(* [cocone D c] is the set of cocones from the base D to the vertex c in C *)
Proof.
  intros. refine (_,,_).
  - intro c. exists (cocone D c). abstract (set_logic) using L.
  - simpl. intros c c' f φ. exists (λ i, f ∘ φ i).
    abstract (
        intros i j e; refine (assoc _ _ _ @ _);
        apply (maponpaths (λ h, _ ∘ h)); apply coconeInCommutes) using L.
Defined.

Definition cocone_functor {C:Precategory}
           {I: graph} (D: diagram I C) : C ==> SET.
Proof. intros. exists (cocone_functor_data D). abstract eqn_logic using L. Defined.

Definition Colimit {C:Precategory} {I} (D: diagram I C)
  := Representation.Data (cocone_functor D).

Definition Object {C:Precategory} {I} {D: diagram I C} (r:Colimit D) : ob C
  := Representation.Object r.

Definition Cocone {C:Precategory} {I} {D: diagram I C} (r:Colimit D) : cocone D (Object r)
  := Representation.Element r.

Coercion Cocone : Colimit >-> cocone.

Definition In {C:Precategory} {I} {D: diagram I C} (r:Colimit D) (i:I) :
  Hom (D i) (Object r).
Proof. intros. exact (r i). Defined.

Definition InCommutes {C:Precategory}
           {I} {D: diagram I C} (r:Colimit D)
           {i j:I} (f:edge i j) :
  In r j ∘ dmor D f = In r i.
Proof. intros. apply coconeInCommutes. Defined.

Definition hasColimits (C:Precategory) := ∀ I (D: diagram I C), Colimit D.

Definition functorPrecategory (C D:Precategory) : Precategory.
Proof.
  intros. exists (functor_precategory C D (homset_property D)).
  abstract set_logic using L.
Defined.

Notation "[ C , D ]" := (functorPrecategory C D) : cat.

Definition diagram_eval {A B I} : diagram I [A, B] -> A -> diagram I B.
Proof.
  intros ? ? ? D a. refine (_,,_).
  - intro i. exact ((D i : _ ==> _) a).
  - simpl. intros i j e. exact ((dmor D e : _ ⟶ _) a).
Defined.

Definition diagram_map {C I} (D D' : diagram I C) :=
  Σ (f : ∀ i, D i → D' i), ∀ i j (e:edge i j), f j ∘ dmor D e = dmor D' e ∘ f i.

Definition diagram_map_on_vertex {C I} {D D' : diagram I C} (f : diagram_map D D') i : D i → D' i
  := pr1 f i.

Coercion diagram_map_on_vertex : diagram_map >-> Funclass.

Definition diagram_identity_map {C I} (D : diagram I C) : diagram_map D D.
Proof.
  intros. exists (λ i, identity (D i)). intros. exact (id_right _ @ ! id_left _).
Defined.

Definition diagram_map_composite {C I} {D D' D'': diagram I C}
           (f : diagram_map D D') (g : diagram_map D' D'') : diagram_map D D''.
Proof.
  intros. exists (λ i, g i ∘ f i). intros.
  refine (assoc _ _ _ @ _ @ assoc _ _ _). intermediate_path (g j ∘ (dmor D' e ∘ f i)).
  - apply (maponpaths (λ q, g j ∘ q)). apply (pr2 f).
  - refine (! assoc _ _ _ @ _). apply (maponpaths (λ q, q ∘ f i)). apply (pr2 g).
Defined.

Definition diagram_map_comm {C I} {D D' : diagram I C}
           (f : diagram_map D D') {i j : I} (e : edge i j) :
  f j ∘ dmor D e = dmor D' e ∘ f i
  := pr2 f i j e.

Definition diagram_map_on_cocone_functor {C:Precategory} {I} {D D' : diagram I C}
           (f : diagram_map D D') :
  cocone_functor D' ⟶ cocone_functor D. (* the notation means the result is a natural transformation *)
Proof.
  intros. refine (_,,_).
  - intros c φ. unfold cocone_functor in φ; simpl in φ. refine (_,,_).
    + intros i. exact (φ i ∘ f i).
    + simpl.
      abstract (
          intros i j e;
          refine (_ @ maponpaths (λ p, p ∘ f i) (coconeInCommutes φ i j e));
          refine (assoc _ _ _ @ _ @ ! assoc _ _ _);
          apply (maponpaths (λ p, _ ∘ p));
          apply diagram_map_comm ) using L.
  - abstract eqn_logic using L.
Defined.

(* we should make [diagram I C] into the objects of a category *)

Definition diagram_map_on_diagram_identity_map {C:Precategory} {I} (D:diagram I C) :
   diagram_map_on_cocone_functor (diagram_identity_map D) = nat_trans_id (cocone_functor D).
Proof.
  intros.
  refine (total2_paths2 _ _).
  - apply funextsec; intro c; apply funextsec; intro coco.
    refine (total2_paths _ _).
    + abstract (apply funextsec; intro i; apply id_left) using L.
    + abstract eqn_logic using L.
  - abstract (apply isaprop_is_nat_trans, category_hset.has_homsets_HSET) using L.
Defined.

Definition diagram_map_on_colim {C:Precategory} {I} {D D' : diagram I C}
           (colimD : Colimit D) (colimD' : Colimit D') (f : diagram_map D D') :
  Object colimD → Object colimD'.
Proof.
  intros. apply Representation.objectMap.
  apply diagram_map_on_cocone_functor. exact f.
Defined.

Definition diagram_eval_map {A B I} (D : diagram I [A, B]) {a a':A} (f:a→a') :
  diagram_map (diagram_eval D a) (diagram_eval D a').
Proof.
  intros. refine (_,,_).
  - intro i. unfold diagram_eval; simpl. exact (# (D i : _ ==> _) f).
  - abstract eqn_logic using L.
Defined.

Definition diagram_eval_map_on_identity {A B I} (D : diagram I [A, B]) a :
  diagram_eval_map D (identity a) = diagram_identity_map (diagram_eval D a).
Proof.
  intros.
  unfold diagram_eval_map, diagram_identity_map.
  refine (total2_paths2 _ _).
  - simpl. apply funextsec; intro i.
    exact (pr1 (pr2 (D i : _ ==> _)) a). (* there must be an abbreviation for this *)
  - eqn_logic.
Defined.

Definition diagram_eval_map_on_composite {A B I} (D : diagram I [A, B]) {a a' a'':A} (f:a→a') (g:a'→a'') :
  diagram_eval_map D (g ∘ f) = diagram_map_composite (diagram_eval_map D f) (diagram_eval_map D g).
Proof.
  intros.


Abort.

Theorem functorPrecategoryColimits (A B:Precategory) : hasColimits B -> hasColimits [A,B].
Proof.
  intros ? ? colim ? ?.
  unfold Colimit. unfold Representation.Data.
  refine (InitialAndFinalObject.make_InitialObject _ _ _).
  - refine (_,,_).
    + refine (_,,_).
      * refine (_,,_).
        { intro a. exact (Object (colim I (diagram_eval D a))). }
        { simpl. intros a a' f. apply diagram_map_on_colim.
          apply diagram_eval_map. exact f. }
      * split.
        { intro a; simpl.
          refine (_ @ Representation.objectMapIdentity _).
          unfold diagram_map_on_colim.
          apply maponpaths.
          rewrite diagram_eval_map_on_identity.
          apply diagram_map_on_diagram_identity_map. }
        { intros a a' a'' f g. simpl.

Abort.


(*
Local Variables:
compile-command: "make -C ../.. TAGS TAGS-Ktheory UniMath/Ktheory/DiagramColimit.vo"
End:
*)
