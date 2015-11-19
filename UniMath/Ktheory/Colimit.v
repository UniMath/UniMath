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

Arguments diagram_from_functor [J C] F.

Coercion diagram_from_functor : functor >-> diagram.

Definition cocone' {C I:Precategory} (D: I==>C) (c:C) : UU
  := cocone (diagram_from_functor D) c.

Identity Coercion cocone'_to_cocone : cocone' >-> cocone.

Definition cocone_functor {C I:Precategory} : [I,C]^op ==> [C,SET].
Proof.
  intros.
  refine (_,,_).
  { refine (_,,_).
    { intros D. refine (_,,_).
      { refine (_,,_).
        - intro c. exists (cocone' D c). abstract (set_logic) using L.
        - simpl. intros c c' f φ. exists (λ i, f ∘ φ i).
          abstract (
              intros i j e; refine (assoc _ _ _ @ _);
              apply (maponpaths (λ h, _ ∘ h)); apply coconeInCommutes) using L. }
      { abstract eqn_logic using L. } }
    { intros D D' f; simpl.
      refine (_,,_).
      - simpl. unfold cocone'. intros c φ. refine (_,,_).
        + intros i. exact (φ i ∘ pr1 f i).
        + simpl.
          abstract (
              intros i j e;
              refine (_ @ maponpaths (λ p, p ∘ (f : _ ⟶ _) i) (coconeInCommutes φ i j e));
              refine (assoc _ _ _ @ _ @ ! assoc _ _ _);
              apply (maponpaths (λ p, _ ∘ p));
              apply nat_trans_ax ) using L.
      - abstract eqn_logic using L. } }
  { unfold cocone'. split.
    { intros D. refine (total2_paths2 _ _).
      - apply funextsec; intro c. simpl.
        apply funextsec; intro φ.
        refine (total2_paths _ _).
        + simpl. apply funextsec; intro i. apply id_left.
        + apply funextsec; intro i.
          apply funextsec; intro j.
          apply funextsec; intro e.
          apply homset_property.
      - apply isaprop_is_nat_trans, homset_property. }
    { intros D D' D'' p q.
      simpl.
      refine (total2_paths2 _ _).
      - apply funextsec; intro c. simpl. apply funextsec; intro φ.
        refine (total2_paths2 _ _).
        + simpl. apply funextsec; intro i. apply pathsinv0, assoc.
        + apply funextsec; intro i.
          apply funextsec; intro j.
          apply funextsec; intro e.
          apply homset_property.
      - apply isaprop_is_nat_trans. exact (homset_property SET). } }
Defined.

Definition Colimit {C I:Precategory} (D: I==>C) := Representation.Data (cocone_functor D).

Definition colimitObject {C I:Precategory} {D: I==>C} (r:Colimit D) : ob C
  := Representation.Object r.

Coercion colimitObject : Colimit >-> ob.

Definition colimitCocone {C I:Precategory} {D: I==>C} (colim:Colimit D) : cocone' D colim
  := Representation.Element colim.

Coercion colimitCocone : Colimit >-> cocone'.

Definition colimitIn {C I:Precategory} {D: I==>C} (colim:Colimit D) (i:I) :
  Hom (D i) colim.
Proof. intros. exact (colim i). Defined.

Definition colimitInTriangle {C I:Precategory} {D: I==>C} (colim:Colimit D) {i j:I} (f:i→j) :
  colimitIn colim j ∘ # D f = colimitIn colim i.
Proof. intros. exact (coconeInCommutes colim i j f). Defined.

Definition hasColimits (C:Precategory) := ∀ (I:Precategory) (D: I==>C), Colimit D.

Definition functor_eval {A B:Precategory} : A -> [A,B] ==> B.
Proof.
  intros ? ? a.
  refine (_,,_).
  - refine (_,,_).
    + intro F. exact ((F:_==>_) a).
    + intros F G p. simpl. exact (pr1 p a). (* change pr1 to the appropriate notation *)
  - eqn_logic.
Defined.

Definition diagram_eval {A B I:Precategory} : I ==> [A, B] -> A -> I ==> B.
Proof.
  intros ? ? ? D a. refine (_,,_).
  - refine (_,,_).
    + intro i. exact ((D i : _ ==> _) a).
    + simpl. intros i j e. exact ((# D e : _ ⟶ _) a).
  - split.
    + intro i; simpl.
      exact (maponpaths (λ F : _⟶_, F _) (functor_id D _)). (* how to add this to eqn_logic? *)
    + intros i j k f g; simpl.
      exact (maponpaths (λ F : _⟶_, F _) (functor_comp D _ _ _ _ _)).
Defined.

(* we should make [diagram I C] into the objects of a category *)

Definition diagram_map_on_diagram_identity_map {C:Precategory} {I} (D:diagram I C) :
   diagram_map_on_cocone_functor (diagram_identity_map D) = nat_trans_id (cocone_functor D).
Proof.
  intros. abstract eqn_logic using L.
Defined.

Definition diagram_map_on_colim {C:Precategory} {I} {D D' : diagram I C}
           (colimD : Colimit D) (colimD' : Colimit D') (f : diagram_map D D') :
  colimitObject colimD → colimitObject colimD'.
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
  intros. abstract eqn_logic using L.
Defined.

Definition diagram_eval_map_on_composite {A B I} (D : diagram I [A, B]) {a a' a'':A} (f:a→a') (g:a'→a'') :
  diagram_eval_map D (g ∘ f) = diagram_map_composite (diagram_eval_map D f) (diagram_eval_map D g).
Proof.
  intros. abstract eqn_logic using L.
Defined.

Theorem functorPrecategoryColimits (A B:Precategory) : hasColimits B -> hasColimits [A,B].
Proof.
  intros ? ? colim ? ?.
  unfold Colimit. unfold Representation.Data.
  refine (InitialAndFinalObject.make_InitialObject _ _ _).
  - refine (_,,_).
    + refine (_,,_).
      * refine (_,,_).
        { intro a. exact (colimitObject (colim I (diagram_eval D a))). }
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
