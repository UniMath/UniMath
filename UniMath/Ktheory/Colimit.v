Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Sets
        UniMath.Ktheory.Precategories
        UniMath.Ktheory.Representation
        UniMath.CategoryTheory.colimits.colimits.

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

Definition Colimit {C I:Precategory} (D: I==>C) := Representation (cocone_functor D).

Definition colimitObject {C I:Precategory} {D: I==>C} (colim:Colimit D) : ob C
  := universalObject colim.

Coercion colimitObject : Colimit >-> ob.

Definition colimitCocone {C I:Precategory} {D: I==>C} (colim:Colimit D) : cocone' D colim
  := universalElement colim.

Coercion colimitCocone : Colimit >-> cocone'.

Definition colimitIn {C I:Precategory} {D: I==>C} (colim:Colimit D) (i:I) : D i → colim.
Proof. intros. exact (colim i). Defined.

Definition colimitInTriangle {C I:Precategory} {D: I==>C} (colim:Colimit D) {i j:I} (f:i→j) :
  colimitIn colim j ∘ # D f = colimitIn colim i.
Proof. intros. exact (coconeInCommutes colim i j f). Defined.

Definition hasColimits (C:Precategory) := ∀ (I:Precategory) (D: I==>C), Colimit D.

Definition diagram_eval {A B I:Precategory} : I ==> [A, B] -> A -> I ==> B.
Proof.
  intros ? ? ? D a. refine (_,,_).
  - refine (_,,_).
    + intro i. exact ((D i : _ ==> _) a).
    + simpl. intros i j e. exact ((# D e : _ ⟶ _) a).
  - split.
    + intro i; simpl.
      exact (maponpaths (λ F : _⟶_, F _) (functor_id D _)).
    + intros i j k f g; simpl.
      exact (maponpaths (λ F : _⟶_, F _) (functor_comp D _ _ _ _ _)).
Defined.

Definition bifunctor_comm {I A B:Precategory} : [I, [A, B] ] ==> [A, [I, B] ].
Proof.
  intros.
  refine (_,,_).
  { refine (_,,_).
    { intros D.
      refine (_,,_).
      { refine (_,,_).
        { intros a.
          refine (_,,_).
          - refine (_,,_).
            + intro i. exact (((D : _ ==> _) i : _ ==> _) a).
            + simpl. intros i j e. exact ((# (D : _ ==> _) e : _ ⟶ _) a).
          - abstract (split ;
                      [abstract (intro i; simpl;
                        exact (maponpaths (λ F : _⟶_, F _) (functor_id D _)))
                      |(intros i j k f g; simpl;
                        exact (maponpaths (λ F : _⟶_, F _) (functor_comp D _ _ _ _ _)))])
            using is_functor_0.
          }
        intros a a' f.
        refine (_,,_).
        { simpl. intro i. exact (# ((D:_==>_) i :_==>_) f). }
        { abstract (intros i j r; simpl; eqn_logic) using is_nat_trans_0. } }
      { abstract ( split;
                   [intros a; simpl; eqn_logic
                   |
                   intros a b g r s; simpl;
                   refine (total2_paths2 _ _) ;
                   [ abstract (apply funextsec; intro i; simpl; apply functor_comp) |
                     eqn_logic ]]) using is_functor_0. } }
    { intros D D' p. simpl.
      refine (_,,_).
      { intros a. simpl.
        refine (_,,_).
        { intros i; simpl. exact (((p : _ ⟶ _) i : _ ⟶ _) a). }
        { abstract (intros i j e; simpl;
                    exact (maponpaths (λ v : _ ⟶ _, v a) (nat_trans_ax p _ _ e))) using is_nat_trans_0. } }
      { abstract (intros a b f; simpl;
                  refine (total2_paths2 _ _);
                  [ apply funextsec; intro i; simpl;
                    exact (nat_trans_ax ((p : _ ⟶ _) i) _ _ f)
                    | simpl; apply isaprop_is_nat_trans, homset_property ]) using is_nat_trans_0. } } }
  { abstract (split;
    [ abstract (
          intros D; simpl; refine (total2_paths2 _ _);
          [ abstract (apply funextsec; intro a; refine (total2_paths2 _ _) ;
            [ reflexivity | apply isaprop_is_nat_trans, homset_property ] )
          |
          simpl; apply isaprop_is_nat_trans; apply (homset_property [I,B]) ]) using functor_idax_0 |
      abstract (
          simpl; intros D D' D'' p q; simpl; refine (total2_paths2 _ _);
          [abstract (
                apply funextsec; intro a; refine (total2_paths2 _ _);
                [ reflexivity |
                  apply funextsec; intro i;
                  apply funextsec; intro j;
                  apply funextsec; intro e;
                  apply homset_property])
          | apply isaprop_is_nat_trans; exact (homset_property [I,B]) ]) using functor_compax_0 ])
    using is_functor_0. }
Defined.


Theorem functorPrecategoryColimits (A B:Precategory) : hasColimits B -> hasColimits [A,B].
Proof.
  intros ? ? colim ? ?.
  unfold Colimit. unfold Representation.
  - refine (_,,_).
    + refine (_,,_).
      * refine (_,,_).
        { intro a. exact (colimitObject (colim I (diagram_eval D a))). }
      (*   { simpl. intros a a' f. apply diagram_map_on_colim. *)
      (*     apply diagram_eval_map. exact f. } *)
      (* * split. *)
      (*   { intro a; simpl. *)
      (*     refine (_ @ Representation.objectMapIdentity _). *)
      (*     unfold diagram_map_on_colim. *)
      (*     apply maponpaths. *)
      (*     rewrite diagram_eval_map_on_identity. *)
      (*     apply diagram_map_on_diagram_identity_map. } *)
      (*   { intros a a' a'' f g. simpl. *)

Abort.


(*
Local Variables:
compile-command: "make -C ../.. TAGS TAGS-Ktheory UniMath/Ktheory/DiagramColimit.vo"
End:
*)
