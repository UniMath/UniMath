Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories
        UniMath.CategoryTheory.colimits.colimits.

Local Open Scope cat.

Coercion coconeIn : cocone >-> Funclass.
Coercion vertex : graph >-> UU.
Coercion dob : diagram >-> Funclass.
Coercion diagram_from_functor : functor >-> diagram.
Arguments diagram_from_functor [J C] F.

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
