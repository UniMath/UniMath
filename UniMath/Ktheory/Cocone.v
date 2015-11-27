Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories
        UniMath.CategoryTheory.colimits.colimits
        UniMath.CategoryTheory.limits.limits.

Set Automatic Introduction.
Local Open Scope cat.

Definition cone {I C:Precategory} (c:C) (D: [I,C]) : UU
  := Σ (φ : ∀ i, Hom C c (D ◾ i)),
     ∀ i j (e : i → j), D ▭ e ∘ φ i = φ j.

Lemma cone_eq {C I:Precategory} (c:C^op) (D: I==>C) (p q:cone (C:=C) c D) :
  pr1 p ~ pr1 q -> p = q.
Proof.
  intros h. apply subtypeEquality.
  { intro r.
    apply impred_isaprop; intro i;
    apply impred_isaprop; intro j;
    apply impred_isaprop; intro e.
    apply homset_property. }
  apply funextsec; intro i; apply h.
Qed.

Open Scope cat'.

Definition cone_functor {I C:Precategory} : [I,C] ==> [C^op,SET].
Proof.
  intros.
  refine (_,,_).
  { refine (_,,_).
    { intros D. refine (_,,_).
      { refine (_,,_).
        - intro c. exists (cone (C:=C) c D).
          abstract (
              apply isaset_total2;
              [ apply impred_isaset; intro i; apply homset_property
              | intros φ;
                apply impred_isaset; intro i;
                apply impred_isaset; intro j;
                apply impred_isaset; intro e; apply isasetaprop;
                apply homset_property]) using LLL.
        - simpl; intros a b f φ.
          exists (λ i, pr1 φ i ∘ f).
          abstract (
              intros i j e; simpl;
              rewrite <- assoc;
              apply maponpaths;
              apply (pr2 φ)) using M. }
      { abstract (split;
        [ intro c; simpl;
          apply funextsec; intro p;
          apply cone_eq;
          intro i; simpl;
          apply id_left
        | intros a b c f g; simpl; apply funextsec; intro p;
          apply cone_eq; simpl; intro i; apply pathsinv0, assoc ]) using N. } }
    { intros D D' f; simpl.
      refine (_,,_).
      - simpl. unfold cone. intros c φ.
        refine (_,,_).
        + intros i. exact (pr1 f i ∘ pr1 φ i).
        + abstract (
              simpl; intros i j e; assert (L := pr2 φ i j e); simpl in L;
              rewrite <- L; rewrite <- assoc; rewrite <- assoc;
              apply maponpaths; apply pathsinv0; apply nat_trans_ax) using P.
      - abstract (intros a b g; simpl;
                  apply funextsec; intro p; apply cone_eq; intro i; simpl;
                  apply pathsinv0, assoc) using Q. } }
  { abstract ( unfold cone; split;
    [ intros D; simpl;
      refine (total2_paths2 _ _);
      [ apply funextsec; intro c;
        apply funextsec; intro φ; simpl;
        refine (total2_paths _ _);
        [ simpl; apply funextsec; intro i; apply id_right
        | apply funextsec; intro i;
          apply funextsec; intro j;
          apply funextsec; intro e;
          apply homset_property ]
      | apply isaprop_is_nat_trans; exact (homset_property SET)]
    | intros D D' D'' p q;
      simpl;
      refine (total2_paths2 _ _);
      [ apply funextsec; intro c; simpl; apply funextsec; intro φ;
        refine (total2_paths2 _ _);
        [ simpl; apply funextsec; intro i; apply assoc
        | apply funextsec; intro i;
          apply funextsec; intro j;
          apply funextsec; intro e;
          apply homset_property ]
      | apply isaprop_is_nat_trans; exact (homset_property SET)] ]) using R. }
Defined.

Definition cocone_functor {I C:Precategory} : [I,C]^op ==> [C^op^op,SET]
  := cone_functor □ op_move op_functor.

(*  *)