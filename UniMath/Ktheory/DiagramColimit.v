Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories
        UniMath.CategoryTheory.colimits.colimits.
Require UniMath.Ktheory.Representation.

Definition cocone_functor_data {C:precategory} (h: has_homsets C)
           {Γ: graph} (D: diagram Γ C) : functor_data C SET.
Proof.
  intros. refine (_,,_).
  - intro c. exists (cocone D c). unfold cocone. apply (isofhleveltotal2 2).
    + apply impred_isaset; intro g. apply h.
    + intro φ. apply impred_isaset; intro g.
      apply impred_isaset; intro g'. apply impred_isaset; intro e.
      apply isasetaprop. apply h.
  - intros c c' f φ; simpl. exists (λ g, compose (coconeIn φ g) f).
    intros g g' e; simpl. rewrite assoc. now rewrite coconeInCommutes.
Defined.

Definition cocone_functor {C:precategory} (h: has_homsets C)
           {Γ: graph} (D: diagram Γ C) : C ==> SET.
Proof.
  intros. exists (cocone_functor_data h D). split.
  - intros c. apply funextfun; intros f. refine (total2_paths _ _).
    * apply funextsec; intro g. apply id_right.
    * apply funextsec; intro g. apply funextsec; intro g'. apply funextsec; intro e. apply h.
  - intros a b c p q. apply funextfun; intro r. refine (total2_paths _ _).
    * apply funextsec; intro g. apply assoc.
    * apply funextsec; intro g. apply funextsec; intro g'. apply funextsec; intro e. apply h.
Defined.

Definition type  {C:precategory} (h: has_homsets C) {Γ: graph} (D: diagram Γ C) :=
  Representation.Data (cocone_functor h D).



(* Definition Object {C:precategory} (hs: has_homsets C) {I} {c:I -> ob C} (r:type C hs c) *)
(*            : ob C := Representation.Object r. *)
(* Definition In {C:precategory} (hs: has_homsets C) {I} {b:I -> ob C} (B:type C hs b) i : *)
(*      Hom (b i) (Object hs B). *)
(* Proof. intros. exact (Representation.Element B i). Defined. *)
(* Module Coercions. *)
(*   Coercion Object : type >-> ob. *)
(* End Coercions. *)
