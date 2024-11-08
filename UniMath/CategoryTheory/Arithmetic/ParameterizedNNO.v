(**********************************************************************************************

 Parameterized natural number objects

 In a category with a terminal object, we can define the notion of a natural numbers object.
 Such an object satisfies a universal mapping property that represents the recursion principle
 of the natural numbers, and thus this object plays the role of the natural umbers in the
 internal language of that category.

 However, if our category is not Cartesian closed, then it is better to use a slightly stronger
 notion, namely that of a parameterized natural numbers object. The definition of a parameterized
 natural numbers object is quite similar to that of an ordinary natural numbers object: the only
 difference is that we require a slightly stronger recursion principle where one can use an arbitrary
 object of parameters (see, for instance, Definition 2.1 in "Joyal's arithmetic universe as
 list-arithmetic pretopos" by Maietti). There are various kinds of categories that are not Cartesian
 closed but which support such a parameterized natural numbers object, namely list-arithmetic
 pretoposes and arithmetical universes. Note that to formulate the notion of a parameterized
 natural numbers object we use binary products.

 References
 - "Joyal's arithmetic universe as list-arithmetic pretopos" by Maietti

 Content
 1. Parameterized NNOs
 2. Accessors
 3. Every parameterized NNO is an NNO
 4. Uniqueness of parameterized NNOs
 5. Preservation of parameterized NNOs
 6. Examples of functors that preserve parameterized NNOs
 7. Independence of the choice of binary products

 **********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.

Local Open Scope cat.

Section ParameterizedNNO.
  Context {C : category}
          {T : Terminal C}
          {BC : BinProducts C}.

  (** * 1. Parameterized NNOs *)
  Definition is_parameterized_NNO
             (N : C)
             (z : T --> N)
             (s : N --> N)
    : UU
    := ∏ (b y : C)
         (zy : b --> y)
         (sy : y --> y),
       ∃! (f : BC b N --> y),
       (BinProductArrow _ _ (identity _) (TerminalArrow _ _ · z) · f = zy)
       ×
       (BinProductOfArrows _ _ _ (identity _) s · f = f · sy).

  Proposition isaprop_is_parameterized_NNO
              (N : C)
              (z : T --> N)
              (s : N --> N)
    : isaprop (is_parameterized_NNO N z s).
  Proof.
    do 4 (use impred ; intro).
    apply isapropiscontr.
  Qed.

  Definition parameterized_NNO
    : UU
    := ∑ (N : C)
         (z : T --> N)
         (s : N --> N),
       is_parameterized_NNO N z s.

  (** * 2. Accessors *)
  Coercion parameterized_NNO_carrier
           (N : parameterized_NNO)
    : C
    := pr1 N.

  Section Accessors.
    Context (N : parameterized_NNO).

    Definition parameterized_NNO_Z
      : T --> N
      := pr12 N.

    Definition parameterized_NNO_S
      : N --> N
      := pr122 N.

    Let H : is_parameterized_NNO N parameterized_NNO_Z parameterized_NNO_S
      := pr222 N.

    Definition parameterized_NNO_mor
               (b y : C)
               (zy : b --> y)
               (sy : y --> y)
      : BC b N --> y
      := pr11 (H b y zy sy).

    Proposition parameterized_NNO_mor_Z
                (b y : C)
                (zy : b --> y)
                (sy : y --> y)
      : BinProductArrow _ _ (identity _) (TerminalArrow _ _ · parameterized_NNO_Z)
        · parameterized_NNO_mor b y zy sy
        =
        zy.
    Proof.
      exact (pr121 (H b y zy sy)).
    Qed.

    Proposition parameterized_NNO_mor_S
                (b y : C)
                (zy : b --> y)
                (sy : y --> y)
      : BinProductOfArrows _ _ _ (identity _) parameterized_NNO_S
        · parameterized_NNO_mor b y zy sy
        =
        parameterized_NNO_mor b y zy sy · sy.
    Proof.
      exact (pr221 (H b y zy sy)).
    Qed.

    Proposition parameterized_NNO_mor_unique
                {b y : C}
                {zy : b --> y}
                {sy : y --> y}
                (g g' : BC b N --> y)
                (gz : BinProductArrow
                        _ _
                        (identity _)
                        (TerminalArrow T b · parameterized_NNO_Z)
                      · g
                      =
                      zy)
                (gs : BinProductOfArrows
                        _ _ _
                        (identity b)
                        parameterized_NNO_S
                      · g
                      =
                      g · sy)
                (gz' : BinProductArrow
                         _ _
                         (identity _)
                         (TerminalArrow T b · parameterized_NNO_Z)
                       · g'
                       =
                       zy)
                (gs' : BinProductOfArrows
                         _ _ _
                         (identity b)
                         parameterized_NNO_S
                       · g'
                       =
                       g' · sy)
      : g = g'.
    Proof.
      refine (maponpaths
                (λ z, pr1 z)
                (proofirrelevance
                   _
                   (isapropifcontr (H b y zy sy))
                   (g ,, _ ,, _) (g' ,, _ ,, _))).
      - exact gz.
      - exact gs.
      - exact gz'.
      - exact gs'.
    Qed.
  End Accessors.

  (**
     These are specialized accessors to show that every parameterized NNO is an NNO
   *)
  Section NNOAccessors.
    Context (N : parameterized_NNO)
            (y : C)
            (zy : T --> y)
            (sy : y --> y).

    Definition is_NNO_parameterized_NNO_mor
      : N --> y
      := BinProductArrow _ _ (TerminalArrow _ _) (identity _)
         · parameterized_NNO_mor N T y zy sy.

    Proposition is_NNO_parameterized_NNO_mor_Z
      : parameterized_NNO_Z N · is_NNO_parameterized_NNO_mor = zy.
    Proof.
      unfold is_NNO_parameterized_NNO_mor ; cbn.
      refine (_ @ parameterized_NNO_mor_Z N T y zy sy).
      rewrite !assoc.
      apply maponpaths_2.
      rewrite precompWithBinProductArrow.
      rewrite (TerminalEndo_is_identity (TerminalArrow T T)).
      rewrite id_left, id_right.
      apply maponpaths_2.
      apply TerminalArrowEq.
    Qed.

    Proposition is_NNO_parameterized_NNO_mor_S
      : parameterized_NNO_S N · is_NNO_parameterized_NNO_mor
        =
        is_NNO_parameterized_NNO_mor · sy.
    Proof.
      unfold is_NNO_parameterized_NNO_mor.
      rewrite !assoc'.
      rewrite <- parameterized_NNO_mor_S.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite precompWithBinProductArrow.
      rewrite postcompWithBinProductArrow.
      rewrite id_left, !id_right.
      apply maponpaths_2.
      apply TerminalArrowEq.
    Qed.

    Proposition is_NNO_parameterized_NNO_unique
                {g₁ g₂ : N --> y}
                (zg₁ : parameterized_NNO_Z N · g₁ = zy)
                (sg₁ : parameterized_NNO_S N · g₁ = g₁ · sy)
                (zg₂ : parameterized_NNO_Z N · g₂ = zy)
                (sg₂ : parameterized_NNO_S N · g₂ = g₂ · sy)
      : g₁ = g₂.
    Proof.
      assert (BinProductPr2 _ (BC T N) · g₁
              =
              BinProductPr2 _ (BC T N) · g₂)
        as p.
      {
        use parameterized_NNO_mor_unique.
        - exact zy.
        - exact sy.
        - rewrite !assoc.
          rewrite BinProductPr2Commutes.
          refine (_ @ zg₁).
          rewrite (TerminalEndo_is_identity (TerminalArrow T T)).
          rewrite id_left.
          apply idpath.
        - rewrite !assoc.
          rewrite BinProductOfArrowsPr2.
          rewrite !assoc'.
          apply maponpaths.
          exact sg₁.
        - rewrite !assoc.
          rewrite BinProductPr2Commutes.
          refine (_ @ zg₂).
          rewrite (TerminalEndo_is_identity (TerminalArrow T T)).
          rewrite id_left.
          apply idpath.
        - rewrite !assoc.
          rewrite BinProductOfArrowsPr2.
          rewrite !assoc'.
          apply maponpaths.
          exact sg₂.
      }
      pose proof (maponpaths
                    (λ z, BinProductArrow _ _ (TerminalArrow _ _) (identity _) · z)
                    p)
        as q.
      cbn in q.
      refine (_ @ q @ _).
      - rewrite !assoc.
        rewrite BinProductPr2Commutes.
        rewrite id_left.
        apply idpath.
      - rewrite !assoc.
        rewrite BinProductPr2Commutes.
        rewrite id_left.
        apply idpath.
    Qed.
  End NNOAccessors.

  Definition make_parameterized_NNO
             (N : C)
             (z : T --> N)
             (s : N --> N)
             (H : is_parameterized_NNO N z s)
    : parameterized_NNO
    := N ,, z ,, s ,, H.

  (** * 3. Every parameterized NNO is an NNO *)
  Section ParameterizedNNOToNNO.
    Context (N : parameterized_NNO).

    Proposition is_NNO_parameterized_NNO_isaprop
                (y : C)
                (zy : T --> y)
                (sy : y --> y)
      : isaprop
          (∑ (u : N --> y),
           (parameterized_NNO_Z N · u = zy)
           ×
           (parameterized_NNO_S N · u = u · sy)).
    Proof.
      use invproofirrelevance.
      intros g₁ g₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use is_NNO_parameterized_NNO_unique.
      - exact zy.
      - exact sy.
      - exact (pr12 g₁).
      - exact (pr22 g₁).
      - exact (pr12 g₂).
      - exact (pr22 g₂).
    Qed.

    Definition is_NNO_parameterized_NNO
      : isNNO T N (parameterized_NNO_Z N) (parameterized_NNO_S N).
    Proof.
      intros y zy sy.
      use iscontraprop1.
      - exact (is_NNO_parameterized_NNO_isaprop y zy sy).
      - simple refine (_ ,, _ ,, _).
        + exact (is_NNO_parameterized_NNO_mor N y zy sy).
        + exact (is_NNO_parameterized_NNO_mor_Z N y zy sy).
        + exact (is_NNO_parameterized_NNO_mor_S N y zy sy).
    Defined.
  End ParameterizedNNOToNNO.

  (** * 4. Uniqueness of parameterized NNOs *)
  Definition mor_between_parameterized_NNO
             (N₁ N₂ : parameterized_NNO)
    : N₁ --> N₂.
  Proof.
    use is_NNO_parameterized_NNO_mor.
    - exact (parameterized_NNO_Z N₂).
    - exact (parameterized_NNO_S N₂).
  Defined.

  Proposition mor_between_parameterized_NNO_Z
              (N₁ N₂ : parameterized_NNO)
    : parameterized_NNO_Z N₁ · mor_between_parameterized_NNO N₁ N₂
      =
      parameterized_NNO_Z N₂.
  Proof.
    apply is_NNO_parameterized_NNO_mor_Z.
  Qed.

  Proposition mor_between_parameterized_NNO_S
              (N₁ N₂ : parameterized_NNO)
    : parameterized_NNO_S N₁ · mor_between_parameterized_NNO N₁ N₂
      =
      mor_between_parameterized_NNO N₁ N₂ · parameterized_NNO_S N₂.
  Proof.
    apply is_NNO_parameterized_NNO_mor_S.
  Qed.

  Proposition mor_between_parameterized_NNO_eq
              (N₁ N₂ : parameterized_NNO)
    : mor_between_parameterized_NNO N₁ N₂ · mor_between_parameterized_NNO N₂ N₁
      =
      identity _.
  Proof.
    use is_NNO_parameterized_NNO_unique.
    - exact (parameterized_NNO_Z N₁).
    - exact (parameterized_NNO_S N₁).
    - rewrite !assoc.
      rewrite !mor_between_parameterized_NNO_Z.
      apply idpath.
    - rewrite !assoc.
      rewrite mor_between_parameterized_NNO_S.
      rewrite !assoc'.
      rewrite mor_between_parameterized_NNO_S.
      apply idpath.
    - apply id_right.
    - rewrite id_left, id_right.
      apply idpath.
  Qed.

  Proposition parameterized_NNO_eq
              {N₁ N₂ : parameterized_NNO}
              (p : (N₁ : C) = N₂)
              (pz : parameterized_NNO_Z N₁ · idtoiso p
                    =
                    parameterized_NNO_Z N₂)
              (ps : parameterized_NNO_S N₁ · idtoiso p
                    =
                    idtoiso p · parameterized_NNO_S N₂)
    : N₁ = N₂.
  Proof.
    induction N₁ as [ N₁ [ z₁ [ s₁ H₁ ] ] ].
    induction N₂ as [ N₂ [ z₂ [ s₂ H₂ ] ] ].
    cbn in *.
    induction p ; cbn in *.
    rewrite id_right in pz.
    rewrite id_left, id_right in ps.
    induction pz, ps.
    do 3 apply maponpaths.
    apply isaprop_is_parameterized_NNO.
  Qed.

  Proposition parameterized_NNO_from_iso
              (HC : is_univalent C)
              {N₁ N₂ : parameterized_NNO}
              (f : z_iso N₁ N₂)
              (pz : parameterized_NNO_Z N₁ · f
                    =
                    parameterized_NNO_Z N₂)
              (ps : parameterized_NNO_S N₁ · f
                    =
                    f · parameterized_NNO_S N₂)
    : N₁ = N₂.
  Proof.
    use parameterized_NNO_eq.
    - exact (isotoid _ HC f).
    - rewrite idtoiso_isotoid.
      exact pz.
    - rewrite !idtoiso_isotoid.
      exact ps.
  Qed.

  Proposition isaprop_parameterized_NNO_if_univalent
              (HC : is_univalent C)
    : isaprop parameterized_NNO.
  Proof.
    use invproofirrelevance.
    intros N₁ N₂.
    use (parameterized_NNO_from_iso HC).
    - use make_z_iso.
      + exact (mor_between_parameterized_NNO N₁ N₂).
      + exact (mor_between_parameterized_NNO N₂ N₁).
      + split ; apply mor_between_parameterized_NNO_eq.
    - apply mor_between_parameterized_NNO_Z.
    - apply mor_between_parameterized_NNO_S.
  Qed.
End ParameterizedNNO.

Arguments is_parameterized_NNO {C} T BC.
Arguments parameterized_NNO {C} T BC.

Proposition isaprop_parameterized_NNO
            (C : univalent_category)
            (T : Terminal C)
            (BC : BinProducts C)
  : isaprop (parameterized_NNO T BC).
Proof.
  use isaprop_parameterized_NNO_if_univalent.
  apply univalent_category_is_univalent.
Qed.

(** * 5. Preservation of parameterized NNOs *)
Section PreservationNNO.
  Context {C₁ C₂ : category}
          {T₁ : Terminal C₁}
          {BC₁ : BinProducts C₁}
          {T₂ : Terminal C₂}
          {BC₂ : BinProducts C₂}
          (N₁ : parameterized_NNO T₁ BC₁)
          (N₂ : parameterized_NNO T₂ BC₂)
          (F : C₁ ⟶ C₂)
          (HF : preserves_terminal F).

  Definition preserves_parameterized_NNO_mor
    : N₂ --> F N₁.
  Proof.
    use is_NNO_parameterized_NNO_mor.
    - exact (TerminalArrow (preserves_terminal_to_terminal F HF T₁) _
             · #F (parameterized_NNO_Z N₁)).
    - exact (#F (parameterized_NNO_S N₁)).
  Defined.

  Proposition preserves_parameterized_NNO_mor_Z
    : parameterized_NNO_Z N₂ · preserves_parameterized_NNO_mor
      =
      TerminalArrow (preserves_terminal_to_terminal F HF T₁) _
      · #F (parameterized_NNO_Z N₁).
  Proof.
    apply is_NNO_parameterized_NNO_mor_Z.
  Qed.

  Proposition preserves_parameterized_NNO_mor_S
    : parameterized_NNO_S N₂ · preserves_parameterized_NNO_mor
      =
      preserves_parameterized_NNO_mor · #F (parameterized_NNO_S N₁).
  Proof.
    apply is_NNO_parameterized_NNO_mor_S.
  Qed.

  Definition preserves_parameterized_NNO
    : UU
    := is_z_isomorphism preserves_parameterized_NNO_mor.

  Proposition isaprop_preserves_parameterized_NNO
    : isaprop preserves_parameterized_NNO.
  Proof.
    apply isaprop_is_z_isomorphism.
  Qed.
End PreservationNNO.

(** * 6. Examples of functors that preserve parameterized NNOs *)
Proposition id_preserves_parameterized_NNO_eq
            {C : category}
            (T : Terminal C)
            (BC : BinProducts C)
            (N : parameterized_NNO T BC)
  : identity N
    =
    preserves_parameterized_NNO_mor N N _ (identity_preserves_terminal C).
Proof.
  use is_NNO_parameterized_NNO_unique.
  - exact (parameterized_NNO_Z N).
  - exact (parameterized_NNO_S N).
  - apply id_right.
  - rewrite id_left, id_right.
    apply idpath.
  - etrans.
    {
      exact (preserves_parameterized_NNO_mor_Z N N _ (identity_preserves_terminal C)).
    }
    cbn.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (functor_on_terminal_arrow _ (identity_preserves_terminal _)).
    }
    cbn.
    etrans.
    {
      apply maponpaths_2.
      exact (TerminalEndo_is_identity (TerminalArrow T T)).
    }
    apply id_left.
  - exact (preserves_parameterized_NNO_mor_S N N _ (identity_preserves_terminal C)).
Qed.

Proposition id_preserves_parameterized_NNO
            {C : category}
            (T : Terminal C)
            (BC : BinProducts C)
            (N : parameterized_NNO T BC)
  : preserves_parameterized_NNO
      N N
      (functor_identity C)
      (identity_preserves_terminal _).
Proof.
  use is_z_isomorphism_path.
  - apply identity.
  - apply id_preserves_parameterized_NNO_eq.
  - apply is_z_isomorphism_identity.
Defined.

Section Composition.
  Context {C₁ C₂ C₃ : category}
          {T₁ : Terminal C₁}
          {BC₁ : BinProducts C₁}
          {N₁ : parameterized_NNO T₁ BC₁}
          {T₂ : Terminal C₂}
          {BC₂ : BinProducts C₂}
          {N₂ : parameterized_NNO T₂ BC₂}
          {T₃ : Terminal C₃}
          {BC₃ : BinProducts C₃}
          {N₃ : parameterized_NNO T₃ BC₃}
          {F : C₁ ⟶ C₂}
          {HF : preserves_terminal F}
          (HFN : preserves_parameterized_NNO N₁ N₂ F HF)
          {G : C₂ ⟶ C₃}
          {HG : preserves_terminal G}
          (HGN : preserves_parameterized_NNO N₂ N₃ G HG).

  Proposition comp_preserves_parameterized_NNO_eq
    : preserves_parameterized_NNO_mor N₂ N₃ G HG
      · # G (preserves_parameterized_NNO_mor N₁ N₂ F HF)
      =
      preserves_parameterized_NNO_mor N₁ N₃ (F ∙ G) (composition_preserves_terminal HF HG).
  Proof.
    use is_NNO_parameterized_NNO_unique.
    - exact (TerminalArrow
               (preserves_terminal_to_terminal
                  _
                  (composition_preserves_terminal HF HG)
                  T₁)
               _
             · #G(#F(parameterized_NNO_Z N₁))).
    - exact (#G(#F(parameterized_NNO_S N₁))).
    - rewrite !assoc.
      rewrite preserves_parameterized_NNO_mor_Z.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (!(functor_comp G _ _)).
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply preserves_parameterized_NNO_mor_Z.
      }
      rewrite functor_comp.
      rewrite !assoc.
      apply maponpaths_2.
      apply (TerminalArrowEq (T := preserves_terminal_to_terminal _ _ _)).
    - rewrite !assoc.
      rewrite preserves_parameterized_NNO_mor_S.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (!(functor_comp G _ _)).
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply preserves_parameterized_NNO_mor_S.
      }
      rewrite functor_comp.
      apply idpath.
    - exact (preserves_parameterized_NNO_mor_Z
               N₁ N₃
               _
               (composition_preserves_terminal HF HG)).
    - exact (preserves_parameterized_NNO_mor_S
               N₁ N₃
               _
               (composition_preserves_terminal HF HG)).
  Qed.

  Proposition comp_preserves_parameterized_NNO
    : preserves_parameterized_NNO
        N₁ N₃
        (F ∙ G)
        (composition_preserves_terminal HF HG).
  Proof.
    use is_z_isomorphism_path.
    - exact (preserves_parameterized_NNO_mor N₂ N₃ G HG
             · #G (preserves_parameterized_NNO_mor N₁ N₂ F HF)).
    - exact comp_preserves_parameterized_NNO_eq.
    - use is_z_isomorphism_comp.
      + exact HGN.
      + use functor_on_is_z_isomorphism.
        exact HFN.
  Defined.
End Composition.

(** * 7. Independence of the choice of binary products *)
Proposition is_parameterized_NNO_prod_independent
            {C : univalent_category}
            {T : Terminal C}
            {BC₁ : BinProducts C}
            (BC₂ : BinProducts C)
            (N : parameterized_NNO T BC₁)
  : is_parameterized_NNO T BC₂ N (parameterized_NNO_Z N) (parameterized_NNO_S N).
Proof.
  refine (transportf (λ z, is_parameterized_NNO _ z _ _ _) _ (pr222 N)).
  use funextsec ; intro x.
  use funextsec ; intro y.
  apply isaprop_BinProduct.
  apply univalent_category_is_univalent.
Qed.

Definition parameterized_NNO_prod_independent
           {C : univalent_category}
           {T : Terminal C}
           {BC₁ : BinProducts C}
           (BC₂ : BinProducts C)
           (N : parameterized_NNO T BC₁)
  : parameterized_NNO T BC₂.
Proof.
  use make_parameterized_NNO.
  - exact N.
  - exact (parameterized_NNO_Z N).
  - exact (parameterized_NNO_S N).
  - apply is_parameterized_NNO_prod_independent.
Defined.

Definition preserves_parameterized_NNO_prod_independent
           {C₁ C₂ : univalent_category}
           {T₁ : Terminal C₁}
           {BC₁ BC₁' : BinProducts C₁}
           {T₂ : Terminal C₂}
           {BC₂ BC₂' : BinProducts C₂}
           {N₁ : parameterized_NNO T₁ BC₁}
           {N₂ : parameterized_NNO T₂ BC₂}
           {F : C₁ ⟶ C₂}
           {HF : preserves_terminal F}
           (HFN : preserves_parameterized_NNO N₁ N₂ F HF)
  : preserves_parameterized_NNO
      (parameterized_NNO_prod_independent BC₁' N₁)
      (parameterized_NNO_prod_independent BC₂' N₂)
      F HF.
Proof.
  refine (is_z_isomorphism_path _ HFN).
  assert (BC₂ = BC₂') as p.
  {
    use funextsec ; intro x.
    use funextsec ; intro y.
    apply isaprop_BinProduct.
    apply univalent_category_is_univalent.
  }
  induction p.
  use is_NNO_parameterized_NNO_unique.
  - exact (TerminalArrow (preserves_terminal_to_terminal F HF T₁) T₂
           · # F (parameterized_NNO_Z N₁)).
  - exact (#F (parameterized_NNO_S N₁)).
  - rewrite preserves_parameterized_NNO_mor_Z.
    apply idpath.
  - rewrite preserves_parameterized_NNO_mor_S.
    apply idpath.
  - etrans.
    {
      apply (preserves_parameterized_NNO_mor_Z
               (parameterized_NNO_prod_independent BC₁' N₁)
               (parameterized_NNO_prod_independent BC₂ N₂)).
    }
    apply idpath.
  - etrans.
    {
      apply (preserves_parameterized_NNO_mor_S
               (parameterized_NNO_prod_independent BC₁' N₁)
               (parameterized_NNO_prod_independent BC₂ N₂)).
    }
    apply idpath.
Qed.
