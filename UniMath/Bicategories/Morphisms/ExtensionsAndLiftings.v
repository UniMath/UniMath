(****************************************************************************

 Extensions and liftings in bicategories

 A fundamental notion in category theory is that of a Kan extension. These
 come in various flavors, among which are global Kan extensions and absolute
 Kan extensions. In this file, we define various notions of Kan extensions
 internal to arbitrary bicategories.

 One nice aspect of this approach is that there is one unifying definition
 for all variations. By instantiating the notion of left Kan extensions to
 various bicategories, we can recover other variations of extensions. This
 is summarized in the following table:

 Notion of Kan extension/lifting  | Corresponding bicategory
 -----------------------------------------------------------
 Left Kan extension               | B
 Left lifting                     | B^op
 Right Kan extension              | B^co
 Right lifting                    | B^coop

 Concretely, left Kan extensions in `B^op` are the same as left liftings in
 `B`, and the same for the other rows.

 We also define when 1-cells preserve left Kan extensions, and using that,
 we define the notion of absolute Kan extensions.

 An overview of these definitions can be found in:
   Yoneda structures from 2-toposes by Mark Weber

 Contents:
 1. Left extensions
 2. Left liftings
 3. Left liftings as left extensions in the opposite bicategory
 4. Right extensions
 5. Right extension as left extensions
 6. Right liftings
 7. Right liftings as left extensions

 ****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.

Local Open Scope cat.

(**
 1. Left extensions
 *)
Section LeftExtension.
  Context {B : bicat}
          {x y z : B}
          (f : x --> z)
          (g : x --> y).

  Definition is_left_extension
             {h : y --> z}
             (τ : f ==> g · h)
    : UU
    := ∏ (k : y --> z), isweq (λ (θ : h ==> k), τ • (g ◃ θ)).

  Section Projections.
    Context {h : y --> z}
            {τ : f ==> g · h}
            (Hτ : is_left_extension τ).

    Definition is_left_extension_extend
               {k : y --> z}
               (θ : f ==> g · k)
      : h ==> k
      := invmap (make_weq _ (Hτ k)) θ.

    Proposition is_left_extension_extend_left
                {k : y --> z}
                (θ : h ==> k)
      : is_left_extension_extend (τ • (g ◃ θ)) = θ.
    Proof.
      exact (homotinvweqweq (make_weq _ (Hτ k)) θ).
    Qed.

    Proposition is_left_extension_extend_right
                {k : y --> z}
                (θ : f ==> g · k)
      : τ • (g ◃ is_left_extension_extend θ) = θ.
    Proof.
      exact (homotweqinvweq (make_weq _ (Hτ k)) θ).
    Qed.
  End Projections.

  Proposition make_is_left_extension
              {h : y --> z}
              (τ : f ==> g · h)
              (F : ∏ (k : y --> z) (θ : f ==> g · k), h ==> k)
              (HF₁ : ∏ (k : y --> z) (θ : h ==> k), F k (τ • (g ◃ θ)) = θ)
              (HF₂ : ∏ (k : y --> z) (θ : f ==> g · k), τ • (g ◃ F k θ) = θ)
    : is_left_extension τ.
  Proof.
    intros k.
    use isweq_iso.
    - exact (F k).
    - exact (HF₁ k).
    - exact (HF₂ k).
  Defined.

  Proposition isaprop_is_left_extension
              {h : y --> z}
              (τ : f ==> g · h)
    : isaprop (is_left_extension τ).
  Proof.
    use impred ; intro.
    apply isapropisweq.
  Qed.

  Definition left_extension
    : UU
    := ∑ (h : y --> z)
         (τ : f ==> g · h),
       is_left_extension τ.

  Coercion mor_of_left_extension
           (h : left_extension)
    : y --> z
    := pr1 h.

  Definition cell_of_left_extension
             (h : left_extension)
    : f ==> g · h
    := pr12 h.

  Coercion left_extension_is_left_extension
           (h : left_extension)
    : is_left_extension (cell_of_left_extension h)
    := pr22 h.
End LeftExtension.

Definition preserves_is_left_extension
           {B : bicat}
           {x y z a : B}
           {f : x --> z}
           {g : x --> y}
           (k : z --> a)
           {h : y --> z}
           {τ : f ==> g · h}
           (Hτ : is_left_extension f g τ)
  : UU
  := is_left_extension (f · k) g ((τ ▹ k) • rassociator _ _ _).

Proposition isaprop_preserves_is_left_extension
            {B : bicat}
            {x y z a : B}
            {f : x --> z}
            {g : x --> y}
            (k : z --> a)
            {h : y --> z}
            {τ : f ==> g · h}
            (Hτ : is_left_extension f g τ)
  : isaprop (preserves_is_left_extension k Hτ).
Proof.
  apply isaprop_is_left_extension.
Qed.

Definition is_absolute_left_extension
           {B : bicat}
           {x y z : B}
           {f : x --> z}
           {g : x --> y}
           {h : y --> z}
           {τ : f ==> g · h}
           (Hτ : is_left_extension f g τ)
  : UU
  := ∏ (a : B)
       (k : z --> a),
     preserves_is_left_extension k Hτ.

Proposition isaprop_is_absolute_left_extension
            {B : bicat}
            {x y z : B}
            {f : x --> z}
            {g : x --> y}
            {h : y --> z}
            {τ : f ==> g · h}
            (Hτ : is_left_extension f g τ)
  : isaprop (is_absolute_left_extension Hτ).
Proof.
  do 2 (use impred ; intro).
  apply isaprop_preserves_is_left_extension.
Qed.

(**
 2. Left liftings
 *)
Section LeftLifting.
  Context {B : bicat}
          {x y z : B}
          (f : z --> x)
          (g : y --> x).

  Definition is_left_lifting
             {h : z --> y}
             (τ : f ==> h · g)
    : UU
    := ∏ (k : z --> y), isweq (λ (θ : h ==> k), τ • (θ ▹ g)).

  Section Projections.
    Context {h : z --> y}
            {τ : f ==> h · g}
            (Hτ : is_left_lifting τ).

    Definition is_left_lifting_lift
               {k : z --> y}
               (θ : f ==> k · g)
      : h ==> k
      := invmap (make_weq _ (Hτ k)) θ.

    Proposition is_left_lifting_lift_left
                {k : z --> y}
                (θ : h ==> k)
      : is_left_lifting_lift (τ • (θ ▹ g)) = θ.
    Proof.
      exact (homotinvweqweq (make_weq _ (Hτ k)) θ).
    Qed.

    Proposition is_left_lifting_lift_right
                {k : z --> y}
                (θ : f ==> k · g)
      : τ • (is_left_lifting_lift θ ▹ g) = θ.
    Proof.
      exact (homotweqinvweq (make_weq _ (Hτ k)) θ).
    Qed.
  End Projections.

  Proposition make_is_left_lifting
              {h : z --> y}
              (τ : f ==> h · g)
              (F : ∏ (k : z --> y) (θ : f ==> k · g), h ==> k)
              (HF₁ : ∏ (k : z --> y) (θ : h ==> k), F k (τ • (θ ▹ g)) = θ)
              (HF₂ : ∏ (k : z --> y) (θ : f ==> k · g), τ • (F k θ ▹ g) = θ)
    : is_left_lifting τ.
  Proof.
    intros k.
    use isweq_iso.
    - exact (F k).
    - exact (HF₁ k).
    - exact (HF₂ k).
  Defined.

  Proposition isaprop_is_left_lifting
              {h : z --> y}
              (τ : f ==> h · g)
    : isaprop (is_left_lifting τ).
  Proof.
    use impred ; intro.
    apply isapropisweq.
  Qed.

  Definition left_lifting
    : UU
    := ∑ (h : z --> y)
         (τ : f ==> h · g),
       is_left_lifting τ.

  Coercion mor_of_left_lifting
           (h : left_lifting)
    : z --> y
    := pr1 h.

  Definition cell_of_left_lifting
             (h : left_lifting)
    : f ==> h · g
    := pr12 h.

  Coercion left_lifting_is_left_lifting
           (h : left_lifting)
    : is_left_lifting (cell_of_left_lifting h)
    := pr22 h.
End LeftLifting.

Definition preserves_is_left_lifting
           {B : bicat}
           {x y z a : B}
           {f : z --> x}
           {g : y --> x}
           (k : a --> z)
           {h : z --> y}
           {τ : f ==> h · g}
           (Hτ : is_left_lifting f g τ)
  : UU
  := is_left_lifting (k · f) g ((k ◃ τ) • lassociator _ _ _).

Proposition isaprop_preserves_is_left_lifting
            {B : bicat}
            {x y z a : B}
            {f : z --> x}
            {g : y --> x}
            (k : a --> z)
            {h : z --> y}
            {τ : f ==> h · g}
            (Hτ : is_left_lifting f g τ)
  : isaprop (preserves_is_left_lifting k Hτ).
Proof.
  apply isaprop_is_left_lifting.
Qed.

Definition is_absolute_left_lifting
           {B : bicat}
           {x y z : B}
           {f : z --> x}
           {g : y --> x}
           {h : z --> y}
           {τ : f ==> h · g}
           (Hτ : is_left_lifting f g τ)
  : UU
  := ∏ (a : B)
       (k : a --> z),
     preserves_is_left_lifting k Hτ.

Proposition isaprop_is_absolute_left_lifting
            {B : bicat}
            {x y z : B}
            {f : z --> x}
            {g : y --> x}
            {h : z --> y}
            {τ : f ==> h · g}
            (Hτ : is_left_lifting f g τ)
  : isaprop (is_absolute_left_lifting Hτ).
Proof.
  do 2 (use impred ; intro).
  apply isaprop_preserves_is_left_lifting.
Qed.

(**
 3. Left liftings as left extensions in the opposite bicategory
 *)
Definition is_left_extension_weq_is_left_lifting_op
           {B : bicat}
           {x y z : B}
           (f : z --> x)
           (g : y --> x)
           {h : z --> y}
           (τ : f ==> h · g)
  : is_left_lifting _ _ τ
    ≃
    @is_left_extension (op1_bicat B) x y z f g h τ.
Proof.
  exact (idweq _).
Defined.

Definition preserves_is_left_extension_weq_preserves_is_left_lifting_op
           {B : bicat}
           {x y z a : B}
           {f : z --> x}
           {g : y --> x}
           (k : a --> z)
           {h : z --> y}
           {τ : f ==> h · g}
           (Hτ : is_left_lifting f g τ)
  : preserves_is_left_lifting k Hτ
    ≃
    @preserves_is_left_extension (op1_bicat B) _ _ _ _ _ _ k _ _ Hτ.
Proof.
  exact (idweq _).
Defined.

Definition is_absolute_left_extension_weq_is_absolute_left_lifting_op
           {B : bicat}
           {x y z : B}
           {f : z --> x}
           {g : y --> x}
           {h : z --> y}
           {τ : f ==> h · g}
           (Hτ : is_left_lifting f g τ)
  : is_absolute_left_lifting Hτ
    ≃
    @is_absolute_left_extension (op1_bicat B) _ _ _ _ _ _ _ Hτ.
Proof.
  exact (idweq _).
Defined.

(**
 4. Right extensions
 *)
Section RightExtension.
  Context {B : bicat}
          {x y z : B}
          (f : x --> z)
          (g : x --> y).

  Definition is_right_extension
             {h : y --> z}
             (τ : g · h ==> f)
    : UU
    := ∏ (k : y --> z), isweq (λ (θ : k ==> h), (g ◃ θ) • τ).

  Section Projections.
    Context {h : y --> z}
            {τ : g · h ==> f}
            (Hτ : is_right_extension τ).

    Definition is_right_extension_extend
               {k : y --> z}
               (θ : g · k ==> f)
      : k ==> h
      := invmap (make_weq _ (Hτ k)) θ.

    Proposition is_right_extension_extend_left
                {k : y --> z}
                (θ : k ==> h)
      : is_right_extension_extend ((g ◃ θ) • τ) = θ.
    Proof.
      exact (homotinvweqweq (make_weq _ (Hτ k)) θ).
    Qed.

    Proposition is_right_extension_extend_right
                {k : y --> z}
                (θ : g · k ==> f)
      : (g ◃ is_right_extension_extend θ) • τ = θ.
    Proof.
      exact (homotweqinvweq (make_weq _ (Hτ k)) θ).
    Qed.
  End Projections.

  Proposition make_is_right_extension
              {h : y --> z}
              (τ : g · h ==> f)
              (F : ∏ (k : y --> z) (θ : g · k ==> f), k ==> h)
              (HF₁ : ∏ (k : y --> z) (θ : k ==> h), F k ((g ◃ θ) • τ) = θ)
              (HF₂ : ∏ (k : y --> z) (θ : g · k ==> f), (g ◃ F k θ) • τ = θ)
    : is_right_extension τ.
  Proof.
    intros k.
    use isweq_iso.
    - exact (F k).
    - exact (HF₁ k).
    - exact (HF₂ k).
  Defined.

  Proposition isaprop_is_right_extension
              {h : y --> z}
              (τ : g · h ==> f)
    : isaprop (is_right_extension τ).
  Proof.
    use impred ; intro.
    apply isapropisweq.
  Qed.

  Definition right_extension
    : UU
    := ∑ (h : y --> z)
         (τ : g · h ==> f),
       is_right_extension τ.

  Coercion mor_of_right_extension
           (h : right_extension)
    : y --> z
    := pr1 h.

  Definition cell_of_right_extension
             (h : right_extension)
    : g · h ==> f
    := pr12 h.

  Coercion right_extension_is_right_extension
           (h : right_extension)
    : is_right_extension (cell_of_right_extension h)
    := pr22 h.
End RightExtension.

Definition preserves_is_right_extension
           {B : bicat}
           {x y z a : B}
           {f : x --> z}
           {g : x --> y}
           (k : z --> a)
           {h : y --> z}
           {τ : g · h ==> f}
           (Hτ : is_right_extension f g τ)
  : UU
  := is_right_extension (f · k) g (lassociator _ _ _ • (τ ▹ k)).

Proposition isaprop_preserves_is_right_extension
            {B : bicat}
            {x y z a : B}
            {f : x --> z}
            {g : x --> y}
            (k : z --> a)
            {h : y --> z}
            {τ : g · h ==> f}
            (Hτ : is_right_extension f g τ)
  : isaprop (preserves_is_right_extension k Hτ).
Proof.
  apply isaprop_is_right_extension.
Qed.

Definition is_absolute_right_extension
           {B : bicat}
           {x y z : B}
           {f : x --> z}
           {g : x --> y}
           {h : y --> z}
           {τ : g · h ==> f}
           (Hτ : is_right_extension f g τ)
  : UU
  := ∏ (a : B)
       (k : z --> a),
     preserves_is_right_extension k Hτ.

Proposition isaprop_is_absolute_right_extension
            {B : bicat}
            {x y z : B}
            {f : x --> z}
            {g : x --> y}
            {h : y --> z}
            {τ : g · h ==> f}
            (Hτ : is_right_extension f g τ)
  : isaprop (is_absolute_right_extension Hτ).
Proof.
  do 2 (use impred ; intro).
  apply isaprop_preserves_is_right_extension.
Qed.

(**
 5. Right extension as left extensions
 *)
Definition is_left_extension_weq_is_right_extension_co
           {B : bicat}
           {x y z : B}
           (f : x --> z)
           (g : x --> y)
           {h : y --> z}
           (τ : g · h ==> f)
  : is_right_extension f g τ
    ≃
    @is_left_extension (op2_bicat B) x y z f g h τ.
Proof.
  exact (idweq _).
Defined.

Definition preserves_is_left_extension_weq_preserves_is_right_extension_co
           {B : bicat}
           {x y z a : B}
           {f : x --> z}
           {g : x --> y}
           (k : z --> a)
           {h : y --> z}
           {τ : g · h ==> f}
           (Hτ : is_right_extension f g τ)
  : preserves_is_right_extension k Hτ
    ≃
    @preserves_is_left_extension (op2_bicat B) _ _ _ _ _ _ k _ _ Hτ.
Proof.
  exact (idweq _).
Defined.

Definition is_absolute_left_extension_weq_is_absolute_right_extension_op
           {B : bicat}
           {x y z : B}
           {f : x --> z}
           {g : x --> y}
           {h : y --> z}
           {τ : g · h ==> f}
           (Hτ : is_right_extension f g τ)
  : is_absolute_right_extension Hτ
    ≃
    @is_absolute_left_extension (op2_bicat B) _ _ _ _ _ _ _ Hτ.
Proof.
  exact (idweq _).
Defined.

(**
 6. Right liftings
 *)
Section RightLifting.
  Context {B : bicat}
          {x y z : B}
          (f : z --> x)
          (g : y --> x).

  Definition is_right_lifting
             {h : z --> y}
             (τ : h · g ==> f)
    : UU
    := ∏ (k : z --> y), isweq (λ (θ : k ==> h), (θ ▹ g) • τ).

  Section Projections.
    Context {h : z --> y}
            {τ : h · g ==> f}
            (Hτ : is_right_lifting τ).

    Definition is_right_lifting_lift
               {k : z --> y}
               (θ : k · g ==> f)
      : k ==> h
      := invmap (make_weq _ (Hτ k)) θ.

    Proposition is_right_lifting_lift_left
                {k : z --> y}
                (θ : k ==> h)
      : is_right_lifting_lift ((θ ▹ g) • τ) = θ.
    Proof.
      exact (homotinvweqweq (make_weq _ (Hτ k)) θ).
    Qed.

    Proposition is_right_lifting_lift_right
                {k : z --> y}
                (θ : k · g ==> f)
      : (is_right_lifting_lift θ ▹ g) • τ = θ.
    Proof.
      exact (homotweqinvweq (make_weq _ (Hτ k)) θ).
    Qed.
  End Projections.

  Proposition make_is_right_lifting
              {h : z --> y}
              (τ : h · g ==> f)
              (F : ∏ (k : z --> y) (θ : k · g ==> f), k ==> h)
              (HF₁ : ∏ (k : z --> y) (θ : k ==> h), F k ((θ ▹ g) • τ) = θ)
              (HF₂ : ∏ (k : z --> y) (θ : k · g ==> f), (F k θ ▹ g) • τ = θ)
    : is_right_lifting τ.
  Proof.
    intros k.
    use isweq_iso.
    - exact (F k).
    - exact (HF₁ k).
    - exact (HF₂ k).
  Defined.

  Proposition isaprop_is_right_lifting
              {h : z --> y}
              (τ : h · g ==> f)
    : isaprop (is_right_lifting τ).
  Proof.
    use impred ; intro.
    apply isapropisweq.
  Qed.

  Definition right_lifting
    : UU
    := ∑ (h : z --> y)
         (τ : h · g ==> f),
       is_right_lifting τ.

  Coercion mor_of_right_lifting
           (h : right_lifting)
    : z --> y
    := pr1 h.

  Definition cell_of_right_lifting
             (h : right_lifting)
    : h · g ==> f
    := pr12 h.

  Coercion right_lifting_is_left_lifting
           (h : right_lifting)
    : is_right_lifting (cell_of_right_lifting h)
    := pr22 h.
End RightLifting.

Definition preserves_is_right_lifting
           {B : bicat}
           {x y z a : B}
           {f : z --> x}
           {g : y --> x}
           (k : a --> z)
           {h : z --> y}
           {τ : h · g ==> f}
           (Hτ : is_right_lifting f g τ)
  : UU
  := is_right_lifting (k · f) g (rassociator _ _ _ • (k ◃ τ)).

Proposition isaprop_preserves_is_right_lifting
            {B : bicat}
            {x y z a : B}
            {f : z --> x}
            {g : y --> x}
            (k : a --> z)
            {h : z --> y}
            {τ : h · g ==> f}
            (Hτ : is_right_lifting f g τ)
  : isaprop (preserves_is_right_lifting k Hτ).
Proof.
  apply isaprop_is_right_lifting.
Qed.

Definition is_absolute_right_lifting
           {B : bicat}
           {x y z : B}
           {f : z --> x}
           {g : y --> x}
           {h : z --> y}
           {τ : h · g ==> f}
           (Hτ : is_right_lifting f g τ)
  : UU
  := ∏ (a : B)
       (k : a --> z),
     preserves_is_right_lifting k Hτ.

Proposition isaprop_is_absolute_right_lifting
            {B : bicat}
            {x y z : B}
            {f : z --> x}
            {g : y --> x}
            {h : z --> y}
            {τ : h · g ==> f}
            (Hτ : is_right_lifting f g τ)
  : isaprop (is_absolute_right_lifting Hτ).
Proof.
  do 2 (use impred ; intro).
  apply isaprop_preserves_is_right_lifting.
Qed.

(**
 7. Right liftings as left extensions
 *)
Definition is_left_extension_weq_is_right_lifting_coop
           {B : bicat}
           {x y z : B}
           (f : z --> x)
           (g : y --> x)
           {h : z --> y}
           (τ : h · g ==> f)
  : is_right_lifting f g τ
    ≃
    @is_left_extension (op2_bicat (op1_bicat B)) x y z f g h τ.
Proof.
  exact (idweq _).
Defined.

Definition preserves_is_left_extension_weq_preserves_is_right_lifting_coop
           {B : bicat}
           {x y z a : B}
           {f : z --> x}
           {g : y --> x}
           (k : a --> z)
           {h : z --> y}
           {τ : h · g ==> f}
           (Hτ : is_right_lifting f g τ)
  : preserves_is_right_lifting k Hτ
    ≃
    @preserves_is_left_extension (op2_bicat (op1_bicat B)) _ _ _ _ _ _ k _ _ Hτ.
Proof.
  exact (idweq _).
Defined.

Definition is_absolute_left_extension_weq_is_absolute_right_lifting_coop
           {B : bicat}
           {x y z : B}
           {f : z --> x}
           {g : y --> x}
           {h : z --> y}
           {τ : h · g ==> f}
           (Hτ : is_right_lifting f g τ)
  : is_absolute_right_lifting Hτ
    ≃
    @is_absolute_left_extension (op2_bicat (op1_bicat B)) _ _ _ _ _ _ _ Hτ.
Proof.
  exact (idweq _).
Defined.
