(********************************************************************************************

 The tripos of predicates valued in a complete Heyting algebra

 Fix a complete Heyting algebra `H`. We define the following displayed category over `Set`:
 - Objects over a set `X` are functions `X → H`
 - Morphisms are induced by the partial order on `H`
 This displayed category has a lot of structure: it is a fibration, it is univalent, and one
 can interpret first-order logic on it. In fact, it is a tripos. In this file, we establish
 this fact.

 This tripos is used for independence proofs, or, more concretely forcing (this is why this
 tripos is called the forcing tripos in "Implicative algebras: a new foundation for realizability
 and forcing" by Alexandra Miquel). From every Heyting algebra we can construct a tripos, and
 by picking the Heyting algebra in a clever way, we can guarantee that some axioms are satisfied
 in the topos that arises from this tripos. These ideas are used in, for instance, "Intuitionistic
 Set Theory" by John Bell to construct a model of intuitionistic set theory where `ℕ → ℕ` is
 subcountable (which, in turn, is based on work by Andrej Bauer).

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts
 - "Implicative algebras: a new foundation for realizability and forcing" by Alexandra Miquel
 - "Intuitionistic Set Theory" by John Bell
 - "An injection from NN to N" by Andrej Bauer. Link:
 [https://math.andrej.com/2011/06/15/constructive-gem-an-injection-from-baire-space-to-natural-numbers/]

 Content
 1. The displayed category of H-valued predicates
 2. Properties of this displayed category
 3. The hyperdoctrine of H-valued predicates
 4. Logic of H-valued predicates
 4.1. Fiberwise terminal object
 4.2. Fiberwise initial object
 4.3. Fiberwise binary products
 4.4. Fiberwise binary coproducts
 4.5. Fiberwise exponentials
 4.6. Dependent products
 4.7. Dependent sums
 5. The first-order hyperdoctrine of H-valued predicates
 6. The tripos of H-valued predicates

 ********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.Tripos.

Local Open Scope cat.
Local Open Scope heyting.

Section HValuedSets.
  Context (H : complete_heyting_algebra).

  (** * 1. The displayed category of H-valued predicates *)
  Definition disp_cat_ob_mor_h_valued_sets
    : disp_cat_ob_mor SET.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (X : hSet), X → H).
    - exact (λ (X Y : hSet)
               (P : X → H)
               (Q : Y → H)
               (f : X → Y),
             ∏ (x : X), P x ≤ Q(f x)).
  Defined.

  Proposition disp_cat_id_comp_h_valued_sets
    : disp_cat_id_comp SET disp_cat_ob_mor_h_valued_sets.
  Proof.
    split.
    - intros X P x ; cbn in *.
      apply cha_le_refl.
    - intros X Y Z f g P Q R p q x ; cbn in *.
      refine (cha_le_trans (p x) _).
      apply q.
  Qed.

  Definition disp_cat_data_h_valued_sets
    : disp_cat_data SET.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_ob_mor_h_valued_sets.
    - exact disp_cat_id_comp_h_valued_sets.
  Defined.

  Proposition locally_propositional_h_valued_sets
    : locally_propositional
        disp_cat_data_h_valued_sets.
  Proof.
    intro ; intros.
    use impred ; intro.
    apply propproperty.
  Qed.

  Proposition disp_cat_axioms_h_valued_sets
    : disp_cat_axioms SET disp_cat_data_h_valued_sets.
  Proof.
    repeat split ; intros.
    - apply locally_propositional_h_valued_sets.
    - apply locally_propositional_h_valued_sets.
    - apply locally_propositional_h_valued_sets.
    - apply isasetaprop.
      apply locally_propositional_h_valued_sets.
  Qed.

  Definition disp_cat_h_valued_sets
    : disp_cat SET.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_data_h_valued_sets.
    - exact disp_cat_axioms_h_valued_sets.
  Defined.

  (** * 2. Properties of this displayed category *)
  Proposition is_univalent_disp_h_valued_sets
    : is_univalent_disp disp_cat_h_valued_sets.
  Proof.
    use is_univalent_disp_from_fibers.
    intros X P Q.
    use isweqimplimpl.
    - cbn in *.
      intro p.
      use funextsec ; intro x.
      use cha_le_antisymm.
      + exact (pr1 p x).
      + exact (pr12 p x).
    - use funspace_isaset.
      apply setproperty.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply locally_propositional_h_valued_sets.
  Qed.

  Definition cleaving_h_valued_sets
    : cleaving disp_cat_h_valued_sets.
  Proof.
    intros Y X f Q.
    simple refine ((λ x, Q(f x)) ,, _ ,, _).
    - abstract
        (intro ;
         apply cha_le_refl).
    - intros W g R p.
      use iscontraprop1.
      + abstract
          (use isaproptotal2 ; [ | intros ; apply locally_propositional_h_valued_sets ] ;
           intro ;
           apply disp_cat_h_valued_sets).
      + abstract
          (refine (p ,, _) ;
           apply locally_propositional_h_valued_sets).
  Defined.

  (** * 3. The hyperdoctrine of H-valued predicates *)
  Definition h_valued_sets_hyperdoctrine
    : hyperdoctrine.
  Proof.
    use make_hyperdoctrine.
    - exact SET.
    - exact disp_cat_h_valued_sets.
    - exact TerminalHSET.
    - exact BinProductsHSET.
    - exact cleaving_h_valued_sets.
    - exact locally_propositional_h_valued_sets.
    - exact is_univalent_disp_h_valued_sets.
  Defined.

  (** * 4. Logic of H-valued predicates *)

  (** * 4.1. Fiberwise terminal object *)
  Definition fiberwise_terminal_h_valued_sets
    : fiberwise_terminal cleaving_h_valued_sets.
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - exact locally_propositional_h_valued_sets.
    - exact (λ (X : hSet) (x : X), ⊤).
    - abstract
        (cbn ;
         intros X P x ;
         apply cha_le_top).
    - abstract
        (cbn ;
         intros X Y f ;
         apply idpath).
  Defined.

  (** * 4.2. Fiberwise initial object *)
  Definition fiberwise_initial_h_valued_sets
    : fiberwise_initial cleaving_h_valued_sets.
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - exact locally_propositional_h_valued_sets.
    - exact (λ (X : hSet) (x : X), ⊥).
    - abstract
        (cbn ;
         intros X P x ;
         apply cha_bot_le).
    - abstract
        (cbn ;
         intros X Y f ;
         apply idpath).
  Defined.

  (** * 4.3. Fiberwise binary products *)
  Definition fiberwise_binproducts_h_valued_sets
    : fiberwise_binproducts cleaving_h_valued_sets.
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - exact locally_propositional_h_valued_sets.
    - exact (λ (X : hSet) (P Q : X → H) (x : X), P x ∧ Q x).
    - abstract
        (intros X P Q x ; apply cha_min_le_l).
    - abstract
        (intros X P Q x ; apply cha_min_le_r).
    - abstract
        (intros X P Q R p q x ;
         exact (cha_min_le_case (p x) (q x))).
    - abstract
        (intros X Y f P Q ;
         apply idpath).
  Defined.

  (** * 4.4. Fiberwise binary coproducts *)
  Definition fiberwise_bincoproducts_h_valued_sets
    : fiberwise_bincoproducts cleaving_h_valued_sets.
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - exact locally_propositional_h_valued_sets.
    - exact (λ (X : hSet) (P Q : X → H) (x : X), P x ∨ Q x).
    - abstract
        (intros X P Q x ; apply cha_max_le_l).
    - abstract
        (intros X P Q x ; apply cha_max_le_r).
    - abstract
        (intros X P Q R p q x ;
         exact (cha_max_le_case (p x) (q x))).
    - abstract
        (intros X Y f P Q ;
         apply idpath).
  Defined.

  (** * 4.5. Fiberwise exponentials *)
  Definition fiberwise_exponentials_h_valued_sets
    : fiberwise_exponentials fiberwise_binproducts_h_valued_sets.
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - exact locally_propositional_h_valued_sets.
    - exact (λ (X : hSet) (P Q : X → H) (x : X), P x ⇒ Q x).
    - abstract
        (intros X P Q x ; cbn ;
         rewrite cha_min_comm ;
         apply cha_exp_eval).
    - abstract
        (intros X P Q R p x ; cbn in * ;
         use cha_to_le_exp ;
         rewrite cha_min_comm ;
         exact (p x)).
    - abstract
        (intros X Y f P Q ; cbn ;
         apply idpath).
  Defined.

  (** * 4.6. Dependent products *)
  Definition has_dependent_products_h_valued_sets
    : has_dependent_products cleaving_h_valued_sets.
  Proof.
    use make_has_dependent_products_poset.
    - exact locally_propositional_h_valued_sets.
    - exact (λ (X Y : hSet)
               (f : X → Y)
               (P : X → H)
               (y : Y),
             /\_{ z : ∑ (x : X), f x = y } P (pr1 z)).
    - abstract
        (intros X Y f P x ; cbn in * ;
         use cha_glb_le ; [ exact (x ,, idpath _) | ] ;
         cbn ;
         apply cha_le_refl).
    - abstract
        (intros X Y f P Q p y ; cbn in * ;
         use cha_le_glb ;
         intros z ;
         induction z as [ x q ] ;
         induction q ; cbn ;
         apply p).
    - abstract
        (intros Y₂ Y₁ X₂ X₁ f₁ f₂ g₁ g₂ p Hp P y ; cbn in * ;
         use cha_le_glb ;
         intros z ;
         induction z as [ z zp ] ;
         use cha_glb_le ;
         [ exact (el_pullback_set Hp z y zp ,, el_pullback_set_pr2 Hp z y zp)
         | ] ;
         cbn ;
         rewrite el_pullback_set_pr1 ;
         apply cha_le_refl).
  Defined.

  (** * 4.7. Dependent sums *)
  Definition has_dependent_sums_h_valued_sets
    : has_dependent_sums cleaving_h_valued_sets.
  Proof.
    use make_has_dependent_sums_poset.
    - exact locally_propositional_h_valued_sets.
    - exact (λ (X Y : hSet)
               (f : X → Y)
               (P : X → H)
               (y : Y),
             \/_{ z : ∑ (x : X), f x = y } P (pr1 z)).
    - abstract
        (intros X Y f P x ; cbn in * ;
         use cha_le_lub  ; [ exact (x ,, idpath _) | ] ;
         cbn ;
         apply cha_le_refl).
    - abstract
        (intros X Y f P Q p y ; cbn in * ;
         use cha_lub_le ;
         intros z ;
         induction z as [ x q ] ;
         induction q ; cbn ;
         apply p).
    - abstract
        (intros Y₂ Y₁ X₂ X₁ f₁ f₂ g₁ g₂ p Hp P y ; cbn in * ;
         use cha_lub_le ;
         intros z ;
         induction z as [ z zp ] ;
         use cha_le_lub ;
         [ exact (el_pullback_set Hp z y zp ,, el_pullback_set_pr2 Hp z y zp)
         | ] ;
         cbn ;
         rewrite el_pullback_set_pr1 ;
         apply cha_le_refl).
  Defined.

  (** * 5. The first-order hyperdoctrine of H-valued predicates *)
  Definition h_valued_sets_first_order_hyperdoctrine
    : first_order_hyperdoctrine.
  Proof.
    use make_first_order_hyperdoctrine.
    - exact h_valued_sets_hyperdoctrine.
    - exact fiberwise_terminal_h_valued_sets.
    - exact fiberwise_initial_h_valued_sets.
    - exact fiberwise_binproducts_h_valued_sets.
    - exact fiberwise_bincoproducts_h_valued_sets.
    - exact fiberwise_exponentials_h_valued_sets.
    - exact has_dependent_products_h_valued_sets.
    - exact has_dependent_sums_h_valued_sets.
  Defined.

  (** * 6. The tripos of H-valued predicates *)
  Local Open Scope hd.

  Section TriposOfHValuedSets.
    Context (X : hSet).

    Definition power_h_valued_set
      : hSet
      := funset X H.

    Definition in_power_h_valued_set
      : X × power_h_valued_set → H
      := λ xf, pr2 xf (pr1 xf).
  End TriposOfHValuedSets.

  Definition is_tripos_h_valued_sets
    : is_tripos h_valued_sets_first_order_hyperdoctrine.
  Proof.
    intro X ; cbn in * ; unfold prodtofuntoprod ; cbn.
    refine (power_h_valued_set X ,, in_power_h_valued_set X ,, _).
    intros Γ R tt.
    induction tt.
    use cha_le_glb.
    intros z.
    induction z as [ z pz ].
    induction z as [ tt γ ].
    cbn in pz.
    induction pz.
    induction tt.
    cbn.
    use cha_le_lub.
    - simple refine (((tt ,, γ) ,, _) ,, idpath _).
      exact (λ (x : X), R (x ,, γ)).
    - cbn.
      use cha_le_glb.
      intros z.
      induction z as [ [ [ [ tt γ' ] P ] x ] q ].
      cbn in *.
      induction tt.
      assert ((λ x : X, R (x,, γ)) = P) as p.
      {
        exact (maponpaths dirprod_pr2 (!q)).
      }
      induction p.
      assert (γ = γ') as p.
      {
        exact (maponpaths (λ z, dirprod_pr2 (dirprod_pr1 z)) (!q)).
      }
      induction p.
      use cha_min_le_case.
      + use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        apply cha_le_refl.
      + use cha_to_le_exp.
        rewrite cha_lunit_min_top.
        apply cha_le_refl.
  Qed.

  Definition tripos_h_valued_sets
    : tripos.
  Proof.
    use make_tripos.
    - exact h_valued_sets_first_order_hyperdoctrine.
    - exact is_tripos_h_valued_sets.
  Defined.
End HValuedSets.
