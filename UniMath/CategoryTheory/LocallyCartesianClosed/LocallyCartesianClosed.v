(*********************************************************************************************

 Locally cartesian closed categories

 In this file, we define locally cartesian closed categories. There are multiple equivalent
 definitions for locally cartesian closed categories:
 1. The first definition says that a category is locally cartesian closed categories if each
    of its slice category is cartesian closed.
 2. The second definition says that a category is locally cartesian closed if the pullback
    functor has a right adjoint.
 Note that for both definitions we need to assume that the involved category has pullbacks.
 We use the second definition.

 From the perspective of dependent type theory, we can interpret these definitions. Suppose
 that `C` is a finitely complete category. In `C`, we can thus interpret dependent type
 theory with `∑`-types, product types, unit types, and extensional identity types (using the
 codomain fibration). The first definition says that `C` has function types, whereas the
 second definition says that `C` has dependent products. Using this interpretation, we can
 also understand why these two variations are equivalent: dependent functions from `X` to a
 type family `Y` over `X` are the same as ordinary functions from `X` to `∑ (x : X), Y x` for
 which the composition with the first projection is the identity.

 We use the second variation of the definition in this file, because in dependent type theory,
 usually dependent products are used as the basic type former rather than function types.

 Contents
 1. Locally Cartesian closed categories
 2. Accessors for locally Cartesian closed categories
 3. Functoriality in locally Cartesian closed categories
 4. The slices of locally Cartesian closed categories are Cartesian closed
 5. Some properties of locally Cartesian closed categories

 *********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Examples.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodDomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.DisjointBinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Local Open Scope cat.

(** * 1. Locally Cartesian closed categories *)
Definition is_locally_cartesian_closed
           {C : category}
           (PB : Pullbacks C)
  : UU
  := ∏ (x y : C)
       (f : x --> y),
     is_left_adjoint (cod_pb PB f).

(** * 2. Accessors for locally Cartesian closed categories *)
(**
   Suppose that `C` is a locally Cartesian closed category.
   Exponentials in `C` are calculated with the following data:
   - an object `Γ : C`, which represents the context
   - an object `πA : C/Γ`, which represents a type `A` in context `Γ`
   - an object `πB : C/cod_dom πA`, which represents a type `B` in context `Γ , A`
   Note that `cod_dom πA` (i.e., the domain of `πA`) represents the extended context.
   The resulting ∏-type is an object in `C/Γ`, so a type in context `Γ`.
 *)
Definition lccc_exp_fib
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           (πA : C/Γ)
           (πB : C/cod_dom πA)
  : C/Γ
  := right_adjoint (HC _ _ (cod_mor πA)) πB.

Definition lccc_exp
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           (πA : C/Γ)
           (πB : C/cod_dom πA)
  : C
  := cod_dom (lccc_exp_fib HC πA πB).

(**
   We define evaluation in a categorical and a type theoretical style. In the categorical
   style ([lccc_exp_eval_fib]), we use the counit of the adjunction and we directly obtain
   the desired morphisms. The type theoretical style ([lccc_exp_eval]) is formulated using
   sections of morphisms, and it is closer to what one uses in type theory.
 *)
Definition lccc_exp_eval_fib
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           (πA : C/Γ)
           (πB : C/cod_dom πA)
  : cod_pb PB (cod_mor πA) (lccc_exp_fib HC πA πB) --> πB
  := counit_from_left_adjoint (HC _ _ (cod_mor πA)) πB.

Definition lccc_exp_eval_mor
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA : C/Γ}
           {πB : C/cod_dom πA}
           (f : section_of_mor (cod_mor (lccc_exp_fib HC πA πB)))
           (t : section_of_mor (cod_mor πA))
  : Γ --> cod_dom (cod_pb PB t πB).
Proof.
  use PullbackArrow.
  - refine (_ · dom_mor (lccc_exp_eval_fib HC _ _)).
    use PullbackArrow.
    + exact f.
    + exact t.
    + abstract
        (refine (section_of_mor_eq f @ _) ;
         exact (!(section_of_mor_eq t))).
  - exact (identity _).
  - abstract
      (rewrite id_left ;
       rewrite assoc' ;
       etrans ;
       [ apply maponpaths ;
         exact (mor_eq (lccc_exp_eval_fib HC πA πB))
       | ] ;
       apply PullbackArrow_PullbackPr2).
Defined.

(**
   Here we have
   - a context `Γ`
   - a type `A` in context `Γ` (i.e., a morphism `πA : A --> Γ`)
   - a type `B` in context `Γ , A` (i.e. an object `πB : B --> A`)
   In addition, we have a term `f` of type `∏ (a : A), B a` and a term `t` of type `A`.
 *)
Definition lccc_exp_eval
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA : C/Γ}
           {πB : C/cod_dom πA}
           (f : section_of_mor (cod_mor (lccc_exp_fib HC πA πB)))
           (t : section_of_mor (cod_mor πA))
  : section_of_mor (cod_mor (cod_pb PB t πB)).
Proof.
  use make_section_of_mor.
  - exact (lccc_exp_eval_mor HC f t).
  - abstract
      (apply PullbackArrow_PullbackPr2).
Defined.

(**
   We formulate λ-abstractions in two ways, namely in a categorical and in a type-theoretic
   way. The categorical way ([lccc_exp_lam_fib]) follows directly from the adjunction. The
   type theoretic way ([lccc_exp_lam]) is a reformulation using sections.

   Note that in the categorical style we have an additional substitution.
 *)
Definition lccc_exp_lam_fib
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA Δs : C/Γ}
           {πB : C/cod_dom πA}
           (t : cod_pb PB (cod_mor πA) Δs --> πB)
  : Δs --> lccc_exp_fib HC πA πB
  := φ_adj (pr2 (HC _ _ (cod_mor πA))) t.

Definition lccc_exp_lam_mor
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA : C/Γ}
           {πB : C/cod_dom πA}
           (t : section_of_mor (cod_mor πB))
  : cod_pb PB (cod_mor πA) (cod_fib_id Γ) --> πB.
Proof.
  use make_cod_fib_mor.
  - exact (PullbackPr2 _ · t).
  - abstract
      (rewrite !assoc' ;
       rewrite (section_of_mor_eq t) ;
       rewrite id_right ;
       apply idpath).
Defined.

(**
   Here we have:
   - a context `Γ`
   - a type `A` in context `Γ` (i.e., a morphism `πA : A --> Γ`)
   - a type `B` in context `Γ , A` (i.e. an object `πB : B --> A`)
   - a term `Γ , A ⊢ t : B` (i.e., a section of `πB`)
 *)
Definition lccc_exp_lam
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA : C/Γ}
           {πB : C/cod_dom πA}
           (t : section_of_mor (cod_mor πB))
  : section_of_mor (cod_mor (lccc_exp_fib HC πA πB)).
Proof.
  use make_section_of_mor.
  - refine (dom_mor (lccc_exp_lam_fib HC (πA := πA) (Δs := cod_fib_id _) (πB := πB) _)).
    exact (lccc_exp_lam_mor HC t).
  - abstract
      (exact (mor_eq (lccc_exp_lam_fib HC (lccc_exp_lam_mor HC t)))).
Defined.

(**
   The following is the β-rule for ∏-types.
 *)
Proposition lccc_exp_beta_fib
            {C : category}
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            {Γ : C}
            (f h : C/Γ)
            (g : C/cod_dom f)
            (k : cod_pb PB (cod_mor f) h --> g)
  : #(cod_pb PB (cod_mor f)) (lccc_exp_lam_fib HC k)
    · lccc_exp_eval_fib HC f g
    =
    k.
Proof.
  unfold lccc_exp_lam_fib.
  etrans.
  {
    apply maponpaths_2.
    apply functor_comp.
  }
  refine (assoc' _ _ _ @ _).
  etrans.
  {
    apply maponpaths.
    exact (nat_trans_ax (counit_from_left_adjoint (HC _ _ (cod_mor f))) _ _ _).
  }
  refine (assoc _ _ _ @ _).
  etrans.
  {
    apply maponpaths_2.
    exact (triangle_id_left_ad (pr2 (HC _ _ (cod_mor f))) h).
  }
  apply id_left.
Qed.

Definition lccc_exp_beta_subst_mor
           {C : category}
           (PB : Pullbacks C)
           {Γ : C}
           {πA : C/Γ}
           {πB : C/cod_dom πA}
           (f : section_of_mor (cod_mor πB))
           (t : section_of_mor (cod_mor πA))
  : Γ --> cod_dom (cod_pb PB t πB).
Proof.
  use PullbackArrow.
  - exact (t · f).
  - exact (identity _).
  - abstract
      (rewrite id_left ;
       rewrite !assoc' ;
       refine (_ @ id_right _) ;
       apply maponpaths ;
       exact (section_of_mor_eq f)).
Defined.

Definition lccc_exp_beta_subst
           {C : category}
           (PB : Pullbacks C)
           {Γ : C}
           {πA : C/Γ}
           {πB : C/cod_dom πA}
           (f : section_of_mor (cod_mor πB))
           (t : section_of_mor (cod_mor πA))
  : section_of_mor (cod_mor (cod_pb PB t πB)).
Proof.
  use make_section_of_mor.
  - exact (lccc_exp_beta_subst_mor PB f t).
  - abstract
      (apply PullbackArrow_PullbackPr2).
Defined.

Definition lccc_exp_beta_mor
           {C : category}
           (PB : Pullbacks C)
           {Γ : C}
           {πA : C/Γ}
           (t : section_of_mor (cod_mor πA))
  : Γ --> PB _ _ _ (identity Γ) (cod_mor πA).
Proof.
  use PullbackArrow.
  - exact (identity _).
  - exact t.
  - rewrite id_left.
    exact (!(section_of_mor_eq t)).
Defined.

Proposition lccc_exp_beta
            {C : category}
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            {Γ : C}
            {πA : C/Γ}
            {πB : C/cod_dom πA}
            (f : section_of_mor (cod_mor πB))
            (t : section_of_mor (cod_mor πA))
  : lccc_exp_eval HC (lccc_exp_lam HC f) t
    =
    lccc_exp_beta_subst PB f t.
Proof.
  pose (maponpaths
          dom_mor
          (lccc_exp_beta_fib HC πA (cod_fib_id Γ) πB (lccc_exp_lam_mor HC f)))
    as p.
  rewrite comp_in_cod_fib in p.
  cbn -[cod_pb lccc_exp_lam_fib] in p.
  use eq_section_of_mor.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - simpl ; unfold lccc_exp_eval_mor, lccc_exp_beta_subst_mor ; simpl.
    rewrite !PullbackArrow_PullbackPr1.
    refine (_ @ maponpaths (λ z, lccc_exp_beta_mor PB t · z) p @ _).
    + rewrite !assoc.
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      * rewrite PullbackArrow_PullbackPr1.
        refine (!_).
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (PB _ _ _ _ _)).
        }
        rewrite transportf_cod_disp.
        simpl.
        rewrite assoc.
        etrans.
        {
          apply maponpaths_2.
          apply PullbackArrow_PullbackPr1.
        }
        rewrite id_left.
        apply idpath.
      * rewrite PullbackArrow_PullbackPr2.
        refine (!_).
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (PB _ _ _ _ _)).
        }
        simpl.
        rewrite id_right.
        apply PullbackArrow_PullbackPr2.
    + unfold lccc_exp_beta_mor.
      rewrite assoc.
      rewrite PullbackArrow_PullbackPr2.
      apply idpath.
  - simpl ; unfold lccc_exp_eval_mor, lccc_exp_beta_subst_mor ; simpl.
    rewrite !PullbackArrow_PullbackPr2.
    apply idpath.
Qed.

(**
   The η-law for ∏-types
 *)
Proposition lccc_exp_eta_fib
            {C : category}
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            {Γ : C}
            (πA πA' : C/Γ)
            (πB : C/cod_dom πA)
            (k : πA' --> lccc_exp_fib HC πA πB)
  : k
    =
    lccc_exp_lam_fib
      HC
      (#(cod_pb PB (cod_mor πA)) k
       · lccc_exp_eval_fib HC πA πB).
Proof.
  refine (!_).
  etrans.
  {
    refine (maponpaths (λ z, _ · z) _).
    apply (functor_comp (right_adjoint (HC (cod_dom πA) Γ (cod_mor πA)))).
  }
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply (nat_trans_ax (unit_from_left_adjoint (HC (cod_dom πA) Γ (cod_mor πA)))).
  }
  refine (assoc' _ _ _ @ _).
  etrans.
  {
    apply maponpaths.
    apply (triangle_id_right_ad (pr2 (HC _ _ (cod_mor πA)))).
  }
  apply id_right.
Qed.

(** * 3. Functoriality in locally Cartesian closed categories *)

(**
   We show that the dependent product in a locally Cartesian closed category is
   functorial in both arguments (see [lccc_exp_functor_fib]). It is contravariant
   in its first argument and covariant in the second.
 *)
Definition lccc_exp_functor_base_fib_mor
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA πA' : C/Γ}
           (πB : C/cod_dom πA)
           (f : πA' --> πA)
  : cod_pb PB (cod_mor πA') (lccc_exp_fib HC πA πB)
    -->
    cod_pb PB (dom_mor f) πB.
Proof.
  use make_cod_fib_mor.
  - use PullbackArrow.
    + simple refine (cod_pb_left_functorial _ _ f · _).
      exact (dom_mor (lccc_exp_eval_fib HC πA πB)).
    + exact (PullbackPr2 _).
    + abstract
        (unfold cod_pb_left_functorial ;
         rewrite !assoc' ;
         etrans ;
         [ apply maponpaths ;
           exact (mor_eq (lccc_exp_eval_fib HC πA πB))
         | ] ;
         apply PullbackArrow_PullbackPr2).
  - abstract
      (apply PullbackArrow_PullbackPr2).
Defined.

Definition lccc_exp_functor_base_fib
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA πA' : C/Γ}
           {πB : C/cod_dom πA}
           (f : πA' --> πA)
  : lccc_exp_fib HC πA πB
    -->
    lccc_exp_fib HC πA' (cod_pb PB (dom_mor f) πB).
Proof.
  use lccc_exp_lam_fib.
  exact (lccc_exp_functor_base_fib_mor HC πB f).
Defined.

Definition lccc_exp_functor_fib
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA πA' : C/Γ}
           {πB : C/cod_dom πA}
           {πB' : C/cod_dom πA'}
           {f : πA' --> πA}
           (hg : cod_pb PB (dom_mor f) πB --> πB')
  : lccc_exp_fib HC πA πB --> lccc_exp_fib HC πA' πB'
  := lccc_exp_functor_base_fib HC f · #(right_adjoint (HC _ _ (cod_mor πA'))) hg.

Definition lccc_exp_functor
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {πA πA' : C/Γ}
           {πB : C/cod_dom πA}
           {πB' : C/cod_dom πA'}
           {hf : cod_dom πA' --> cod_dom πA}
           (p : cod_mor πA' = hf · cod_mor πA)
           (hg : cod_pb PB hf πB --> πB')
  : cod_dom (lccc_exp_fib HC πA πB) --> cod_dom (lccc_exp_fib HC πA' πB').
Proof.
  simple refine (dom_mor (lccc_exp_functor_fib HC _)).
  - use make_cod_fib_mor.
    + exact hf.
    + exact (!p).
  - exact hg.
Defined.

Definition lccc_exp_functor_eq_mor
           {C : category}
           {PB : Pullbacks C}
           {Γ : C}
           {f : C/Γ}
           {g : C/cod_dom f}
           {f' : C/Γ}
           {hf hf' : cod_dom f' --> cod_dom f}
           (q : hf = hf')
  : cod_dom (cod_pb PB hf g) --> cod_dom (cod_pb PB hf' g).
Proof.
  use PullbackArrow.
  - exact (PullbackPr1 _).
  - exact (PullbackPr2 _).
  - abstract
      (refine (PullbackSqrCommutes _ @ _) ;
       rewrite q ;
       apply idpath).
Defined.

Definition lccc_exp_functor_fib_eq
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {f : C/Γ}
           {g : C/cod_dom f}
           {f' : C/Γ}
           {g' : C/cod_dom f'}
           {hf hf' : f' --> f}
           (hg : cod_pb PB (dom_mor hf) g --> g')
           (hg' : cod_pb PB (dom_mor hf') g --> g')
           (q : hf = hf')
           (q' : dom_mor hg
                 =
                 lccc_exp_functor_eq_mor (maponpaths dom_mor q) · dom_mor hg')
  : lccc_exp_functor_fib HC hg = lccc_exp_functor_fib HC hg'.
Proof.
  induction q.
  enough (hg = hg') as ->.
  {
    apply idpath.
  }
  use eq_mor_cod_fib.
  refine (q' @ _ @ id_left _).
  apply maponpaths_2.
  unfold lccc_exp_functor_eq_mor.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - rewrite id_left.
    apply PullbackArrow_PullbackPr1.
  - rewrite id_left.
    apply PullbackArrow_PullbackPr2.
Qed.

Definition lccc_exp_functor_eq
           {C : category}
           {PB : Pullbacks C}
           (HC : is_locally_cartesian_closed PB)
           {Γ : C}
           {f : C/Γ}
           {g : C/cod_dom f}
           {f' : C/Γ}
           {g' : C/cod_dom f'}
           {hf hf' : cod_dom f' --> cod_dom f}
           (p : cod_mor f' = hf · cod_mor f)
           (p' : cod_mor f' = hf' · cod_mor f)
           (hg : cod_pb PB hf g --> g')
           (hg' : cod_pb PB hf' g --> g')
           (q : hf = hf')
           (q' : dom_mor hg = lccc_exp_functor_eq_mor q · dom_mor hg')
  : lccc_exp_functor HC p hg = lccc_exp_functor HC p' hg'.
Proof.
  unfold lccc_exp_functor.
  apply maponpaths.
  use lccc_exp_functor_fib_eq.
  - use eq_mor_cod_fib.
    exact q.
  - refine (q' @ _).
    apply maponpaths_2.
    apply maponpaths.
    apply homset_property.
Qed.

Proposition lccc_exp_functor_on_id_fib
            {C : category}
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            {Γ : C}
            {πA : C/Γ}
            {πB: C/cod_dom πA}
            {hf : πA --> πA}
            (phf : identity _ = hf)
            (hg : cod_pb PB (dom_mor hf) πB --> πB)
            (hgp : dom_mor hg = PullbackPr1 _)
  : lccc_exp_functor_fib HC hg = identity _.
Proof.
  refine (assoc' _ _ _ @ _).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    exact (functor_comp (right_adjoint (HC (cod_dom πA) Γ (cod_mor πA))) _ _).
  }
  assert (lccc_exp_functor_base_fib_mor HC πB hf · hg
          =
          lccc_exp_eval_fib HC πA πB)
    as r.
  {
    use eq_mor_cod_fib.
    refine (comp_in_cod_fib _ _ @ _).
    rewrite hgp.
    simpl.
    rewrite PullbackArrow_PullbackPr1.
    refine (_ @ id_left _).
    apply maponpaths_2.
    induction phf.
    apply cod_pb_left_functorial_id.
  }
  rewrite r.
  apply (triangle_id_right_ad (pr2 (HC _ _ (cod_mor πA)))).
Qed.

Proposition lccc_exp_functor_on_id
            {C : category}
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            {Γ : C}
            {πA : C/Γ}
            {πB : C/cod_dom πA}
            {hf : cod_dom πA --> cod_dom πA}
            (p : cod_mor πA = hf · cod_mor πA)
            (phf : identity _ = hf)
            (hg : cod_pb PB hf πB --> πB)
            (hgp : dom_mor hg = PullbackPr1 _)
  : lccc_exp_functor HC p hg = identity _.
Proof.
  simple refine (maponpaths dom_mor (lccc_exp_functor_on_id_fib HC _ _ _)).
  - use eq_mor_cod_fib.
    exact phf.
  - exact hgp.
Qed.

Definition cod_pb_comp_fib_mor_fib_mor
           {C : category}
           {PB : Pullbacks C}
           {Γ : C}
           {πA₁ πA₂ πA₃ : C/Γ}
           {πB : C/cod_dom πA₁}
           (f₁ : πA₂ --> πA₁)
           (f₂ : πA₃ --> πA₂)
  : cod_dom (cod_pb PB (dom_mor (f₂ · f₁)) πB)
    -->
    cod_dom (cod_pb PB (dom_mor f₁) πB).
Proof.
  use PullbackArrow.
  - exact (PullbackPr1 _).
  - exact (PullbackPr2 _ · dom_mor f₂).
  - abstract
      (refine (PullbackSqrCommutes _ @ _ @ assoc _ _ _) ;
       apply maponpaths ;
       apply comp_in_cod_fib).
Defined.

Definition cod_pb_comp_fib_mor_fib
           {C : category}
           {PB : Pullbacks C}
           {Γ : C}
           {πA₁ πA₂ πA₃ : C/Γ}
           {πB : C/cod_dom πA₁}
           (f₁ : πA₂ --> πA₁)
           (f₂ : πA₃ --> πA₂)
  : cod_pb PB (dom_mor (f₂ · f₁)) πB
    -->
    cod_pb PB (dom_mor f₂) (cod_pb PB (dom_mor f₁) πB).
Proof.
  use make_cod_fib_mor.
  - use PullbackArrow.
    + exact (cod_pb_comp_fib_mor_fib_mor f₁ f₂).
    + exact (PullbackPr2 _).
    + abstract
        (exact (PullbackArrow_PullbackPr2 _ _ _ _ _)).
  - abstract
      (exact (PullbackArrow_PullbackPr2 _ _ _ _ _)).
Defined.

Definition cod_pb_comp_fib_mor_mor_pb_mor
           {C : category}
           {PB : Pullbacks C}
           {Γ : C}
           {πA₁ πA₂ πA₃ : C/Γ}
           {πB : C/cod_dom πA₁}
           (f₁ : cod_dom πA₂ --> cod_dom πA₁)
           (f₂ : cod_dom πA₃ --> cod_dom πA₂)
  : cod_dom (cod_pb PB (f₂ · f₁) πB)
    -->
    cod_dom (cod_pb PB f₁ πB).
Proof.
  use PullbackArrow.
  - exact (PullbackPr1 _).
  - exact (PullbackPr2 _ · f₂).
  - abstract
      (refine (PullbackSqrCommutes _ @ _) ;
       rewrite assoc ;
       apply idpath).
Defined.

Definition cod_pb_comp_fib_mor_mor
           {C : category}
           {PB : Pullbacks C}
           {Γ : C}
           {πA₁ πA₂ πA₃ : C/Γ}
           {πB : C/cod_dom πA₁}
           (f₁ : cod_dom πA₂ --> cod_dom πA₁)
           (f₂ : cod_dom πA₃ --> cod_dom πA₂)
  : cod_dom (cod_pb PB (f₂ · f₁) πB)
    -->
    cod_dom (cod_pb PB f₂ (cod_pb PB f₁ πB)).
Proof.
  use PullbackArrow.
  - exact (cod_pb_comp_fib_mor_mor_pb_mor f₁ f₂).
  - apply PullbackPr2.
  - abstract
      (exact (PullbackArrow_PullbackPr2 _ _ _ _ _)).
Defined.

Definition cod_pb_comp_fib_mor
           {C : category}
           {PB : Pullbacks C}
           {Γ : C}
           {πA₁ πA₂ πA₃ : C/Γ}
           {πB : C/cod_dom πA₁}
           (f₁ : cod_dom πA₂ --> cod_dom πA₁)
           (f₂ : cod_dom πA₃ --> cod_dom πA₂)
  : cod_pb PB (f₂ · f₁) πB
    -->
    cod_pb PB f₂ (cod_pb PB f₁ πB).
Proof.
  use make_cod_fib_mor.
  - exact (cod_pb_comp_fib_mor_mor f₁ f₂).
  - abstract
      (exact (PullbackArrow_PullbackPr2 _ _ _ _ _)).
Defined.

Proposition lccc_exp_functor_base_fib_mor_natural
            {C : category}
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            {Γ : C}
            {πA₁ πA₂ πA₃ : C/Γ}
            (πB₁ : C/cod_dom πA₁)
            (f₁ : πA₂ --> πA₁)
            (f₂ : πA₃ --> πA₂)
  : dom_mor (lccc_exp_functor_base_fib_mor HC πB₁ (f₂ · f₁))
    · cod_pb_comp_fib_mor_fib_mor f₁ f₂
    =
    cod_pb_left_functorial PB _ f₂
    · dom_mor (lccc_exp_functor_base_fib_mor HC πB₁ f₁).
Proof.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr1.
    }
    etrans.
    {
      apply PullbackArrow_PullbackPr1.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr1.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite cod_pb_left_functorial_comp.
    apply idpath.
  - rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr2.
    }
    etrans.
    {
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply PullbackArrow_PullbackPr2.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr2.
    }
    apply PullbackArrow_PullbackPr2.
Qed.

Proposition lccc_exp_functor_on_comp_fib
            {C : category}
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            {Γ : C}
            {πA₁ πA₂ πA₃ : C/Γ}
            {πB₁ : C/cod_dom πA₁}
            {πB₂ : C/cod_dom πA₂}
            {πB₃ : C/cod_dom πA₃}
            {f₁ : πA₂ --> πA₁}
            {f₂ : πA₃ --> πA₂}
            (g₁ : cod_pb PB (dom_mor f₁) πB₁ --> πB₂)
            (g₂ : cod_pb PB (dom_mor f₂) πB₂ --> πB₃)
  : lccc_exp_functor_fib HC g₁
    · lccc_exp_functor_fib HC g₂
    =
    lccc_exp_functor_fib
      HC
      (cod_pb_comp_fib_mor_fib f₁ f₂ · #(cod_pb PB (dom_mor f₂)) g₁ · g₂).
Proof.
  unfold lccc_exp_functor_fib.
  rewrite functor_comp.
  rewrite !assoc.
  apply maponpaths_2.
  unfold lccc_exp_functor_base_fib, lccc_exp_lam_fib, φ_adj.
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    exact (nat_trans_ax
             (unit_from_left_adjoint (HC (cod_dom πA₃) Γ (cod_mor πA₃)))
             _ _
             (unit_from_left_adjoint
                (HC (cod_dom πA₂) Γ (cod_mor πA₂))
                (lccc_exp_fib HC πA₁ πB₁)
                 · #(right_adjoint (HC (cod_dom πA₂) Γ (cod_mor πA₂)))
                    (lccc_exp_functor_base_fib_mor HC πB₁ f₁)
                 · #(right_adjoint (HC (cod_dom πA₂) Γ (cod_mor πA₂))) g₁)).
  }
  rewrite !assoc'.
  apply maponpaths.
  refine (_ @ functor_comp (right_adjoint (HC (cod_dom πA₃) Γ (cod_mor πA₃))) _ _).
  refine (!(functor_comp (right_adjoint (HC (cod_dom πA₃) Γ (cod_mor πA₃))) _ _) @ _).
  apply maponpaths.
  use eq_mor_cod_fib.
  refine (comp_in_cod_fib _ _ @ _).
  refine (!_).
  refine (comp_in_cod_fib _ _ @ _).
  etrans.
  {
    apply maponpaths.
    refine (comp_in_cod_fib _ _ @ _).
    rewrite cod_fiber_functor_on_mor.
    apply idpath.
  }
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply PullbackArrow_PullbackPr1.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply PullbackArrow_PullbackPr1.
    }
    etrans.
    {
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply lccc_exp_functor_base_fib_mor_natural.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr1.
    }
    etrans.
    {
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!_).
      apply cod_pb_left_functorial_natural.
    }
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    unfold lccc_exp_eval_fib.
    rewrite !functor_comp.
    rewrite !comp_in_cod_fib.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!(comp_in_cod_fib _ _) @ _).
      apply maponpaths.
      apply (nat_trans_ax (counit_from_left_adjoint (HC (cod_dom πA₂) Γ (cod_mor πA₂)))).
    }
    rewrite comp_in_cod_fib.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!(comp_in_cod_fib _ _) @ _).
      apply maponpaths.
      apply (nat_trans_ax (counit_from_left_adjoint (HC (cod_dom πA₂) Γ (cod_mor πA₂)))).
    }
    rewrite comp_in_cod_fib.
    rewrite assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    etrans.
    {
      refine (!(comp_in_cod_fib _ _) @ _).
      apply maponpaths.
      apply triangle_id_left_ad.
    }
    apply idpath.
  - rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply PullbackArrow_PullbackPr2.
    }
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr2.
    }
    etrans.
    {
      apply PullbackArrow_PullbackPr2.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr2.
    }
    rewrite cod_fiber_functor_on_mor.
    apply PullbackArrow_PullbackPr2.
Qed.

Proposition lccc_exp_functor_on_comp_eq
            {C : category}
            {Γ : C}
            {πA₁ πA₂ πA₃ : C/Γ}
            {f₁ : cod_dom πA₂ --> cod_dom πA₁}
            {f₂ : cod_dom πA₃ --> cod_dom πA₂}
            (p₁ : cod_mor πA₂ = f₁ · cod_mor πA₁)
            (p₂ : cod_mor πA₃ = f₂ · cod_mor πA₂)
  : cod_mor πA₃ = f₂ · f₁ · cod_mor πA₁.
Proof.
  rewrite p₂.
  rewrite assoc'.
  rewrite p₁.
  apply idpath.
Qed.

Proposition lccc_exp_functor_on_comp
            {C : category}
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            {Γ : C}
            {πA₁ πA₂ πA₃ : C/Γ}
            {πB₁ : C/cod_dom πA₁}
            {πB₂ : C/cod_dom πA₂}
            {πB₃ : C/cod_dom πA₃}
            {f₁ : cod_dom πA₂ --> cod_dom πA₁}
            {f₂ : cod_dom πA₃ --> cod_dom πA₂}
            (g₁ : cod_pb PB f₁ πB₁ --> πB₂)
            (g₂ : cod_pb PB f₂ πB₂ --> πB₃)
            (p₁ : cod_mor πA₂ = f₁ · cod_mor πA₁)
            (p₂ : cod_mor πA₃ = f₂ · cod_mor πA₂)
  : lccc_exp_functor HC p₁ g₁
    · lccc_exp_functor HC p₂ g₂
    =
    lccc_exp_functor
      HC
      (lccc_exp_functor_on_comp_eq p₁ p₂)
      (cod_pb_comp_fib_mor f₁ f₂ · #(cod_pb PB f₂) g₁ · g₂).
Proof.
  unfold lccc_exp_functor.
  refine (!(comp_in_cod_fib _ _) @ _).
  etrans.
  {
    apply maponpaths.
    apply lccc_exp_functor_on_comp_fib.
  }
  apply maponpaths.
  use lccc_exp_functor_fib_eq.
  - abstract
      (use eq_mor_cod_fib ;
       rewrite !comp_in_cod_fib ;
       apply idpath).
  - refine (comp_in_cod_fib _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (comp_in_cod_fib _ _ @ _).
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !cod_fiber_functor_on_mor.
    apply maponpaths_2.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    + rewrite assoc'.
      etrans.
      {
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      refine (!_).
      etrans.
      {
        apply PullbackArrow_PullbackPr1.
      }
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      * etrans.
        {
          apply PullbackArrow_PullbackPr1.
        }
        refine (!_).
        rewrite assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackArrow_PullbackPr1.
        }
        apply PullbackArrow_PullbackPr1.
      * etrans.
        {
          apply PullbackArrow_PullbackPr2.
        }
        refine (!_).
        rewrite assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackArrow_PullbackPr2.
        }
        rewrite assoc.
        apply maponpaths_2.
        apply PullbackArrow_PullbackPr2.
    + rewrite assoc'.
      etrans.
      {
        apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      etrans.
      {
        apply PullbackArrow_PullbackPr2.
      }
      refine (!_).
      apply PullbackArrow_PullbackPr2.
Qed.

(** * 4. The slices of locally Cartesian closed categories are Cartesian closed *)
Definition locally_cartesian_closed_to_exponentials_nat_trans_data
           {C : category}
           (PB : Pullbacks C)
           {Γ : C}
           (BP := codomain_fib_binproducts PB Γ)
           (πA : C/Γ)
  : nat_trans_data
      (cod_pb PB (cod_mor πA) ∙ comp_functor (cod_mor πA))
      (constprod_functor1 BP πA).
Proof.
  intros πB.
  use make_cod_fib_mor.
  - apply (swap_pullback_z_iso (cod_mor πB) (cod_mor πA)).
  - abstract
      (cbn ;
       unfold swap_pullback_mor ;
       rewrite !assoc ;
       rewrite PullbackArrow_PullbackPr1 ;
       apply idpath).
Defined.

Definition slice_constprod_functor1_mor
           {C : category}
           (PB : Pullbacks C)
           {Γ : C}
           (BP := codomain_fib_binproducts PB Γ)
           (πA : C/Γ)
           {πB₁ πB₂ : C/Γ}
           (hp : πB₁ --> πB₂)
  : cod_dom (constprod_functor1 BP πA πB₁)
    -->
    cod_dom (constprod_functor1 BP πA πB₂).
Proof.
  use PullbackArrow.
  - apply PullbackPr1.
  - exact (PullbackPr2 _ · dom_mor hp).
  - abstract
      (cbn ;
       refine (PullbackSqrCommutes _ @ _) ;
       rewrite !assoc' ;
       rewrite (mor_eq hp) ;
       apply idpath).
Defined.

Proposition slice_constprod_functor1_mor_eq
            {C : category}
            (PB : Pullbacks C)
            {Γ : C}
            (BP := codomain_fib_binproducts PB Γ)
            (πA : C/Γ)
            {πB₁ πB₂ : C/Γ}
            (hp : πB₁ --> πB₂)
  : dom_mor (#(constprod_functor1 BP πA) hp)
    =
    slice_constprod_functor1_mor PB πA hp.
Proof.
  unfold slice_constprod_functor1_mor.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - rewrite PullbackArrow_PullbackPr1.
    etrans.
    {
      cbn -[fiber_category].
      apply (PullbackArrow_PullbackPr1 (make_Pullback _ (pr22 (PB _ _ _ _ _)))).
    }
    rewrite id_right.
    cbn.
    apply idpath.
  - rewrite PullbackArrow_PullbackPr2.
    etrans.
    {
      cbn -[fiber_category].
      apply (PullbackArrow_PullbackPr2 (make_Pullback _ (pr22 (PB _ _ _ _ _)))).
    }
    rewrite comp_in_cod_fib.
    cbn.
    apply idpath.
Qed.

Proposition locally_cartesian_closed_to_exponentials_nat_trans_laws
            {C : category}
            (PB : Pullbacks C)
            {Γ : C}
            (BP := codomain_fib_binproducts PB Γ)
            (πA : C/Γ)
  : is_nat_trans
      _ _
      (locally_cartesian_closed_to_exponentials_nat_trans_data PB πA).
Proof.
  intros πB₁ πB₂ hp.
  use eq_mor_cod_fib.
  rewrite !comp_in_cod_fib.
  etrans.
  {
    cbn -[cod_pb].
    apply maponpaths_2.
    apply maponpaths.
    apply cod_fiber_functor_on_mor.
  }
  rewrite slice_constprod_functor1_mor_eq.
  cbn ; unfold swap_pullback_mor, slice_constprod_functor1_mor.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - rewrite !assoc'.
    rewrite !PullbackArrow_PullbackPr1.
    rewrite PullbackArrow_PullbackPr2.
    apply idpath.
  - rewrite !assoc'.
    rewrite !PullbackArrow_PullbackPr2.
    rewrite PullbackArrow_PullbackPr1.
    rewrite assoc.
    rewrite PullbackArrow_PullbackPr2.
    apply idpath.
Qed.

Definition locally_cartesian_closed_to_exponentials_nat_trans
           {C : category}
           (PB : Pullbacks C)
           {Γ : C}
           (BP := codomain_fib_binproducts PB Γ)
           (πA : C/Γ)
  : cod_pb PB (cod_mor πA) ∙ comp_functor (cod_mor πA)
    ⟹
    constprod_functor1 BP πA.
Proof.
  use make_nat_trans.
  - exact (locally_cartesian_closed_to_exponentials_nat_trans_data PB πA).
  - apply locally_cartesian_closed_to_exponentials_nat_trans_laws.
Defined.

Definition locally_cartesian_closed_to_exponentials_nat_z_iso
           {C : category}
           (PB : Pullbacks C)
           {Γ : C}
           (BP := codomain_fib_binproducts PB Γ)
           (πA : C/Γ)
  : nat_z_iso
      (cod_pb PB (cod_mor πA) ∙ comp_functor (cod_mor πA))
      (constprod_functor1 BP πA).
Proof.
  use make_nat_z_iso.
  - apply locally_cartesian_closed_to_exponentials_nat_trans.
  - intro.
    use is_z_iso_fiber_from_is_z_iso_disp.
    use is_z_iso_disp_codomain.
    exact (z_iso_is_z_isomorphism (swap_pullback_z_iso _ _ _ _)).
Defined.

Definition locally_cartesian_closed_to_exponentials
           {C : category}
           (PB : Pullbacks C)
           (HC : is_locally_cartesian_closed PB)
           (Γ : C)
           (BP := codomain_fib_binproducts PB Γ)
  : Exponentials BP.
Proof.
  intros πA.
  use is_left_adjoint_nat_z_iso.
  - exact (cod_pb PB (cod_mor πA) ∙ comp_functor (cod_mor πA)).
  - use is_left_adjoint_functor_composite.
    + apply HC.
    + exact (is_left_adjoint_left_adjoint
               (is_right_adjoint_cod_fiber_functor PB (cod_mor πA))).
  - exact (locally_cartesian_closed_to_exponentials_nat_z_iso PB πA).
Defined.

(** * 5. Some properties of locally Cartesian closed categories *)
Proposition is_strict_initial_from_exponentials
            {C : category}
            {BP : BinProducts C}
            (exp : Exponentials BP)
            (I : Initial C)
  : is_strict_initial I.
Proof.
  intros w f.
  pose (I' := make_Initial _ (left_adjoint_preserves_initial _ (exp w) _ (pr2 I))).
  use make_is_z_isomorphism.
  - apply InitialArrow.
  - split.
    + rewrite <- (BinProductPr2Commutes _ _ _ (BP w I) _ (identity _) f).
      refine (_ @ BinProductPr1Commutes _ _ _ (BP w I) _ (identity _) f).
      rewrite !assoc'.
      apply maponpaths.
      apply (InitialArrowEq (O := I')).
    + apply InitialArrowEq.
Qed.

Proposition is_strict_initial_from_locally_cartesian_closed
            {C : category}
            (T : Terminal C)
            {PB : Pullbacks C}
            (HC : is_locally_cartesian_closed PB)
            (I : Initial C)
  : is_strict_initial I.
Proof.
  intros w f.
  refine (functor_on_is_z_isomorphism
            (cod_fib_terminal_to_base T)
            (is_strict_initial_from_exponentials
               (locally_cartesian_closed_to_exponentials PB HC T)
               (initial_cod_fib T I)
               (make_cod_fib_ob (TerminalArrow T w))
               (f ,, _))).
  apply TerminalArrowEq.
Qed.

Proposition is_locally_cartesian_closed_stable_bincoproducts
            {C : category}
            {PB : Pullbacks C}
            (BC : BinCoproducts C)
            (HC : is_locally_cartesian_closed PB)
  : stable_bincoproducts BC.
Proof.
  use stable_bincoproducts_from_pb_preserves_bincoproduct.
  - exact PB.
  - intros x y f.
    exact (left_adjoint_preserves_bincoproduct _ (HC x y f)).
Qed.
