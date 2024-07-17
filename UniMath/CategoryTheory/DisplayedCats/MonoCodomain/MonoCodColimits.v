(***************************************************************************************

 Colimits in the slice category of monomorphisms

 Let `C` be a category with a strict initial object. Then we can construct an initial
 object in the slice category of monomorphisms. The construction is the same as the
 construction of initial objects in the slice category.

 The construction of fiberwise coproducts is more interesting. Usually, one is interested
 in the notion of a coherent category in this context. A coherent category is a regular
 category such that subobjects have finite unions. However, while usually one defines
 the subobjects of an object `y` as a quotient of the set of monomorphisms into `y`, one
 does not need to take a quotient if one uses univalent categories. As such, rather than
 defining a notion of coherent category, we give a construct of fiberwise coproducts in
 the slice of monomorphisms if our category satisfies suitable assumptions. These
 assumptions are regularity (so that we have suitable epi-mono factorizations), that
 binary coproducts exists, and that binary coproducts are stable under pullback.

 It is not too difficult to show that fiberwise coproducts exists. To construct the union
 of two monomorphisms, we take the disjoint union of their domain and then we factorize
 the map from the disjoint union as an epimorphism followed by a monomorphism. The main
 difficulty lies in showing that this construction is stable under pullback. Here we use
 that binary coproducts are stable under substitution and that regular epimorphisms are
 stable under substitution.

 Contents
 1. Initial object in the slice of monomorphisms
 2. Binary coproducts in the slice of monomorphisms

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.DisjointBinCoproducts.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.Inclusion.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.

Local Open Scope cat.

(** * 1. Initial object in the slice of monomorphisms *)
Definition to_initial_slice_mono
           {C : category}
           {y : C}
           (I : C /m y)
           (H : isInitial C (mono_cod_dom I))
  : isInitial (C /m y) I.
Proof.
  intros f.
  pose (II := make_Initial _ H).
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use eq_mor_mono_cod_fib).
  - use make_mono_cod_fib_mor.
    + exact (InitialArrow II _).
    + abstract
        (use (InitialArrowEq (O := II))).
Defined.

Definition initial_mono_cod_fib
           {C : category}
           (y : C)
           (I : Initial C)
           (HI : is_strict_initial I)
  : Initial (C /m y).
Proof.
  use make_Initial.
  - use make_mono_cod_fib_ob.
    + exact I.
    + apply monic_from_strict_initial.
      exact HI.
  - use to_initial_slice_mono.
    exact (pr2 I).
Defined.

Definition mono_codomain_fiberwise_initial
           {C : category}
           (HC : Pullbacks C)
           (HD : cleaving (disp_mono_codomain C) := mono_cod_disp_cleaving HC)
           (I : Initial C)
           (HI : is_strict_initial I)
  : fiberwise_initial HD.
Proof.
  split.
  - intros x.
    exact (initial_mono_cod_fib x I HI).
  - abstract
      (intros x y f z Hz ;
       use to_initial_slice_mono ;
       use (is_initial_mor_to_strict_initial (I ,, HI)) ;
       refine (PullbackPr1 _ · _) ;
       refine (pr1 (InitialArrow (z ,, Hz) (_ ,, _))) ;
       apply monic_from_strict_initial ;
       exact HI).
Defined.

(** * 2. Binary coproducts in the slice of monomorphisms *)
#[local] Opaque regular_category_epi_mono_factorization.

Section BinCoproductsMonoSlice.
  Context {C : category}
          (BC : BinCoproducts C)
          (HC : is_regular_category C)
          {y : C}
          (xf₁ xf₂ : C /m y).

  (**
     Some useful notation
   *)
  Let x₁ : C := mono_cod_dom xf₁.
  Let x₂ : C := mono_cod_dom xf₂.
  Let f₁ : x₁ --> y := mono_cod_mor xf₁.
  Let f₂ : x₂ --> y := mono_cod_mor xf₂.

  Let s : BinCoproduct x₁ x₂ := BC x₁ x₂.

  Definition sum_mor_mono_cod
    : s --> y
    := BinCoproductArrow s f₁ f₂.

  Definition bincoproduct_ob_dom_mono_cod
    : C
    := pr1 (regular_category_epi_mono_factorization HC sum_mor_mono_cod).

  Definition bincoproduct_ob_mor_mono_cod
    : Monic C bincoproduct_ob_dom_mono_cod y.
  Proof.
    use make_Monic.
    - exact (pr122 (regular_category_epi_mono_factorization HC sum_mor_mono_cod)).
    - exact (pr12 (pr222 (regular_category_epi_mono_factorization HC sum_mor_mono_cod))).
  Defined.

  Definition bincoproduct_ob_mono_cod_dom
    : C /m y
    := make_mono_cod_fib_ob bincoproduct_ob_mor_mono_cod.

  (**
     Unions of subobjects as constructed using a epi-mono factorization.
     This is similar to what happens in type theory. If we have two propositions,
     then their disjunction is given as the propositional truncation of their
     disjoint union.
   *)
  Definition bincoproduct_ob_epi
    : s --> bincoproduct_ob_dom_mono_cod
    := pr12 (regular_category_epi_mono_factorization HC sum_mor_mono_cod).

  Proposition is_regular_epi_bincoproduct_ob_epi
    : is_regular_epi bincoproduct_ob_epi.
  Proof.
    exact (pr1 (pr222 (regular_category_epi_mono_factorization HC sum_mor_mono_cod))).
  Qed.

  Proposition is_strong_epi_bincoproduct_ob_epi
    : is_strong_epi bincoproduct_ob_epi.
  Proof.
    use is_strong_epi_regular_epi.
    exact is_regular_epi_bincoproduct_ob_epi.
  Qed.

  Proposition bincoproduct_ob_comm
    : bincoproduct_ob_epi · bincoproduct_ob_mor_mono_cod
      =
      sum_mor_mono_cod.
  Proof.
    exact (!(pr22 (pr222 (regular_category_epi_mono_factorization HC sum_mor_mono_cod)))).
  Qed.

  Definition bincoproduct_ob_mono_cod
    : C /m y
    := make_mono_cod_fib_ob bincoproduct_ob_mor_mono_cod.

  Definition bincoproduct_in1_mono_cod
    : xf₁ --> bincoproduct_ob_mono_cod.
  Proof.
    use make_mono_cod_fib_mor.
    - exact (BinCoproductIn1 s · bincoproduct_ob_epi).
    - abstract
        (rewrite !assoc' ;
         etrans ; [ apply maponpaths ; apply bincoproduct_ob_comm | ] ;
         apply BinCoproductIn1Commutes).
  Defined.

  Definition bincoproduct_in2_mono_cod
    : xf₂ --> bincoproduct_ob_mono_cod.
  Proof.
    use make_mono_cod_fib_mor.
    - exact (BinCoproductIn2 s · bincoproduct_ob_epi).
    - abstract
        (rewrite !assoc' ;
         etrans ; [ apply maponpaths ; apply bincoproduct_ob_comm | ] ;
         apply BinCoproductIn2Commutes).
  Defined.

  Section UMP.
    Context {gz : C /m y}
            (φp : xf₁ --> gz)
            (ψq : xf₂ --> gz).

    Let z : C := mono_cod_dom gz.
    Let g : z --> y := mono_cod_mor gz.
    Let φ : x₁ --> z := mono_dom_mor φp.
    Let ψ : x₂ --> z := mono_dom_mor ψq.

    Definition mor_from_mono_cod_bincoproduct_from_sum
      : s --> mono_cod_dom gz
      := BinCoproductArrow s φ ψ.

    Let ζ := mor_from_mono_cod_bincoproduct_from_sum.

    Lemma mor_from_mono_cod_bincoproduct_mor_eq
      : bincoproduct_ob_epi · bincoproduct_ob_mor_mono_cod
        =
        ζ · mono_cod_mor gz.
    Proof.
      unfold ζ, mor_from_mono_cod_bincoproduct_from_sum.
      use BinCoproductArrowsEq.
      - rewrite bincoproduct_ob_comm.
        rewrite !assoc.
        unfold sum_mor_mono_cod.
        rewrite !BinCoproductIn1Commutes.
        refine (_ @ !(mono_mor_eq φp)).
        apply idpath.
      - rewrite bincoproduct_ob_comm.
        rewrite !assoc.
        unfold sum_mor_mono_cod.
        rewrite !BinCoproductIn2Commutes.
        refine (_ @ !(mono_mor_eq ψq)).
        apply idpath.
    Qed.

    Let fact : ∑ (l : bincoproduct_ob_dom_mono_cod --> mono_cod_dom gz),
               l · mono_cod_mor gz
               =
               bincoproduct_ob_mor_mono_cod
               ×
               bincoproduct_ob_epi · l = ζ
      := pr1 (is_strong_epi_bincoproduct_ob_epi
                (mono_cod_dom gz)
                y
                (mono_cod_mor gz)
                ζ
                bincoproduct_ob_mor_mono_cod
                mor_from_mono_cod_bincoproduct_mor_eq
                (MonicisMonic _ _)).

    Definition mor_from_mono_cod_bincoproduct_mor
      : mono_cod_dom bincoproduct_ob_mono_cod --> mono_cod_dom gz
      := pr1 fact.

    Let l := mor_from_mono_cod_bincoproduct_mor.

    Proposition mor_from_mono_cod_bincoproduct_mor_eq1
      : l · mono_cod_mor gz
        =
        bincoproduct_ob_mor_mono_cod.
    Proof.
      exact (pr12 fact).
    Qed.

    Definition mor_from_mono_cod_bincoproduct
      : bincoproduct_ob_mono_cod --> gz.
    Proof.
      use make_mono_cod_fib_mor.
      - exact l.
      - apply mor_from_mono_cod_bincoproduct_mor_eq1.
    Defined.
  End UMP.
End BinCoproductsMonoSlice.

Section BinCoproductsStable.
  Context {C : category}
          (BC : BinCoproducts C)
          (HBC : stable_bincoproducts BC)
          (HC : is_regular_category C)
          {y₁ y₂ : C}
          {f : y₁ --> y₂}
          (xg₁ xg₂ : C /m y₂).

  Let PB : Pullbacks C := is_regular_category_pullbacks HC.
  Let HD : cleaving (disp_mono_codomain C) := mono_cod_disp_cleaving PB.

  (**
     We start by introducing some notation that we use.

     Concretely, our goal is to make the following diagram

<<
        f^*(x₁ + x₂) --> f^* x₁ + f^* x₂ --> im_f
               |                              |
               |                              |
               V                              V
           f^*(im) ------------------------>  y₁
>>

     Here `im` is the image of `x₁ + x₂ --> y₂`
     and `im_f` is the image of `f^* x₁ + f^* x₂ --> y₁`.
     We use the notation `f^*` for pullback along `f`.

     By showing that the map `f^*(x₁ + x₂) --> f^*(im)` is a strong epimorphism
     and that `im_f --> y'_1` is mono, we get the desired morphisms as a lift.
   *)

  Let x₁ : C := mono_cod_dom xg₁.
  Let x₂ : C := mono_cod_dom xg₂.
  Let g₁ : x₁ --> y₂ := mono_cod_mor xg₁.
  Let g₂ : x₂ --> y₂ := mono_cod_mor xg₂.

  Let im : C := bincoproduct_ob_dom_mono_cod BC HC xg₁ xg₂.
  Let s : BinCoproduct x₁ x₂ := BC x₁ x₂.
  Let e : s --> im := bincoproduct_ob_epi BC HC xg₁ xg₂.
  Let m : im --> y₂ := bincoproduct_ob_mor_mono_cod BC HC xg₁ xg₂.

  Let sum : C / y₂ := make_cod_fib_ob (sum_mor_mono_cod BC xg₁ xg₂).

  Let fx₁ : C := mono_cod_dom (mono_cod_pb PB f xg₁).
  Let fx₂ : C := mono_cod_dom (mono_cod_pb PB f xg₂).
  Let fg₁ : fx₁ --> y₁ := mono_cod_mor (mono_cod_pb PB f xg₁).
  Let fg₂ : fx₂ --> y₁ := mono_cod_mor (mono_cod_pb PB f xg₂).

  Let im_f : C
    := bincoproduct_ob_dom_mono_cod BC HC (mono_cod_pb PB f xg₁) (mono_cod_pb PB f xg₂).

  Let sf : BinCoproduct fx₁ fx₂ := BC fx₁ fx₂.
  Let ef : sf --> im_f := bincoproduct_ob_epi BC HC _ _.
  Let mf : Monic _ im_f y₁ := bincoproduct_ob_mor_mono_cod BC HC _ _.

  Let sumf : C / y₁
    := make_cod_fib_ob (sum_mor_mono_cod BC (mono_cod_pb PB f xg₁) (mono_cod_pb PB f xg₂)).

  (**
     Now we define some more maps in the desired diagram.
     We start with the map `f^*(im) --> y₁`, which we call `f_e_im`

     The reason why this morphism exists, is because we constructed
     `f^*(im)` as the following pullback

<<
      f^*(im) --------> im
        |               |
        |               |
        V               V
        y₁ -----------> y₂
>>
   *)
  Let im_m_slice : C/y₂ := make_cod_fib_ob m.
  Let f_im : C := cod_dom (cod_pb PB f im_m_slice).
  Let f_e_im : f_im --> y₁ := cod_mor (cod_pb PB f im_m_slice).

  (**
     Next we construct the map `f^*(x₁ + x₂) --> f^*(im)`.
     This map exists by the functoriality of taking the pullback.
     We call this map `f_epi`.
   *)
  Local Definition sum_im_map
    : sum --> im_m_slice.
  Proof.
    use make_cod_fib_mor.
    - exact e.
    - apply bincoproduct_ob_comm.
  Defined.

  Local Definition f_epi
    : cod_dom (cod_pb PB f sum) --> f_im
    := dom_mor (#(cod_pb PB f) sum_im_map).

  (**
     Finally, we construct the map `f^*(x₁ + x₂) --> f^* x₁ + f^* x₂`.
     This map exists since we assume coproducts are stable under pullback.
   *)
  Local Definition stable_pb_sum_map
    : cod_pb PB f sum --> sumf.
  Proof.
    pose (make_BinCoproduct
            _ _ _ _ _ _
            (from_stable BC PB HBC
               f
               (mono_cod_to_cod_fib _ xg₁)
               (mono_cod_to_cod_fib _ xg₂)))
      as CP.
    use (BinCoproductArrow CP).
    - simple refine (_ ,, _).
      + exact (BinCoproductIn1 _).
      + abstract
          (cbn ;
           unfold sum_mor_mono_cod ;
           rewrite BinCoproductIn1Commutes ;
           rewrite id_right ;
           apply idpath).
    - simple refine (_ ,, _).
      + exact (BinCoproductIn2 _).
      + abstract
          (cbn ;
           unfold sum_mor_mono_cod ;
           rewrite BinCoproductIn2Commutes ;
           rewrite id_right ;
           apply idpath).
  Defined.

  (**
     We can show that the desired diagram commutes
   *)
  Local Lemma diagram_commutes
    : f_epi · f_e_im
      =
      dom_mor stable_pb_sum_map · ef · mf.
  Proof.
    refine (mor_eq (# (cod_pb PB f) sum_im_map) @ _).
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (bincoproduct_ob_comm BC HC (mono_cod_pb PB f xg₁) (mono_cod_pb PB f xg₂)).
    }
    exact (mor_eq stable_pb_sum_map).
  Qed.

  (**
     Note that we need that `f_epi` is a strong epimorphism.
     To see why, first note that we have the following diagram

<<
      f^*(x₁ + x₂) ---> x₁ + x₂
        |                  |
        |                  |
        V                  V
      f^*(im) -----------> im
        |                  |
        |                  |
        V                  V
        y₁ ------------->  y₂
>>

     In this digram, both the lower and the whole square are pullback squares.
     Hence, the upper square is a pullback square as well.
     Since our category is regular, we have that regular epis are stable under pullbacks,
     and thus `f_epi` is a regular epi.
   *)
  Local Definition left_map
    : f_im --> bincoproduct_ob_dom_mono_cod BC HC xg₁ xg₂
    := PullbackPr1 (PB _ _ _ m f).

  Local Definition top_map
    : cod_dom (cod_pb PB f sum) --> BC x₁ x₂
    := PullbackPr1 _.

  Local Lemma pb_sqr_commutes
    : top_map · bincoproduct_ob_epi BC HC xg₁ xg₂
      =
      dom_mor (cod_fiber_functor_pb PB f sum_im_map) · left_map.
  Proof.
    unfold left_map.
    refine (!_).
    etrans.
    {
      cbn.
      rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    }
    apply idpath.
  Qed.

  Section UMP.
    Context {w : C}
            {h : w --> BC x₁ x₂}
            {k : w --> f_im}
            (p : h · e = k · left_map).

    Let P : Pullback (sum_mor_mono_cod BC xg₁ xg₂) f
      := PB _ _ _ (sum_mor_mono_cod BC xg₁ xg₂) f.
    Let Q : Pullback m f := PB _ _ _ m f.

    Proposition is_regular_epi_f_epi_unique
      : isaprop
          (∑ (hk : w --> cod_dom (cod_pb PB f sum)),
           hk · top_map = h
           ×
           hk · dom_mor (cod_fiber_functor_pb PB f sum_im_map) = k).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro ; apply isapropdirprod ; apply homset_property.
      }
      use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
      - exact (pr12 ζ₁ @ !(pr12 ζ₂)).
      - pose proof (maponpaths (λ z, z · PullbackPr2 _) (pr22 ζ₁ @ !(pr22 ζ₂))) as r.
        cbn in r.
        rewrite !assoc' in r.
        rewrite !PullbackArrow_PullbackPr2 in r.
        exact r.
    Qed.

    Local Definition is_regular_epi_f_epi_map
      : w --> cod_dom (cod_pb PB f sum).
    Proof.
      use (PullbackArrow P).
      - exact h.
      - exact (k · cod_mor (cod_pb PB f im_m_slice)).
      - abstract
          (unfold left_map in p ;
           pose proof (maponpaths (λ z, z · m) p) as q ;
           simpl in q ;
           rewrite !assoc' in q ;
           refine (maponpaths (λ z, h · z) (!_) @ q @ _) ;
           [ apply bincoproduct_ob_comm | ] ;
           rewrite !assoc' ;
           apply maponpaths ;
           apply PullbackSqrCommutes).
    Defined.

    Proposition is_regular_epi_f_epi_map_pr2
      : is_regular_epi_f_epi_map · dom_mor (cod_fiber_functor_pb PB f sum_im_map)
        =
        k.
    Proof.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (PB y₂ im y₁ m f))).
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackArrow_PullbackPr1.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply PullbackArrow_PullbackPr1.
        }
        exact p.
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackArrow_PullbackPr2.
        }
        apply PullbackArrow_PullbackPr2.
    Qed.
  End UMP.

  Local Lemma is_regular_epi_f_epi
    : is_strong_epi f_epi.
  Proof.
    use is_strong_epi_regular_epi.
    unfold f_epi.
    rewrite cod_fiber_functor_on_mor.
    use (is_regular_category_regular_epi_pb_stable
           HC
           _ _ _ _ _ _ _ _ _ _
           (is_regular_epi_bincoproduct_ob_epi BC HC xg₁ xg₂)).
    - exact left_map.
    - exact top_map.
    - exact pb_sqr_commutes.
    - intros w h k p.
      use iscontraprop1.
      + apply is_regular_epi_f_epi_unique.
      + refine (is_regular_epi_f_epi_map p ,, _ ,, _).
        * abstract
            (exact (PullbackArrow_PullbackPr1 _ _ _ _ _)).
        * apply is_regular_epi_f_epi_map_pr2.
  Qed.

  (**
     This allows us to construct the desired lift.
   *)
  Let ℓ : f_im --> im_f
    := pr11 (is_regular_epi_f_epi _ _ _ _ _ diagram_commutes (MonicisMonic _ _)).

  Let ℓl : ℓ · mf = f_e_im
    := pr121 (is_regular_epi_f_epi _ _ _ _ _ diagram_commutes (MonicisMonic _ _)).
  Let ℓr : f_epi · ℓ = dom_mor stable_pb_sum_map · ef
    := pr221 (is_regular_epi_f_epi _ _ _ _ _ diagram_commutes (MonicisMonic _ _)).

  Definition mono_codomain_fiberwise_bincoproducts_stable
    : mono_cod_pb PB f (bincoproduct_ob_mono_cod BC HC xg₁ xg₂)
      -->
      bincoproduct_ob_mono_cod BC HC (mono_cod_pb PB f xg₁) (mono_cod_pb PB f xg₂).
  Proof.
    use make_mono_cod_fib_mor.
    - exact ℓ.
    - exact ℓl.
  Defined.
End BinCoproductsStable.

Definition mono_codomain_fiberwise_bincoproducts
           {C : category}
           (HC : is_regular_category C)
           (PB := is_regular_category_pullbacks HC)
           (HD : cleaving (disp_mono_codomain C) := mono_cod_disp_cleaving PB)
           (BC : BinCoproducts C)
           (HBC : stable_bincoproducts BC)
  : fiberwise_bincoproducts HD.
Proof.
  use make_fiberwise_bincoproducts_locally_propositional.
  - apply locally_propositional_mono_cod_disp_cat.
  - exact (λ Γ, bincoproduct_ob_mono_cod BC HC).
  - apply bincoproduct_in1_mono_cod.
  - apply bincoproduct_in2_mono_cod.
  - apply mor_from_mono_cod_bincoproduct.
  - apply mono_codomain_fiberwise_bincoproducts_stable.
    exact HBC.
Qed.
