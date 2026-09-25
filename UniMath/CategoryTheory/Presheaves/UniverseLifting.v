(**

 The Hofmann-Streicher lifting of universes

 We show that every universe of sets gives rise to a universe of presheaves. Our
 construction follows Hofmann and Streicher, and it is similar to the construction
 of the subobject classifier of presheaves. If we have a (small) category `C`,
 then the subobject classifier of presheaves is defined to be the presheaf that
 maps every `x : C` to the set of sieves on `x`. Sieves on `x` are the same as
 functors from `(C/x)^op` to the category `hProp`, whose objects are propositions
 and whose morphisms are functions. We construct the lifting of a set universe in
 a similar way. Given a universe `u` of sets, we define the lifting presheaf as
 follows: it maps every `x` to the set of functors from `(C/x)^op` to the category
 `u`, whose objects are inhabitants of `u` and whose morphisms are functions between
 the associated types.

 We also give a definition of families of presheaves valued in a given universe of
 sets. This definition follows the definition of dependent presheaf, and the only
 difference is that the given universe of sets takes the place of `hSet`.

 References
 - "Lifting Grothendieck universes" by Hofmann and Streicher

 Content
 1. A useful lemma
 2. The unvierse lifting as a dependent presheaf
 3. Lemmas to construct the associated type
 4. The associated type
 5. Dependent presheaves valued in a set universe
 6. Equality of presheaves valued in a universe of sets

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.SetUniverses.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Categories.UniverseToCat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodDomain.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.

Local Open Scope cat.

(** * 1. A useful lemma *)
Proposition functor_to_set_universe_eq_ob
            {C : category}
            {u : set_universe}
            {F G : C ⟶ set_universe_to_category u}
            (p : F = G)
            (x : C)
  : F x = G x.
Proof.
  induction p ;cbn.
  apply idpath.
Qed.

Proposition functor_to_set_universe_eq
            {C : category}
            {u : set_universe}
            {F G : C ⟶ set_universe_to_category u}
            (p : F = G)
            {x y : C}
            (f : x --> y)
            (a : set_universe_el (F x))
  : #F f a
    =
    set_universe_eq
      (eqtohomot (maponpaths (λ z, pr11 z) (!p)) y)
      (#G f (set_universe_eq (eqtohomot (maponpaths (λ z, pr11 z) p) x) a)).
Proof.
  induction p ;cbn.
  apply idpath.
Qed.

Proposition functor_to_set_universe_mor_eq
            {C : category}
            {u : set_universe}
            (F : C ⟶ set_universe_to_category u)
            {x₁ x₂ y₁ y₂ : C}
            {f : x₁ --> y₁}
            {g : x₂ --> y₂}
            (px : x₁ = x₂)
            (py : y₁ = y₂)
            (q : f · idtoiso py = idtoiso px ·  g)
            (a : set_universe_el (F x₁))
  : #F f a
    =
    set_universe_eq (maponpaths F (!py)) (#F g (set_universe_eq (maponpaths F px) a)).
Proof.
  induction px, py.
  cbn in q.
  rewrite id_left, id_right in q.
  induction q.
  cbn.
  apply idpath.
Qed.

Section Lifting.
  Context (C : category)
          (u : set_universe).

  (** * 2. The unvierse lifting as a dependent presheaf *)
  Definition presheaf_universe
    : dep_psh (constant_functor (C^op) HSET unitset).
  Proof.
    use make_dep_psh.
    - exact (λ x _,
             set_functors_to_set_category
               ((C/x)^op)
               (set_universe_to_setcategory u)).
    - exact (λ x y _ _ f _ F, functor_op (comp_functor f) ∙ F).
    - abstract
        (intros x ? ? F ;
         cbn ;
         rewrite comp_functor_identity ;
         use functor_eq ; [ apply set_universe_to_category | ] ;
         apply idpath).
    - abstract
        (intros x y z ? ? ? f g p q r F ;
         cbn ;
         rewrite comp_functor_comp ;
         use functor_eq ; [ apply set_universe_to_category | ] ;
         cbn ;
         apply idpath).
  Defined.

  Definition presheaf_universe_ctx
             (Γ : C^op ⟶ HSET)
    : dep_psh Γ
    := dep_psh_subst
         (TerminalArrow Terminal_PreShv Γ)
         presheaf_universe.

  (** * 3. Lemmas to construct the associated type *)
  Lemma psh_term_set_universe_eq
        {Γ : C^op ⟶ HSET}
        (τ : psh_term (presheaf_universe_ctx Γ))
        {x : C}
        (xx : (Γ x : hSet))
        {f₁ f₂ f₁' f₂' : C/x}
        {g : f₁ --> f₂}
        {g' : f₁' --> f₂'}
        (p₁ : f₁' = f₁)
        (p₂ : f₂' = f₂)
        (r : g' · idtoiso p₂ = idtoiso p₁ · g)
        (a : set_universe_el ((τ x xx : _ ⟶ _) f₂))
    : #(τ x xx : _ ⟶ _) g a
      =
      set_universe_eq
        (maponpaths (τ _ _ : _ ⟶ _) p₁)
        (#(τ x xx : _ ⟶ _) g' (set_universe_eq (maponpaths (τ _ _ : _ ⟶ _) (!p₂)) a)).
  Proof.
    induction p₁, p₂.
    cbn.
    apply maponpaths_2.
    refine (_ @ !r @ _).
    - exact (!(id_left _)).
    - exact (id_right _).
  Qed.

  Lemma psh_term_universe_id_path
        {Γ : C^op ⟶ HSET}
        (τ : psh_term (presheaf_universe_ctx Γ))
        {x : C}
        (xx : (Γ x : hSet))
    : (τ x xx : _ ⟶ _) (cod_fib_id x)
      =
      (τ x xx : _ ⟶ _) (cod_fib_comp (identity x) (cod_fib_id x)).
  Proof.
    apply maponpaths.
    refine (maponpaths (λ z, _ ,, z) _).
    cbn.
    exact (!(id_left _)).
  Qed.

  Lemma psh_universe_id_lem_1
        (x : C)
    : cod_fib_id x = cod_fib_comp (identity x) (cod_fib_id x).
  Proof.
    refine (maponpaths (λ z, _ ,, z) _).
    cbn.
    exact (!(id_left _)).
  Defined.

  Lemma psh_universe_id_lem_2
        (x : C)
    : identity (cod_fib_id x) · identity _
      =
      idtoiso (psh_universe_id_lem_1 x) · cod_fib_comp_mor (identity x).
  Proof.
    unfold psh_universe_id_lem_1.
    use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    rewrite !dom_mor_idtoiso.
    refine (id_right _ @ _ @ !(id_right _)).
    refine (!_).
    cbn.
    etrans.
    {
      do 2 apply maponpaths.
      refine (maponpathscomp (λ z, _ ,, z) cod_dom _ @ _).
      apply maponpaths_for_constant_function.
    }
    cbn.
    apply idpath.
  Qed.

  Lemma psh_term_universe_id
        {Γ : C^op ⟶ HSET}
        (τ : psh_term (presheaf_universe_ctx Γ))
        {x : C}
        (xx : (Γ x : hSet))
        (a : set_universe_el ((τ x xx : _ ⟶ _) (cod_fib_id x)))
    : # (τ x xx : _ ⟶ _) (cod_fib_comp_mor (identity x)) a
      =
      set_universe_eq (psh_term_universe_id_path τ xx) a.
  Proof.
    cbn in *.
    etrans.
    {
      use (psh_term_set_universe_eq τ xx _ (idpath _)).
      - exact (cod_fib_id x).
      - apply identity.
      - exact (psh_universe_id_lem_1 x).
      - exact (psh_universe_id_lem_2 x).
    }
    cbn.
    etrans.
    {
      apply maponpaths.
      exact (eqtohomot (functor_id (τ x xx) (cod_fib_id x)) a).
    }
    apply set_universe_eq_path.
  Qed.

  Lemma psh_term_universe_comp_path₁
        {Γ : C^op ⟶ HSET}
        (τ : psh_term (presheaf_universe_ctx Γ))
        {x y z : C}
        (s₁ : x --> y)
        (s₂ : y --> z)
        (zz : (Γ z : hSet))
    : (τ y (#Γ s₂ zz) : _ ⟶ _) (cod_fib_comp s₁ (cod_fib_id x))
      =
      (τ z zz : _ ⟶ _) (cod_fib_comp (s₁ · s₂) (cod_fib_id x)).
  Proof.
    refine (maponpaths (λ (z : _ ⟶ _), z _) (psh_term_naturality τ s₂ zz) @ _).
    cbn.
    apply maponpaths.
    refine (maponpaths (λ z, _ ,, z) _).
    cbn.
    rewrite !id_left.
    apply idpath.
  Qed.

  Lemma psh_term_universe_comp_path₂
        {Γ : C^op ⟶ HSET}
        (τ : psh_term (presheaf_universe_ctx Γ))
        {x y : C}
        (s : x --> y)
        (yy : (Γ y : hSet))
    : (τ y yy : _ ⟶ _) (cod_fib_comp s (cod_fib_id x))
      =
      (τ x (#Γ s yy) :_ ⟶ _) (cod_fib_id x).
  Proof.
    cbn.
    refine (!_).
    exact (maponpaths (λ (z : _ ⟶ _), z _) (psh_term_naturality τ s yy)).
  Qed.

  Lemma psh_term_universe_comp_lem_1
        {x y z : C}
        (s₁ : x --> y)
        (s₂ : y --> z)
    : comp_functor s₂ (cod_fib_comp s₁ (cod_fib_id x))
      =
      cod_fib_comp (s₁ · s₂) (cod_fib_id x).
  Proof.
    refine (maponpaths (λ z, _ ,, z) _).
    cbn.
    rewrite !id_left.
    apply idpath.
  Defined.

  Lemma psh_term_universe_comp_lem_2
        {x y z : C}
        (s₁ : x --> y)
        (s₂ : y --> z)
    : #(comp_functor s₂) (cod_fib_comp_mor s₁)
      · cod_fib_comp_mor s₂
      · identity _
      =
      idtoiso (psh_term_universe_comp_lem_1 s₁ s₂)
      · cod_fib_comp_mor (s₁ · s₂).
  Proof.
    use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    rewrite !dom_mor_idtoiso.
    cbn.
    rewrite id_right.
    refine (!(id_left _) @ !_).
    apply maponpaths_2.
    etrans.
    {
      do 2 apply maponpaths.
      refine (maponpathscomp (λ z, _ ,, z) cod_dom _ @ _).
      apply maponpaths_for_constant_function.
    }
    cbn.
    apply idpath.
  Qed.

  Lemma psh_term_universe_comp
        {Γ : C^op ⟶ HSET}
        (τ : psh_term (presheaf_universe_ctx Γ))
        {x y z : C}
        (s₁ : x --> y)
        (s₂ : y --> z)
        (zz : (Γ z : hSet))
        (a : set_universe_el ((τ z zz : _ ⟶ _) (cod_fib_id z)))
    : # (τ z zz : _ ⟶ _) (cod_fib_comp_mor (s₁ · s₂)) a
      =
      set_universe_eq
        (psh_term_universe_comp_path₁ τ s₁ s₂ zz)
        (# (τ y (#Γ s₂ zz) : _ ⟶ _)
           (cod_fib_comp_mor s₁)
           (set_universe_eq
              (psh_term_universe_comp_path₂ τ s₂ zz)
              (# (τ z zz : _ ⟶ _)
                 (cod_fib_comp_mor s₂)
                 a))).
  Proof.
    cbn.
    etrans.
    {
      refine (psh_term_set_universe_eq τ zz _ (idpath _) _ _).
      exact (psh_term_universe_comp_lem_2 s₁ s₂).
    }
    etrans.
    {
      apply maponpaths.
      exact (maponpaths (λ z, z _) (functor_comp (τ z zz) _ _)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (functor_to_set_universe_eq (psh_term_naturality τ s₂ zz)).
    }
    rewrite !set_universe_eq_comp.
    rewrite !set_universe_eq_idpath.
    apply set_universe_eq_path.
  Qed.

  (** * 4. The associated type *)
  Proposition presheaf_el_map_path
              {Γ : C^op ⟶ HSET}
              (τ : psh_term (presheaf_universe_ctx Γ))
              {x y : C}
              {xx : (Γ x : hSet)}
              {yy : (Γ y : hSet)}
              (s : y --> x)
              (p : #Γ s xx = yy)
    : (τ x xx : _ ⟶ _) (cod_fib_comp s (cod_fib_id y))
      =
      (τ y yy : _ ⟶ _) (cod_fib_id y).
  Proof.
    induction p.
    pose (psh_term_naturality τ s xx) as q.
    cbn in q.
    exact (maponpaths (λ (z : _ ⟶ _), z _) (!q)).
  Qed.

  Definition presheaf_el_map
             {Γ : C^op ⟶ HSET}
             (τ : psh_term (presheaf_universe_ctx Γ))
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ x xx, set_universe_el ((τ x xx : _ ⟶ _) (cod_fib_id x))).
    - exact (λ x y xx yy s p a,
             set_universe_eq
               (presheaf_el_map_path τ s p)
               (#(τ x xx : _ ⟶ _) (cod_fib_comp_mor s) a)).
    - abstract
        (cbn ;
         intros x xx p a ;
         etrans ;
         [ apply maponpaths ;
           apply psh_term_universe_id
         | ] ;
         rewrite set_universe_eq_comp ;
         apply set_universe_eq_idpath).
    - abstract
        (intros x y z xx yy zz s₁ s₂ p q r a ;
         induction p, q ;
         cbn in * ;
         etrans ;
         [ apply maponpaths ;
           apply psh_term_universe_comp
         | ] ;
         rewrite set_universe_eq_comp ;
         refine (set_universe_eq_path _ _ _ @ _) ;
         do 2 apply maponpaths ;
         apply set_universe_eq_path).
  Defined.

  Definition presheaf_el_map_eq
             {Γ : C^op ⟶ HSET}
             {a b : psh_term (presheaf_universe_ctx Γ)}
             (p : a = b)
    : dep_psh_nat_trans
        (presheaf_el_map a)
        (presheaf_el_map b)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x xx, set_universe_eq _).
      abstract
        (cbn ;
         induction p ;
         apply idpath).
    - abstract
        (intros x y xx yy f q₁ q₂ z ;
         induction p ; cbn ;
         rewrite set_universe_eq_comp ;
         rewrite set_universe_eq_idpath ;
         apply set_universe_eq_path).
  Defined.

  Definition total_psh_el_map_nat_z_iso
             {Γ : C^op ⟶ HSET}
             {a b : psh_term (presheaf_universe_ctx Γ)}
             (p : a = b)
    : nat_z_iso
        (total_psh
           (presheaf_el_map a))
        (total_psh
           (presheaf_el_map b)).
  Proof.
    use total_psh_nat_z_iso.
    - exact (presheaf_el_map_eq p).
    - intros x xx.
      use isweq_iso.
      + refine (set_universe_eq _).
        abstract
          (induction p ; cbn ;
           apply idpath).
      + abstract
          (intro z ; cbn ;
           rewrite set_universe_eq_comp ;
           apply set_universe_eq_idpath).
      + abstract
          (intro z ; cbn ;
           rewrite set_universe_eq_comp ;
           apply set_universe_eq_idpath).
  Defined.
End Lifting.

Arguments presheaf_universe_ctx {C} u Γ.
Arguments presheaf_el_map {C u Γ} τ.

Section SmallDependentPresheaf.
  Context {C : category}
          {u : set_universe}.

  (** * 5. Dependent presheaves valued in a set universe *)
  Definition set_universe_dep_psh_data
             (Γ : C^op ⟶ set_universe_to_setcategory u)
    : UU
    := ∑ (Fo : ∏ (x : C) (xx : set_universe_el (Γ x)), u),
       ∏ (x y : C)
         (xx : set_universe_el (Γ x))
         (yy : set_universe_el (Γ y))
         (s : y --> x)
         (p : #Γ s xx = yy),
       set_universe_el (Fo x xx)
       → set_universe_el (Fo y yy).

  Definition make_set_universe_dep_psh_data
             {Γ : C^op ⟶ set_universe_to_setcategory u}
             (Fo : ∏ (x : C) (xx : set_universe_el (Γ x)), u)
             (Fm : ∏ (x y : C)
                     (xx : set_universe_el (Γ x))
                     (yy : set_universe_el (Γ y))
                     (s : y --> x)
                     (p : #Γ s xx = yy),
                   set_universe_el (Fo x xx)
                   → set_universe_el (Fo y yy))
    : set_universe_dep_psh_data Γ
    := Fo ,, Fm.

  Definition set_universe_dep_psh_ob
             {Γ : C^op ⟶ set_universe_to_setcategory u}
             (F : set_universe_dep_psh_data Γ)
             (x : C)
             (xx : set_universe_el (Γ x))
    : u
    := pr1 F x xx.

  Coercion set_universe_dep_psh_ob : set_universe_dep_psh_data >-> Funclass.

  Definition set_universe_dep_psh_mor
             {Γ : C^op ⟶ set_universe_to_setcategory u}
             (F : set_universe_dep_psh_data Γ)
             {x y : C}
             {xx : set_universe_el (Γ x)}
             {yy : set_universe_el (Γ y)}
             (s : y --> x)
             (p : #Γ s xx = yy)
             (a : set_universe_el (F x xx))
    : set_universe_el (F y yy)
    := pr2 F x y xx yy s p a.

  Notation "#s" := set_universe_dep_psh_mor : cat.

  Definition set_universe_dep_psh_laws
             {Γ : C^op ⟶ set_universe_to_setcategory u}
             (F : set_universe_dep_psh_data Γ)
    : UU
    := (∏ (x : C)
          (xx : set_universe_el (Γ x))
          (p : #Γ (identity x) xx = xx)
          (a : set_universe_el (F x xx)),
        #s F (identity _) p a = a)
       ×
       (∏ (x y z : C)
          (xx : set_universe_el (Γ x))
          (yy : set_universe_el (Γ y))
          (zz : set_universe_el (Γ z))
          (s₁ : y --> x)
          (s₂ : z --> y)
          (p : #Γ s₁ xx = yy)
          (q : #Γ s₂ yy = zz)
          (r : #Γ (s₂ · s₁) xx = zz)
          (a : set_universe_el (F x xx)),
        #s F (s₂ · s₁) r a = #s F s₂ q (#s F s₁ p a)).

  Proposition isaprop_set_universe_dep_psh_laws
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              (F : set_universe_dep_psh_data Γ)
    : isaprop (set_universe_dep_psh_laws F).
  Proof.
    use isapropdirprod.
    - repeat (use impred ; intro).
      apply setproperty.
    - repeat (use impred ; intro).
      apply setproperty.
  Qed.

  Definition set_universe_dep_psh
             (Γ : C^op ⟶ set_universe_to_setcategory u)
    : UU
    := ∑ (F : set_universe_dep_psh_data Γ),
       set_universe_dep_psh_laws F.

  Definition make_set_universe_dep_psh
             {Γ : C^op ⟶ set_universe_to_setcategory u}
             (F : set_universe_dep_psh_data Γ)
             (H : set_universe_dep_psh_laws F)
    : set_universe_dep_psh Γ
    := F ,, H.

  Coercion set_universe_dep_psh_to_data
           {Γ : C^op ⟶ set_universe_to_setcategory u}
           (F : set_universe_dep_psh Γ)
    : set_universe_dep_psh_data Γ
    := pr1 F.

  Proposition set_universe_dep_psh_id
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              (F : set_universe_dep_psh Γ)
              {x : C}
              {xx : set_universe_el (Γ x)}
              (p : #Γ (identity x) xx = xx)
              (a : set_universe_el (F x xx))
    : #s F (identity _) p a = a.
  Proof.
    exact (pr12 F x xx p a).
  Defined.

  Proposition set_universe_dep_psh_comp
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              (F : set_universe_dep_psh Γ)
              {x y z : C}
              {xx : set_universe_el (Γ x)}
              {yy : set_universe_el (Γ y)}
              {zz : set_universe_el (Γ z)}
              {s₁ : y --> x}
              {s₂ : z --> y}
              (p : #Γ s₁ xx = yy)
              (q : #Γ s₂ yy = zz)
              (r : #Γ (s₂ · s₁) xx = zz)
              (a : set_universe_el (F x xx))
    : #s F (s₂ · s₁) r a = #s F s₂ q (#s F s₁ p a).
  Proof.
    exact (pr22 F x y z xx yy zz s₁ s₂ p q r a).
  Defined.

  Proposition set_universe_dep_psh_mor_eq_path
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              {x y : C}
              {xx : set_universe_el (Γ x)}
              {yy : set_universe_el (Γ y)}
              {s s' : y --> x}
              (p : #Γ s xx = yy)
              (q : s = s')
    : #Γ s' xx = yy.
  Proof.
    induction q.
    exact p.
  Defined.

  Proposition set_universe_dep_psh_mor_eq
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              (F : set_universe_dep_psh Γ)
              {x y : C}
              {xx : set_universe_el (Γ x)}
              {yy : set_universe_el (Γ y)}
              {s s' : y --> x}
              (p : #Γ s xx = yy)
              (q : s = s')
              (a : set_universe_el (F x xx))
    : #s F s p a = #s F s' (set_universe_dep_psh_mor_eq_path p q) a.
  Proof.
    induction q.
    cbn.
    apply idpath.
  Qed.

  (** * 6. Equality of presheaves valued in a universe of sets *)
  Proposition set_universe_dep_psh_data_path_help
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              {F G : set_universe_dep_psh_data Γ}
              (q₁ : pr1 F = pr1 G)
              (q₂ : ∏ (x y : C)
                      (xx : set_universe_el (Γ x))
                      (yy : set_universe_el (Γ y))
                      (s : y --> x)
                      (p : #Γ s xx = yy)
                      (a : set_universe_el (F x xx)),
                    set_universe_eq
                      (toforallpaths _ _ _ (toforallpaths _ _ _ q₁ y) yy)
                      (#s F s p a)
                    =
                    #s G s p (set_universe_eq
                                (toforallpaths _ _ _ (toforallpaths _ _ _ q₁ x) xx)
                                a))
    : F = G.
  Proof.
    induction F as [ Fo Fm ], G as [ Go Gm ].
    cbn in q₁.
    induction q₁.
    apply maponpaths.
    cbn in q₂.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro xx.
    use funextsec ; intro yy.
    use funextsec ; intro s.
    use funextsec ; intro p.
    use funextsec ; intro a.
    apply q₂.
  Qed.

  Proposition set_universe_dep_psh_data_path
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              {F G : set_universe_dep_psh_data Γ}
              (q₁ : ∏ (x : C) (xx : set_universe_el (Γ x)), F x xx = G x xx)
              (q₂ : ∏ (x y : C)
                      (xx : set_universe_el (Γ x))
                      (yy : set_universe_el (Γ y))
                      (s : y --> x)
                      (p : #Γ s xx = yy)
                      (a : set_universe_el (F x xx)),
                    set_universe_eq (q₁ y yy) (#s F s p a)
                    =
                    #s G s p (set_universe_eq (q₁ x xx) a))
    : F = G.
  Proof.
    use set_universe_dep_psh_data_path_help.
    - use funextsec.
      intros x.
      use funextsec.
      intros xx.
      exact (q₁ x xx).
    - intros x y xx yy s p a.
      rewrite !toforallpaths_funextsec.
      apply q₂.
  Qed.

  Proposition set_universe_dep_psh_eq
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              (F : set_universe_dep_psh_data Γ)
              {x y : C}
              {xx xx' : set_universe_el (Γ x)}
              {yy yy' : set_universe_el (Γ y)}
              (s : y --> x)
              (p : #Γ s xx = yy)
              (q : F x xx' = F x xx)
              (q' : yy' = yy)
              (q'' : xx' = xx)
              (a : set_universe_el (F x xx'))
    : #s F s p (set_universe_eq q a)
      =
      set_universe_eq
        (maponpaths (F y) q')
        (#s F s (maponpaths (# Γ s) q'' @ p @ !q') a).
  Proof.
    induction q'.
    induction q''.
    cbn.
    rewrite set_universe_eq_idpath.
    apply maponpaths_2.
    apply setproperty.
  Qed.

  Proposition set_universe_dep_psh_path
              {Γ : C^op ⟶ set_universe_to_setcategory u}
              {F G : set_universe_dep_psh Γ}
              (p : (F : set_universe_dep_psh_data Γ) = G)
    : F = G.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_set_universe_dep_psh_laws.
    }
    exact p.
  Qed.
End SmallDependentPresheaf.

Notation "#s" := set_universe_dep_psh_mor : cat.
