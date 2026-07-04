(**

 ∏-types of sheaves

 We show that sheaves are closed under ∏-types. Specifically, we show that if `A` is
 a dependent presheaf over `Γ` and that `B` is a dependent sheaf over the total space
 of `A`, then their ∏-type is a sheaf. Note that we only require the codomain to be a
 sheaf and that we do not assume anything about the domain. Intuitively, the reason
 why we only need to assume that `B` is a dependent sheaf, is because the amalgamations
 in the ∏-type are solely computed using amalgamations in `B`. This is because they are
 defined pointwise.

 Content
 1. The amalgamations in the ∏-type
 2. Uniqueness
 3. The ∏-type for sheaves

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.PiTypes.

Local Open Scope cat.

Section PiSheaf.
  Context {C : site}
          {Γ : C^op ⟶ HSET}
          (A : dep_psh Γ)
          {B : dep_psh (total_psh A)}
          (HB : is_dep_sheaf B).

  (** * 1. The amalgamations in the ∏-type *)
  Section Amalgamation.
    Context {x : C}
            {ω : sieve x}
            (p : C x ω)
            {z : matching_family Γ ω}
            {a : amalgamation z}
            (zz : matching_family_dep (pi_dep_psh A B) z).

    Definition subst_matching_family_total
               (y : C)
               (f : y --> x)
               (aa : A y (#Γ f a))
      : matching_family (total_psh A) (f ^* ω).
    Proof.
      use make_matching_family.
      - refine (λ y' f' p', z y' _ p' ,, _).
        refine (#d A f' _ aa).
        abstract
          (refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _) ;
           exact (amalgamation_restr a _ p')).
      - abstract
          (intros y₁ y₂ f₁ f₂ g p' q₁ q₂ ;
           use dep_psh_total_space_path ;
           [ cbn ;
             refine (matching_family_restr z _ _ _) ;
             rewrite assoc ;
             rewrite p' ;
             apply idpath
           | cbn ;
             rewrite !dep_psh_mor_comp' ;
             use dep_psh_mor_path_eq ;
             rewrite id_left ;
             exact p' ]).
    Defined.

    Proposition subst_matching_family_total_law
                (y : C)
                (f : y --> x)
                (aa : A y (#Γ f a))
      : amalgamation_law (subst_matching_family_total y f aa) (#Γ f a ,, aa).
    Proof.
      intros w g q.
      use dep_psh_total_space_path.
      - cbn.
        refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _).
        exact (amalgamation_restr a _ q).
      - cbn.
        rewrite dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        apply id_left.
    Qed.

    Proposition subst_matching_family_amalgamation
                (y : C)
                (f : y --> x)
                (aa : A y (#Γ f a))
      : amalgamation (subst_matching_family_total y f aa).
    Proof.
      use make_amalgamation.
      - exact (#Γ f a ,, aa).
      - exact (subst_matching_family_total_law y f aa).
    Defined.

    Proposition pi_matching_family_dep_pt_eq1
                {w y : C}
                {f : y --> x}
                {g : w --> y}
                (q : ω w (g · f))
      : #Γ g (#Γ f a) = #Γ (identity w) (z w (g · f) q).
    Proof.
      refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _).
      refine (amalgamation_restr a (g · f) q @ !_).
      exact (eqtohomot (functor_id Γ _) _).
    Qed.

    Proposition pi_matching_family_dep_pt_eq2
                {w y : C}
                {f : y --> x}
                {g : w --> y}
                (aa : A y (#Γ f a))
                (q : ω w (g · f))
      : # (total_psh A)
          (identity w)
          (#Γ (identity w) (z w (g · f) q)
           ,,
           #d A g (pi_matching_family_dep_pt_eq1 q) aa)
        =
        subst_matching_family_total y f aa w g q.
    Proof.
      use dep_psh_total_space_path.
      - cbn.
        refine (eqtohomot (functor_id Γ _) _ @ _).
        apply (eqtohomot (functor_id Γ _) _).
      - cbn.
        rewrite !dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        rewrite !id_left.
        apply idpath.
    Qed.

    Definition pi_matching_family_dep_pt
               {w y : C}
               {f : y --> x}
               {g : w --> y}
               (aa : A y (#Γ f a))
               (q : ω w (g · f))
      : B w (subst_matching_family_total y f aa w g q)
      := #d B
            (identity _)
            (pi_matching_family_dep_pt_eq2 aa q)
            ((zz _ _ q : dep_pi_psh_function _ _ _ _)
               _
               (identity _)
               (#d A g (pi_matching_family_dep_pt_eq1 q) aa)).

    Proposition pi_matching_family_dep_restr
                {w₁ w₂ y : C}
                {f : y --> x}
                {g₁ : w₁ --> y}
                {g₂ : w₂ --> y}
                {h : w₁ --> w₂}
                (q : h · g₂ = g₁)
                (r₁ : ω w₁ (g₁ · f))
                (r₂ : ω w₂ (g₂ · f))
                (aa : A y (#Γ f a))
                (p' : # (total_psh A) h (subst_matching_family_total y f aa w₂ g₂ r₂)
                      =
                      subst_matching_family_total y f aa w₁ g₁ r₁)
      :  #d B h p' (pi_matching_family_dep_pt aa r₂)
         =
         pi_matching_family_dep_pt aa r₁.
    Proof.
      unfold pi_matching_family_dep_pt.
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        refine (maponpaths
                  (λ (φ : dep_pi_psh_function _ _ _ _), φ w₁ _ _)
                  (matching_family_dep_restr zz _ r₁ r₂)).
        abstract
          (rewrite !assoc ;
           rewrite q ;
           apply idpath).
      }
      cbn.
      rewrite !dep_psh_mor_comp'.
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_fun_eq _ _ _ _ _ _).
        exact (id_left _ @ !(id_right _)).
      }
      rewrite dep_psh_mor_comp'.
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ _ _ _ _).
        etrans.
        {
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          - exact (h · g₂).
          - refine (eqtohomot (!(functor_comp Γ _ _)) _ @ _).
            cbn.
            rewrite q.
            refine (amalgamation_restr a _ r₁ @ _).
            refine (!_).
            rewrite id_right.
            apply (matching_family_restr z).
            rewrite assoc.
            rewrite q.
            apply idpath.
          - rewrite !id_left.
            exact (!q).
        }
        apply dep_psh_mor_comp.
      }
      cbn.
      rewrite dep_psh_mor_comp'.
      etrans.
      {
        apply maponpaths.
        apply (!(dep_pi_psh_function_natural _ _ (zz w₂ (g₂ · f) r₂) h (identity _) _)).
      }
      rewrite dep_psh_mor_comp'.
      use dep_psh_mor_path_eq.
      rewrite !id_left, id_right.
      apply idpath.
    Qed.

    Definition pi_matching_family_dep
               (y : C)
               (f : y --> x)
               (aa : A y (#Γ f a))
      : matching_family_dep B (subst_matching_family_total y f aa).
    Proof.
      use make_matching_family_dep.
      - exact (λ w g q, pi_matching_family_dep_pt aa q).
      - intros w₁ w₂ g₁ g₂ h q r₁ r₂.
        apply pi_matching_family_dep_restr.
        exact q.
    Defined.

    Definition pi_sheaf_amalgamation_fun
               (y : C)
               (f : y --> x)
               (aa : A y (#Γ f a))
      : B y (#Γ f a ,, aa)
      := dep_sheaf_amalgamation
           HB
           (site_sieve_stable f p)
           (subst_matching_family_total y f aa)
           (subst_matching_family_amalgamation y f aa)
           (pi_matching_family_dep y f aa).

    Proposition pi_sheaf_amalgamation_natural
      : is_natural_dep_pi_psh_function A B pi_sheaf_amalgamation_fun.
    Proof.
      intros y₁ y₂ f₁ f₂ aa.
      unfold pi_sheaf_amalgamation_fun.
      use (dep_sheaf_amalgamation_unique'
               HB
               (site_sieve_stable (f₁ · f₂) p)
               (a := subst_matching_family_amalgamation _ _ _)).
      intros y₃ g q.
      cbn ; unfold pi_matching_family_dep_pt ; cbn.
      refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
      cbn in q.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (maponpaths
                  (λ (φ : dep_pi_psh_function _ _ _ _), φ y₃ _ _)
                  (matching_family_dep_fam_fun_eq zz _ _)).
        apply assoc.
      }
      refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
      cbn.
      pose proof (dep_sheaf_amalgamation_restr
                    HB
                    (site_sieve_stable f₂ p)
                    (subst_matching_family_total y₁ f₂ aa)
                    (subst_matching_family_amalgamation y₁ f₂ aa)
                    (pi_matching_family_dep y₁ f₂ aa)
                    (#ω ω (identity y₃) (id_left (g · (f₁ · f₂)) @ assoc g f₁ f₂) q))
        as r.
      refine (!_).
      etrans.
      {
        simple refine (_ @ maponpaths (#d B (identity _) _) r).
        {
          rewrite dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite id_left.
          apply idpath.
        }
        use dep_psh_total_space_path.
        - refine (eqtohomot (functor_id Γ _) _ @ _).
          cbn.
          use matching_family_fam_fun_eq.
          apply assoc'.
        - cbn.
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite !id_left.
          apply idpath.
      }
      cbn.
      unfold pi_matching_family_dep_pt.
      refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_fun_eq _ _ _ _ _ _).
        apply id_left.
      }
      refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ _ _ _ _).
        refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        refine (dep_psh_mor_path_eq _ _ (pi_matching_family_dep_pt_eq1 _) _ _).
        rewrite !id_left.
        apply idpath.
      }
      refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
      cbn.
      use dep_psh_mor_path_eq.
      rewrite !id_left.
      apply idpath.
    Qed.

    Definition pi_sheaf_amalgamation_ob
      : dep_pi_psh_function A B x a.
    Proof.
      use make_dep_pi_psh_function.
      - exact pi_sheaf_amalgamation_fun.
      - exact pi_sheaf_amalgamation_natural.
    Defined.

    Proposition pi_sheaf_amalgamation_law
      : amalgamation_dep_law zz pi_sheaf_amalgamation_ob.
    Proof.
      intros y₁ f₁ q.
      use dep_pi_psh_function_eq.
      intros y₂ f₂ b.
      cbn.
      unfold pi_sheaf_amalgamation_fun.
      cbn in *.
      pose (r := #ω ω f₂ (!(id_left _)) q).
      pose (dep_sheaf_amalgamation_restr
              HB
              (site_sieve_stable (f₂ · f₁) p)
              (subst_matching_family_total
                 y₂
                 (f₂ · f₁)
                 (#d A (identity y₂)
                       (dep_pi_psh_function_mor_eq1 f₂ f₁ (amalgamation_restr a f₁ q)) b))
              (subst_matching_family_amalgamation
                 y₂
                 (f₂ · f₁)
                 (#d A (identity y₂)
                       (dep_pi_psh_function_mor_eq1 f₂ f₁ (amalgamation_restr a f₁ q)) b))
              (pi_matching_family_dep
                 y₂
                 (f₂ · f₁)
                 (#d A (identity y₂)
                    (dep_pi_psh_function_mor_eq1 f₂ f₁ (amalgamation_restr a f₁ q)) b))
              r)
        as eq.
      simple refine (_ @ maponpaths (#d B (identity _) _) eq @ _) ; clear eq.
      - rewrite dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        rewrite id_left.
        apply idpath.
      - use dep_psh_total_space_path.
        + cbn.
          refine (eqtohomot (functor_id Γ _) _ @ _).
          cbn.
          refine (!_).
          apply (matching_family_restr z).
          rewrite id_left.
          apply idpath.
        + cbn.
          rewrite !dep_psh_mor_comp'.
          apply dep_psh_mor_id'.
          rewrite !id_left.
          apply idpath.
      - cbn ; unfold pi_matching_family_dep_pt.
        rewrite dep_psh_mor_comp'.
        cbn.
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   (λ (φ : dep_pi_psh_function _ _ _ _), φ y₂ _ _)
                   (matching_family_dep_fam_fun_eq zz (id_left _) _)).
        }
        cbn.
        rewrite dep_psh_mor_comp'.
        etrans.
        {
          apply maponpaths.
          refine (maponpaths
                    (λ (φ : dep_pi_psh_function _ _ _ _), φ y₂ _ _)
                    _).
          pose (matching_family_dep_restr zz (idpath (f₂ · f₁)) (#ω ω _ (idpath _) q) q)
            as eq.
          etrans.
          {
            use (matching_family_dep_el_eq zz).
            exact (#ω ω f₂ (idpath (f₂ · f₁)) q).
          }
          cbn.
          apply maponpaths.
          exact (!eq).
        }
        do 2 refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        cbn.
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_fun_eq _ _ _ _ _ _).
          rewrite !id_left.
          apply idpath.
        }
        rewrite dep_psh_mor_comp'.
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ _ _ _ _).
          rewrite !dep_psh_mor_comp'.
          apply dep_psh_mor_id'.
          rewrite !id_left.
          apply idpath.
        }
        rewrite dep_psh_mor_comp'.
        apply dep_psh_mor_id'.
        rewrite !id_left.
        apply idpath.
    Qed.

    Definition pi_sheaf_amalgamation
      : amalgamation_dep a zz.
    Proof.
      use make_amalgamation_dep.
      - exact pi_sheaf_amalgamation_ob.
      - exact pi_sheaf_amalgamation_law.
    Defined.

    (** * 2. Uniqueness *)
    Proposition pi_sheaf_amalgamation_unique
                (aa : amalgamation_dep a zz)
      : pr1 aa = pi_sheaf_amalgamation.
    Proof.
      use dep_pi_psh_function_eq ; cbn.
      intros y f b.
      unfold pi_sheaf_amalgamation_fun.
      use (dep_sheaf_amalgamation_unique' HB _ (a := make_amalgamation _ _)).
      intros y' f' q' ; cbn.
      unfold pi_matching_family_dep_pt.
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        pose (amalgamation_dep_restr aa (f' · f) q') as r.
        exact (maponpaths (λ (φ : dep_pi_psh_function _ _ _ _), φ y' _ _) r).
      }
      cbn.
      rewrite dep_psh_mor_comp'.
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_fun_eq _ _ (pr1 aa) _ _ _).
        apply id_left.
      }
      rewrite dep_psh_mor_comp'.
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ (pr1 aa) _ _ _).
        rewrite !dep_psh_mor_comp'.
        refine (dep_psh_mor_path_eq _ _ _ _ _).
        2: rewrite !id_left ; apply idpath.
        exact (!(eqtohomot (functor_comp Γ _ _) _)).
      }
      rewrite dep_psh_mor_comp'.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (dep_pi_psh_function_natural _ _ (pr1 aa) f' f).
      }
      rewrite dep_psh_mor_comp'.
      apply dep_psh_mor_path_eq.
      rewrite !id_left.
      apply idpath.
    Qed.
  End Amalgamation.

  (** * 3. The ∏-type for sheaves *)
  Definition is_dep_sheaf_pi_dep_psh
    : is_dep_sheaf (pi_dep_psh A B).
  Proof.
    intros x ω p z a zz.
    use make_iscontr.
    - exact (pi_sheaf_amalgamation p zz).
    - intro aa.
      use amalgamation_dep_eq.
      exact (pi_sheaf_amalgamation_unique p zz aa).
  Defined.
End PiSheaf.
