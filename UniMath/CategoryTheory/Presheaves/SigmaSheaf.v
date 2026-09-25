(**

 ∑-types of sheaves

 We show that sheaves are closed under ∑-types. In essence, the proof is mostly the
 same as the proof that sheaves are closed under binary products, but it is slightly
 more complicated due to the involved dependencies.

 Content
 1. Matching families in ∑-types
 2. The amalgamation in the ∑-type
 3. Sheaves are closed under ∑-types

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SigmaTypes.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.

Local Open Scope cat.

(** * 1. Matching families in ∑-types *)
Definition pr1_sigma_matching_family
           {C : site}
           {Γ : C^op ⟶ SET}
           {A : dep_psh Γ}
           {B : dep_psh (total_psh A)}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (zz : matching_family_dep (sigma_dep_psh A B) z)
  : matching_family_dep A z.
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, pr1 (zz y f p)).
  - intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn.
    exact (path_sigma_dep_psh_pr1 _ _ (matching_family_dep_restr zz p q₁ q₂)).
Defined.

Definition pr2_sigma_matching_family
           {C : site}
           {Γ : C^op ⟶ SET}
           {A : dep_psh Γ}
           {B : dep_psh (total_psh A)}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (zz : matching_family_dep (sigma_dep_psh A B) z)
  : matching_family_dep B (make_matching_family_total_psh z (pr1_sigma_matching_family zz)).
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, pr2 (zz y f p)).
  - intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn.
    pose (path_sigma_dep_psh_pr2 _ _ (!(matching_family_dep_restr zz p q₁ q₂))) as q.
    cbn in q.
    simple refine (_ @ maponpaths (#d B (identity _) _) (!q) @ _).
    + cbn.
      rewrite !dep_psh_mor_comp'.
      use dep_psh_mor_path_eq.
      rewrite !id_left.
      apply idpath.
    + use dep_psh_total_space_path.
      * exact (eqtohomot (functor_id Γ _) _).
      * cbn.
        rewrite !dep_psh_mor_comp'.
        apply dep_psh_mor_id'.
        rewrite id_left.
        apply idpath.
    + cbn.
      apply dep_psh_mor_id'.
      apply idpath.
Defined.

Section SigmaSheaf.
  Context {C : site}
          {Γ : C^op ⟶ HSET}
          {A : dep_psh Γ}
          (HA : is_dep_sheaf A)
          {B : dep_psh (total_psh A)}
          (HB : is_dep_sheaf B).

  (** * 2. The amalgamation in the ∑-type *)
  Section Amalgamation.
    Context {x : C}
            {ω : sieve x}
            (p : C x ω)
            {z : matching_family Γ ω}
            {a : amalgamation z}
            (zz : matching_family_dep (sigma_dep_psh A B) z).

    Definition sigma_sheaf_amalgamation_ob
      : sigma_dep_psh A B x a.
    Proof.
      simple refine (_ ,, _).
      - exact (dep_sheaf_amalgamation HA p z a (pr1_sigma_matching_family zz)).
      - exact (dep_sheaf_amalgamation
                 HB
                 p
                 (make_matching_family_total_psh z (pr1_sigma_matching_family zz))
                 (make_amalgamation_total_psh
                    (dep_sheaf_amalgamation_dep HA p z a (pr1_sigma_matching_family zz)))
                 (pr2_sigma_matching_family zz)).
    Defined.

    Proposition sigma_sheaf_amalgamation_law
      : amalgamation_dep_law zz sigma_sheaf_amalgamation_ob.
    Proof.
      intros y f q ; cbn.
      use path_sigma_dep_psh_ob.
      - cbn.
        exact (dep_sheaf_amalgamation_restr HA p z a (pr1_sigma_matching_family zz) q).
      - cbn.
        pose (dep_sheaf_amalgamation_restr
                HB
                p
                (make_matching_family_total_psh z (pr1_sigma_matching_family zz))
                (make_amalgamation_total_psh
                   (dep_sheaf_amalgamation_dep HA p z a (pr1_sigma_matching_family zz)))
                (pr2_sigma_matching_family zz)
                q)
          as r.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!r).
        }
        cbn.
        rewrite dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        apply id_left.
    Qed.

    Definition sigma_sheaf_amalgamation
      : amalgamation_dep a zz.
    Proof.
      use make_amalgamation_dep.
      - exact sigma_sheaf_amalgamation_ob.
      - exact sigma_sheaf_amalgamation_law.
    Defined.

    Arguments sigma_sheaf_amalgamation_ob /.
    Arguments sigma_sheaf_amalgamation /.

    Proposition sigma_sheaf_amalgamation_unique
                (aa : amalgamation_dep a zz)
      : aa = sigma_sheaf_amalgamation.
    Proof.
      use amalgamation_dep_eq.
      use path_sigma_dep_psh_ob.
      - use (dep_sheaf_amalgamation_unique' HA p).
        intros y f q ; cbn.
        exact (path_sigma_dep_psh_pr1 _ _ (amalgamation_dep_restr aa f q)).
      - use (dep_sheaf_amalgamation_unique
                HB
                p
                (a := make_amalgamation _ _)).
        + exact (make_matching_family_total_psh z (pr1_sigma_matching_family zz)).
        + cbn.
          intros y f q ; cbn.
          use dep_psh_total_space_path.
          * cbn.
            exact (amalgamation_restr a f q).
          * cbn.
            rewrite dep_psh_mor_comp'.
            refine (_ @ maponpaths pr1 (amalgamation_dep_restr aa f q)).
            cbn.
            use dep_psh_mor_path_eq.
            rewrite id_left.
            apply idpath.
        + exact (pr2_sigma_matching_family zz).
        + intros y f q ; cbn.
          refine (_ @ !(path_sigma_dep_psh_pr2 _ _ (!(amalgamation_dep_restr aa f q)))).
          cbn.
          rewrite dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite id_left.
          apply idpath.
        + intros y f q ; cbn.
          pose (dep_sheaf_amalgamation_restr
                  HB
                  p
                  (make_matching_family_total_psh z (pr1_sigma_matching_family zz))
                  (make_amalgamation_total_psh
                     (dep_sheaf_amalgamation_dep HA p z a (pr1_sigma_matching_family zz)))
                  (pr2_sigma_matching_family zz)
                  q)
            as r.
          refine (_ @ r).
          cbn.
          rewrite dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite id_right.
          apply idpath.
    Qed.
  End Amalgamation.

  (** * 3. Sheaves are closed under ∑-types *)
  Definition is_dep_sheaf_sigma_dep_psh
    : is_dep_sheaf (sigma_dep_psh A B).
  Proof.
    intros x ω p z a zz.
    use make_iscontr.
    - exact (sigma_sheaf_amalgamation p zz).
    - exact (sigma_sheaf_amalgamation_unique p zz).
  Defined.
End SigmaSheaf.
