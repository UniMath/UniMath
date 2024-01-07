Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.ModelCategories.Lifting.
Require Import UniMath.CategoryTheory.ModelCategories.Retract.
Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.
Require Import UniMath.CategoryTheory.ModelCategories.WFS.
Require Import UniMath.CategoryTheory.ModelCategories.WeakEquivalences.

Section modelcat.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope retract.

Definition is_model_category {C : category} (W K F : morphism_class C) :=
    is_weak_equivalences W × is_wfs K (F ∩ W) × is_wfs (K ∩ W) F.

Definition make_is_model_category {C : category} (W K F : morphism_class C) 
    (weq : is_weak_equivalences W) (cfw_wfs : is_wfs K (F ∩ W)) (cwf_wfs : is_wfs (K ∩ W) F) : is_model_category W K F :=
  make_dirprod weq (make_dirprod cfw_wfs cwf_wfs).

Definition model_category (C : category) :=
  ∑ (W K F : morphism_class C), is_model_category W K F.

Lemma isprop_is_model_category {C : category} (W K F : morphism_class C) : isaprop (is_model_category W K F).
Proof.
  apply isapropdirprod.
  apply isaprop_is_weak_equivalences.
  apply isapropdirprod; apply isaprop_is_wfs.
Defined.

Lemma is_model_category_mk' {C : category} {W K AF AK F : morphism_class C}
    (weq : is_weak_equivalences W)
    (kaf : is_wfs K AF) (akf : is_wfs AK F)
    (hAF : AF = F ∩ W) (hAK : AK ⊆ W) :
    is_model_category W K F.
Proof.
  use make_is_model_category.
  - assumption. (* W are still the weak equivalences *)
  - rewrite hAF in kaf. (* K and AF = F ∩ W is a WFS by assumption (caf) *)
    assumption.
  - (* suffices to show K ∩ W ⊆ AK *)
    enough (K ∩ W ⊆ AK) as kw_sak.
    {
      (* since then K ∩ W = AK *)
      assert (K ∩ W = AK) as kw_ak.
      {
        (* only need to show other inclusion *)
        apply (morphism_class_subset_antisymm kw_sak).
        (* take f ∈ AC *)
        intros a b f hf.
        split.
        - (* AC = llp F *)
          rewrite (is_wfs_llp akf) in hf.
          (* C = llp AF *)
          rewrite (is_wfs_llp kaf).
          (* so now goal is llp F ⊆ llp AF *)
          revert a b f hf.
          (* use antisymmetry of llp to convert goal into AF ⊆ F *)
          apply llp_anti.
          intros x y g hg.
          (* this is trivial, since AF = F ∩ W, but requires some work in UniMath *)
          rewrite hAF in hg.
          destruct hg as [hgf ?].
          exact hgf.
        - (* f ∈ AC ⊆ W (by hAC) *)
          exact (hAK _ _ _ hf).
      }
      (* K ∩ W = AK and F are a WFS by assumption (akf) *)
      rewrite kw_ak.
      exact akf.
    }
    {
      (* we show that indeed, C ∩ W ⊆ AC *)
      intros a b f hf.
      destruct hf as [f_k f_w].

      (* factorize f through c, g : a --> c ∈ AK, h : c --> b ∈ F *)
      set (acf_fact := (is_wfs_fact akf) _ _ f).
      use (hinhuniv _ acf_fact).
      clear acf_fact; intro acf_fact.
      destruct acf_fact as [c [g [h [g_ak [h_f gh]]]]].

      (* h ∈ W by 2 out of 3 property (h ∘ g = f) *)
      assert (h_w : (W _ _) h).
      {
        (* g ∈ AC ⊆ W *)
        specialize (hAK _ _ _ g_ak) as g_w.
        apply ((is_weq_cancel_left weq) _ _ _ _ _ g_w).
        rewrite gh.
        exact f_w.
      }
      
      (* h ∈ AF because AF = F ∩ W and h ∈ F by definition *)
      assert (h_af : (AF _ _) h).
      {
        rewrite hAF.
        split.
        - exact h_f.
        - exact h_w.
      }
      
      (* extract lift l from
            g
        a ----> c
        | l   / |
      f |   /   | h
        v /     v
        b ===== b
      *)
      use (wfs'lp (make_wfs K AF kaf) f_k h_af g (identity b)).
      {
        (* commutativity of diagram *)
        rewrite id_right.
        exact gh.
      }

      intros hl.
      destruct hl as [l [hl1 hl2]].

      (* this uses the retract argument
        a ===== a ===== a
        |       |       |
      f |       | g     | f
        v       v       v
        b ----> c ----> b
            l       h
        to show that f is a retract of g
      *)
      assert (r : retract g f).
      {
        use (make_retract (identity a) (identity a) l h).
        use make_is_retract.
        - now rewrite id_left.
        - assumption.
        - rewrite id_left. now symmetry.
        - rewrite id_left. now symmetry.
      }

      (* so since g ∈ AK in a WFS acf = (AK, F), so must f be *)
      exact (wfs_L_retract (make_wfs AK F akf) r g_ak).
    }
Qed.


End modelcat.