Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.ModelCategories.Retract.
Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.
Require Import UniMath.CategoryTheory.ModelCategories.WFS.
Require Import UniMath.CategoryTheory.ModelCategories.WeakEquivalences.

Section modelcat.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope retract.

Definition is_model_category {M : category} (W C F : morphism_class M) :=
    is_weak_equivalences W × is_wfs C (F ∩ W) × is_wfs (C ∩ W) F.

Definition make_is_model_category {M : category} (W C F : morphism_class M) 
    (weq : is_weak_equivalences W) (cfw_wfs : is_wfs C (F ∩ W)) (cwf_wfs : is_wfs (C ∩ W) F) : is_model_category W C F :=
  make_dirprod weq (make_dirprod cfw_wfs cwf_wfs).

Definition model_category (M : category) :=
  ∑ (W C F : morphism_class M), is_model_category W C F.

Lemma isprop_is_model_category {M : category} (W C F : morphism_class M) : isaprop (is_model_category W C F).
Proof.
  apply isapropdirprod.
  apply isaprop_is_weak_equivalences.
  apply isapropdirprod; apply isaprop_is_wfs.
Defined.

Lemma is_model_category_mk' {M : category} {W C AF AC F : morphism_class M}
    (weq : is_weak_equivalences W)
    (caf : is_wfs C AF) (acf : is_wfs AC F)
    (hAF : AF = F ∩ W) (hAC : AC ⊆ W) :
    is_model_category W C F.
Proof.
  use make_is_model_category.
  - assumption. (* W are still the weak equivalences *)
  - rewrite hAF in caf. (* C and AF = F ∩ W is a WFS by assumption (caf) *)
    assumption.
  - (* suffices to show C ∩ W ⊆ AC *)
    enough (C ∩ W ⊆ AC) as cw_sac.
    {
      (* since then C ∩ W = AC *)
      assert (C ∩ W = AC) as cw_ac.
      {
        (* only need to show other inclusion *)
        apply (morphism_class_subset_antisymm cw_sac).
        (* take f ∈ AC *)
        intros a b f hf.
        split.
        - (* AC = llp F *)
          rewrite (is_wfs_llp acf) in hf.
          (* C = llp AF *)
          rewrite (is_wfs_llp caf).
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
          exact (hAC _ _ _ hf).
      }
      (* C ∩ W = AC and F are a WFS by assumption (acf) *)
      rewrite cw_ac.
      exact acf.
    }
    {
      (* we show that indeed, C ∩ W ⊆ AC *)
      intros a b f hf.
      destruct hf as [f_c f_w].

      (* factorize f through c, g : a --> c ∈ AC, h : c --> b ∈ F *)
      use ((is_wfs_fact acf) _ _ f).
      intro H.
      destruct H as [c [g [h [g_ac [h_f gh]]]]].

      (* h ∈ W by 2 out of 3 property (h ∘ g = f) *)
      assert (h_w : (W _ _) h).
      {
        (* g ∈ AC ⊆ W *)
        specialize (hAC _ _ _ g_ac) as g_w.
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
      use (wfs'lp (make_wfs C AF caf) f_c h_af g (identity b)).
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

      (* so since g ∈ AC in a WFS acf = (AC, F), so must f be *)
      exact (wfs_L_retract (make_wfs AC F acf) r g_ac).
    }
Defined.


End modelcat.