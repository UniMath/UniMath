Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Require Import UniMath.CategoryTheory.limits.cones.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.


Section ColimitsAsLimits.

  Definition graph_op (g : graph)
    : graph.
  Proof.
    exists (pr1 g).
    exact (λ v1 v2, pr2 g v2 v1).
  Defined.

  Definition edge_op {g : graph} {v w : pr1 g} (e : pr2 g v w)
    : pr2 (graph_op g) w v := e.

  Definition diagram_op
             {C : category}
             {g : graph} (d : diagram g C)
    : diagram (graph_op g) (opp_cat C).
  Proof.
    exists (λ v, pr1 d v).
    exact (λ v1 v2 e, pr2 d v2 v1 (edge_op e)).
  Defined.

  Definition cone_op
             {C : category}
             {g : graph} {d : diagram g C}
             {c : C} (cc : cone d c)
    : cocone (diagram_op d) c.
  Proof.
    exists (λ v, pr1 cc v).
    exact (λ v w e, pr2 cc w v e).
  Defined.

  Definition cocone_op
             {C : category}
             {g : graph} {d : diagram g C}
             {c : C} (cc : cocone d c)
    : cone (diagram_op d) c.
  Proof.
    exists (λ v, pr1 cc v).
    exact (λ v w e, pr2 cc w v e).
  Defined.

  Definition iscolimcocone_op
             {C : category} {g : graph} {d : diagram g C}
             {c : C} {cc : cocone d c} (cc_lim : isColimCocone d c cc)
    : isLimCone (diagram_op d) c (cocone_op cc).
  Proof.
    intros c0 cc0.
    apply (cc_lim c0 (cone_op cc0)).
  Defined.

  Definition islimcone_op
             {C : category} {g : graph} {d : diagram g C}
             {c : C} {cc : cone d c} (cc_lim : isLimCone d c cc)
    : isColimCocone (diagram_op d) c (cone_op cc).
  Proof.
    intros c0 cc0.
    apply (cc_lim c0 (cocone_op cc0)).
  Defined.

  Definition LimCone_op
             {C : category} {g : graph} {d : diagram g C}
             (cc : LimCone d)
    : ColimCocone (diagram_op d).
  Proof.
    exists (pr1 (pr1 cc) ,, cone_op (pr2 (pr1 cc))).
    exact (islimcone_op (pr2 cc)).
  Defined.

  Definition chain_op {C : category} (ch : chain C)
    : cochain (opp_cat C).
  Proof.
    exists (λ v, pr1 ch v).
    exact (λ v w e, pr2 ch w v (edge_op e)).
  Defined.

  Definition cochain_op {C : category} (ch : cochain C)
    : chain (opp_cat C).
  Proof.
    exists (λ v, pr1 ch v).
    exact (λ v w e, pr2 ch w v (edge_op e)).
  Defined.

  Definition islimcone_chain_op
             {C : category} {g : chain C}
             {c : C} {cc : cone g c} (cc_lim : isLimCone g c cc)
    : isColimCocone (chain_op g) c (cone_op cc).
  Proof.
    apply (islimcone_op cc_lim).
  Defined.

  Definition islimcone_cochain_op
             {C : category} {g : cochain C}
             {c : C} {cc : cone g c} (cc_lim : isLimCone g c cc)
    : isColimCocone (cochain_op g) c (cone_op cc).
  Proof.
    apply (islimcone_op cc_lim).
  Defined.

  Definition iscolimcocone_chain_op
             {C : category} {g : chain C}
             {c : C} {cc : cocone g c} (cc_lim : isColimCocone g c cc)
    : isLimCone (chain_op g) c (cocone_op cc).
  Proof.
    apply (iscolimcocone_op cc_lim).
  Defined.

  Definition is_omega_cont_op
             {C D : category} {F : functor C D}
             (oc : is_omega_cont F)
    : is_omega_cocont (functor_op F).
  Proof.
    intros ch c cc.
    set (t := oc (chain_op ch) c (cocone_op cc)).
    intro col.
    set (tt := iscolimcocone_chain_op col).
    intros c0 cc0.
    apply (t tt c0 (cocone_op cc0)).
  Defined.

  Definition is_omega_cocont_op
             {C D : category} {F : functor C D}
             (oc : is_omega_cocont F)
    : is_omega_cont (functor_op F).
  Proof.
    intros ch c cc.
    set (t := oc (cochain_op ch) c (cone_op cc)).
    intro lm.
    set (tt := islimcone_cochain_op lm).
    intros c0 cc0.
    apply (t tt c0 (cone_op cc0)).
  Defined.

  Definition is_cont_op
             {C D : category} {F : functor C D}
             (oc : is_cont F)
    : is_cocont (functor_op F).
  Proof.
    intros g d c cc.
    set (t := oc _ _ c (cocone_op cc)).
    intro lm.
    set (tt := iscolimcocone_op lm).
    intros c0 cc0.
    apply (t tt c0 (cocone_op cc0)).
  Defined.

  Definition is_cocont_op
             {C D : category} {F : functor C D}
             (oc : is_cocont F)
    : is_cont (functor_op F).
  Proof.
    intros g d c cc.
    set (t := oc _ _ c (cone_op cc)).
    intro lm.
    set (tt := islimcone_op lm).
    intros c0 cc0.
    apply (t tt c0 (cone_op cc0)).
  Defined.

End ColimitsAsLimits.
