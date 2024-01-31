(** * 2-cells of algebras over a polynomial functor. *)
(**
Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021.

Derived from the code in the GitHub repository #<a href="https://github.com/HoTT/Archive/tree/master/LICS2012">#
https://github.com/HoTT/Archive/tree/master/LICS2012 #</a>#, which accompanies the paper
"_Inductive Types in Homotopy Type Theory_", by S. Awodey, N. Gambino and K. Sojakova.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Induction.FunctorAlgebras_legacy.

Local Open Scope cat.
Local Notation "a ;; b" := (funcomp a b).

Section Misc.

(** Horizontal composition of a path with a function  *)

Definition comppathwithfun {X Y Z : UU} {f_1 f_2 : X → Y} (e: f_1 = f_2) (g: Y → Z)
 : f_1 ;; g = f_2 ;; g.
Proof.
  induction e.
  apply idpath.
Defined.

(** Horizontal composition of a function with a path *)

Definition compfunwithpath {X Y Z : UU} (f : X → Y) {g_1 g_2 : Y → Z} (e : g_1 = g_2) :
  f ;; g_1 = f ;; g_2.
Proof.
  induction e.
  apply idpath.
Defined.

(** Paths and homotopies
We relate operations on paths and on homotopies using function extensionality. *)

(** Result of applying toforallpaths to a vertical composition of paths.
First done pointwise then globally. *)

Definition comppathcomphom {X Y : UU} {f g h : X → Y} (p : f = g) (q : g = h)
  : ∏ x : X, (homotcomp (toforallpaths _ f g  p) (toforallpaths _ g h q)) x
             = toforallpaths _ f h (pathscomp0 p q) x.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Definition comppathcomphom2 {X Y : UU} {f g h : X → Y} (p : f = g) (q : g = h)
  : homotcomp (toforallpaths _ f g  p) (toforallpaths _ g h q)
    = λ x : X,  toforallpaths _ f h (p @ q) x.
Proof.
  intros.
  apply funextsec.
  intro x.
  apply comppathcomphom.
Defined.

(** Result of applying funextfun on vertical composition of homotopies. *)

Definition compcomphomcomppath {X Y : UU} {f g h : X → Y} (phi : f ~ g) (psi : g ~ h)
  : funextfun _ _ (homotcomp phi psi) = (funextfun _  _ phi) @ (funextfun  _ _ psi).
Proof.
  set (p := funextfun _ _ phi).
  set (q := funextfun _ _ psi).
  set (p_flat := toforallpaths _ _ _ p).
  set (q_flat := toforallpaths _ _ _ q).
  assert (e_1 : p_flat = phi) by (apply (homotweqinvweq (weqtoforallpaths _ f g) phi)).
  assert (e_2 : q_flat = psi) by (apply (homotweqinvweq (weqtoforallpaths _ g h) psi)).
  apply (transportf (λ u, funextfun f h (homotcomp u psi) = p @ q) e_1).
  apply (transportf (λ v, funextfun f h (homotcomp p_flat v) = p @ q) e_2).
  assert (e_3 : homotcomp p_flat q_flat = λ x : X, toforallpaths _ f h (p @ q) x)
    by apply (comppathcomphom2 p q).
  apply (transportb (λ u : f ~ h, funextfun f h u = p @ q) e_3).
  apply (pathsinv0 (homotinvweqweq0 (weqtoforallpaths _ f h) (p @ q))).
Defined.

(** Result of applying toforallpaths to horizontal composition of path with a function. *)

Definition comparefuncompwithpathwithfuncompwithhomot {X Y Z : UU} {f_1 f_2 : X → Y} (g : Y → Z) (e : f_1 = f_2)
  : toforallpaths _ _ _ (comppathwithfun e g) = homotfun (toforallpaths _ _ _ e) g.
Proof.
  intros.
  induction e.
  apply idpath.
Defined.

(** Result of applying funextfun to horizontal composition of homotopy with a function. *)

Definition comparefuncompwithpathwithfuncompwithhomot2  {X Y Z : UU} {f_1 f_2 : X → Y} (g : Y → Z) (alpha : f_1 ~ f_2)
  : funextfun _ _ (homotfun alpha g) = comppathwithfun (funextfun _ _  alpha) g.
Proof.
  set (e := funextfun _ _ alpha).
  assert (p_1 : toforallpaths _ _ _ e = alpha)
    by apply (homotweqinvweq (weqtoforallpaths _ f_1 f_2) alpha).
  assert (p_2 : paths (comppathwithfun e g) (funextfun _ _ (toforallpaths _ _ _ (comppathwithfun e g))))
    by apply (homotinvweqweq0 (weqtoforallpaths _ (f_1 ;; g)(f_2 ;; g)) (comppathwithfun e g)).
  apply (transportb (λ v, funextfun (f_1 ;; g) (f_2 ;; g) (homotfun alpha g)
                          = v) p_2).
  apply maponpaths.
  apply (transportf (λ v, homotfun v g
                          = toforallpaths _ (f_1 ;; g) (f_2 ;; g) (comppathwithfun e g)) p_1).
  apply (pathsinv0 (comparefuncompwithpathwithfuncompwithhomot g e)).
Defined.

(** Result of applying toforallpaths to horizontal composition of a function with a path *)

Definition comparepathcompwithfunwithhomotcompwithfun {X Y Z : UU} (f : X → Y) {g_1 g_2 : Y → Z} (e : g_1 = g_2)
  : toforallpaths _ _ _ (compfunwithpath f e) = funhomot f (toforallpaths _ _ _ e).
Proof.
  intros.
  induction e.
  apply idpath.
Defined.

(** Result of applying funextfun to horizontal composition of a function with a homotopy *)

Definition comparehomotopycompwithfunwithpathcompwithfun {X Y Z : UU} (f : X → Y) {g_1 g_2 : Y → Z} (alpha : g_1 ~ g_2)
  : funextfun _ _  (funhomot f alpha) = compfunwithpath f (funextfun _ _  alpha).
Proof.
  set (e := funextfun _ _ alpha).
  set (e_flat := toforallpaths _ _ _ e).
  assert (p : e_flat = alpha)
    by apply (homotweqinvweq (weqtoforallpaths _ g_1 g_2) alpha).
  apply (transportf (λ u, funextfun _ _ (funhomot f u) = compfunwithpath f e) p).
  apply (transportb (λ u, funextfun (f ;; g_1) (f ;; g_2) u  = compfunwithpath f e)
                    (! (comparepathcompwithfunwithhomotcompwithfun f e))).
  apply (! (homotinvweqweq0 (weqtoforallpaths _ (f ;; g_1) (f ;; g_2)) (compfunwithpath f e))).
Defined.

(** Sigma-types and identity types *)

Definition sigmaidtoidsigma {A : UU} {B : A → UU} (c_1 c_2: total2 B)
  : total2 (λ v : pr1 c_1 = pr1 c_2, transportf B v (pr2 c_1) = pr2 c_2) → c_1 = c_2.
Proof.
  induction c_1 as [a_1 b_1].
  induction c_2 as [a_2 b_2].
  intro e.
  induction e as [u v].
  apply (total2_paths2_f u v).
Defined.

Definition idsigmatosigmaid {A : UU} {B : A → UU} (c_1 c_2 : total2 B)
  : c_1 = c_2 → total2 (λ v : pr1 c_1 = pr1 c_2, transportf B v (pr2 c_1) = pr2 c_2).
Proof.
  intro u.
  induction u.
  exists (idpath _).
  apply idpath.
Defined.

Definition idsigmaidsigma {A : UU} {B : A → UU} (c_1 c_2: total2 B) (e : c_1 = c_2)
   : sigmaidtoidsigma c_1 c_2 (idsigmatosigmaid c_1 c_2 e) = e.
Proof.
  induction e.
  apply idpath.
Defined.

Definition sigmaidsigmaid {A : UU} {B : A → UU} (c_1 c_2: total2 B)
                          (e : total2 (λ v : pr1 c_1 = pr1 c_2, transportf B v (pr2 c_1) = pr2 c_2))
  : idsigmatosigmaid _ _ (sigmaidtoidsigma c_1 c_2 e) = e.
Proof.
  induction c_1 as [a_1 b_1].
  induction c_2 as [a_2 b_2].
  induction e as [u v].
  simpl in u, v.
  induction u, v.
  apply idpath.
Defined.

Definition isweqsigmaidtoidsigma {A : UU} {B : A → UU} (c_1 c_2 : total2 B)
  : isweq (sigmaidtoidsigma c_1 c_2).
Proof.
  apply (isweq_iso (sigmaidtoidsigma c_1 c_2) (idsigmatosigmaid c_1 c_2)).
  apply (sigmaidsigmaid c_1 c_2).
  apply (idsigmaidsigma c_1 c_2).
Defined.

Definition weqsigmaidtoidsigma {A : UU} {B : A → UU} (c_1 c_2 : total2 B)
  : total2 (λ v : pr1 c_1 = pr1 c_2, transportf B v (pr2 c_1) = pr2 c_2) ≃ (c_1 = c_2).
Proof.
  unfold weq.
  exists (sigmaidtoidsigma c_1 c_2).
  apply isweqsigmaidtoidsigma.
Defined.

End Misc.

Section PolynomialFunctor.

Context {A: UU} (B: A → UU).

Notation P := (polynomial_functor A B).

(** Action of P on paths *)

Let P_2 {X Y : UU} {f g : X → Y} (p: f = g): # P f = # P g.
Proof.
  apply maponpaths.
  assumption.
Defined.

(** We define an action of P on homotopies. For this we need an auxiliary map. *)

Definition tau {X Y : UU} {f g : X → Y} (x : A) (u : B x → X) (v : ∏ (y : B x), f (u y) = g (u y))
  : x,, u ;; f = tpair (λ a : A, B a → Y) x (u ;; g).
Proof.
  apply maponpaths.
  apply funextfun.
  intro.
  apply v.
Defined.

(** We record the effect of the computation rules on tau. *)

Definition tau_comp {X Y : UU} {f : X → Y} (x : A) (u : B x → X)
  : tau x u (λ y : B x, idpath (f (u y))) = idpath (x ,, u ;; f).
Proof.
  unfold tau.
  assert (e : idpath (u ;; f) = funextfun _ _ (λ y : B x, idpath (f (u y)))).
  {
    apply homotinvweqweq0.
  }
  set (C := λ (p : u ;; f = u ;; f)
              , pair_path_in2 (λ a : A, B a → Y) p = idpath _).
  apply (transportf C e).
  apply idpath.
Defined.

(** Action of P on homotopies *)

Definition P_2_h {X Y : UU} {f g : X → Y} (h: f ~ g): # P f ~ # P g.
Proof.
  intro c.
  induction c as [x u].
  apply (tau x u (λ y : B x, h (u y))).
Defined.

(** The result of applying toforallpaths to P(e), where e is a path *)

Definition compareP2withP2h {X Y : UU} {f g : X → Y} (e : f = g) :
 toforallpaths _ _ _ (P_2 e) = P_2_h (toforallpaths _ _ _ e).
Proof.
  induction e.
  cbn - [P].
  apply funextsec.
  intro c.
  induction c as [x u].
  unfold P_2_h.
  apply (transportb (λ e, idpath (# P f (x ,, u)) = e) (tau_comp x u)).
  apply idpath.
Defined.

(** The result of applying P_h(alpha), where alpha is a homotopy *)

Definition compareP2withP2h2 {X Y : UU} {f g : X → Y} (alpha : f ~ g) :
  P_2 (funextfun _ _ alpha) = funextfun _ _ (P_2_h alpha).
Proof.
  set (e := funextfun _ _ alpha).
  set (e_flat := toforallpaths _ _ _ e).
  assert (p_1 : e_flat = alpha).
  {
  apply (homotweqinvweq (weqtoforallpaths _ f g) alpha).
  }
  assert (p_2 : funextfun _  _ (P_2_h alpha) = funextfun _  _ (P_2_h e_flat)).
  {
    do 2 apply maponpaths.
    apply (pathsinv0 p_1).
  }
  apply (transportb (λ u, P_2 e = u) p_2).
  assert (p_3 : funextfun _ _ (P_2_h e_flat) = (funextfun _ _ (toforallpaths _ _ _ (P_2 e)))).
  {
    apply maponpaths.
    apply (pathsinv0 (compareP2withP2h e)).
  }
  apply (transportb (λ u, P_2 e = u) p_3).
  apply homotinvweqweq0.
Defined.

(** The type of algebra 2-cells between two algebra maps. An algebra 2-cell is a pair
 consisting of a path between the underlying functions and a path witnessing a coherence
condition *)

Definition isalg2cell {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY) (e: pr1 ff = pr1 gg)
  : UU := pr2 ff @ (comppathwithfun (maponpaths (# P) e) (pr2 YY))
          = compfunwithpath (alg_map P XX) e @ (pr2 gg).

Definition algebra_2cell {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY)
  : UU := ∑ (e: pr1 ff = pr1 gg), isalg2cell _ _  e.

(** Analysis of algebra 2-cells
We compare
 - Paths between algebra maps
 - Pairs of paths involving transport
 - Algebra 2-cells

 Using this one shows that two algebra maps are equal iff
 there is an algebra 2-cell between them. *)

(** Alternative definition of algebra 2-cell. An alternative
 algebra 2-cell from (f,s_f) to (g,s_g) is a pair (e,s_e)
 where e : f = g and s_e : e_!(s_f) = s_g. *)

Definition isalg2cellalt {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY) (e : pr1 ff = pr1 gg)
  : UU := transportf (is_algebra_mor P XX YY) e (pr2 ff) = pr2 gg.

Definition algebra_2cellalt {XX YY : algebra_ob P}(ff gg : algebra_mor P XX YY)
  : UU := ∑ (e: pr1 ff = pr1 gg), isalg2cellalt ff gg e.

(** For each e : f = g, the map isalg2cell(e) -→ e_!(s_f) = s_g *)

Definition fiberwise2cellto2cellalt {XX YY: algebra_ob P} (ff gg : algebra_mor P XX YY) (e: pr1 ff = pr1 gg)
 : isalg2cell ff gg e → isalg2cellalt ff gg e.
Proof.
  induction ff as [f s_f].
  induction gg as [g s_g].
  simpl in e.
  unfold isalg2cellalt.
  induction e.
  intro p.
  change (s_f = s_g).
  apply (transportf (λ u, u = s_g) (pathscomp0rid s_f)).
  apply p.
Defined.

(** For each e, the map constructed above is a weak equivalence. *)

Definition isweqfiberwise2cellto2cellalt {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY) (e : pr1 ff = pr1 gg)
  : isweq (fiberwise2cellto2cellalt ff gg e).
Proof.
  induction ff as [f s_f].
  induction gg as [g s_g].
  simpl in e.
  unfold fiberwise2cellto2cellalt.
  induction e.
  simpl.
  apply (isweqtransportf (λ u, u = s_g) (pathscomp0rid s_f)).
Defined.

Definition weqfiberwise2cellto2cellalt  {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY) (e : pr1 ff = pr1 gg)
  : isalg2cell ff gg e ≃ isalg2cellalt ff gg e.
Proof.
  exists (fiberwise2cellto2cellalt ff gg e).
  apply isweqfiberwise2cellto2cellalt.
Defined.

(** The map from standard to alternative 2-cells, taking total spaces. *)

Definition from2cellto2cellalt  {XX YY: algebra_ob P} (ff gg : algebra_mor P XX YY)
  : algebra_2cell ff gg → algebra_2cellalt ff gg.
Proof.
  intro ee.
  apply (totalfun _ _ (fiberwise2cellto2cellalt ff gg) ee).
Defined.

(** This map is a weak equivalence because it is fiberwise a weak equivalence *)

Definition isweqfrom2cellto2cellalt {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY)
  : isweq (from2cellto2cellalt ff gg).
Proof.
  apply (isweqfibtototal _ _ (weqfiberwise2cellto2cellalt ff gg)).
Defined.

Definition weqfrom2cellto2cellalt {XX YY: algebra_ob P} (ff gg : algebra_mor P XX YY)
 : algebra_2cell ff gg ≃ algebra_2cellalt ff gg.
Proof.
  exists (from2cellto2cellalt ff gg).
  apply isweqfrom2cellto2cellalt.
Defined.

(** As a special case of the general results obtained before for Id/Sigma we get
 that there is a weak equivalence between alternative algebra 2-cells and paths
 between algebra maps. *)

Definition weqfrom2cellalttoidalgmap {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY)
  : algebra_2cellalt ff gg ≃ ff = gg.
Proof.
  apply weqsigmaidtoidsigma.
Defined.

(* Composing with the previous weak equivalence, we obtain that there is a weak
 equivalence between algebra 2-cells and paths between algebra maps. *)

Definition weqfromalg2celltoidalgmap {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY)
  : algebra_2cell ff gg ≃ ff = gg.
Proof.
  exact (weqcomp (weqfrom2cellto2cellalt ff gg) (weqfrom2cellalttoidalgmap ff gg)).
Defined.

Definition weqfromaidalgmaptoalg2cell {XX YY : algebra_ob P} (ff gg : algebra_mor P XX YY)
  : weq (ff = gg) (algebra_2cell ff gg).
Proof.
  exact (invweq (weqfromalg2celltoidalgmap ff gg)).
Defined.

(** The type of algebra map homotopies *)

Definition isalgmaphomotopy {X : UU} {s_X : P X → X} {Y : UU} {s_Y : P Y → Y}
                            (f : X → Y) (sigma_f : s_X ;; f ~ # P f ;; s_Y)
                            (g : X → Y) (sigma_g : s_X ;; g ~ # P g ;; s_Y)
                            (alpha : f ~ g) : UU
 := homotcomp (funhomot s_X alpha) (sigma_g) ~ homotcomp (sigma_f) (homotfun (P_2_h alpha) s_Y).

Definition immisalghomotopy {X : UU} {s_X : P X → X} {Y : UU} {s_Y : P Y → Y}
                            (f : X → Y) (sigma_f : s_X ;; f ~ # P f ;; s_Y)
                            (g : X → Y) (sigma_g : s_X ;; g ~ # P g ;; s_Y)
                            (alpha : f ~ g)
  : isalgmaphomotopy f sigma_f g sigma_g alpha
    → homotcomp (funhomot s_X alpha) (sigma_g) = (homotcomp (sigma_f) (homotfun (P_2_h alpha) s_Y)).
Proof.
  intro is.
  apply funextsec.
  intro c.
  apply (is c).
Defined.

(* We show that if we have an algebra map homotopy we can construct an algebra 2-cell
 This is a long equational reasoning, which uses what has been done on relating paths
and homotopies. *)

Definition alghomotopytoalg2cell {X : UU} {s_X : P X → X} {Y : UU} {s_Y : P Y → Y}
                                 (f : X → Y) (sigma_f : s_X ;; f ~ # P f ;; s_Y)
                                 (g : X → Y) (sigma_g : s_X ;; g ~ # P g ;; s_Y)
                                 (alpha : f ~ g)
  : isalgmaphomotopy f sigma_f g sigma_g alpha →
       isalg2cell (tpair (is_algebra_mor P (X ,, s_X) (tpair _ Y s_Y)) f (funextfun _ _ sigma_f))
                  (g ,, (funextfun _ _ sigma_g)) (funextfun f g alpha).
Proof.
  intro is.
  set (s_alpha := immisalghomotopy f sigma_f g sigma_g alpha is).
  set (XX := X ,, s_X : algebra_ob P).
  set (YY := Y ,, s_Y : algebra_ob P).
  set (sigma_f_sharp := (funextfun (s_X ;; f) (# P f ;; s_Y) sigma_f)).
  set (sigma_g_sharp := (funextfun (s_X ;; g) (# P g ;; s_Y) sigma_g)).
  set (alpha_sharp := (funextfun f g alpha)).
  unfold isalg2cell.
  simpl.
  assert (e_1 : P_2 alpha_sharp = funextfun _ _ (P_2_h alpha)).
  {
    apply compareP2withP2h2.
  }
  apply (transportb (λ u, sigma_f_sharp @ (comppathwithfun u s_Y)
                       = compfunwithpath s_X alpha_sharp @ sigma_g_sharp) e_1).
  assert (e_2 : funextfun _ _  (funhomot s_X alpha) = compfunwithpath s_X alpha_sharp).
  {
     apply comparehomotopycompwithfunwithpathcompwithfun.
  }
  apply (transportf (λ u, sigma_f_sharp @ (comppathwithfun (funextfun (# P f) (# P g) (P_2_h alpha)) s_Y)
                                          = u @ sigma_g_sharp) e_2).
  unfold sigma_g_sharp.
  assert (e_3 : funextfun _ _ (homotcomp (funhomot s_X alpha) sigma_g)
                = (funextfun _ _ (funhomot s_X alpha)) @ (funextfun _ _ sigma_g)).
  {
    apply (compcomphomcomppath (funhomot s_X alpha) sigma_g).
  }
  apply (transportf (λ u, sigma_f_sharp @ (comppathwithfun (funextfun (# P f) (# P g) (P_2_h alpha)) s_Y) = u) e_3).
  assert (e_4 : funextfun _ _ (homotfun (P_2_h alpha) s_Y) = comppathwithfun (funextfun _ _ (P_2_h alpha)) s_Y).
  {
    apply (comparefuncompwithpathwithfuncompwithhomot2 s_Y (P_2_h alpha)).
  }
  apply (transportf (λ u, sigma_f_sharp @ u
                          = (funextfun (s_X ;; f) (# P g ;; s_Y) (homotcomp (funhomot s_X alpha) sigma_g))) e_4).
  assert (e_5 : sigma_f_sharp @ funextfun _ _ (homotfun (P_2_h alpha) s_Y)
                = funextfun _ _ (homotcomp sigma_f (homotfun (P_2_h alpha) s_Y))).
  {
    apply (pathsinv0 (compcomphomcomppath sigma_f (homotfun (P_2_h alpha) s_Y))).
  }
  apply (transportb (λ u, u = (funextfun (s_X ;; f) (# P g ;; s_Y)
                    (homotcomp (funhomot s_X alpha) sigma_g))) e_5).
  apply maponpaths.
  apply (pathsinv0 s_alpha).
Defined.

End PolynomialFunctor.
