Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.SyntheticHomotopyTheory.Circle2.
Require Import UniMath.SyntheticHomotopyTheory.AffineLine.
Require Import UniMath.NumberSystems.Integers.
Local Open Scope hz.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.GroupAction.
Local Open Scope abgr.
Local Open Scope action_scope.
Local Notation "0" := (toℤ 0).
Local Notation "1" := (toℤ 1).

Section A.

  Goal ∏ (X:Type) (f := eqweqmap (idpath X)), f = idweq X.
    reflexivity. Qed.

  Goal ∏ (X:Type), invmap (idweq X) = idfun X.
    reflexivity. Qed.

  Goal ∏ (X:Type) (x:X), iscontrpr1 (iscontrcoconusfromt X x) = (x,,idpath x).
    reflexivity. Qed.

  Goal ∏ (X:Type) (x:X), iscontrpr1 (iscontrcoconustot X x) = (x,,idpath x).
    reflexivity. Qed.

  Goal ∏ (X Y:Type) (f:X≃Y), invmap (invweq f) = f.
    reflexivity. Qed.

  Goal ∏ (X Y Z:Type) (f:X≃Y) (g:Y≃Z), pr1weq (weqcomp f g) = funcomp f g.
    reflexivity. Qed.

  Goal ∏ (X Y Z:Type) (f:X≃Y) (g:Y≃Z), invmap (weqcomp f g) = funcomp (invmap g) (invmap f).
    reflexivity. Qed.

  Goal ∏ {X : UU} (P Q : X -> Type) (f : ∏ x, P x ≃ Q x) (x:X) (p:P x), weqfibtototal _ _ f (x,,p) = (x,,f x p).
    reflexivity. Qed.

  Goal ∏ {X : UU} (P Q : X -> Type) (f : ∏ x, P x ≃ Q x) (x:X) (q:Q x), invmap (weqfibtototal _ _ f) (x,,q) = (x,,invmap (f x) q).
    reflexivity. Qed.

  Goal ∏ {X Y : Type} (w : X ≃ Y) (is : iscontr Y), iscontrpr1 (iscontrweqb w is) = invmap w (iscontrpr1 is).
    reflexivity. Qed.

  Goal ∏ {X Y : Type} (w : X ≃ Y) (is : iscontr X), iscontrpr1 (iscontrweqf w is) = w (iscontrpr1 is).
    reflexivity. Qed.

  Goal ∏ (X:Type) (i : isConnected X) (P:X->hProp) (x0:X) (p:P x0), predicateOnConnectedType X i P x0 p x0 = p.
    Fail reflexivity. Abort.

  Goal ∏ (X:Type) (i : iscontr X) (x0 := pr1 i : X), pr2 i x0 = idpath x0.
    Fail reflexivity. Abort.

  Goal ∏ (X Y:Type) (p:X=Y) (x:X), eqweqmap p x = cast p x.
    Fail reflexivity. Abort.

  Goal ∏ (X Y:Type) (p:X=Y) (x:X), eqweqmap p x = transportf (λ T, T) p x.
    Fail reflexivity. Abort.

  Goal ∏ {X:Type} (bc : BaseConnected X) (t := pr1 bc : X), pr2 (baseConnectedness X bc) t t = hinhpr (idpath t).
    Fail reflexivity.
  Abort.

  Goal ∏ (G:gr), pr1 (BaseConnected_BG G) = trivialTorsor G.
    reflexivity.
  Qed.

  Goal ∏ (G:gr), pr2 (BaseConnected_BG G) (trivialTorsor G)
                 = hinhpr (idpath (trivialTorsor G)).
    Fail reflexivity.
  Abort.

  Goal ∏ (n:ℤ), (n+0 = n)%hz.
    Fail reflexivity.
  Abort.

  Goal ∏ (n:ℤ), (0+n = n)%hz.
    Fail reflexivity.
  Abort.

  Goal ∏ (X : UU) (P : hProp) (f : X → P) (x : X), hinhuniv f (hinhpr x) = f x.
    reflexivity.
  Qed.

End A.
