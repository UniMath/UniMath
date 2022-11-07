(**
This line is there to enforce that all tactics are used either on a single focused goal or with a local selector ("strict focusing mode").

Hence, it enforces an element of UniMath coding style.

Do not copy this line into the files but put
[[Require Export UniMath.Tactics.EnsureStructuredProofs.]]
into the header part.
 *)

Export Set Default Goal Selector "!".
